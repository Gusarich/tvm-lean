import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFNOTREF

/-
IFNOTREF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Ifnotref.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xe301` decode with `takeRefInv`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifnotref _` rejected by assembler)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_do_with_cell(..., "IFNOTREF")` + negate lambda in opcode `0xe301`)

Branch map covered by this suite:
- decode branch:
  - `0xe301` with at least one attached ref decodes to `.ifnotref`;
  - missing ref is `.invOpcode` before stack bool checks.
- dispatch branch:
  - only `.ifnotref` is handled by `execInstrFlowIfnotref`; others fall through.
- execution branch:
  - pop order: exactly one `popBool` from stack;
  - negate split: `0` => taken (call ref continuation), non-zero => skipped;
  - taken-only side effect: `registerCellLoad` + call transition;
  - skipped branch must not load the referenced cell.
- error ordering branch:
  - with present ref, bool pop errors (`stkUnd`/`typeChk`/`intOv`) occur at pop site;
  - with missing ref in code cell, decode fails first (`invOpcode`) regardless of stack shape.
-/

private def ifnotrefId : InstrId := { name := "IFNOTREF" }

private def ifnotrefOpcode : Nat := 0xe301

private def dispatchSentinel : Int := 33033

private def tailMarker : Int := 717

private def branchMarker : Int := 4041

private def q0 : Value :=
  .cont (.quit 0)

private def refLeafA : Cell :=
  Cell.ofUInt 8 0xa5

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x15 5) #[refLeafA]

private def sliceA : Slice :=
  Slice.ofCell refLeafA

private def assembleOrPanic (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c => c
  | .error e => panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def mkIfnotrefInstr (refCell : Cell) : Instr :=
  .ifnotref (Slice.ofCell refCell)

private def mkPrefixedIfnotrefCodeCell
    (pre : Array Instr)
    (refCell : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let prefixCell := assembleOrPanic "mkPrefixedIfnotrefCodeCell/prefix" pre
  let tailCell := assembleOrPanic "mkPrefixedIfnotrefCodeCell/tail" tail
  Cell.mkOrdinary
    (prefixCell.bits ++ natToBits ifnotrefOpcode 16 ++ tailCell.bits)
    (prefixCell.refs ++ #[refCell] ++ tailCell.refs)

private def mkIfnotrefCodeCell
    (refCell : Cell)
    (tail : Array Instr := #[]) : Cell :=
  mkPrefixedIfnotrefCodeCell #[] refCell tail

private def mkIfnotrefMissingRefCodeCell
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleOrPanic "mkIfnotrefMissingRefCodeCell/tail" tail
  Cell.mkOrdinary
    (natToBits ifnotrefOpcode 16 ++ tailCell.bits)
    tailCell.refs

private def mkTwoIfnotrefCodeCell
    (refA refB : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleOrPanic "mkTwoIfnotrefCodeCell/tail" tail
  Cell.mkOrdinary
    (natToBits ifnotrefOpcode 16 ++ natToBits ifnotrefOpcode 16 ++ tailCell.bits)
    (#[refA, refB] ++ tailCell.refs)

private def mkTwoIfnotrefOneRefCodeCell
    (refA : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleOrPanic "mkTwoIfnotrefOneRefCodeCell/tail" tail
  Cell.mkOrdinary
    (natToBits ifnotrefOpcode 16 ++ natToBits ifnotrefOpcode 16 ++ tailCell.bits)
    (#[refA] ++ tailCell.refs)

private def runIfnotrefDirect (refCell : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfnotref (mkIfnotrefInstr refCell) stack

private def runIfnotrefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfnotref instr (VM.push (intV dispatchSentinel)) stack

private def runIfnotrefRaw
    (refCell : Cell)
    (stack : Array Value)
    (gasLimit : Int := 1_000_000)
    (cc : Continuation := .quit 71) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      gas := GasLimits.ofLimits gasLimit gasLimit 0 }
  (execInstrFlowIfnotref (mkIfnotrefInstr refCell) (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  match res with
  | (.ok _, st) => pure st
  | (.error e, _) =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  match res with
  | (.error e, st) =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | (.ok _, st) =>
      throw (IO.userError s!"{label}: expected error {expected}, got success with state {reprStr st}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnotrefId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def branchNoop : Cell :=
  Cell.empty

private def branchPushMarker : Cell :=
  assembleOrPanic "branchPushMarker" #[.pushInt (.num branchMarker)]

private def branchAdd : Cell :=
  assembleOrPanic "branchAdd" #[.add]

private def codeObserveMarkerTail : Cell :=
  mkIfnotrefCodeCell branchPushMarker #[.pushInt (.num tailMarker)]

private def codeBranchAddTail : Cell :=
  mkIfnotrefCodeCell branchAdd #[.pushInt (.num tailMarker)]

private def codeMissingRefTail : Cell :=
  mkIfnotrefMissingRefCodeCell #[.pushInt (.num tailMarker)]

private def codePushNanThenIfnotref : Cell :=
  mkPrefixedIfnotrefCodeCell #[.pushInt .nan] branchNoop #[.pushInt (.num tailMarker)]

private def codeTwoIfnotrefNoopTail : Cell :=
  mkTwoIfnotrefCodeCell branchNoop branchNoop #[.pushInt (.num tailMarker)]

private def codeTwoIfnotrefOneRefTail : Cell :=
  mkTwoIfnotrefOneRefCodeCell branchNoop #[.pushInt (.num tailMarker)]

private def codeTruncated8WithRef : Cell :=
  Cell.mkOrdinary (natToBits 0xe3 8) #[branchNoop]

private def ifnotrefOracleFamilies : Array String :=
  #[
    "ok/branch/taken/",
    "ok/branch/skipped/",
    "ok/branch-add/",
    "ok/two-ifnotref/noop/",
    "err/branch-add/",
    "err/popbool/",
    "err/decode/missing-ref/",
    "err/decode/truncated-",
    "err/decode/two-ifnotref-one-ref/"
  ]

private def ifnotrefFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := ifnotrefOracleFamilies
    mutationModes := #[
      0, 0, 0, 0,
      1, 1, 1,
      2, 2,
      3, 3, 3,
      4
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := ifnotrefId
  unit := #[
    { name := "unit/raw/branch-inversion-and-cell-load-gating"
      run := do
        let ccOrd : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        let stTaken ← expectRawOk "raw/taken"
          (runIfnotrefRaw branchPushMarker #[intV 9, intV 0] (cc := ccOrd))
        if stTaken.stack != #[intV 9] then
          throw (IO.userError s!"raw/taken: expected stack #[9], got {reprStr stTaken.stack}")
        if stTaken.loadedCells.size != 1 then
          throw (IO.userError s!"raw/taken: expected one loaded cell, got {stTaken.loadedCells.size}")
        if stTaken.cc == ccOrd then
          throw (IO.userError "raw/taken: expected call transition, cc stayed unchanged")
        match stTaken.regs.c0 with
        | .ordinary _ _ _ _ => pure ()
        | other =>
            throw (IO.userError s!"raw/taken: expected ordinary return c0, got {reprStr other}")

        let stSkip ← expectRawOk "raw/skip"
          (runIfnotrefRaw branchPushMarker #[intV 9, intV 5] (cc := ccOrd))
        if stSkip.stack != #[intV 9] then
          throw (IO.userError s!"raw/skip: expected stack #[9], got {reprStr stSkip.stack}")
        if !stSkip.loadedCells.isEmpty then
          throw (IO.userError s!"raw/skip: expected no loaded cells, got {reprStr stSkip.loadedCells}")
        if stSkip.cc != ccOrd then
          throw (IO.userError s!"raw/skip: expected unchanged cc, got {reprStr stSkip.cc}")
        if stSkip.regs.c0 != .quit 0 then
          throw (IO.userError s!"raw/skip: expected unchanged c0=quit0, got {reprStr stSkip.regs.c0}") }
    ,
    { name := "unit/raw/popbool-errors-pop-top-and-skip-cell-load"
      run := do
        let stType ← expectRawErr "raw/type-popbool"
          (runIfnotrefRaw branchPushMarker #[intV 44, .null])
          .typeChk
        if stType.stack != #[intV 44] then
          throw (IO.userError s!"raw/type-popbool: expected stack #[44], got {reprStr stType.stack}")
        if !stType.loadedCells.isEmpty then
          throw (IO.userError "raw/type-popbool: unexpected cell-load side effect")

        let stNan ← expectRawErr "raw/intov-popbool"
          (runIfnotrefRaw branchPushMarker #[intV 55, .int .nan])
          .intOv
        if stNan.stack != #[intV 55] then
          throw (IO.userError s!"raw/intov-popbool: expected stack #[55], got {reprStr stNan.stack}")
        if !stNan.loadedCells.isEmpty then
          throw (IO.userError "raw/intov-popbool: unexpected cell-load side effect") }
    ,
    { name := "unit/direct/underflow-type-and-negate-contract"
      run := do
        expectErr "underflow/empty" (runIfnotrefDirect branchNoop #[]) .stkUnd
        expectErr "type/top-null" (runIfnotrefDirect branchNoop #[.null]) .typeChk
        expectErr "type/top-cell" (runIfnotrefDirect branchNoop #[.cell refLeafA]) .typeChk
        expectErr "type/top-slice" (runIfnotrefDirect branchNoop #[.slice sliceA]) .typeChk
        expectErr "type/top-builder" (runIfnotrefDirect branchNoop #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runIfnotrefDirect branchNoop #[.tuple #[]]) .typeChk
        expectErr "type/top-cont" (runIfnotrefDirect branchNoop #[q0]) .typeChk
        expectErr "intov/top-nan" (runIfnotrefDirect branchNoop #[.int .nan]) .intOv
        expectOkStack "negate/zero-taken-pops-bool"
          (runIfnotrefDirect branchNoop #[intV 7, intV 0])
          #[intV 7]
        expectOkStack "negate/nonzero-skipped-pops-bool"
          (runIfnotrefDirect branchNoop #[intV 7, intV (-3)])
          #[intV 7] }
    ,
    { name := "unit/raw/out-of-gas-only-on-taken-branch"
      run := do
        let stTaken ← expectRawErr "oog/taken"
          (runIfnotrefRaw branchPushMarker #[intV 0] 0)
          .outOfGas
        if stTaken.stack != #[] then
          throw (IO.userError s!"oog/taken: expected empty stack, got {reprStr stTaken.stack}")
        if stTaken.loadedCells.size != 1 then
          throw (IO.userError s!"oog/taken: expected one loaded cell, got {stTaken.loadedCells.size}")

        let stSkip ← expectRawOk "oog/skip"
          (runIfnotrefRaw branchPushMarker #[intV 1] 0)
        if stSkip.stack != #[] then
          throw (IO.userError s!"oog/skip: expected empty stack, got {reprStr stSkip.stack}")
        if !stSkip.loadedCells.isEmpty then
          throw (IO.userError "oog/skip: expected no loaded cells") }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfnotrefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/matched-ifnotref-no-next"
          (runHandlerDirectWithNext execInstrFlowIfnotref (mkIfnotrefInstr branchNoop)
            (VM.push (intV dispatchSentinel)) #[intV 1])
          #[] }
    ,
    { name := "unit/decode/opcode-and-missing-ref-guard"
      run := do
        match decodeCp0WithBits (Slice.ofCell codeObserveMarkerTail) with
        | .ok (.ifnotref code, bits, rest) =>
            if bits != 16 then
              throw (IO.userError s!"decode/ok: expected 16 bits, got {bits}")
            else if code.cell != branchPushMarker then
              throw (IO.userError s!"decode/ok: expected referenced branch cell, got {reprStr code.cell}")
            else if rest.bitsRemaining = 0 then
              throw (IO.userError "decode/ok: expected tail bits after IFNOTREF")
            else
              pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/ok: expected IFNOTREF, got {reprStr instr} ({bits} bits)")
        | .error e =>
            throw (IO.userError s!"decode/ok: expected success, got {e}")

        match decodeCp0WithBits (Slice.ofCell codeMissingRefTail) with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"decode/missing-ref: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/missing-ref: expected failure, got {reprStr instr} ({bits} bits)")

        match decodeCp0WithBits (Slice.ofCell codeTruncated8WithRef) with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"decode/truncated: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/truncated: expected failure, got {reprStr instr} ({bits} bits)") }
  ]
  oracle := #[
    -- Branch-observable matrix: ref branch pushes `branchMarker`; tail pushes `tailMarker`.
    mkCase "ok/branch/taken/zero-basic"
      #[intV 0]
      codeObserveMarkerTail,
    mkCase "ok/branch/taken/zero-deep-null"
      #[.null, intV 0]
      codeObserveMarkerTail,
    mkCase "ok/branch/taken/zero-deep-int-cell"
      #[intV 9, .cell refLeafA, intV 0]
      codeObserveMarkerTail,
    mkCase "ok/branch/taken/zero-deep-slice-builder"
      #[.slice sliceA, .builder Builder.empty, intV 0]
      codeObserveMarkerTail,
    mkCase "ok/branch/taken/zero-below-max257"
      #[intV maxInt257, intV 0]
      codeObserveMarkerTail,
    mkCase "ok/branch/taken/zero-below-min257"
      #[intV minInt257, intV 0]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/one-basic"
      #[intV 1]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/minus-one"
      #[intV (-1)]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/two"
      #[intV 2]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/minus-two"
      #[intV (-2)]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/max257"
      #[intV maxInt257]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/min257"
      #[intV minInt257]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/deep-cell-int"
      #[.cell refLeafB, intV 7, intV 5]
      codeObserveMarkerTail,
    mkCase "ok/branch/skipped/deep-tuple-builder"
      #[.tuple #[], .builder Builder.empty, intV (-9)]
      codeObserveMarkerTail,
    mkCase "ok/branch/taken/deep-tuple-builder"
      #[.tuple #[], .builder Builder.empty, intV 0]
      codeObserveMarkerTail,
    mkCase "ok/branch/taken/cont-noise-below"
      #[q0, intV 0]
      codeObserveMarkerTail,

    -- Branch body that can fail (`ADD`) to prove taken/skip split.
    mkCase "err/branch-add/taken-underflow"
      #[intV 0]
      codeBranchAddTail,
    mkCase "ok/branch-add/skipped-underflow-avoided"
      #[intV 1]
      codeBranchAddTail,
    mkCase "ok/branch-add/taken-two-ints"
      #[intV 5, intV 6, intV 0]
      codeBranchAddTail,
    mkCase "ok/branch-add/skipped-two-ints"
      #[intV 5, intV 6, intV 1]
      codeBranchAddTail,
    mkCase "err/branch-add/taken-type-null"
      #[.null, intV 7, intV 0]
      codeBranchAddTail,
    mkCase "ok/branch-add/skipped-type-null-avoided"
      #[.null, intV 7, intV 1]
      codeBranchAddTail,
    mkCase "err/branch-add/taken-type-cell"
      #[.cell refLeafA, intV 7, intV 0]
      codeBranchAddTail,
    mkCase "ok/branch-add/skipped-type-cell-avoided"
      #[.cell refLeafA, intV 7, intV 1]
      codeBranchAddTail,
    mkCase "err/branch-add/taken-underflow-one-int"
      #[intV 9, intV 0]
      codeBranchAddTail,
    mkCase "ok/branch-add/skipped-underflow-one-int-avoided"
      #[intV 9, intV 2]
      codeBranchAddTail,

    -- Bool-pop site failures with valid referenced branch cell.
    mkCase "err/popbool/underflow-empty"
      #[]
      codeObserveMarkerTail,
    mkCase "err/popbool/type-null"
      #[.null]
      codeObserveMarkerTail,
    mkCase "err/popbool/type-cell"
      #[.cell refLeafA]
      codeObserveMarkerTail,
    mkCase "err/popbool/type-slice"
      #[.slice sliceA]
      codeObserveMarkerTail,
    mkCase "err/popbool/type-builder"
      #[.builder Builder.empty]
      codeObserveMarkerTail,
    mkCase "err/popbool/type-tuple-empty"
      #[.tuple #[]]
      codeObserveMarkerTail,
    mkCase "err/popbool/type-cont-quit0"
      #[q0]
      codeObserveMarkerTail,
    mkCase "err/popbool/intov-nan-from-prefix"
      #[]
      codePushNanThenIfnotref,
    mkCase "err/popbool/type-top-first-over-valid-below"
      #[intV 77, .null]
      codeObserveMarkerTail,
    mkCase "err/popbool/type-top-first-over-deep-below"
      #[.cell refLeafA, intV 8, .builder Builder.empty]
      codeObserveMarkerTail,

    -- Decode ordering: missing ref must fail before bool stack checks.
    mkCase "err/decode/missing-ref-empty-stack"
      #[]
      codeMissingRefTail,
    mkCase "err/decode/missing-ref-null-stack"
      #[.null]
      codeMissingRefTail,
    mkCase "err/decode/missing-ref-int-stack"
      #[intV 0]
      codeMissingRefTail,
    mkCase "err/decode/missing-ref-deep-stack"
      #[.cell refLeafA, intV 9, .builder Builder.empty]
      codeMissingRefTail,
    mkCase "err/decode/truncated-8bits-even-with-ref"
      #[intV 0]
      codeTruncated8WithRef,

    -- Two-opcode sequencing (success and second-opcode missing-ref failure).
    mkCase "err/decode/two-ifnotref-one-ref/first-taken-second-missing"
      #[intV 1, intV 0]
      codeTwoIfnotrefOneRefTail,
    mkCase "err/decode/two-ifnotref-one-ref/first-skipped-second-missing"
      #[intV 0, intV 1]
      codeTwoIfnotrefOneRefTail,
    mkCase "ok/two-ifnotref/noop/both-taken"
      #[intV 0, intV 0]
      codeTwoIfnotrefNoopTail,
    mkCase "ok/two-ifnotref/noop/first-taken-second-skipped"
      #[intV 1, intV 0]
      codeTwoIfnotrefNoopTail,
    mkCase "ok/two-ifnotref/noop/first-skipped-second-taken"
      #[intV 0, intV 1]
      codeTwoIfnotrefNoopTail,
    mkCase "ok/two-ifnotref/noop/both-skipped"
      #[intV 1, intV 1]
      codeTwoIfnotrefNoopTail,
    mkCase "ok/two-ifnotref/noop/deep-mixed"
      #[.null, .cell refLeafA, intV 1, intV 0]
      codeTwoIfnotrefNoopTail,
    mkCase "ok/two-ifnotref/noop/deep-maxmin"
      #[intV maxInt257, intV minInt257, intV 1, intV 0]
      codeTwoIfnotrefNoopTail
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile ifnotrefId ifnotrefFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.IFNOTREF
