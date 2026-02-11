import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFNOTJMPREF

/-
IFNOTJMPREF branch map (Lean vs C++ `contops.cpp`, `register_continuation_cond_loop_ops`,
`exec_do_with_cell` + IFNOTJMPREF negate lambda):
- decode-time ref guard first (`have_refs(1)` / `takeRefInv`): missing ref => `invOpcode`;
- bool pop/evaluation happens before jump load path (`pop_bool` / `popBool`);
- negate branch: jump iff popped bool is false/zero;
- taken branch converts ref cell to continuation and jumps;
- `load_cell_slice_ref` path charges load gas and rejects special/exotic cells (`cell_und`);
- non-taken branch must not load/validate the ref cell.
-/

private def ifnotjmprefId : InstrId := { name := "IFNOTJMPREF" }

private def ifnotjmprefOpcode : Nat := 0xe303

private def ifnotjmprefInstr (code : Slice) : Instr :=
  .ifnotjmpref code

private def dispatchSentinel : Int := 90351
private def jumpMarker : Int := 333
private def tailMarker : Int := 777

private def q0 : Value := .cont (.quit 0)

private def emptySlice : Slice :=
  Slice.ofCell Cell.empty

private def noiseCell : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[]

private def specialTargetCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def opcodeBits : BitString :=
  natToBits ifnotjmprefOpcode 16

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.size = 0 then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def assembleNoRefBits! (label : String) (program : Array Instr) : BitString :=
  (assembleNoRefCell! label program).bits

private def mkIfnotjmprefCode (target : Cell) (tail : Array Instr := #[]) : Cell :=
  Cell.mkOrdinary (opcodeBits ++ assembleNoRefBits! "ifnotjmpref/tail" tail) #[target]

private def targetMarkerCell : Cell :=
  assembleNoRefCell! "ifnotjmpref/target-marker" #[.pushInt (.num jumpMarker)]

private def branchObservableCode : Cell :=
  mkIfnotjmprefCode targetMarkerCell #[.pushInt (.num tailMarker)]

private def noTailCode : Cell :=
  mkIfnotjmprefCode targetMarkerCell #[]

private def specialBranchCode : Cell :=
  mkIfnotjmprefCode specialTargetCell #[.pushInt (.num tailMarker)]

private def missingRefCode : Cell :=
  Cell.mkOrdinary opcodeBits #[]

private def missingRefWithTailCode : Cell :=
  Cell.mkOrdinary
    (opcodeBits ++ assembleNoRefBits! "ifnotjmpref/missing-ref-tail" #[.pushInt (.num tailMarker)])
    #[]

private def truncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xe3 8) #[]

private def truncated15Code : Cell :=
  Cell.mkOrdinary (natToBits 0x7181 15) #[]

private def runIfnotjmprefDirect
    (code : Slice)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfnotjmpref (ifnotjmprefInstr code) stack

private def runIfnotjmprefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfnotjmpref instr (VM.push (intV dispatchSentinel)) stack

private def runIfnotjmprefRaw
    (code : Slice)
    (stack : Array Value)
    (cc : Continuation := .quit 71)
    (loaded : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      loadedCells := loaded }
  (execInstrFlowIfnotjmpref (ifnotjmprefInstr code) (pure ())).run st0

private def runIfnotjmprefState
    (code : Slice)
    (stack : Array Value)
    (cc : Continuation := .quit 71)
    (loaded : Array (Array UInt8) := #[]) : Except Excno VmState :=
  let (res, st1) := runIfnotjmprefRaw code stack cc loaded
  match res with
  | .ok _ => .ok st1
  | .error e => .error e

private def sameSlice (a b : Slice) : Bool :=
  a.bitPos == b.bitPos && a.refPos == b.refPos && a.cell == b.cell

private def expectStateStayed
    (label : String)
    (res : Except Excno VmState)
    (expectedQuit : Int)
    (expectedStack : Array Value)
    (expectedLoaded : Nat) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.stack != expectedStack then
        throw (IO.userError s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st.stack}")
      else if st.loadedCells.size != expectedLoaded then
        throw (IO.userError s!"{label}: expected loadedCells={expectedLoaded}, got {st.loadedCells.size}")
      else
        match st.cc with
        | .quit n =>
            if n = expectedQuit then
              pure ()
            else
              throw (IO.userError s!"{label}: expected cc quit({expectedQuit}), got quit({n})")
        | _ =>
            throw (IO.userError s!"{label}: expected cc quit({expectedQuit}), got {reprStr st.cc}")

private def expectStateJumpedToCode
    (label : String)
    (res : Except Excno VmState)
    (expectedCode : Slice)
    (expectedStack : Array Value)
    (expectedLoaded : Nat) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.stack != expectedStack then
        throw (IO.userError s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st.stack}")
      else if st.loadedCells.size != expectedLoaded then
        throw (IO.userError s!"{label}: expected loadedCells={expectedLoaded}, got {st.loadedCells.size}")
      else
        match st.cc with
        | .ordinary code _ _ _ =>
            if sameSlice code expectedCode then
              pure ()
            else
              throw (IO.userError s!"{label}: expected jump code {reprStr expectedCode}, got {reprStr code}")
        | _ =>
            throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr st.cc}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectDecodeOkIfnotjmpref
    (label : String)
    (code : Cell)
    (expectedTarget : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (.ifnotjmpref s, bits, _) =>
      if bits != 16 then
        throw (IO.userError s!"{label}: expected decoded bits=16, got {bits}")
      else if !(sameSlice s (Slice.ofCell expectedTarget)) then
        throw (IO.userError s!"{label}: decoded target mismatch")
      else
        pure ()
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected IFNOTJMPREF, got instr={reprStr instr}, bits={bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := branchObservableCode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnotjmprefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

def suite : InstrSuite where
  id := ifnotjmprefId
  unit := #[
    { name := "unit/branch-negate-cc-stack-and-load-side-effects"
      run := do
        let targetSlice := Slice.ofCell targetMarkerCell
        expectStateJumpedToCode "jump/zero"
          (runIfnotjmprefState targetSlice #[intV 0] (.quit 71))
          targetSlice
          #[]
          1
        expectStateStayed "nojump/one"
          (runIfnotjmprefState targetSlice #[intV 1] (.quit 71))
          71
          #[]
          0
        expectStateStayed "nojump/minus-five"
          (runIfnotjmprefState targetSlice #[intV (-5)] (.quit 71))
          71
          #[]
          0
        expectStateJumpedToCode "jump/deep-stack"
          (runIfnotjmprefState targetSlice #[.null, intV 9, intV 0] (.quit 71))
          targetSlice
          #[.null, intV 9]
          1
        expectStateStayed "nojump/deep-stack"
          (runIfnotjmprefState targetSlice #[.null, intV 9, intV 2] (.quit 71))
          71
          #[.null, intV 9]
          0 }
    ,
    { name := "unit/underflow-type-and-intov-at-bool-pop-site"
      run := do
        let targetSlice := Slice.ofCell targetMarkerCell
        expectErr "underflow/empty" (runIfnotjmprefDirect targetSlice #[]) .stkUnd
        expectErr "type/null" (runIfnotjmprefDirect targetSlice #[.null]) .typeChk
        expectErr "type/cell" (runIfnotjmprefDirect targetSlice #[.cell noiseCell]) .typeChk
        expectErr "type/slice" (runIfnotjmprefDirect targetSlice #[.slice emptySlice]) .typeChk
        expectErr "type/builder" (runIfnotjmprefDirect targetSlice #[.builder Builder.empty]) .typeChk
        expectErr "type/tuple" (runIfnotjmprefDirect targetSlice #[.tuple #[]]) .typeChk
        expectErr "type/cont" (runIfnotjmprefDirect targetSlice #[q0]) .typeChk
        expectErr "intov/nan" (runIfnotjmprefDirect targetSlice #[.int .nan]) .intOv }
    ,
    { name := "unit/special-cell-ordering-and-load-side-effects"
      run := do
        let specialSlice := Slice.ofCell specialTargetCell

        let (resTaken, stTaken) := runIfnotjmprefRaw specialSlice #[intV 0]
        match resTaken with
        | .error .cellUnd =>
            if stTaken.loadedCells.size = 1 then
              pure ()
            else
              throw (IO.userError s!"special/taken: expected one loaded cell, got {stTaken.loadedCells.size}")
        | .error e =>
            throw (IO.userError s!"special/taken: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "special/taken: expected cellUnd, got success")

        let (resNotTaken, stNotTaken) := runIfnotjmprefRaw specialSlice #[intV 1]
        match resNotTaken with
        | .ok _ =>
            if stNotTaken.loadedCells.isEmpty then
              pure ()
            else
              throw (IO.userError s!"special/not-taken: expected no load, got {stNotTaken.loadedCells.size}")
        | .error e =>
            throw (IO.userError s!"special/not-taken: expected success, got {e}")

        let (resType, stType) := runIfnotjmprefRaw specialSlice #[.null]
        match resType with
        | .error .typeChk =>
            if stType.loadedCells.isEmpty then
              pure ()
            else
              throw (IO.userError s!"special/type-order: expected no load, got {stType.loadedCells.size}")
        | .error e =>
            throw (IO.userError s!"special/type-order: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "special/type-order: expected typeChk, got success")

        let (resNan, stNan) := runIfnotjmprefRaw specialSlice #[.int .nan]
        match resNan with
        | .error .intOv =>
            if stNan.loadedCells.isEmpty then
              pure ()
            else
              throw (IO.userError s!"special/intov-order: expected no load, got {stNan.loadedCells.size}")
        | .error e =>
            throw (IO.userError s!"special/intov-order: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "special/intov-order: expected intOv, got success") }
    ,
    { name := "unit/decode-ref-guard-and-truncation"
      run := do
        expectDecodeOkIfnotjmpref "decode/ok" (mkIfnotjmprefCode targetMarkerCell #[]) targetMarkerCell
        expectDecodeErr "decode/missing-ref" missingRefCode .invOpcode
        expectDecodeErr "decode/missing-ref-with-tail" missingRefWithTailCode .invOpcode
        expectDecodeErr "decode/truncated-8bit" truncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15bit" truncated15Code .invOpcode }
    ,
    { name := "unit/dispatch-non-ifnotjmpref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runIfnotjmprefDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel] }
  ]
  oracle := #[
    mkCase "branch/observable/jump-when-zero" #[intV 0] branchObservableCode,
    mkCase "branch/observable/nojump-when-one" #[intV 1] branchObservableCode,
    mkCase "branch/observable/nojump-when-minus-one" #[intV (-1)] branchObservableCode,
    mkCase "branch/observable/nojump-when-two" #[intV 2] branchObservableCode,
    mkCase "branch/observable/nojump-when-minus-two" #[intV (-2)] branchObservableCode,
    mkCase "branch/observable/nojump-when-big-pos" #[intV (pow2 200)] branchObservableCode,
    mkCase "branch/observable/nojump-when-big-neg" #[intV (-(pow2 200))] branchObservableCode,
    mkCase "branch/observable/deep-jump-zero" #[.null, intV 9, intV 0] branchObservableCode,
    mkCase "branch/observable/deep-nojump-one" #[.null, intV 9, intV 1] branchObservableCode,
    mkCase "branch/observable/deep-nojump-minus-seven" #[.null, intV 9, intV (-7)] branchObservableCode,
    mkCase "branch/observable/deep-jump-cell-noise" #[.cell noiseCell, .tuple #[], intV 0] branchObservableCode,
    mkCase "branch/observable/deep-nojump-cell-noise" #[.cell noiseCell, .tuple #[], intV 5] branchObservableCode,

    mkCase "ok/no-tail/jump-zero" #[intV 0] noTailCode,
    mkCase "ok/no-tail/nojump-one" #[intV 1] noTailCode,
    mkCase "ok/no-tail/nojump-minus-one" #[intV (-1)] noTailCode,
    mkCase "ok/no-tail/deep-jump-zero" #[.null, .builder Builder.empty, intV 0] noTailCode,
    mkCase "ok/no-tail/deep-nojump-one" #[.null, .builder Builder.empty, intV 1] noTailCode,
    mkCase "ok/no-tail/deep-nojump-big" #[.tuple #[], intV (pow2 120)] noTailCode,

    mkCase "underflow/empty" #[] branchObservableCode,
    mkCase "type/bool-null" #[.null] branchObservableCode,
    mkCase "type/bool-cell" #[.cell noiseCell] branchObservableCode,
    mkCase "type/bool-slice" #[.slice emptySlice] branchObservableCode,
    mkCase "type/bool-builder" #[.builder Builder.empty] branchObservableCode,
    mkCase "type/bool-tuple" #[.tuple #[]] branchObservableCode,
    mkCase "type/bool-cont" #[q0] branchObservableCode,
    mkCase "type/bool-cont-with-noise-below" #[.null, q0] branchObservableCode,

    mkCase "special/taken-zero-cellund" #[intV 0] specialBranchCode,
    mkCase "special/not-taken-one-tail-runs" #[intV 1] specialBranchCode,
    mkCase "special/not-taken-minus-one-tail-runs" #[intV (-1)] specialBranchCode,
    mkCase "special/error-order/type-before-cellund-null" #[.null] specialBranchCode,
    mkCase "special/error-order/type-before-cellund-cell" #[.cell noiseCell] specialBranchCode,
    mkCase "special/error-order/underflow-before-cellund" #[] specialBranchCode,
    mkCase "special/deep-taken-zero-cellund" #[.null, intV 0] specialBranchCode,
    mkCase "special/deep-not-taken-one-tail-runs" #[.null, intV 1] specialBranchCode,

    mkCase "decode/missing-ref/empty-stack" #[] missingRefCode,
    mkCase "decode/missing-ref/bool-zero" #[intV 0] missingRefCode,
    mkCase "decode/missing-ref/bool-one" #[intV 1] missingRefCode,
    mkCase "decode/missing-ref/type-null" #[.null] missingRefCode,
    mkCase "decode/missing-ref/deep-stack" #[.tuple #[], intV 0] missingRefCode,
    mkCase "decode/missing-ref/with-tail" #[intV 0] missingRefWithTailCode,
    mkCase "decode/truncated-8bit-prefix" #[intV 0] truncated8Code,
    mkCase "decode/truncated-15bit-prefix" #[intV 0] truncated15Code
  ]
  fuzz := #[ mkReplayOracleFuzzSpec ifnotjmprefId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.IFNOTJMPREF
