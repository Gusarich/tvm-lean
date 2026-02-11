import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFREFELSE

/-
IFREFELSE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/IfrefElse.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xe30d` decode with `takeRefInv`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifrefElse _` rejected by assembler)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_ifelse_ref(..., mode=true)` for `IFREFELSE`)

Branch map covered by this suite:
- decode/ref gate:
  - `0xe30d` requires one attached reference;
  - missing/truncated ref payload fails with `invOpcode` before stack pops.
- stack pop ordering and errors:
  - `checkUnderflow(2)` / `checkUnderflow 2` first;
  - pop order is `cont` first, then `bool`;
  - error site ordering is underflow -> cont type -> bool type/intov.
- mode=true branch selection:
  - non-zero bool selects referenced continuation;
  - zero bool selects popped stack continuation.
- call-side effects:
  - selected continuation is invoked via `call` (not jump, not plain `callTo`),
    so stack shaping and `c0` handling follow full call semantics.
-/

private def ifrefElseId : InstrId := { name := "IFREFELSE" }

private def ifrefElseOpcode : Nat := 0xe30d

private def dispatchSentinel : Int := 9036

private def branchMarker : Int := 4141
private def contMarker : Int := 5252
private def tailMarker : Int := 9393

private def q0 : Value :=
  .cont (.quit 0)

private def assembleOrPanic (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c => c
  | .error e => panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def mkIfrefElseInstr (refCell : Cell) : Instr :=
  .ifrefElse (Slice.ofCell refCell)

private def mkPrefixedIfrefElseCodeCell
    (pre : Array Instr)
    (refCell : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let preCell := assembleOrPanic "mkPrefixedIfrefElseCodeCell/pre" pre
  let tailCell := assembleOrPanic "mkPrefixedIfrefElseCodeCell/tail" tail
  Cell.mkOrdinary
    (preCell.bits ++ natToBits ifrefElseOpcode 16 ++ tailCell.bits)
    (preCell.refs ++ #[refCell] ++ tailCell.refs)

private def mkIfrefElseCodeCell
    (refCell : Cell)
    (tail : Array Instr := #[]) : Cell :=
  mkPrefixedIfrefElseCodeCell #[] refCell tail

private def mkPrefixedIfrefElseMissingRefCodeCell
    (pre : Array Instr)
    (tail : Array Instr := #[]) : Cell :=
  let preCell := assembleOrPanic "mkPrefixedIfrefElseMissingRefCodeCell/pre" pre
  let tailCell := assembleOrPanic "mkPrefixedIfrefElseMissingRefCodeCell/tail" tail
  Cell.mkOrdinary
    (preCell.bits ++ natToBits ifrefElseOpcode 16 ++ tailCell.bits)
    (preCell.refs ++ tailCell.refs)

private def mkIfrefElseMissingRefCodeCell
    (tail : Array Instr := #[]) : Cell :=
  mkPrefixedIfrefElseMissingRefCodeCell #[] tail

private def mkTwoIfrefElseCodeCell
    (refA refB : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleOrPanic "mkTwoIfrefElseCodeCell/tail" tail
  Cell.mkOrdinary
    (natToBits ifrefElseOpcode 16 ++ natToBits ifrefElseOpcode 16 ++ tailCell.bits)
    (#[refA, refB] ++ tailCell.refs)

private def mkTwoIfrefElseOneRefCodeCell
    (refA : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleOrPanic "mkTwoIfrefElseOneRefCodeCell/tail" tail
  Cell.mkOrdinary
    (natToBits ifrefElseOpcode 16 ++ natToBits ifrefElseOpcode 16 ++ tailCell.bits)
    (#[refA] ++ tailCell.refs)

private def ifrefElseTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits ifrefElseOpcode 15) #[]

private def ifrefElseTruncated8WithRefCode : Cell :=
  Cell.mkOrdinary (natToBits 0xe3 8) #[Cell.empty]

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 5) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0x13 5) #[refLeafA, refLeafB]

private def sliceNoiseA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x5a 8) #[refLeafA])

private def sliceNoiseB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x1ace 13) #[refLeafB, refLeafC])

private def builderNoise : Builder :=
  Builder.empty.storeBits #[true, false, true, true, false]

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refLeafA]

private def noiseB : Array Value :=
  #[.slice sliceNoiseA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[.cell refLeafB, .slice sliceNoiseB, .builder builderNoise]

private def withCond
    (below : Array Value)
    (cond : Int)
    (cont : Value := q0) : Array Value :=
  below ++ #[intV cond, cont]

private def withCondRaw
    (below : Array Value)
    (cond : Value)
    (cont : Value := q0) : Array Value :=
  below ++ #[cond, cont]

private def branchNoop : Cell :=
  Cell.empty

private def branchPushMarker : Cell :=
  assembleOrPanic "branchPushMarker" #[.pushInt (.num branchMarker)]

private def branchAdd : Cell :=
  assembleOrPanic "branchAdd" #[.add]

private def branchDeep : Cell :=
  Cell.mkOrdinary (natToBits 0x12f 9) #[refLeafB, refLeafC]

private def contPushMarkerCode : Cell :=
  assembleOrPanic "contPushMarkerCode" #[.pushInt (.num contMarker)]

private def contAddCode : Cell :=
  assembleOrPanic "contAddCode" #[.add]

private def contPushMarker : Continuation :=
  .ordinary (Slice.ofCell contPushMarkerCode) (.quit 0) OrdCregs.empty OrdCdata.empty

private def contAdd : Continuation :=
  .ordinary (Slice.ofCell contAddCode) (.quit 0) OrdCregs.empty OrdCdata.empty

private def contCaptured : Continuation :=
  .ordinary
    (Slice.ofCell branchNoop)
    (.quit 0)
    OrdCregs.empty
    { stack := #[intV 41, intV 42], nargs := -1 }

private def contCapturedCalled : Continuation :=
  .ordinary (Slice.ofCell branchNoop) (.quit 0) OrdCregs.empty OrdCdata.empty

private def contWithOwnC0 : Continuation :=
  let cregs : OrdCregs := { OrdCregs.empty with c0 := some (.quit 77) }
  .ordinary (Slice.ofCell branchNoop) (.quit 0) cregs OrdCdata.empty

private def codeNoop : Cell :=
  mkIfrefElseCodeCell branchNoop

private def codeDeep : Cell :=
  mkIfrefElseCodeCell branchDeep

private def codeObserveTail : Cell :=
  mkIfrefElseCodeCell branchPushMarker #[.pushInt (.num tailMarker)]

private def codeBranchAddTail : Cell :=
  mkIfrefElseCodeCell branchAdd #[.pushInt (.num tailMarker)]

private def codeMissingRefTail : Cell :=
  mkIfrefElseMissingRefCodeCell #[.pushInt (.num tailMarker)]

private def codePushNanThenIfrefElse : Cell :=
  mkPrefixedIfrefElseCodeCell #[.pushInt .nan, .pushCtr 0] branchNoop

private def codeTwoIfrefElseNoopTail : Cell :=
  mkTwoIfrefElseCodeCell branchNoop branchNoop #[.pushInt (.num tailMarker)]

private def codeTwoIfrefElseOneRefTail : Cell :=
  mkTwoIfrefElseOneRefCodeCell branchNoop #[.pushInt (.num tailMarker)]

private def runIfrefElseDirect
    (refCell : Cell)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfrefElse (mkIfrefElseInstr refCell) stack

private def runIfrefElseDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfrefElse instr (VM.push (intV dispatchSentinel)) stack

private def runIfrefElseRaw
    (refCell : Cell)
    (stack : Array Value)
    (c0 : Continuation := .quit 0)
    (loaded : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let seed := VmState.initial Cell.empty
  let st0 : VmState :=
    { seed with
      stack := stack
      regs := { seed.regs with c0 := c0 }
      loadedCells := loaded }
  (execInstrFlowIfrefElse (mkIfrefElseInstr refCell) (pure ())).run st0

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
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")
  | (.ok _, st) =>
      throw (IO.userError s!"{label}: expected error {expected}, got success with state {reprStr st}")

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got instr={reprStr instr}, bits={bits}")

private def runIfrefElseLean (code : Cell) (initStack : Array Value) (fuel : Nat := 200_000) : StepResult :=
  let st0 : VmState := { (VmState.initial code) with stack := initStack }
  VmState.run nativeHost fuel st0

private def expectExit (label : String) (expectedExit : Int) (res : StepResult) : IO VmState := do
  match res with
  | .halt exitCode st =>
      if exitCode = expectedExit then
        pure st
      else
        throw (IO.userError s!"{label}: expected exit {expectedExit}, got {exitCode}")
  | .continue _ =>
      throw (IO.userError s!"{label}: execution did not halt")

private def expectStackEq (label : String) (expected : Array Value) (st : VmState) : IO Unit := do
  if st.stack == expected then
    pure ()
  else
    throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st.stack}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifrefElseId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

def suite : InstrSuite where
  id := ifrefElseId
  unit := #[
    { name := "unit/state/true-loads-ref-and-ignores-popped-cont"
      run := do
        let st ← expectRawOk "state/true"
          (runIfrefElseRaw branchPushMarker (withCond #[] 1 (.cont contPushMarker)))
        if st.stack != #[] then
          throw (IO.userError s!"state/true: expected empty stack, got {reprStr st.stack}")
        match st.cc with
        | .ordinary code _ _ _ =>
            if code != Slice.ofCell branchPushMarker then
              throw (IO.userError
                s!"state/true: expected cc code from referenced branch, got {reprStr code}")
        | other =>
            throw (IO.userError s!"state/true: expected ordinary cc, got {reprStr other}")
        let expectedHash := Cell.hashBytes branchPushMarker
        if st.loadedCells != #[expectedHash] then
          throw (IO.userError
            s!"state/true: expected one loaded branch hash, got {reprStr st.loadedCells}")
        if st.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError
            s!"state/true: expected gas {cellLoadGasPrice}, got {st.gas.gasConsumed}") }
    ,
    { name := "unit/state/false-uses-popped-cont-and-skips-ref-load"
      run := do
        let st ← expectRawOk "state/false"
          (runIfrefElseRaw branchDeep (withCond #[] 0 (.cont contPushMarker)))
        if st.stack != #[] then
          throw (IO.userError s!"state/false: expected empty stack, got {reprStr st.stack}")
        if !st.loadedCells.isEmpty then
          throw (IO.userError s!"state/false: expected no loaded cells, got {reprStr st.loadedCells}")
        if st.gas.gasConsumed != 0 then
          throw (IO.userError s!"state/false: expected zero gas, got {st.gas.gasConsumed}")
        if st.cc != contPushMarker then
          throw (IO.userError s!"state/false: expected cc=stack cont, got {reprStr st.cc}") }
    ,
    { name := "unit/state/false-uses-full-call-semantics-captured-stack"
      run := do
        let st ← expectRawOk "state/false/call-shape"
          (runIfrefElseRaw branchDeep (withCond #[intV 7] 0 (.cont contCaptured)))
        if st.stack != #[intV 41, intV 42, intV 7] then
          throw (IO.userError
            s!"state/false/call-shape: expected captured-prefix stack, got {reprStr st.stack}")
        if st.cc != contCapturedCalled then
          throw (IO.userError
            s!"state/false/call-shape: expected called ordinary cont with empty cdata, got {reprStr st.cc}")
        match st.regs.c0 with
        | .ordinary _ _ _ _ => pure ()
        | other =>
            throw (IO.userError
              s!"state/false/call-shape: expected return continuation in c0, got {reprStr other}") }
    ,
    { name := "unit/state/false-call-reduces-to-jump-when-callee-has-c0"
      run := do
        let oldC0 : Continuation := .quit 55
        let st ← expectRawOk "state/false/own-c0"
          (runIfrefElseRaw branchNoop (withCond #[] 0 (.cont contWithOwnC0)) oldC0)
        if st.regs.c0 != oldC0 then
          throw (IO.userError
            s!"state/false/own-c0: expected c0 unchanged ({reprStr oldC0}), got {reprStr st.regs.c0}")
        if st.cc != contWithOwnC0 then
          throw (IO.userError
            s!"state/false/own-c0: expected jump to callee cont, got {reprStr st.cc}") }
    ,
    { name := "unit/errors/underflow-before-type"
      run := do
        expectErr "underflow/empty" (runIfrefElseDirect branchNoop #[]) .stkUnd
        expectErr "underflow/one-bool" (runIfrefElseDirect branchNoop #[intV 1]) .stkUnd
        expectErr "underflow/one-cont" (runIfrefElseDirect branchNoop #[q0]) .stkUnd
        expectErr "underflow/one-null" (runIfrefElseDirect branchNoop #[.null]) .stkUnd }
    ,
    { name := "unit/errors/pop-order-and-pop-site"
      run := do
        let stPopCont ← expectRawErr "err/popcont/type"
          (runIfrefElseRaw branchNoop #[intV 1, .null]) .typeChk
        if stPopCont.stack != #[intV 1] then
          throw (IO.userError s!"err/popcont/type: expected bool still on stack, got {reprStr stPopCont.stack}")

        let stPopBoolType ← expectRawErr "err/popbool/type"
          (runIfrefElseRaw branchNoop #[.null, q0]) .typeChk
        if stPopBoolType.stack != #[] then
          throw (IO.userError s!"err/popbool/type: expected both operands consumed, got {reprStr stPopBoolType.stack}")

        let stPopBoolNan ← expectRawErr "err/popbool/intov"
          (runIfrefElseRaw branchNoop #[.int .nan, q0]) .intOv
        if stPopBoolNan.stack != #[] then
          throw (IO.userError s!"err/popbool/intov: expected both operands consumed, got {reprStr stPopBoolNan.stack}")
        if !stPopBoolNan.loadedCells.isEmpty then
          throw (IO.userError s!"err/popbool/intov: expected no ref-load side effects, got {reprStr stPopBoolNan.loadedCells}") }
    ,
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runIfrefElseDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/match"
          (runIfrefElseDispatchFallback (mkIfrefElseInstr branchNoop) (withCond #[] 1))
          #[] }
    ,
    { name := "unit/decode/opcode-ref-gate-and-asm-rejection"
      run := do
        let bits : BitString :=
          natToBits 0xe30d 16 ++
          natToBits 0xe30e 16 ++
          natToBits 0xe30f 16 ++
          natToBits 0xa0 8
        let code : Cell := Cell.mkOrdinary bits #[branchNoop, branchDeep, branchPushMarker, branchNoop]
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ifrefelse" s0 (.ifrefElse (Slice.ofCell branchNoop)) 16
        let s2 ← expectDecodeStep "decode/ifelseref" s1 (.ifelseRef (Slice.ofCell branchDeep)) 16
        let s3 ← expectDecodeStep "decode/ifrefelseref" s2
          (.ifrefElseRef (Slice.ofCell branchPushMarker) (Slice.ofCell branchNoop)) 16
        let s4 ← expectDecodeStep "decode/add-tail" s3 .add 8
        if s4.bitsRemaining = 0 && s4.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got bits={s4.bitsRemaining} refs={s4.refsRemaining}")

        expectDecodeErr "decode/missing-ref"
          (Slice.ofCell codeMissingRefTail) .invOpcode
        expectDecodeErr "decode/truncated-15"
          (Slice.ofCell ifrefElseTruncated15Code) .invOpcode
        expectDecodeErr "decode/truncated-8-with-ref"
          (Slice.ofCell ifrefElseTruncated8WithRefCode) .invOpcode

        match assembleCp0 [mkIfrefElseInstr branchNoop] with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"asm/ifrefelse: expected invOpcode, got {e}")
        | .ok c =>
            throw (IO.userError s!"asm/ifrefelse: expected invOpcode, got assembled code {reprStr c}") }
    ,
    { name := "unit/full-run/mode-true-selection-and-gating"
      run := do
        let stTrueRef ← expectExit "full/select/true-ref" (~~~ 0)
          (runIfrefElseLean codeObserveTail (withCond #[] 1 (.cont contAdd)))
        expectStackEq "full/select/true-ref"
          #[intV branchMarker, intV tailMarker]
          stTrueRef

        let _ ← expectExit "full/select/false-cont" (~~~ Excno.stkUnd.toInt)
          (runIfrefElseLean codeObserveTail (withCond #[] 0 (.cont contAdd)))

        let _ ← expectExit "full/gating/true-add" (~~~ Excno.stkUnd.toInt)
          (runIfrefElseLean codeBranchAddTail (withCond #[] 1 (.cont contPushMarker)))

        let stFalseSkip ← expectExit "full/gating/false-skip-add" (~~~ 0)
          (runIfrefElseLean codeBranchAddTail (withCond #[] 0 (.cont contPushMarker)))
        expectStackEq "full/gating/false-skip-add"
          #[intV contMarker, intV tailMarker]
          stFalseSkip }
  ]
  oracle := #[
    -- True branch (`mode=true`): non-zero bool selects referenced continuation.
    mkCase "ok/true/basic-1" (withCond #[] 1) codeNoop,
    mkCase "ok/true/basic-neg1" (withCond #[] (-1)) codeNoop,
    mkCase "ok/true/max-int257" (withCond #[] maxInt257) codeDeep,
    mkCase "ok/true/min-int257" (withCond #[] minInt257) codeDeep,
    mkCase "ok/true/deep-noise-a" (withCond noiseA 7) codeDeep,
    mkCase "ok/true/deep-noise-b" (withCond noiseB (-5)) codeDeep,
    mkCase "ok/true/deep-noise-c" (withCond noiseC 255) codeDeep,

    -- False branch: zero bool selects popped stack continuation (`quit0` in oracle harness).
    mkCase "ok/false/basic-zero" (withCond #[] 0) codeNoop,
    mkCase "ok/false/deep-noise-a" (withCond noiseA 0) codeDeep,
    mkCase "ok/false/deep-noise-b" (withCond noiseB 0) codeDeep,
    mkCase "ok/false/deep-noise-c" (withCond noiseC 0) codeDeep,
    mkCase "ok/false/preserve-max" (withCond #[intV maxInt257] 0) codeDeep,
    mkCase "ok/false/preserve-min" (withCond #[intV minInt257] 0) codeDeep,
    mkCase "ok/false/slice-builder" (withCond #[.slice sliceNoiseA, .builder Builder.empty] 0) codeDeep,
    mkCase "ok/false/tuple-cont" (withCond #[.tuple #[], q0] 0) codeDeep,

    -- Underflow must happen before any pop-site type/intov checks.
    mkCase "err/underflow/empty" #[] codeNoop,
    mkCase "err/underflow/one-bool" #[intV 1] codeNoop,
    mkCase "err/underflow/one-cont" #[q0] codeNoop,

    -- popCont type failures (top item is not a continuation).
    mkCase "err/type/popcont-int" #[intV 0, intV 1] codeNoop,
    mkCase "err/type/popcont-null" #[intV 0, .null] codeNoop,
    mkCase "err/type/popcont-cell" #[intV 0, .cell refLeafA] codeNoop,
    mkCase "err/type/popcont-slice" #[intV 0, .slice sliceNoiseA] codeNoop,
    mkCase "err/type/popcont-builder" #[intV 0, .builder Builder.empty] codeNoop,
    mkCase "err/type/popcont-tuple" #[intV 0, .tuple #[]] codeNoop,

    -- popBool failures after successful popCont.
    mkCase "err/type/popbool-null" (withCondRaw #[] .null) codeNoop,
    mkCase "err/type/popbool-cell" (withCondRaw #[] (.cell refLeafA)) codeNoop,
    mkCase "err/type/popbool-slice" (withCondRaw #[] (.slice sliceNoiseB)) codeNoop,
    mkCase "err/type/popbool-builder" (withCondRaw #[] (.builder Builder.empty)) codeNoop,
    mkCase "err/type/popbool-tuple" (withCondRaw #[] (.tuple #[])) codeNoop,
    mkCase "err/type/popbool-cont" (withCondRaw #[] q0) codeNoop,
    mkCase "err/intov/popbool-nan-from-prefix" #[] codePushNanThenIfrefElse,

    -- Decode/ref gate failures must occur before stack-dependent checks.
    mkCase "err/decode/missing-ref-empty" #[] codeMissingRefTail,
    mkCase "err/decode/missing-ref-int" #[intV 1] codeMissingRefTail,
    mkCase "err/decode/missing-ref-deep" #[.null, .cell refLeafA, intV 0, q0] codeMissingRefTail,
    mkCase "err/decode/truncated-15-empty" #[] ifrefElseTruncated15Code,
    mkCase "err/decode/truncated-15-deep" #[.builder Builder.empty, intV 1, q0] ifrefElseTruncated15Code,
    mkCase "err/decode/truncated-8-with-ref" (withCond #[] 1) ifrefElseTruncated8WithRefCode,

    -- Branch body gating with a failing referenced continuation (`ADD`).
    mkCase "err/branchadd/true-underflow" (withCond #[] 1) codeBranchAddTail,
    mkCase "ok/branchadd/false-skip-underflow" (withCond #[] 0) codeBranchAddTail,

    -- Two-opcode sequencing: second IFREFELSE missing ref after first executes.
    mkCase "err/decode/two-ifrefelse-one-ref/first-true"
      #[intV 0, q0, intV 1, q0]
      codeTwoIfrefElseOneRefTail,
    mkCase "err/decode/two-ifrefelse-one-ref/first-true-deep"
      #[.null, .cell refLeafA, intV 0, q0, intV (-1), q0]
      codeTwoIfrefElseOneRefTail,

    -- Two-opcode sequencing with both refs present.
    mkCase "ok/two-ifrefelse-noop/both-true"
      #[intV 1, q0, intV 1, q0]
      codeTwoIfrefElseNoopTail,
    mkCase "ok/two-ifrefelse-noop/first-true-second-false"
      #[intV 0, q0, intV 1, q0]
      codeTwoIfrefElseNoopTail,
    mkCase "ok/two-ifrefelse-noop/deep-mixed"
      #[.tuple #[], .builder Builder.empty, intV 0, q0, intV 1, q0]
      codeTwoIfrefElseNoopTail,

    -- Tail-observable program where true branch must execute the referenced continuation.
    mkCase "ok/observe-tail/true"
      (withCond #[] 1)
      codeObserveTail
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.IFREFELSE
