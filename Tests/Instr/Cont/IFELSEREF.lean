import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFELSEREF

/-
IFELSEREF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/IfelseRef.lean`
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.call` stack/control semantics)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xe30e` decode with one attached ref)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifelseRef _` rejected by standalone assembler)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_ifelse_ref(..., mode=false)` registered at opcode `0xe30e`).

Branch map covered by this suite:
- decode/ref gate:
  - `0xe30e` + one attached ref decodes to `.ifelseRef`;
  - missing ref/truncated decode returns `.invOpcode` before stack checks.
- dispatch:
  - only `.ifelseRef _` is handled by `execInstrFlowIfelseRef`; others fall through.
- pop/order and branch split (`mode=false`):
  - `checkUnderflow 2` first;
  - pop order is continuation first, then bool;
  - bool=false => load referenced cell + call referenced continuation;
  - bool=true => call popped continuation, no referenced cell load.
- call semantics:
  - selected branch must use full `VM.call` (not `callTo`), preserving jump-reduction when callee
    already defines `c0` and enforcing `nargs`/captured-stack contracts.
-/

private def ifelserefId : InstrId := { name := "IFELSEREF" }

private def ifelserefOpcode : Nat := 0xe30e

private def dispatchSentinel : Int := 37037

private def branchMarker : Int := 6061

private def tailMarker : Int := 8082

private def q0 : Value := .cont (.quit 0)

private def refLeafA : Cell :=
  Cell.ofUInt 8 0xa5

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x15 5) #[refLeafA]

private def sliceNoiseA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x5a 8) #[refLeafA])

private def sliceNoiseB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x1ace 13) #[refLeafB])

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refLeafA]

private def noiseB : Array Value :=
  #[.slice sliceNoiseA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[.cell refLeafB, intV (-9), .tuple #[]]

private def assembleOrPanic (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c => c
  | .error e => panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  let c := assembleOrPanic label program
  if c.refs.isEmpty then
    c
  else
    panic! s!"{label}: assembled with unexpected refs={c.refs.size}"

private def mkIfelserefInstr (refCell : Cell) : Instr :=
  .ifelseRef (Slice.ofCell refCell)

private def ordinaryCont
    (code : Cell := Cell.empty)
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def envelopeCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .envelope (.quit 5) OrdCregs.empty { stack := captured, nargs := nargs }

private def ordinaryContWithC0 (saved : Continuation := .quit 99) : Continuation :=
  .ordinary
    (Slice.ofCell Cell.empty)
    (.quit 0)
    { OrdCregs.empty with c0 := some saved }
    OrdCdata.empty

private def mkPrefixedIfelserefCodeCell
    (pre : Array Instr)
    (refCell : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let preCell := assembleNoRefCell! "ifelseref/prefix" pre
  let tailCell := assembleNoRefCell! "ifelseref/tail" tail
  Cell.mkOrdinary
    (preCell.bits ++ natToBits ifelserefOpcode 16 ++ tailCell.bits)
    (preCell.refs ++ #[refCell] ++ tailCell.refs)

private def mkIfelserefCodeCell
    (refCell : Cell)
    (tail : Array Instr := #[]) : Cell :=
  mkPrefixedIfelserefCodeCell #[] refCell tail

private def mkIfelserefMissingRefCodeCell
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "ifelseref/missing-ref-tail" tail
  Cell.mkOrdinary
    (natToBits ifelserefOpcode 16 ++ tailCell.bits)
    tailCell.refs

private def mkTwoIfelserefCodeCell
    (refA refB : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "ifelseref/two-tail" tail
  Cell.mkOrdinary
    (natToBits ifelserefOpcode 16 ++ natToBits ifelserefOpcode 16 ++ tailCell.bits)
    (#[refA, refB] ++ tailCell.refs)

private def mkTwoIfelserefOneRefCodeCell
    (refA : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "ifelseref/two-one-ref-tail" tail
  Cell.mkOrdinary
    (natToBits ifelserefOpcode 16 ++ natToBits ifelserefOpcode 16 ++ tailCell.bits)
    (#[refA] ++ tailCell.refs)

private def branchNoop : Cell :=
  Cell.empty

private def branchPushMarker : Cell :=
  assembleOrPanic "ifelseref/branchPushMarker" #[.pushInt (.num branchMarker)]

private def branchAdd : Cell :=
  assembleOrPanic "ifelseref/branchAdd" #[.add]

private def truePushMarker : Cell :=
  assembleOrPanic "ifelseref/truePushMarker" #[.pushInt (.num 919)]

private def codeObserveTail : Cell :=
  mkIfelserefCodeCell branchPushMarker #[.pushInt (.num tailMarker)]

private def codeElseAddTail : Cell :=
  mkIfelserefCodeCell branchAdd #[.pushInt (.num tailMarker)]

private def codeMissingRefTail : Cell :=
  mkIfelserefMissingRefCodeCell #[.pushInt (.num tailMarker)]

private def codePushCtr0ObserveTail : Cell :=
  mkPrefixedIfelserefCodeCell #[.pushCtr 0] branchPushMarker #[.pushInt (.num tailMarker)]

private def codePushCtr1ObserveTail : Cell :=
  mkPrefixedIfelserefCodeCell #[.pushCtr 1] branchPushMarker #[.pushInt (.num tailMarker)]

private def codePushCtr0ElseAddTail : Cell :=
  mkPrefixedIfelserefCodeCell #[.pushCtr 0] branchAdd #[.pushInt (.num tailMarker)]

private def codePushCtr1ElseAddTail : Cell :=
  mkPrefixedIfelserefCodeCell #[.pushCtr 1] branchAdd #[.pushInt (.num tailMarker)]

private def codePushNanCtr0ThenIfelseref : Cell :=
  mkPrefixedIfelserefCodeCell #[.pushInt .nan, .pushCtr 0] branchNoop #[.pushInt (.num tailMarker)]

private def codeTwoIfelserefNoopTail : Cell :=
  mkTwoIfelserefCodeCell branchNoop branchNoop #[.pushInt (.num tailMarker)]

private def codeTwoIfelserefOneRefTail : Cell :=
  mkTwoIfelserefOneRefCodeCell branchNoop #[.pushInt (.num tailMarker)]

private def codeTruncated8WithRef : Cell :=
  Cell.mkOrdinary (natToBits 0xe3 8) #[branchNoop]

private def codeTruncated15WithRef : Cell :=
  Cell.mkOrdinary (natToBits ifelserefOpcode 15) #[branchNoop]

private def withCondCont
    (below : Array Value)
    (cond : Int)
    (cont : Continuation := .quit 0) : Array Value :=
  below ++ #[intV cond, .cont cont]

private def runIfelserefDirect (refCell : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfelseRef (mkIfelserefInstr refCell) stack

private def runIfelserefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfelseRef instr (VM.push (intV dispatchSentinel)) stack

private def runIfelserefRaw
    (refCell : Cell)
    (stack : Array Value)
    (cc : Continuation := .quit 71)
    (regs : Regs := Regs.initial)
    (loaded : Array (Array UInt8) := #[])
    (gasLimit : Int := 1_000_000) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := regs
      loadedCells := loaded
      gas := GasLimits.ofLimits gasLimit gasLimit 0 }
  (execInstrFlowIfelseRef (mkIfelserefInstr refCell) (pure ())).run st0

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
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")

private def runIfelserefLean (code : Cell) (initStack : Array Value) (fuel : Nat := 200_000) : StepResult :=
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

private def expectTopIntNum (label : String) (expected : Int) (st : VmState) : IO Unit := do
  match st.stack.back? with
  | some (.int (.num n)) =>
      if n = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected top int {expected}, got {n}")
  | some v =>
      throw (IO.userError s!"{label}: expected top int, got {reprStr v}")
  | none =>
      throw (IO.userError s!"{label}: expected non-empty stack")

private def mkCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifelserefId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseWithCont
    (name : String)
    (cond : Int)
    (below : Array Value := #[])
    (codeCell : Cell := codeObserveTail) : OracleCase :=
  mkCase name (withCondCont below cond (.quit 0)) codeCell

private def mkCaseWithFlag
    (name : String)
    (flag : Int)
    (below : Array Value := #[])
    (codeCell : Cell := codePushCtr0ObserveTail) : OracleCase :=
  mkCase name (below ++ #[intV flag]) codeCell

private def ifelserefCondPool : Array Int :=
  #[0, 1, -1, 2, -2, 5, -9, maxInt257, minInt257]

private def ifelserefNoisePool : Array Value :=
  #[.null, intV 7, intV (-3), .cell refLeafA, .cell refLeafB,
    .slice sliceNoiseA, .slice sliceNoiseB, .builder Builder.empty, .tuple #[], q0]

private def ifelserefBadPopContPool : Array Value :=
  #[.null, intV 3, .cell refLeafA, .slice sliceNoiseA, .builder Builder.empty, .tuple #[]]

private def ifelserefBadPopBoolPool : Array Value :=
  #[.null, .cell refLeafA, .slice sliceNoiseB, .builder Builder.empty, .tuple #[]]

private def ifelserefGasZero : OracleGasLimits :=
  { gasLimit := 0, gasMax := 0, gasCredit := 0 }

private def pickFromPool {a : Type} [Inhabited a] (pool : Array a) (rng : StdGen) : a × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genBelowStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool ifelserefNoisePool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def genIfelserefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 25
  let (depth, rng2) := randNat rng1 0 4
  let (below, rng3) := genBelowStack depth rng2
  let (condRaw, rng4) := pickFromPool ifelserefCondPool rng3
  let cond := if condRaw = 0 then 1 else condRaw
  let (badCont, rng5) := pickFromPool ifelserefBadPopContPool rng4
  let (badBool, rng6) := pickFromPool ifelserefBadPopBoolPool rng5
  let base :=
    if shape = 0 then
      mkCaseWithCont s!"fuzz/ok/branch/false/deep-{depth}" 0 below codeObserveTail
    else if shape = 1 then
      mkCaseWithCont s!"fuzz/ok/branch/true/deep-{depth}" cond below codeObserveTail
    else if shape = 2 then
      mkCaseWithCont "fuzz/ok/branch/false/basic" 0 #[] codeObserveTail
    else if shape = 3 then
      mkCaseWithCont "fuzz/ok/branch/true/basic" 1 #[] codeObserveTail
    else if shape = 4 then
      mkCaseWithFlag s!"fuzz/ok/prefix-ctr0/false/deep-{depth}" 0 below codePushCtr0ObserveTail
    else if shape = 5 then
      mkCaseWithFlag s!"fuzz/ok/prefix-ctr0/true/deep-{depth}" cond below codePushCtr0ObserveTail
    else if shape = 6 then
      mkCaseWithFlag s!"fuzz/ok/prefix-ctr1/false/deep-{depth}" 0 below codePushCtr1ObserveTail
    else if shape = 7 then
      mkCaseWithFlag s!"fuzz/ok/prefix-ctr1/true/deep-{depth}" cond below codePushCtr1ObserveTail
    else if shape = 8 then
      mkCaseWithCont "fuzz/err/add/false-underflow" 0 #[] codeElseAddTail
    else if shape = 9 then
      mkCaseWithCont "fuzz/ok/add/true-underflow-avoided" 1 #[] codeElseAddTail
    else if shape = 10 then
      mkCaseWithCont "fuzz/ok/add/false-two-ints" 0 (below ++ #[intV 5, intV 6]) codeElseAddTail
    else if shape = 11 then
      mkCaseWithFlag "fuzz/err/prefix-add/ctr0-false-underflow" 0 #[] codePushCtr0ElseAddTail
    else if shape = 12 then
      mkCaseWithFlag "fuzz/ok/prefix-add/ctr1-true-underflow-avoided" 1 #[] codePushCtr1ElseAddTail
    else if shape = 13 then
      mkCase "fuzz/err/underflow/empty" #[] codeObserveTail
    else if shape = 14 then
      mkCase "fuzz/err/underflow/one-int" #[intV 0] codeObserveTail
    else if shape = 15 then
      mkCase s!"fuzz/err/popcont/type/deep-{depth}" (below ++ #[intV cond, badCont]) codeObserveTail
    else if shape = 16 then
      mkCase s!"fuzz/err/popbool/type/deep-{depth}" (below ++ #[badBool, q0]) codeObserveTail
    else if shape = 17 then
      mkCase "fuzz/err/popbool/intov-nan-from-prefix" #[] codePushNanCtr0ThenIfelseref
    else if shape = 18 then
      mkCase s!"fuzz/err/decode/missing-ref/deep-{depth}"
        (withCondCont below cond (.quit 0))
        codeMissingRefTail
    else if shape = 19 then
      mkCase "fuzz/err/decode/truncated-8bit" #[intV 0] codeTruncated8WithRef
    else if shape = 20 then
      mkCase "fuzz/err/decode/truncated-15bit" #[intV 0] codeTruncated15WithRef
    else if shape = 21 then
      mkCase s!"fuzz/err/two-ifelseref-one-ref/first-false-second-missing/deep-{depth}"
        (below ++ #[intV 0, q0])
        codeTwoIfelserefOneRefTail
    else if shape = 22 then
      mkCase s!"fuzz/ok/two-ifelseref-noop/first-false-second-true/deep-{depth}"
        (below ++ #[intV 1, q0, intV 0, q0])
        codeTwoIfelserefNoopTail
    else if shape = 23 then
      mkCase s!"fuzz/ok/two-ifelseref-noop/both-false/deep-{depth}"
        (below ++ #[intV 0, q0, intV 0, q0])
        codeTwoIfelserefNoopTail
    else if shape = 24 then
      mkCase s!"fuzz/ok/branch/false/replay/deep-{depth}"
        (withCondCont below 0 (.quit 0))
        codeObserveTail
    else
      mkCase s!"fuzz/ok/branch/true/replay/deep-{depth}"
        (withCondCont below cond (.quit 0))
        codeObserveTail
  let (tag, rng7) := randNat rng6 0 999_999
  ({ base with name := s!"{base.name}/{tag}" }, rng7)

def suite : InstrSuite where
  id := ifelserefId
  unit := #[
    { name := "unit/raw/branch-split-load-gating-and-call-transition"
      run := do
        let ccOrd : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

        let stTrue ← expectRawOk "raw/true"
          (runIfelserefRaw branchPushMarker (withCondCont #[intV 9] 1 (ordinaryCont truePushMarker)) (cc := ccOrd))
        if stTrue.stack != #[intV 9] then
          throw (IO.userError s!"raw/true: expected stack #[9], got {reprStr stTrue.stack}")
        if !stTrue.loadedCells.isEmpty then
          throw (IO.userError s!"raw/true: expected no loaded cells, got {reprStr stTrue.loadedCells}")
        if stTrue.gas.gasConsumed != 0 then
          throw (IO.userError s!"raw/true: expected zero gas, got {stTrue.gas.gasConsumed}")
        match stTrue.cc with
        | .ordinary code _ _ _ =>
            if code != Slice.ofCell truePushMarker then
              throw (IO.userError s!"raw/true: expected true continuation code, got {reprStr code}")
        | other =>
            throw (IO.userError s!"raw/true: expected ordinary cc, got {reprStr other}")
        match stTrue.regs.c0 with
        | .ordinary _ _ _ _ => pure ()
        | other =>
            throw (IO.userError s!"raw/true: expected ordinary return c0, got {reprStr other}")

        let stFalse ← expectRawOk "raw/false"
          (runIfelserefRaw branchPushMarker (withCondCont #[intV 9] 0 (.quit 9)) (cc := ccOrd))
        if stFalse.stack != #[intV 9] then
          throw (IO.userError s!"raw/false: expected stack #[9], got {reprStr stFalse.stack}")
        if stFalse.loadedCells.size != 1 then
          throw (IO.userError s!"raw/false: expected one loaded cell, got {stFalse.loadedCells.size}")
        if stFalse.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError
            s!"raw/false: expected gas={cellLoadGasPrice}, got {stFalse.gas.gasConsumed}")
        match stFalse.cc with
        | .ordinary code _ _ _ =>
            if code != Slice.ofCell branchPushMarker then
              throw (IO.userError s!"raw/false: expected referenced code, got {reprStr code}")
        | other =>
            throw (IO.userError s!"raw/false: expected ordinary cc, got {reprStr other}")
        match stFalse.regs.c0 with
        | .ordinary _ _ _ _ => pure ()
        | other =>
            throw (IO.userError s!"raw/false: expected ordinary return c0, got {reprStr other}") }
    ,
    { name := "unit/direct/true-branch-uses-vm-call-contract"
      run := do
        let needThree := ordinaryCont Cell.empty 3 #[]
        expectErr "call/true/nargs-underflow"
          (runIfelserefDirect branchNoop #[intV 4, intV 5, intV 1, .cont needThree])
          .stkUnd

        let capturedOne := ordinaryCont Cell.empty 1 #[intV 44]
        expectOkStack "call/true/ordinary-captured-plus-top1"
          (runIfelserefDirect branchNoop #[intV 7, intV 8, intV 1, .cont capturedOne])
          #[intV 44, intV 8]

        let envCaptured := envelopeCont 1 #[intV 55]
        expectOkStack "call/true/envelope-captured-plus-top1"
          (runIfelserefDirect branchNoop #[intV 3, intV 6, intV 1, .cont envCaptured])
          #[intV 55, intV 6] }
    ,
    { name := "unit/raw/true-branch-c0-defined-cont-reduces-to-jump"
      run := do
        let regsCustom : Regs := { Regs.initial with c0 := .quit 17 }
        let ccOrd : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        let callee := ordinaryContWithC0 (.quit 99)
        let st ← expectRawOk "raw/c0-defined"
          (runIfelserefRaw branchPushMarker (withCondCont #[] 1 callee) (cc := ccOrd) (regs := regsCustom))
        if st.stack != #[] then
          throw (IO.userError s!"raw/c0-defined: expected empty stack, got {reprStr st.stack}")
        if st.cc != callee then
          throw (IO.userError s!"raw/c0-defined: expected jump to callee, got {reprStr st.cc}")
        if st.regs.c0 != regsCustom.c0 then
          throw (IO.userError
            s!"raw/c0-defined: expected c0 unchanged {reprStr regsCustom.c0}, got {reprStr st.regs.c0}")
        if !st.loadedCells.isEmpty then
          throw (IO.userError s!"raw/c0-defined: expected no loaded cells, got {reprStr st.loadedCells}") }
    ,
    { name := "unit/raw/pop-order-and-error-side-effects"
      run := do
        expectErr "underflow/empty" (runIfelserefDirect branchPushMarker #[]) .stkUnd
        expectErr "underflow/one-int" (runIfelserefDirect branchPushMarker #[intV 0]) .stkUnd
        expectErr "underflow/one-cont" (runIfelserefDirect branchPushMarker #[q0]) .stkUnd

        let stContType ← expectRawErr "type/popcont-null-top"
          (runIfelserefRaw branchPushMarker #[intV 77, .null])
          .typeChk
        if stContType.stack != #[intV 77] then
          throw (IO.userError
            s!"type/popcont-null-top: expected stack #[77], got {reprStr stContType.stack}")
        if !stContType.loadedCells.isEmpty then
          throw (IO.userError "type/popcont-null-top: unexpected cell-load side effect")

        let stBoolType ← expectRawErr "type/popbool-null"
          (runIfelserefRaw branchPushMarker #[.null, q0])
          .typeChk
        if stBoolType.stack != #[] then
          throw (IO.userError s!"type/popbool-null: expected empty stack, got {reprStr stBoolType.stack}")
        if !stBoolType.loadedCells.isEmpty then
          throw (IO.userError "type/popbool-null: unexpected cell-load side effect")

        let stBoolNan ← expectRawErr "intov/popbool-nan"
          (runIfelserefRaw branchPushMarker #[.int .nan, q0])
          .intOv
        if stBoolNan.stack != #[] then
          throw (IO.userError s!"intov/popbool-nan: expected empty stack, got {reprStr stBoolNan.stack}")
        if !stBoolNan.loadedCells.isEmpty then
          throw (IO.userError "intov/popbool-nan: unexpected cell-load side effect") }
    ,
    { name := "unit/raw/out-of-gas-only-else-branch-loads-ref"
      run := do
        let stElse ← expectRawErr "oog/else-branch"
          (runIfelserefRaw branchPushMarker (withCondCont #[] 0 (.quit 0)) (gasLimit := 0))
          .outOfGas
        if stElse.stack != #[] then
          throw (IO.userError s!"oog/else-branch: expected empty stack, got {reprStr stElse.stack}")
        if stElse.loadedCells.size != 1 then
          throw (IO.userError s!"oog/else-branch: expected one loaded cell, got {stElse.loadedCells.size}")

        let stTrue ← expectRawOk "oog/true-branch"
          (runIfelserefRaw branchPushMarker (withCondCont #[] 1 (.quit 0)) (gasLimit := 0))
        if stTrue.stack != #[] then
          throw (IO.userError s!"oog/true-branch: expected empty stack, got {reprStr stTrue.stack}")
        if !stTrue.loadedCells.isEmpty then
          throw (IO.userError s!"oog/true-branch: expected no loaded cells, got {reprStr stTrue.loadedCells}") }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfelserefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/matched-ifelseref-no-next"
          (runHandlerDirectWithNext execInstrFlowIfelseRef (mkIfelserefInstr branchNoop)
            (VM.push (intV dispatchSentinel))
            (withCondCont #[] 1 (.quit 0)))
          #[] }
    ,
    { name := "unit/decode/opcode-boundaries-missing-ref-and-asm-rejection"
      run := do
        let bits : BitString :=
          natToBits 0xe30d 16 ++
          natToBits 0xe30e 16 ++
          natToBits 0xe30f 16 ++
          natToBits 0xa0 8
        let code : Cell := Cell.mkOrdinary bits #[branchNoop, branchPushMarker, branchNoop, branchPushMarker]
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ifrefelse" s0 (.ifrefElse (Slice.ofCell branchNoop)) 16
        let s2 ← expectDecodeStep "decode/ifelseref" s1 (mkIfelserefInstr branchPushMarker) 16
        let s3 ← expectDecodeStep "decode/ifrefelseref" s2
          (.ifrefElseRef (Slice.ofCell branchNoop) (Slice.ofCell branchPushMarker)) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 && s4.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/sequence-end: expected exhausted slice, got bits={s4.bitsRemaining} refs={s4.refsRemaining}")

        expectDecodeErr "decode/missing-ref" codeMissingRefTail .invOpcode
        expectDecodeErr "decode/truncated-8bit" codeTruncated8WithRef .invOpcode
        expectDecodeErr "decode/truncated-15bit" codeTruncated15WithRef .invOpcode

        match assembleCp0 [mkIfelserefInstr branchNoop] with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"asm/ifelseref: expected invOpcode, got {e}")
        | .ok c =>
            throw (IO.userError s!"asm/ifelseref: expected invOpcode, got assembled code {reprStr c}") }
    ,
    { name := "unit/full-run/branch-gating-tail-observation-and-ctr-selection"
      run := do
        let stElseTail ← expectExit "full/ctr0/false-runs-else-and-tail" (~~~ 0)
          (runIfelserefLean codePushCtr0ObserveTail #[intV 0])
        expectTopIntNum "full/ctr0/false-runs-else-and-tail" tailMarker stElseTail

        let stTrueCtr0 ← expectExit "full/ctr0/true-calls-c0-and-stops" (~~~ 0)
          (runIfelserefLean codePushCtr0ObserveTail #[intV 1])
        if stTrueCtr0.stack != #[] then
          throw (IO.userError s!"full/ctr0/true-calls-c0-and-stops: expected empty stack, got {reprStr stTrueCtr0.stack}")

        let _ ← expectExit "full/ctr1/true-calls-c1" (~~~ 1)
          (runIfelserefLean codePushCtr1ObserveTail #[intV 1])

        let _ ← expectExit "full/add-gating/false-runs-else-add" (~~~ Excno.stkUnd.toInt)
          (runIfelserefLean codePushCtr0ElseAddTail #[intV 0])

        let stSkipAdd ← expectExit "full/add-gating/true-skips-else-add" (~~~ 0)
          (runIfelserefLean codePushCtr0ElseAddTail #[intV 1])
        if stSkipAdd.stack != #[] then
          throw (IO.userError s!"full/add-gating/true-skips-else-add: expected empty stack, got {reprStr stSkipAdd.stack}") }
  ]
  oracle := #[
    -- Branch-observable matrix with explicit continuation on stack (`quit0` token).
    mkCaseWithCont "ok/branch/false/zero-basic" 0 #[] codeObserveTail,
    mkCaseWithCont "ok/branch/false/zero-noiseA" 0 noiseA codeObserveTail,
    mkCaseWithCont "ok/branch/false/zero-noiseB" 0 noiseB codeObserveTail,
    mkCaseWithCont "ok/branch/false/zero-noiseC" 0 noiseC codeObserveTail,
    mkCaseWithCont "ok/branch/false/zero-max-below" 0 #[intV maxInt257] codeObserveTail,
    mkCaseWithCont "ok/branch/false/zero-min-below" 0 #[intV minInt257] codeObserveTail,
    mkCaseWithCont "ok/branch/true/one-basic" 1 #[] codeObserveTail,
    mkCaseWithCont "ok/branch/true/minus-one" (-1) #[] codeObserveTail,
    mkCaseWithCont "ok/branch/true/two" 2 #[] codeObserveTail,
    mkCaseWithCont "ok/branch/true/max257" maxInt257 #[] codeObserveTail,
    mkCaseWithCont "ok/branch/true/min257" minInt257 #[] codeObserveTail,
    mkCaseWithCont "ok/branch/true/noiseA" 7 noiseA codeObserveTail,
    mkCaseWithCont "ok/branch/true/noiseB" (-9) noiseB codeObserveTail,
    mkCaseWithCont "ok/branch/true/noiseC" 5 noiseC codeObserveTail,

    -- Prefix-pushed continuation (`PUSHCTR`) branch matrix.
    mkCaseWithFlag "ok/prefix-ctr0/false/zero" 0 #[] codePushCtr0ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr0/true/one" 1 #[] codePushCtr0ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr0/true/minus-one" (-1) #[] codePushCtr0ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr0/false/deep-noiseA" 0 noiseA codePushCtr0ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr0/true/deep-noiseB" 3 noiseB codePushCtr0ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr1/false/zero" 0 #[] codePushCtr1ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr1/true/one" 1 #[] codePushCtr1ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr1/true/minus-one" (-1) #[] codePushCtr1ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr1/false/deep-noiseA" 0 noiseA codePushCtr1ObserveTail,
    mkCaseWithFlag "ok/prefix-ctr1/true/deep-noiseB" 4 noiseB codePushCtr1ObserveTail,

    -- Else-branch body (`ADD`) proves taken/skip gating.
    mkCaseWithCont "err/add/false-underflow" 0 #[] codeElseAddTail,
    mkCaseWithCont "ok/add/true-underflow-avoided" 1 #[] codeElseAddTail,
    mkCaseWithCont "ok/add/false-two-ints" 0 #[intV 5, intV 6] codeElseAddTail,
    mkCaseWithCont "ok/add/true-two-ints" 1 #[intV 5, intV 6] codeElseAddTail,
    mkCaseWithCont "err/add/false-type-null" 0 #[.null, intV 7] codeElseAddTail,
    mkCaseWithCont "ok/add/true-type-null-avoided" 1 #[.null, intV 7] codeElseAddTail,
    mkCaseWithCont "err/add/false-underflow-one-int" 0 #[intV 9] codeElseAddTail,
    mkCaseWithCont "ok/add/true-underflow-one-int-avoided" 2 #[intV 9] codeElseAddTail,
    mkCaseWithFlag "err/prefix-add/ctr0-false-underflow" 0 #[] codePushCtr0ElseAddTail,
    mkCaseWithFlag "ok/prefix-add/ctr0-true-underflow-avoided" 1 #[] codePushCtr0ElseAddTail,
    mkCaseWithFlag "err/prefix-add/ctr1-false-underflow" 0 #[] codePushCtr1ElseAddTail,
    mkCaseWithFlag "ok/prefix-add/ctr1-true-underflow-avoided" 1 #[] codePushCtr1ElseAddTail,

    -- Pop-site failures with valid referenced branch cell.
    mkCase "err/underflow/empty" #[] codeObserveTail,
    mkCase "err/underflow/one-int" #[intV 0] codeObserveTail,
    mkCase "err/underflow/one-cont" #[q0] codeObserveTail,
    mkCase "err/popcont/type-null-top" #[intV 0, .null] codeObserveTail,
    mkCase "err/popcont/type-int-top" #[intV 0, intV 3] codeObserveTail,
    mkCase "err/popcont/type-cell-top" #[intV 0, .cell refLeafA] codeObserveTail,
    mkCase "err/popcont/type-slice-top" #[intV 0, .slice sliceNoiseA] codeObserveTail,
    mkCase "err/popcont/type-builder-top" #[intV 0, .builder Builder.empty] codeObserveTail,
    mkCase "err/popcont/type-tuple-top" #[intV 0, .tuple #[]] codeObserveTail,
    mkCase "err/popbool/type-null" #[.null, q0] codeObserveTail,
    mkCase "err/popbool/type-cell" #[.cell refLeafA, q0] codeObserveTail,
    mkCase "err/popbool/type-slice" #[.slice sliceNoiseB, q0] codeObserveTail,
    mkCase "err/popbool/type-builder" #[.builder Builder.empty, q0] codeObserveTail,
    mkCase "err/popbool/type-tuple" #[.tuple #[], q0] codeObserveTail,
    mkCase "err/popbool/intov-nan-from-prefix" #[] codePushNanCtr0ThenIfelseref,

    -- Decode/ref-gate ordering and truncation.
    mkCase "err/decode/missing-ref-empty" #[] codeMissingRefTail,
    mkCase "err/decode/missing-ref-one-int" #[intV 0] codeMissingRefTail,
    mkCase "err/decode/missing-ref-one-cont" #[q0] codeMissingRefTail,
    mkCase "err/decode/missing-ref-deep" #[.cell refLeafA, intV 0, q0] codeMissingRefTail,
    mkCase "err/decode/truncated-8bit" #[intV 0] codeTruncated8WithRef,
    mkCase "err/decode/truncated-15bit" #[intV 0] codeTruncated15WithRef,

    -- Two-opcode sequencing (success and second-opcode missing-ref failure).
    mkCase "err/two-ifelseref-one-ref/first-false-second-missing"
      #[intV 0, q0]
      codeTwoIfelserefOneRefTail,
    mkCase "err/two-ifelseref-one-ref/deep-first-false-second-missing"
      #[.null, intV 0, q0]
      codeTwoIfelserefOneRefTail,
    mkCase "ok/two-ifelseref-noop/both-false"
      #[intV 0, q0, intV 0, q0]
      codeTwoIfelserefNoopTail,
    mkCase "ok/two-ifelseref-noop/first-false-second-true"
      #[intV 1, q0, intV 0, q0]
      codeTwoIfelserefNoopTail,
    mkCase "ok/two-ifelseref-noop/deep-both-false"
      #[.cell refLeafA, intV 0, q0, intV 0, q0]
      codeTwoIfelserefNoopTail,
    mkCase "ok/two-ifelseref-noop/deep-first-false-second-true"
      #[.builder Builder.empty, intV 1, q0, intV 0, q0]
      codeTwoIfelserefNoopTail
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr ifelserefId
      count := 500
      gen := genIfelserefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.IFELSEREF
