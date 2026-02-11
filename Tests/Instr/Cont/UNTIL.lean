import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.UNTIL

/-!
UNTIL branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Until.lean`
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.until` / `.untilEnd`)
  - `TvmLean/Semantics/Step/Step.lean` (`.untilBody`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_until`, `exec_until_end`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::until`, `UntilCont::jump[_w]`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`, `Stack::pop_bool`)

Branch map and ordering covered by this suite:
- instruction dispatch: `.until` handled vs fallback to `next`;
- `pop_cont` underflow/type ordering;
- `extract_cc(1)` side-effect on `c0` (critical for `body.hasC0`);
- `VmState::until` split: `body.hasC0` true/false;
- `UntilCont` runtime branches:
  - bool true (terminate to `after`);
  - bool false + body has/no `c0`;
  - bool pop failures (`stkUnd` / `typeChk` / `intOv`).
-/

private def untilId : InstrId := { name := "UNTIL" }

private def untilInstr : Instr := .until

private def q0 : Value := .cont (.quit 0)

private def dispatchSentinel : Int := 64021

private def tailMarker : Int := 771

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def sliceA : Slice := Slice.ofCell cellA

private def bodyHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 31337) }
    OrdCdata.empty

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def untilTailProgram : Array Instr :=
  #[untilInstr, .pushInt (.num tailMarker)]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[untilInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := untilId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runUntilDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowUntil untilInstr stack

private def runUntilDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowUntil instr (VM.push (intV dispatchSentinel)) stack

private def runUntilState
    (stack : Array Value)
    (c0 : Continuation := .quit 0)
    (cc : Continuation := defaultCc) : Except Excno VmState := do
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := cc }
  let (res, st1) := (execInstrFlowUntil untilInstr (pure ())).run st0
  match res with
  | .ok _ => pure st1
  | .error e => throw e

private def runUntilBodyStep
    (stack : Array Value)
    (body after : Continuation)
    (c0 : Continuation := .quit 0) : StepResult :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := .untilBody body after }
  VmState.step stubHost st0

private def expectStateOk (label : String) (res : Except Excno VmState) : IO VmState := do
  match res with
  | .ok st => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectStateErr
    (label : String)
    (res : Except Excno VmState)
    (expected : Excno) : IO Unit := do
  match res with
  | .ok st => throw (IO.userError s!"{label}: expected error {expected}, got state {reprStr st}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectContinue (label : String) (res : StepResult) : IO VmState := do
  match res with
  | .continue st => pure st
  | .halt code st =>
      throw (IO.userError s!"{label}: expected continue, got halt({code}) with state {reprStr st}")

private def untilSetGasExact : Int :=
  computeExactGasBudget untilInstr

private def untilSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne untilInstr

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, intV (-3)]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell cellA, .slice sliceA, .builder Builder.empty, .tuple #[]]

def suite : InstrSuite where
  id := untilId
  unit := #[
    { name := "unit/state/body-with-c0-resets-c0-to-quit0"
      run := do
        let oldC0 : Continuation := .quit 91
        let st ← expectStateOk "state/body-has-c0" (runUntilState #[intV 7, .cont bodyHasC0] oldC0)
        if st.stack != #[intV 7] then
          throw (IO.userError s!"state/body-has-c0: expected stack #[7], got {reprStr st.stack}")
        if st.cc != bodyHasC0 then
          throw (IO.userError s!"state/body-has-c0: expected cc=bodyHasC0, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"state/body-has-c0: expected c0=quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/body-without-c0-installs-loop-and-captures-c0"
      run := do
        let oldC0 : Continuation := .quit 44
        let st ← expectStateOk "state/body-no-c0" (runUntilState #[intV 8, q0] oldC0)
        if st.stack != #[intV 8] then
          throw (IO.userError s!"state/body-no-c0: expected stack #[8], got {reprStr st.stack}")
        if st.cc != .quit 0 then
          throw (IO.userError s!"state/body-no-c0: expected cc=quit0, got {reprStr st.cc}")
        match st.regs.c0 with
        | .untilBody body after =>
            if body != .quit 0 then
              throw (IO.userError s!"state/body-no-c0: expected until body=quit0, got {reprStr body}")
            match after with
            | .ordinary _ saved cregs cdata =>
                if saved != .quit 0 then
                  throw (IO.userError
                    s!"state/body-no-c0: expected after.savedC0=quit0, got {reprStr saved}")
                if cregs.c0 != some oldC0 then
                  throw (IO.userError
                    s!"state/body-no-c0: expected after.cregs.c0={reprStr oldC0}, got {reprStr cregs.c0}")
                if !cdata.stack.isEmpty ∨ cdata.nargs != -1 then
                  throw (IO.userError
                    s!"state/body-no-c0: expected empty cdata/-1 nargs, got {reprStr cdata}")
            | other =>
                throw (IO.userError s!"state/body-no-c0: expected ordinary after, got {reprStr other}")
        | other =>
            throw (IO.userError s!"state/body-no-c0: expected c0=untilBody, got {reprStr other}") }
    ,
    { name := "unit/state/extractcc-requires-ordinary-current-cc"
      run := do
        expectStateErr "state/non-ordinary-cc"
          (runUntilState #[q0] (.quit 0) (.quit 13))
          .typeChk }
    ,
    { name := "unit/step/untilbody-false-reinstalls-loop-when-body-has-no-c0"
      run := do
        let body : Continuation := .quit 5
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 61
        let st ← expectContinue "step/false/no-c0" (runUntilBodyStep #[intV 0] body after marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/false/no-c0: expected empty stack, got {reprStr st.stack}")
        if st.cc != body then
          throw (IO.userError s!"step/false/no-c0: expected cc=body, got {reprStr st.cc}")
        if st.regs.c0 != .untilBody body after then
          throw (IO.userError
            s!"step/false/no-c0: expected c0 reinstalled untilBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/untilbody-false-keeps-c0-when-body-has-c0"
      run := do
        let marker : Continuation := .quit 62
        let after : Continuation := .quit 17
        let st ← expectContinue "step/false/has-c0" (runUntilBodyStep #[intV 0] bodyHasC0 after marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/false/has-c0: expected empty stack, got {reprStr st.stack}")
        if st.cc != bodyHasC0 then
          throw (IO.userError s!"step/false/has-c0: expected cc=bodyHasC0, got {reprStr st.cc}")
        if st.regs.c0 != marker then
          throw (IO.userError s!"step/false/has-c0: expected c0 unchanged={reprStr marker}, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/untilbody-true-jumps-to-after-and-restores-saved-c0"
      run := do
        let after : Continuation := .ordinary (Slice.ofCell Cell.empty) (.quit 77) OrdCregs.empty OrdCdata.empty
        let st ← expectContinue "step/true" (runUntilBodyStep #[intV 1] (.quit 9) after (.quit 88))
        let expectedCc : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        if st.stack != #[] then
          throw (IO.userError s!"step/true: expected empty stack, got {reprStr st.stack}")
        if st.regs.c0 != .quit 77 then
          throw (IO.userError s!"step/true: expected c0=quit77, got {reprStr st.regs.c0}")
        if st.cc != expectedCc then
          throw (IO.userError s!"step/true: expected cc={reprStr expectedCc}, got {reprStr st.cc}") }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runUntilDirect #[]) .stkUnd
        expectErr "type/top-int" (runUntilDirect #[intV 1]) .typeChk
        expectErr "type/top-null" (runUntilDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runUntilDirect #[.cell cellA]) .typeChk
        expectErr "type/top-slice" (runUntilDirect #[.slice sliceA]) .typeChk
        expectErr "type/top-builder" (runUntilDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty" (runUntilDirect #[.tuple #[]]) .typeChk
        expectErr "order/top-first-before-below-cont"
          (runUntilDirect #[q0, intV 9]) .typeChk }
    ,
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/matched-until"
          (runUntilDispatchFallback untilInstr #[q0])
          #[]
        expectOkStack "dispatch/fallback-add"
          (runUntilDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel] }
  ]
  oracle := #[
    -- Direct `UNTIL` with oracle-encodable continuation K=quit(0).
    mkCase "ok/direct/tail-skipped/basic" #[q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/noise-a" (noiseA ++ #[q0]) untilTailProgram,
    mkCase "ok/direct/tail-skipped/noise-b" (noiseB ++ #[q0]) untilTailProgram,
    mkCase "ok/direct/no-tail/empty-prefix" #[q0],
    mkCase "ok/direct/no-tail/int-noise" #[intV 7, q0],
    mkCase "ok/direct/no-tail/null-noise" #[.null, q0],
    mkCase "ok/direct/no-tail/cell-noise" #[.cell cellA, q0],
    mkCase "ok/direct/no-tail/slice-noise" #[.slice sliceA, q0],
    mkCase "ok/direct/no-tail/builder-noise" #[.builder Builder.empty, q0],
    mkCase "ok/direct/no-tail/tuple-empty-noise" #[.tuple #[], q0],
    mkCase "ok/direct/no-tail/mixed-a" #[.null, intV 9, .cell cellA, q0],
    mkCase "ok/direct/no-tail/mixed-b" #[.slice sliceA, .builder Builder.empty, intV (-3), q0],
    mkCase "ok/direct/no-tail/max-int257" #[intV maxInt257, q0],
    mkCase "ok/direct/no-tail/min-int257" #[intV minInt257, q0],
    mkCase "ok/direct/no-tail/deep-long" (noiseLong ++ #[q0]),

    -- `pop_cont` underflow/type behavior.
    mkCase "err/underflow/empty" #[],
    mkCase "err/type/top-int" #[intV 1],
    mkCase "err/type/top-null" #[.null],
    mkCase "err/type/top-cell" #[.cell cellA],
    mkCase "err/type/top-slice" #[.slice sliceA],
    mkCase "err/type/top-builder" #[.builder Builder.empty],
    mkCase "err/type/top-tuple-empty" #[.tuple #[]],
    mkCase "err/type/top-int-with-below-cont" #[q0, intV 5],
    mkCase "err/type/top-null-with-below-int" #[intV 7, .null],
    mkCase "err/type/top-cell-with-deep-noise" #[.null, intV 7, .cell cellA],

    -- Additional direct execution matrices (oracle-encodable, deterministic).
    mkCase "ok/direct/tail-skipped/max-int257-noise" #[intV maxInt257, q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/min-int257-noise" #[intV minInt257, q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/deep-long" (noiseLong ++ #[q0]) untilTailProgram,
    mkCase "ok/direct/tail-skipped/mixed-slice-builder" #[.slice sliceA, .builder Builder.empty, q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/cell-null-int" #[.cell cellA, .null, intV 12, q0] untilTailProgram,
    mkCase "ok/direct/no-tail/null-slice" #[.null, .slice sliceA, q0],
    mkCase "ok/direct/no-tail/int-triple" #[intV 0, intV 1, intV (-1), q0],
    mkCase "ok/direct/no-tail/builder-tuple-cell" #[.builder Builder.empty, .tuple #[], .cell cellA, q0],
    mkCase "ok/direct/no-tail/int-slice-null" #[intV 123456789, .slice sliceA, .null, q0],
    mkCase "ok/direct/no-tail/cell-int-builder-tuple" #[.cell cellA, intV (-22), .builder Builder.empty, .tuple #[], q0],

    -- Deterministic gas cliff.
    mkCase "gas/exact-succeeds" #[q0]
      #[.pushInt (.num untilSetGasExact), .tonEnvOp .setGasLimit, untilInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[q0]
      #[.pushInt (.num untilSetGasExactMinusOne), .tonEnvOp .setGasLimit, untilInstr]
  ]
  fuzz := #[ mkReplayOracleFuzzSpec untilId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.UNTIL
