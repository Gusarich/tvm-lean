import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.UNTILBRK

/-!
UNTILBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.until true`)
  - `TvmLean/Semantics/Step/Step.lean` (`.untilBody` runtime branches)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (`.untilBody` child-vm mirror)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_until`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::until`, `UntilCont::jump[_w]`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `c1_envelope_if`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_cont`, `pop_bool`)

Branch map covered by this suite:
1. Dispatch: `.contExt (.until true)` handled vs fallback to `next`.
2. Front-end stack behavior: underflow/type/order of `pop_cont`.
3. Setup order: `extract_cc(1)` before `c1_envelope_if(true, ...)`.
4. BRK envelope semantics: `c1` update + captured `c0/c1` in `after` continuation.
5. `VmState::until` split:
   - `body.has_c0` => jump to body, no loop continuation installation;
   - no `c0` => install `.untilBody(body, after)` into `c0`, jump body.
6. Runtime `.untilBody` split:
   - bool `true` => jump to `after` (including `after.nargs` underflow guard);
   - bool `false` + body has/no `c0`;
   - bool pop failures (`stkUnd` / `typeChk` / `intOv`);
   - body jump `nargs` underflow parity with C++ `jump_to + adjust_jump_cont`.
-/

private def untilBrkId : InstrId := { name := "UNTILBRK" }

private def untilBrkInstr : Instr := .contExt (.until true)

private def q0 : Value := .cont (.quit 0)

private def dispatchSentinel : Int := 64029

private def tailMarker : Int := 907

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def sliceA : Slice := Slice.ofCell cellA

private def bodyHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 31337) }
    OrdCdata.empty

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

private def untilTailProgram : Array Instr :=
  #[untilBrkInstr, .pushInt (.num tailMarker)]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[untilBrkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := untilBrkId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runUntilBrkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt untilBrkInstr stack

private def runUntilBrkDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runUntilBrkRaw
    (stack : Array Value)
    (cc : Continuation := defaultCc)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowLoopExt untilBrkInstr (pure ())).run st0

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

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (res, st) := out
  match res with
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def expectContinue (label : String) (res : StepResult) : IO VmState := do
  match res with
  | .continue st => pure st
  | .halt code st =>
      throw (IO.userError s!"{label}: expected continue, got halt({code}) with state {reprStr st}")

private def expectExcContinue (label : String) (res : StepResult) (expected : Excno) : IO VmState := do
  let st ← expectContinue label res
  if st.cc != st.regs.c2 then
    throw (IO.userError s!"{label}: expected cc to jump to c2, got {reprStr st.cc}")
  let expectedStack : Array Value := #[intV 0, intV expected.toInt]
  if st.stack != expectedStack then
    throw (IO.userError
      s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st.stack}")
  pure st

private def untilBrkSetGasExact : Int :=
  computeExactGasBudget untilBrkInstr

private def untilBrkSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne untilBrkInstr

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, intV (-3)]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell cellA, .slice sliceA, .builder Builder.empty, .tuple #[]]

def suite : InstrSuite where
  id := untilBrkId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/matched-untilbrk"
          (runUntilBrkDispatchFallback untilBrkInstr #[q0])
          #[]
        expectOkStack "dispatch/fallback-add"
          (runUntilBrkDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel] }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runUntilBrkDirect #[]) .stkUnd
        expectErr "type/top-int" (runUntilBrkDirect #[intV 1]) .typeChk
        expectErr "type/top-null" (runUntilBrkDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runUntilBrkDirect #[.cell cellA]) .typeChk
        expectErr "type/top-slice" (runUntilBrkDirect #[.slice sliceA]) .typeChk
        expectErr "type/top-builder" (runUntilBrkDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty" (runUntilBrkDirect #[.tuple #[]]) .typeChk
        expectErr "order/top-first-before-below-cont"
          (runUntilBrkDirect #[q0, intV 9]) .typeChk }
    ,
    { name := "unit/state/brk-envelope-body-no-c0"
      run := do
        let oldC0 : Continuation := .quit 44
        let oldC1 : Continuation := .quit 55
        let st ← expectRawOk "state/brk-envelope-no-c0"
          (runUntilBrkRaw #[intV 8, q0] defaultCc oldC0 oldC1)

        if st.stack != #[intV 8] then
          throw (IO.userError s!"state/brk-envelope-no-c0: expected stack #[8], got {reprStr st.stack}")
        else if st.cc != .quit 0 then
          throw (IO.userError s!"state/brk-envelope-no-c0: expected cc=quit0, got {reprStr st.cc}")
        else
          match st.regs.c0 with
          | .untilBody body after =>
              if body != .quit 0 then
                throw (IO.userError s!"state/brk-envelope-no-c0: expected body=quit0, got {reprStr body}")
              else if st.regs.c1 != after then
                throw (IO.userError "state/brk-envelope-no-c0: expected c1 to equal after continuation")
              else
                match after with
                | .ordinary _ saved cregs cdata =>
                    if saved != .quit 0 then
                      throw (IO.userError
                        s!"state/brk-envelope-no-c0: expected after.saved=quit0, got {reprStr saved}")
                    else if cregs.c0 != some oldC0 then
                      throw (IO.userError
                        s!"state/brk-envelope-no-c0: expected captured c0={reprStr oldC0}, got {reprStr cregs.c0}")
                    else if cregs.c1 != some oldC1 then
                      throw (IO.userError
                        s!"state/brk-envelope-no-c0: expected captured c1={reprStr oldC1}, got {reprStr cregs.c1}")
                    else if !(cdataEmpty cdata) then
                      throw (IO.userError
                        s!"state/brk-envelope-no-c0: expected empty cdata, got {reprStr cdata}")
                    else
                      pure ()
                | other =>
                    throw (IO.userError
                      s!"state/brk-envelope-no-c0: expected ordinary after, got {reprStr other}")
          | other =>
              throw (IO.userError s!"state/brk-envelope-no-c0: expected c0=untilBody, got {reprStr other}") }
    ,
    { name := "unit/state/brk-envelope-body-has-c0"
      run := do
        let oldC0 : Continuation := .quit 91
        let oldC1 : Continuation := .quit 92
        let st ← expectRawOk "state/brk-envelope-has-c0"
          (runUntilBrkRaw #[intV 7, .cont bodyHasC0] defaultCc oldC0 oldC1)

        if st.stack != #[intV 7] then
          throw (IO.userError s!"state/brk-envelope-has-c0: expected stack #[7], got {reprStr st.stack}")
        else if st.cc != bodyHasC0 then
          throw (IO.userError s!"state/brk-envelope-has-c0: expected cc=bodyHasC0, got {reprStr st.cc}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"state/brk-envelope-has-c0: expected c0=quit0, got {reprStr st.regs.c0}")
        else
          match st.regs.c1 with
          | .ordinary _ saved cregs cdata =>
              if saved != .quit 0 then
                throw (IO.userError
                  s!"state/brk-envelope-has-c0: expected after.saved=quit0, got {reprStr saved}")
              else if cregs.c0 != some oldC0 then
                throw (IO.userError
                  s!"state/brk-envelope-has-c0: expected captured c0={reprStr oldC0}, got {reprStr cregs.c0}")
              else if cregs.c1 != some oldC1 then
                throw (IO.userError
                  s!"state/brk-envelope-has-c0: expected captured c1={reprStr oldC1}, got {reprStr cregs.c1}")
              else if !(cdataEmpty cdata) then
                throw (IO.userError
                  s!"state/brk-envelope-has-c0: expected empty cdata, got {reprStr cdata}")
              else
                pure ()
          | other =>
              throw (IO.userError
                s!"state/brk-envelope-has-c0: expected ordinary c1 after, got {reprStr other}") }
    ,
    { name := "unit/state/non-ordinary-cc-type-before-envelope"
      run := do
        let st ← expectRawErr "state/non-ordinary" 
          (runUntilBrkRaw #[q0] (.quit 13) (.quit 9) (.quit 6))
          .typeChk

        if st.stack != #[] then
          throw (IO.userError s!"state/non-ordinary: expected stack consumed to #[], got {reprStr st.stack}")
        else if st.regs.c0 != .quit 9 then
          throw (IO.userError s!"state/non-ordinary: expected c0 unchanged=quit9, got {reprStr st.regs.c0}")
        else if st.regs.c1 != .quit 6 then
          throw (IO.userError s!"state/non-ordinary: expected c1 unchanged=quit6, got {reprStr st.regs.c1}")
        else
          pure () }
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
        let after : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 77) OrdCregs.empty OrdCdata.empty
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
    { name := "unit/step/pop-bool-errors-and-after-nargs-underflow"
      run := do
        let _ ← expectExcContinue "step/pop-bool/underflow"
          (runUntilBodyStep #[] (.quit 9) (.quit 17))
          .stkUnd
        let _ ← expectExcContinue "step/pop-bool/type"
          (runUntilBodyStep #[.null] (.quit 9) (.quit 17))
          .typeChk
        let _ ← expectExcContinue "step/pop-bool/intov"
          (runUntilBodyStep #[.int .nan] (.quit 9) (.quit 17))
          .intOv

        let afterNeedArg : Continuation :=
          .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := 1 }
        let _ ← expectExcContinue "step/after-nargs/underflow"
          (runUntilBodyStep #[intV 1] (.quit 9) afterNeedArg)
          .stkUnd
        pure () }
    ,
    { name := "unit/step/body-nargs-underflow-ordering"
      run := do
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 70

        let bodyNeedArgHasC0 : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0)
            { OrdCregs.empty with c0 := some (.quit 404) }
            { stack := #[], nargs := 1 }
        let stHasC0 ← expectExcContinue "step/body-nargs/has-c0"
          (runUntilBodyStep #[intV 0] bodyNeedArgHasC0 after marker)
          .stkUnd
        if stHasC0.regs.c0 != marker then
          throw (IO.userError
            s!"step/body-nargs/has-c0: expected c0 unchanged={reprStr marker}, got {reprStr stHasC0.regs.c0}")

        let bodyNeedArgNoC0 : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0)
            OrdCregs.empty
            { stack := #[], nargs := 1 }
        let stNoC0 ← expectExcContinue "step/body-nargs/no-c0"
          (runUntilBodyStep #[intV 0] bodyNeedArgNoC0 after marker)
          .stkUnd
        if stNoC0.regs.c0 != .untilBody bodyNeedArgNoC0 after then
          throw (IO.userError
            s!"step/body-nargs/no-c0: expected c0 preinstalled to untilBody, got {reprStr stNoC0.regs.c0}")
        pure () }
  ]
  oracle := #[
    -- Direct `UNTILBRK` with oracle-encodable continuation token K=quit(0).
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
    mkCase "ok/direct/no-tail/cell-int-builder-tuple" #[.cell cellA, intV (-22), .builder Builder.empty, .tuple #[], q0],
    mkCase "ok/direct/no-tail/int-slice-null" #[intV 123456789, .slice sliceA, .null, q0],
    mkCase "ok/direct/no-tail/noise-a" (noiseA ++ #[q0]),
    mkCase "ok/direct/no-tail/noise-b" (noiseB ++ #[q0]),

    -- Tail instruction must be skipped when UNTILBRK jumps into the loop body.
    mkCase "ok/direct/tail-skipped/basic" #[q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/noise-a" (noiseA ++ #[q0]) untilTailProgram,
    mkCase "ok/direct/tail-skipped/noise-b" (noiseB ++ #[q0]) untilTailProgram,
    mkCase "ok/direct/tail-skipped/max-int257" #[intV maxInt257, q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/min-int257" #[intV minInt257, q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/deep-long" (noiseLong ++ #[q0]) untilTailProgram,
    mkCase "ok/direct/tail-skipped/mixed-slice-builder" #[.slice sliceA, .builder Builder.empty, q0] untilTailProgram,
    mkCase "ok/direct/tail-skipped/cell-null-int" #[.cell cellA, .null, intV 12, q0] untilTailProgram,

    -- `pop_cont` underflow/type behavior and top-first ordering.
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
    mkCase "err/type/top-builder-with-below-cont" #[q0, .builder Builder.empty],
    mkCase "err/type/top-slice-with-below-cont" #[q0, .slice sliceA],
    mkCase "err/type/top-tuple-with-below-int" #[intV 5, .tuple #[]],

    -- Deterministic gas cliff.
    mkCase "gas/exact-succeeds" #[q0]
      #[.pushInt (.num untilBrkSetGasExact), .tonEnvOp .setGasLimit, untilBrkInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[q0]
      #[.pushInt (.num untilBrkSetGasExactMinusOne), .tonEnvOp .setGasLimit, untilBrkInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.UNTILBRK
