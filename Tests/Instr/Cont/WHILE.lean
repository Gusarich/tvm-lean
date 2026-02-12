import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.WHILE

/-!
WHILE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/While.lean`
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.while/.whileEnd` + BRK variants)
  - `TvmLean/Semantics/Step/Step.lean` / `.../Exec/Flow/Runvm.lean` (`.whileCond/.whileBody`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_while`, `exec_while_end`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::loop_while`, `WhileCont::jump[_w]`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`)

Branch map and ordering covered by this suite:
- dispatch branch (`.while_` handled vs fallback to `next`);
- stack pop ordering (`body` first, then `cond`) with underflow/type checks;
- `extract_cc(1)` ordering for WHILE/WHILEBRK (`pop`s happen before ordinary-cc requirement);
- `extract_cc(0)` ordering for WHILEEND/WHILEENDBRK;
- runtime `.whileCond/.whileBody` transitions:
  - true/false condition branches;
  - `hasC0`-gated c0 reinstallation order (`body.hasC0`, `cond.hasC0`);
  - pop-bool errors delegated through exception path.
-/

private def whileId : InstrId := { name := "WHILE" }

private def whileInstr : Instr := .while_

private def whileBrkInstr : Instr := .contExt (.while true)

private def whileEndInstr : Instr := .contExt (.whileEnd false)

private def whileEndBrkInstr : Instr := .contExt (.whileEnd true)

private def q0 : Value := .cont (.quit 0)

private def dispatchSentinel : Int := 64031

private def tailMarker : Int := 911

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def sliceA : Slice := Slice.ofCell cellA

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def condNoC0 : Continuation := .quit 5

private def bodyNoC0 : Continuation := .quit 6

private def condHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 101) }
    OrdCdata.empty

private def bodyHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 202) }
    OrdCdata.empty

private def whileTailProgram : Array Instr :=
  #[whileInstr, .pushInt (.num tailMarker)]

private def runWhileDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowWhile whileInstr stack

private def runWhileDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowWhile instr (VM.push (intV dispatchSentinel)) stack

private def runWhileRaw
    (stack : Array Value)
    (cc : Continuation := defaultCc)
    (c0 : Continuation := .quit 0) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { Regs.initial with c0 := c0 } }
  (execInstrFlowWhile whileInstr (pure ())).run st0

private def runLoopExtRaw
    (instr : Instr)
    (stack : Array Value)
    (cc : Continuation := defaultCc)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 : Regs := { Regs.initial with c0 := c0, c1 := c1 }
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := regs0 }
  (execInstrFlowLoopExt instr (pure ())).run st0

private def runWhileCondStep
    (stack : Array Value)
    (cond body after : Continuation)
    (c0 : Continuation := .quit 0) : StepResult :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := .whileCond cond body after }
  VmState.step stubHost st0

private def runWhileBodyStep
    (stack : Array Value)
    (cond body after : Continuation)
    (c0 : Continuation := .quit 0) : StepResult :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := .whileBody cond body after }
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

private def whileSetGasExact : Int :=
  computeExactGasBudget whileInstr

private def whileSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne whileInstr

private def whileBrkSetGasExact : Int :=
  computeExactGasBudget whileBrkInstr

private def whileBrkSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne whileBrkInstr

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, intV (-3)]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell cellA, .slice sliceA, .builder Builder.empty, .tuple #[]]

private def pickNoise (rng0 : StdGen) : Array Value × StdGen :=
  let (choice, rng1) := randNat rng0 0 3
  match choice with
  | 0 => (#[], rng1)
  | 1 => (noiseA, rng1)
  | 2 => (noiseB, rng1)
  | _ => (noiseLong, rng1)

private def pickNonCont (rng0 : StdGen) : Value × StdGen :=
  let (choice, rng1) := randNat rng0 0 5
  match choice with
  | 0 => (intV 7, rng1)
  | 1 => (.null, rng1)
  | 2 => (.cell cellA, rng1)
  | 3 => (.slice sliceA, rng1)
  | 4 => (.builder Builder.empty, rng1)
  | _ => (.tuple #[], rng1)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[whileInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := whileId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genWhileFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  match shape with
  | 0 =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/ok/no-tail" (noise ++ #[q0, q0]), rng2)
  | 1 =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/ok/tail" (noise ++ #[q0, q0]) whileTailProgram, rng2)
  | 2 =>
      (mkCase "fuzz/err/underflow" #[], rng1)
  | 3 =>
      let (bad, rng2) := pickNonCont rng1
      (mkCase "fuzz/err/type/top" #[q0, bad], rng2)
  | 4 =>
      let (bad, rng2) := pickNonCont rng1
      (mkCase "fuzz/err/order/cond" #[bad, q0], rng2)
  | 5 =>
      let (useExact, rng2) := randBool rng1
      let gas := if useExact then whileSetGasExact else whileSetGasExactMinusOne
      let name := if useExact then "fuzz/gas/exact" else "fuzz/gas/minus-one"
      let program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, whileInstr]
      (mkCase name #[q0, q0] program, rng2)
  | 6 =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/brk/basic" (noise ++ #[q0, q0]) #[whileBrkInstr], rng2)
  | 7 =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/whileend/basic" (noise ++ #[q0]) #[whileEndInstr], rng2)
  | 8 =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/whileendbrk/basic" (noise ++ #[q0]) #[whileEndBrkInstr], rng2)
  | _ =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/ok/basic" (noise ++ #[q0, q0]), rng2)

def suite : InstrSuite where
  id := whileId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/matched-while"
          (runWhileDispatchFallback whileInstr #[q0, q0])
          #[]
        expectOkStack "dispatch/fallback-add"
          (runWhileDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel] }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runWhileDirect #[]) .stkUnd
        expectErr "underflow/one-cont" (runWhileDirect #[q0]) .stkUnd
        expectErr "underflow/one-int" (runWhileDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-null" (runWhileDirect #[.null]) .stkUnd
        expectErr "underflow/one-cell" (runWhileDirect #[.cell cellA]) .stkUnd
        expectErr "underflow/one-slice" (runWhileDirect #[.slice sliceA]) .stkUnd
        expectErr "underflow/one-builder" (runWhileDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-tuple-empty" (runWhileDirect #[.tuple #[]]) .stkUnd

        let stTop ← expectRawErr "order/top-first-before-below-cont"
          (runWhileRaw #[q0, intV 9]) .typeChk
        if stTop.stack != #[q0] then
          throw (IO.userError s!"order/top-first-before-below-cont: expected #[q0], got {reprStr stTop.stack}")

        let stSecond ← expectRawErr "order/second-pop-after-body"
          (runWhileRaw #[intV 7, q0]) .typeChk
        if !stSecond.stack.isEmpty then
          throw (IO.userError s!"order/second-pop-after-body: expected empty stack, got {reprStr stSecond.stack}") }
    ,
    { name := "unit/state/extractcc-requires-ordinary-cc-after-pops"
      run := do
        let st ← expectRawErr "state/non-ordinary-cc"
          (runWhileRaw #[intV 41, q0, q0] (.quit 13) (.quit 17))
          .typeChk
        if st.stack != #[intV 41] then
          throw (IO.userError s!"state/non-ordinary-cc: expected stack #[41], got {reprStr st.stack}")
        if st.regs.c0 != .quit 17 then
          throw (IO.userError s!"state/non-ordinary-cc: expected c0 unchanged, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/cond-hasc0-does-not-install-loop-c0"
      run := do
        let st ← expectRawOk "state/cond-hasc0"
          (runWhileRaw #[intV 8, .cont condHasC0, .cont bodyNoC0] defaultCc (.quit 44))
        if st.stack != #[intV 8] then
          throw (IO.userError s!"state/cond-hasc0: stack mismatch {reprStr st.stack}")
        if st.cc != condHasC0 then
          throw (IO.userError s!"state/cond-hasc0: expected cc=condHasC0, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"state/cond-hasc0: expected c0=quit0 after extract_cc(1), got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/cond-no-c0-installs-whilecond"
      run := do
        let oldC0 : Continuation := .quit 55
        let st ← expectRawOk "state/cond-no-c0"
          (runWhileRaw #[intV 9, .cont condNoC0, .cont bodyNoC0] defaultCc oldC0)
        if st.stack != #[intV 9] then
          throw (IO.userError s!"state/cond-no-c0: stack mismatch {reprStr st.stack}")
        if st.cc != condNoC0 then
          throw (IO.userError s!"state/cond-no-c0: expected cc=condNoC0, got {reprStr st.cc}")
        match st.regs.c0 with
        | .whileCond cond body after =>
            if cond != condNoC0 then
              throw (IO.userError s!"state/cond-no-c0: cond mismatch {reprStr cond}")
            if body != bodyNoC0 then
              throw (IO.userError s!"state/cond-no-c0: body mismatch {reprStr body}")
            match after with
            | .ordinary _ saved cregs _ =>
                if saved != .quit 0 then
                  throw (IO.userError s!"state/cond-no-c0: expected after.saved=quit0, got {reprStr saved}")
                if cregs.c0 != some oldC0 then
                  throw (IO.userError
                    s!"state/cond-no-c0: expected after.cregs.c0={reprStr oldC0}, got {reprStr cregs.c0}")
            | other =>
                throw (IO.userError s!"state/cond-no-c0: expected ordinary after, got {reprStr other}")
        | other =>
            throw (IO.userError s!"state/cond-no-c0: expected whileCond in c0, got {reprStr other}") }
    ,
    { name := "unit/loopext/whilebrk-c1-envelope-before-loop"
      run := do
        let st ← expectRawOk "loopext/whilebrk"
          (runLoopExtRaw whileBrkInstr #[q0, q0] defaultCc (.quit 5) (.quit 6))
        if st.cc != .quit 0 then
          throw (IO.userError s!"loopext/whilebrk: expected cc=quit0, got {reprStr st.cc}")
        match st.regs.c0 with
        | .whileCond cond body after =>
            if cond != .quit 0 || body != .quit 0 then
              throw (IO.userError s!"loopext/whilebrk: unexpected cond/body in loop state")
            if st.regs.c1 != after then
              throw (IO.userError "loopext/whilebrk: expected c1 to equal while after-cont")
            match after with
            | .ordinary _ saved cregs cdata =>
                if saved != .quit 0 then
                  throw (IO.userError s!"loopext/whilebrk: expected after.saved=quit0, got {reprStr saved}")
                if cregs.c0 != some (.quit 5) then
                  throw (IO.userError s!"loopext/whilebrk: expected after.cregs.c0=quit5, got {reprStr cregs.c0}")
                if cregs.c1 != some (.quit 6) then
                  throw (IO.userError s!"loopext/whilebrk: expected after.cregs.c1=quit6, got {reprStr cregs.c1}")
                if !cdata.stack.isEmpty || cdata.nargs != -1 then
                  throw (IO.userError s!"loopext/whilebrk: expected empty cdata, got {reprStr cdata}")
            | other =>
                throw (IO.userError s!"loopext/whilebrk: expected ordinary after, got {reprStr other}")
        | other =>
            throw (IO.userError s!"loopext/whilebrk: expected whileCond in c0, got {reprStr other}") }
    ,
    { name := "unit/loopext/whileend-uses-extractcc0-order"
      run := do
        let stErr ← expectRawErr "loopext/whileend/non-ordinary-cc"
          (runLoopExtRaw whileEndInstr #[q0] (.quit 9) (.quit 11))
          .typeChk
        if !stErr.stack.isEmpty then
          throw (IO.userError
            s!"loopext/whileend/non-ordinary-cc: expected consumed cond, got {reprStr stErr.stack}")

        let stOk ← expectRawOk "loopext/whileend/ordinary-cc"
          (runLoopExtRaw whileEndInstr #[q0] defaultCc (.quit 33))
        if stOk.cc != .quit 0 then
          throw (IO.userError s!"loopext/whileend/ordinary-cc: expected cc=quit0, got {reprStr stOk.cc}")
        match stOk.regs.c0 with
        | .whileCond cond body after =>
            if cond != .quit 0 then
              throw (IO.userError s!"loopext/whileend/ordinary-cc: cond mismatch {reprStr cond}")
            match body with
            | .ordinary _ saved _ _ =>
                if saved != .quit 0 then
                  throw (IO.userError
                    s!"loopext/whileend/ordinary-cc: expected extracted body saved=quit0, got {reprStr saved}")
            | other =>
                throw (IO.userError s!"loopext/whileend/ordinary-cc: expected ordinary body, got {reprStr other}")
            if after != .quit 33 then
              throw (IO.userError s!"loopext/whileend/ordinary-cc: expected after=quit33, got {reprStr after}")
        | other =>
            throw (IO.userError s!"loopext/whileend/ordinary-cc: expected whileCond in c0, got {reprStr other}") }
    ,
    { name := "unit/step/whilecond-true-body-no-c0-installs-whilebody"
      run := do
        let marker : Continuation := .quit 61
        let after : Continuation := .quit 17
        let st ← expectContinue "step/whilecond-true/no-c0"
          (runWhileCondStep #[intV 1] condNoC0 bodyNoC0 after marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-true/no-c0: expected empty stack, got {reprStr st.stack}")
        if st.cc != bodyNoC0 then
          throw (IO.userError s!"step/whilecond-true/no-c0: expected cc=bodyNoC0, got {reprStr st.cc}")
        if st.regs.c0 != .whileBody condNoC0 bodyNoC0 after then
          throw (IO.userError
            s!"step/whilecond-true/no-c0: expected c0=whileBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/whilecond-true-body-hasc0-keeps-c0"
      run := do
        let marker : Continuation := .quit 62
        let after : Continuation := .quit 17
        let st ← expectContinue "step/whilecond-true/has-c0"
          (runWhileCondStep #[intV 1] condNoC0 bodyHasC0 after marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-true/has-c0: expected empty stack, got {reprStr st.stack}")
        if st.cc != bodyHasC0 then
          throw (IO.userError s!"step/whilecond-true/has-c0: expected cc=bodyHasC0, got {reprStr st.cc}")
        if st.regs.c0 != marker then
          throw (IO.userError
            s!"step/whilecond-true/has-c0: expected c0 unchanged={reprStr marker}, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/whilecond-false-jumps-after-and-restores-saved-c0"
      run := do
        let after : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 77) OrdCregs.empty OrdCdata.empty
        let st ← expectContinue "step/whilecond-false"
          (runWhileCondStep #[intV 0] condNoC0 bodyNoC0 after (.quit 99))
        let expectedCc : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-false: expected empty stack, got {reprStr st.stack}")
        if st.regs.c0 != .quit 77 then
          throw (IO.userError s!"step/whilecond-false: expected restored c0=quit77, got {reprStr st.regs.c0}")
        if st.cc != expectedCc then
          throw (IO.userError s!"step/whilecond-false: expected cc={reprStr expectedCc}, got {reprStr st.cc}") }
    ,
    { name := "unit/step/whilebody-cond-hasc0-vs-no-c0"
      run := do
        let markerA : Continuation := .quit 63
        let markerB : Continuation := .quit 64
        let after : Continuation := .quit 17

        let stNoC0 ← expectContinue "step/whilebody/no-c0"
          (runWhileBodyStep #[] condNoC0 bodyNoC0 after markerA)
        if stNoC0.cc != condNoC0 then
          throw (IO.userError s!"step/whilebody/no-c0: expected cc=condNoC0, got {reprStr stNoC0.cc}")
        if stNoC0.regs.c0 != .whileCond condNoC0 bodyNoC0 after then
          throw (IO.userError
            s!"step/whilebody/no-c0: expected c0=whileCond, got {reprStr stNoC0.regs.c0}")

        let stHasC0 ← expectContinue "step/whilebody/has-c0"
          (runWhileBodyStep #[] condHasC0 bodyNoC0 after markerB)
        if stHasC0.cc != condHasC0 then
          throw (IO.userError s!"step/whilebody/has-c0: expected cc=condHasC0, got {reprStr stHasC0.cc}")
        if stHasC0.regs.c0 != markerB then
          throw (IO.userError
            s!"step/whilebody/has-c0: expected c0 unchanged={reprStr markerB}, got {reprStr stHasC0.regs.c0}") }
  ]
  oracle := #[
    -- Direct WHILE with oracle-encodable continuations K=quit(0).
    mkCase "ok/direct/no-tail/basic" #[q0, q0],
    mkCase "ok/direct/no-tail/noise-a" (noiseA ++ #[q0, q0]),
    mkCase "ok/direct/no-tail/noise-b" (noiseB ++ #[q0, q0]),
    mkCase "ok/direct/no-tail/null-noise" #[.null, q0, q0],
    mkCase "ok/direct/no-tail/int-noise" #[intV 7, q0, q0],
    mkCase "ok/direct/no-tail/cell-noise" #[.cell cellA, q0, q0],
    mkCase "ok/direct/no-tail/slice-noise" #[.slice sliceA, q0, q0],
    mkCase "ok/direct/no-tail/builder-noise" #[.builder Builder.empty, q0, q0],
    mkCase "ok/direct/no-tail/tuple-noise" #[.tuple #[], q0, q0],
    mkCase "ok/direct/no-tail/max-int257-noise" #[intV maxInt257, q0, q0],
    mkCase "ok/direct/no-tail/min-int257-noise" #[intV minInt257, q0, q0],
    mkCase "ok/direct/no-tail/deep-long" (noiseLong ++ #[q0, q0]),
    mkCase "ok/direct/tail-skipped/basic" #[q0, q0] whileTailProgram,
    mkCase "ok/direct/tail-skipped/noise-a" (noiseA ++ #[q0, q0]) whileTailProgram,
    mkCase "ok/direct/tail-skipped/noise-b" (noiseB ++ #[q0, q0]) whileTailProgram,
    mkCase "ok/direct/tail-skipped/max-int257-noise" #[intV maxInt257, q0, q0] whileTailProgram,
    mkCase "ok/direct/tail-skipped/min-int257-noise" #[intV minInt257, q0, q0] whileTailProgram,
    mkCase "ok/direct/tail-skipped/deep-long" (noiseLong ++ #[q0, q0]) whileTailProgram,

    -- pop_cont underflow/type and ordering.
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/one-cont" #[q0],
    mkCase "err/type/top-int" #[intV 1],
    mkCase "err/type/top-null" #[.null],
    mkCase "err/type/top-cell" #[.cell cellA],
    mkCase "err/type/top-slice" #[.slice sliceA],
    mkCase "err/type/top-builder" #[.builder Builder.empty],
    mkCase "err/type/top-tuple-empty" #[.tuple #[]],
    mkCase "err/order/top-first-before-below-cont-int" #[q0, intV 5],
    mkCase "err/order/top-first-before-below-cont-null" #[q0, .null],
    mkCase "err/order/second-pop-cond-int" #[intV 7, q0],
    mkCase "err/order/second-pop-cond-null" #[.null, q0],
    mkCase "err/order/second-pop-cond-cell" #[.cell cellA, q0],
    mkCase "err/order/second-pop-cond-slice" #[.slice sliceA, q0],

    -- Deterministic gas cliff for WHILE.
    mkCase "gas/exact-succeeds" #[q0, q0]
      #[.pushInt (.num whileSetGasExact), .tonEnvOp .setGasLimit, whileInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[q0, q0]
      #[.pushInt (.num whileSetGasExactMinusOne), .tonEnvOp .setGasLimit, whileInstr],

    -- Related BRK variants (same C++ loop_while core + c1 envelope).
    mkCase "brk/direct/no-tail/basic" #[q0, q0] #[whileBrkInstr],
    mkCase "brk/direct/no-tail/noise-a" (noiseA ++ #[q0, q0]) #[whileBrkInstr],
    mkCase "brk/direct/tail-skipped" #[q0, q0] #[whileBrkInstr, .pushInt (.num tailMarker)],
    mkCase "brk/underflow/empty" #[] #[whileBrkInstr],
    mkCase "brk/underflow/one-cont" #[q0] #[whileBrkInstr],
    mkCase "brk/type/top-null" #[.null] #[whileBrkInstr],
    mkCase "brk/order/second-pop-cond-int" #[intV 9, q0] #[whileBrkInstr],
    mkCase "brk/gas/exact-succeeds" #[q0, q0]
      #[.pushInt (.num whileBrkSetGasExact), .tonEnvOp .setGasLimit, whileBrkInstr],
    mkCase "brk/gas/exact-minus-one-out-of-gas" #[q0, q0]
      #[.pushInt (.num whileBrkSetGasExactMinusOne), .tonEnvOp .setGasLimit, whileBrkInstr],

    -- Related WHILEEND variants (extract_cc(0) body capture path).
    mkCase "whileend/basic" #[q0] #[whileEndInstr],
    mkCase "whileend/noise-int" #[intV 7, q0] #[whileEndInstr],
    mkCase "whileend/tail-skipped" #[q0] #[whileEndInstr, .pushInt (.num tailMarker)],
    mkCase "whileend/underflow-empty" #[] #[whileEndInstr],
    mkCase "whileend/type-top-int" #[intV 1] #[whileEndInstr],
    mkCase "whileend/type-top-null" #[.null] #[whileEndInstr],
    mkCase "whileendbrk/basic" #[q0] #[whileEndBrkInstr],
    mkCase "whileendbrk/type-top-null" #[.null] #[whileEndBrkInstr]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr whileId
      count := 500
      gen := genWhileFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.WHILE
