import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.WHILEBRK

/-!
WHILEBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.contExt (.while true)`)
  - `TvmLean/Semantics/Step/Step.lean` (`.whileCond` / `.whileBody`)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (child VM parity for while continuations)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_while(..., brk=true)`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp`
    (`VmState::loop_while`, `WhileCont::jump[_w]`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp`
    (`extract_cc(1)`, `c1_envelope_if`, `adjust_jump_cont`)

Branch map covered by this suite:
1. Dispatch branch (`.while true` handled vs fallback to `next`).
2. Entry pop branch (`check_underflow(2)` + `pop_cont` ordering: body first, then cond).
3. `extract_cc(1)` ordering branch (must run after both pops; non-ordinary `cc` error occurs after pops).
4. BRK after-cont branch (`c1_envelope_if(true, extract_cc(1))`):
   - ordinary-after remains ordinary with captured `c0/c1`;
   - `c1` becomes the captured after-continuation.
5. Loop install branch (`loop_while`): install `.whileCond` in `c0` only when `cond.hasC0 = false`.
6. Runtime while-cont branches:
   - `.whileCond`: bool true/false, `body.hasC0` split, pop-bool errors, and `after.nargs` underflow;
   - `.whileBody`: `cond.hasC0` split.
-/

private def whileBrkId : InstrId := { name := "WHILEBRK" }

private def whileBrkInstr : Instr := .contExt (.while true)

private def q0 : Value := .cont (.quit 0)

private def dispatchSentinel : Int := 64039

private def tailMarker : Int := 913

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def cellB : Cell := Cell.mkOrdinary (natToBits 0x3c 8) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA

private def sliceB : Slice := Slice.ofCell cellB

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def defaultCc : Continuation := mkOrdCont

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

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

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, intV (-3)]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell cellA, .slice sliceB, .builder Builder.empty, .tuple #[]]

private def whileBrkTailProgram : Array Instr :=
  #[whileBrkInstr, .pushInt (.num tailMarker)]

private def runWhileBrkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt whileBrkInstr stack

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runWhileBrkRaw
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
  (execInstrFlowLoopExt whileBrkInstr (pure ())).run st0

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

private def expectExcContinue (label : String) (res : StepResult) (expected : Excno) : IO Unit := do
  let st ← expectContinue label res
  if st.cc != st.regs.c2 then
    throw (IO.userError s!"{label}: expected cc to jump to c2, got {reprStr st.cc}")
  let expectedStack : Array Value := #[intV 0, intV expected.toInt]
  if st.stack != expectedStack then
    throw (IO.userError
      s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st.stack}")

private def whileBrkGasExact : Int :=
  computeExactGasBudget whileBrkInstr

private def whileBrkGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne whileBrkInstr

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[whileBrkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := whileBrkId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def progCondCtr0BodyCtr0 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushCtr 0, whileBrkInstr] ++ tail

private def progCondCtr1BodyCtr0 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushCtr 0, whileBrkInstr] ++ tail

private def progCondCtr0BodyCtr1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushCtr 1, whileBrkInstr] ++ tail

private def progCondHasC0BodyCtr0 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushCtr 0, .setContCtr 0, .pushCtr 0, whileBrkInstr] ++ tail

private def whileBrkOracleFamilies : Array String :=
  #[
    "ok/direct/no-tail/",
    "ok/direct/tail-skipped/",
    "ok/ctr/",
    "err/underflow/",
    "err/type/",
    "err/order/",
    "gas/"
  ]

private def whileBrkSetGasExact : Int :=
  computeExactGasBudget whileBrkInstr

private def whileBrkSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne whileBrkInstr

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

private def genWhileBrkFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  match shape with
  | 0 =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/ok/no-tail" (noise ++ #[q0, q0]), rng2)
  | 1 =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/ok/tail" (noise ++ #[q0, q0]) whileBrkTailProgram, rng2)
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
      let gas := if useExact then whileBrkSetGasExact else whileBrkSetGasExactMinusOne
      let name := if useExact then "fuzz/gas/exact" else "fuzz/gas/minus-one"
      let program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, whileBrkInstr]
      (mkCase name #[q0, q0] program, rng2)
  | _ =>
      let (noise, rng2) := pickNoise rng1
      (mkCase "fuzz/ok/basic" (noise ++ #[q0, q0]), rng2)

def suite : InstrSuite where
  id := whileBrkId
  unit := #[
    { name := "unit/dispatch/whilebrk-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-whilebrk"
          (runLoopExtFallback whileBrkInstr #[q0, q0])
          #[] }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runWhileBrkDirect #[]) .stkUnd
        expectErr "underflow/one-cont" (runWhileBrkDirect #[q0]) .stkUnd
        expectErr "underflow/one-int" (runWhileBrkDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-null" (runWhileBrkDirect #[.null]) .stkUnd
        expectErr "underflow/one-cell" (runWhileBrkDirect #[.cell cellA]) .stkUnd
        expectErr "underflow/one-slice" (runWhileBrkDirect #[.slice sliceA]) .stkUnd
        expectErr "underflow/one-builder" (runWhileBrkDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-tuple-empty" (runWhileBrkDirect #[.tuple #[]]) .stkUnd

        let stTop ← expectRawErr "order/top-first-before-below-cont"
          (runWhileBrkRaw #[q0, intV 9]) .typeChk
        if stTop.stack != #[q0] then
          throw (IO.userError s!"order/top-first-before-below-cont: expected #[q0], got {reprStr stTop.stack}")

        let stSecond ← expectRawErr "order/second-pop-after-body"
          (runWhileBrkRaw #[intV 7, q0]) .typeChk
        if !stSecond.stack.isEmpty then
          throw (IO.userError s!"order/second-pop-after-body: expected empty stack, got {reprStr stSecond.stack}") }
    ,
    { name := "unit/state/extractcc-order-after-both-pops"
      run := do
        let oldC0 : Continuation := .quit 17
        let oldC1 : Continuation := .quit 19
        let st ← expectRawErr "state/non-ordinary-cc"
          (runWhileBrkRaw #[intV 41, q0, q0] (.quit 13) oldC0 oldC1)
          .typeChk
        if st.stack != #[intV 41] then
          throw (IO.userError s!"state/non-ordinary-cc: expected stack #[41], got {reprStr st.stack}")
        if st.regs.c0 != oldC0 then
          throw (IO.userError s!"state/non-ordinary-cc: expected c0 unchanged, got {reprStr st.regs.c0}")
        if st.regs.c1 != oldC1 then
          throw (IO.userError s!"state/non-ordinary-cc: expected c1 unchanged, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/state/brk-cond-no-c0-installs-whilecond-and-captures-c1"
      run := do
        let oldC0 : Continuation := .quit 5
        let oldC1 : Continuation := .quit 6
        let st ← expectRawOk "state/brk-cond-no-c0"
          (runWhileBrkRaw #[q0, q0] defaultCc oldC0 oldC1)
        if st.cc != .quit 0 then
          throw (IO.userError s!"state/brk-cond-no-c0: expected cc=quit0, got {reprStr st.cc}")
        match st.regs.c0 with
        | .whileCond cond body after =>
            if cond != .quit 0 || body != .quit 0 then
              throw (IO.userError s!"state/brk-cond-no-c0: unexpected cond/body in loop state")
            if st.regs.c1 != after then
              throw (IO.userError "state/brk-cond-no-c0: expected c1 to equal after continuation")
            match after with
            | .ordinary _ saved cregs cdata =>
                if saved != .quit 0 then
                  throw (IO.userError s!"state/brk-cond-no-c0: expected after.saved=quit0, got {reprStr saved}")
                if cregs.c0 != some oldC0 then
                  throw (IO.userError s!"state/brk-cond-no-c0: expected captured c0=quit5, got {reprStr cregs.c0}")
                if cregs.c1 != some oldC1 then
                  throw (IO.userError s!"state/brk-cond-no-c0: expected captured c1=quit6, got {reprStr cregs.c1}")
                if !(cdataEmpty cdata) then
                  throw (IO.userError s!"state/brk-cond-no-c0: expected empty cdata, got {reprStr cdata}")
            | other =>
                throw (IO.userError s!"state/brk-cond-no-c0: expected ordinary after, got {reprStr other}")
        | other =>
            throw (IO.userError s!"state/brk-cond-no-c0: expected c0=whileCond, got {reprStr other}") }
    ,
    { name := "unit/state/brk-cond-has-c0-keeps-c0-and-captures-c1"
      run := do
        let oldC0 : Continuation := .quit 50
        let oldC1 : Continuation := .quit 60
        let st ← expectRawOk "state/brk-cond-has-c0"
          (runWhileBrkRaw #[.cont condHasC0, q0] defaultCc oldC0 oldC1)
        if st.cc != condHasC0 then
          throw (IO.userError s!"state/brk-cond-has-c0: expected cc=condHasC0, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"state/brk-cond-has-c0: expected c0=quit0 after extract_cc(1), got {reprStr st.regs.c0}")
        match st.regs.c1 with
        | .ordinary _ saved cregs cdata =>
            if saved != .quit 0 then
              throw (IO.userError s!"state/brk-cond-has-c0: expected after.saved=quit0, got {reprStr saved}")
            if cregs.c0 != some oldC0 then
              throw (IO.userError s!"state/brk-cond-has-c0: expected captured c0 marker, got {reprStr cregs.c0}")
            if cregs.c1 != some oldC1 then
              throw (IO.userError s!"state/brk-cond-has-c0: expected captured c1 marker, got {reprStr cregs.c1}")
            if !(cdataEmpty cdata) then
              throw (IO.userError s!"state/brk-cond-has-c0: expected empty cdata, got {reprStr cdata}")
        | other =>
            throw (IO.userError s!"state/brk-cond-has-c0: expected ordinary c1 envelope, got {reprStr other}") }
    ,
    { name := "unit/regression/c1-envelope-on-ordinary-remains-ordinary"
      run := do
        let st ← expectRawOk "regression/ordinary-after-shape"
          (runWhileBrkRaw #[q0, q0] defaultCc (.quit 7) (.quit 8))
        match st.regs.c1 with
        | .ordinary _ _ _ _ => pure ()
        | other =>
            throw (IO.userError s!"regression/ordinary-after-shape: expected ordinary, got {reprStr other}") }
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
          throw (IO.userError s!"step/whilecond-true/no-c0: expected c0=whileBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/whilecond-true-body-has-c0-keeps-c0"
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
          (runWhileCondStep #[intV 0] condNoC0 bodyNoC0 after (.quit 88))
        let expectedCc : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-false: expected empty stack, got {reprStr st.stack}")
        if st.regs.c0 != .quit 77 then
          throw (IO.userError s!"step/whilecond-false: expected restored c0=quit77, got {reprStr st.regs.c0}")
        if st.cc != expectedCc then
          throw (IO.userError s!"step/whilecond-false: expected cc={reprStr expectedCc}, got {reprStr st.cc}") }
    ,
    { name := "unit/step/whilecond-false-nonordinary-after-keeps-c0"
      run := do
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 88
        let st ← expectContinue "step/whilecond-false/nonordinary-after"
          (runWhileCondStep #[intV 0] condNoC0 bodyNoC0 after marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-false/nonordinary-after: expected empty stack, got {reprStr st.stack}")
        if st.cc != after then
          throw (IO.userError s!"step/whilecond-false/nonordinary-after: expected cc=after, got {reprStr st.cc}")
        if st.regs.c0 != marker then
          throw (IO.userError s!"step/whilecond-false/nonordinary-after: expected c0 unchanged, got {reprStr st.regs.c0}") }
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
          throw (IO.userError s!"step/whilebody/no-c0: expected c0=whileCond, got {reprStr stNoC0.regs.c0}")

        let stHasC0 ← expectContinue "step/whilebody/has-c0"
          (runWhileBodyStep #[] condHasC0 bodyNoC0 after markerB)
        if stHasC0.cc != condHasC0 then
          throw (IO.userError s!"step/whilebody/has-c0: expected cc=condHasC0, got {reprStr stHasC0.cc}")
        if stHasC0.regs.c0 != markerB then
          throw (IO.userError
            s!"step/whilebody/has-c0: expected c0 unchanged={reprStr markerB}, got {reprStr stHasC0.regs.c0}") }
    ,
    { name := "unit/step/pop-bool-errors-and-after-nargs-underflow"
      run := do
        expectExcContinue "step/pop-bool/underflow"
          (runWhileCondStep #[] condNoC0 bodyNoC0 (.quit 17))
          .stkUnd
        expectExcContinue "step/pop-bool/type"
          (runWhileCondStep #[.null] condNoC0 bodyNoC0 (.quit 17))
          .typeChk
        expectExcContinue "step/pop-bool/intov"
          (runWhileCondStep #[.int .nan] condNoC0 bodyNoC0 (.quit 17))
          .intOv

        let afterNeedArgOrd : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := #[], nargs := 1 }
        expectExcContinue "step/after-nargs/ordinary-underflow"
          (runWhileCondStep #[intV 0] condNoC0 bodyNoC0 afterNeedArgOrd)
          .stkUnd

        let afterNeedArgEnv : Continuation :=
          .envelope (.quit 9) OrdCregs.empty { stack := #[], nargs := 2 }
        expectExcContinue "step/after-nargs/envelope-underflow"
          (runWhileCondStep #[intV 44, intV 0] condNoC0 bodyNoC0 afterNeedArgEnv)
          .stkUnd

        let stOk ← expectContinue "step/after-nargs/ordinary-satisfied"
          (runWhileCondStep #[intV 55, intV 0] condNoC0 bodyNoC0 afterNeedArgOrd)
        if stOk.cc == stOk.regs.c2 then
          throw (IO.userError "step/after-nargs/ordinary-satisfied: unexpected exception jump") }
  ]
  oracle := #[
    -- Base WHILEBRK success with oracle-encodable continuations.
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

    -- Tail should be skipped because control transfers to `cond`.
    mkCase "ok/direct/tail-skipped/basic" #[q0, q0] whileBrkTailProgram,
    mkCase "ok/direct/tail-skipped/noise-a" (noiseA ++ #[q0, q0]) whileBrkTailProgram,
    mkCase "ok/direct/tail-skipped/noise-b" (noiseB ++ #[q0, q0]) whileBrkTailProgram,
    mkCase "ok/direct/tail-skipped/max-int257" #[intV maxInt257, q0, q0] whileBrkTailProgram,
    mkCase "ok/direct/tail-skipped/min-int257" #[intV minInt257, q0, q0] whileBrkTailProgram,
    mkCase "ok/direct/tail-skipped/deep-long" (noiseLong ++ #[q0, q0]) whileBrkTailProgram,

    -- Construct cond/body from control registers.
    mkCase "ok/ctr/cond0-body0" #[] (progCondCtr0BodyCtr0),
    mkCase "ok/ctr/cond0-body0/tail-skipped" #[] (progCondCtr0BodyCtr0 #[.pushInt (.num 5)]),
    mkCase "ok/ctr/cond1-body0" #[] (progCondCtr1BodyCtr0),
    mkCase "ok/ctr/cond0-body1" #[] (progCondCtr0BodyCtr1),
    mkCase "ok/ctr/cond-hasc0-body0" #[] (progCondHasC0BodyCtr0),
    mkCase "ok/ctr/cond-hasc0-body0/tail-skipped" #[] (progCondHasC0BodyCtr0 #[.pushInt (.num 6)]),
    mkCase "ok/ctr/cond-hasc0-body0/noise-prefix-a" (noiseA ++ #[intV 9]) (progCondHasC0BodyCtr0),
    mkCase "ok/ctr/cond-hasc0-body0/noise-prefix-b" #[.null, intV (-5)] (progCondHasC0BodyCtr0),

    -- Underflow/type/order matrix for entry pops.
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

    -- Deterministic gas boundaries.
    mkCase "gas/exact-succeeds" #[q0, q0]
      #[.pushInt (.num whileBrkGasExact), .tonEnvOp .setGasLimit, whileBrkInstr]
      (oracleGasLimitsExact whileBrkGasExact),
    mkCase "gas/exact-minus-one-out-of-gas" #[q0, q0]
      #[.pushInt (.num whileBrkGasExactMinusOne), .tonEnvOp .setGasLimit, whileBrkInstr]
      (oracleGasLimitsExact whileBrkGasExactMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr whileBrkId
      count := 500
      gen := genWhileBrkFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.WHILEBRK
