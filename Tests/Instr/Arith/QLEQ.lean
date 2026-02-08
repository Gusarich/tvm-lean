import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLEQ

/-
QLEQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qleq` arm in `execInstrArithContExt`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7bb -> .contExt .qleq`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp(..., mode=0x877, quiet=true)`, opcode wiring for `QLEQ`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Lean-vs-C++ terminal mapping used for this suite:
- fallback path for non-`contExt` and non-`.qleq` variants;
- explicit underflow guard (`check_underflow(2)`) before any pop/type checks;
- pop order (`y` first, then `x`) for type-check ordering;
- quiet-NaN path (`x` or `y` invalid) returns NaN without throwing;
- finite comparison path maps `x ≤ y` to `-1`, `x > y` to `0`.

Key risk areas covered:
- regression fixed here: singleton stack (`#[.null]`) must be `stkUnd`, not `typeChk`;
- pop-order-sensitive type errors (`y` pop site first);
- comparator truth table (`<` and `=` both map to `-1`);
- gas cliff for `PUSHINT n; SETGASLIMIT; QLEQ` (exact vs exact-minus-one);
- oracle serialization hygiene: NaN/out-of-range inputs are program-injected, never in `initStack`.
-/

private def qleqId : InstrId := { name := "QLEQ" }

private def qleqInstr : Instr := .contExt .qleq

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qleqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qleqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qleqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programSuffix) gasLimits fuel

private def runQleqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qleqInstr stack

private def runQleqDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 31415)) stack

private def runQleqRaw
    (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithContExt qleqInstr (pure ())).run st0
  (res, st1.stack)

private def qleqSetGasExact : Int :=
  computeExactGasBudget qleqInstr

private def qleqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qleqInstr

private def qleqOutOfRangeHighPool : Array Int :=
  #[maxInt257 + 1, maxInt257 + 2, pow2 257]

private def qleqOutOfRangeLowPool : Array Int :=
  #[minInt257 - 1, minInt257 - 2, -(pow2 257)]

private def pickQleqOutOfRangeHigh (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qleqOutOfRangeHighPool.size - 1)
  (qleqOutOfRangeHighPool[idx]!, rng')

private def pickQleqOutOfRangeLow (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qleqOutOfRangeLowPool.size - 1)
  (qleqOutOfRangeLowPool[idx]!, rng')

private def pickQleqNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQleqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-boundary" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-random" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-boundary" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/equal-values" #[intV x, intV x], r2)
    else if shape = 5 then
      let (base, r2) := pickInt257Boundary rng1
      let (dir, r3) := randNat r2 0 1
      let y :=
        if base = minInt257 then minInt257 + 1
        else if base = maxInt257 then maxInt257 - 1
        else if dir = 0 then base - 1 else base + 1
      (mkCase s!"fuzz/shape-{shape}/ok/adjacent-neighbor" #[intV base, intV y], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/right-zero" #[intV x, intV 0], r2)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/left-zero" #[intV 0, intV y], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-first" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickQleqNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, nonInt], r3)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickQleqNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[nonInt, intV y], r3)
    else if shape = 13 then
      let (xLike, r2) := pickQleqNonInt rng1
      let (yLike, r3) := pickQleqNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[xLike, yLike], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/right-via-program" #[.num x, .nan], r2)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/left-via-program" #[.nan, .num y], r2)
    else if shape = 16 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/both-via-program" #[.nan, .nan], rng1)
    else if shape = 17 then
      let (x, r2) := pickQleqOutOfRangeHigh rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-high-before-qleq" #[.num x, .num 7], r2)
    else
      let (x, r2) := pickQleqOutOfRangeLow rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-low-before-qleq" #[.num x, .num 7], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qleqId
  unit := #[
    { name := "unit/direct/finite-ordering-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, -1),
            (1, 2, -1),
            (2, 1, 0),
            (-7, -7, -1),
            (-8, -7, -1),
            (-7, -8, 0),
            (-1, 1, -1),
            (1, -1, 0),
            (minInt257, minInt257, -1),
            (maxInt257, maxInt257, -1),
            (minInt257, maxInt257, -1),
            (maxInt257, minInt257, 0),
            (maxInt257 - 1, maxInt257, -1),
            (minInt257 + 1, minInt257, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}<={y}" (runQleqDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-propagates"
      run := do
        expectOkStack "nan/x" (runQleqDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y" (runQleqDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "nan/both" (runQleqDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQleqDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQleqDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQleqDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQleqDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQleqDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQleqDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQleqDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQleqDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/regression/underflow-singleton-does-not-pop"
      run := do
        let (r1, s1) := runQleqRaw #[intV 9]
        match r1 with
        | .error .stkUnd =>
            if s1 == #[intV 9] then
              pure ()
            else
              throw (IO.userError s!"singleton-int stack mutated on underflow: got {reprStr s1}")
        | .error e =>
            throw (IO.userError s!"singleton-int expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "singleton-int expected stkUnd, got success")
        let (r2, s2) := runQleqRaw #[.null]
        match r2 with
        | .error .stkUnd =>
            if s2 == #[.null] then
              pure ()
            else
              throw (IO.userError s!"singleton-non-int stack mutated on underflow: got {reprStr s2}")
        | .error e =>
            throw (IO.userError s!"singleton-non-int expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "singleton-non-int expected stkUnd, got success") }
    ,
    { name := "unit/direct/below-stack-preserved"
      run := do
        expectOkStack "tail/true" (runQleqDirect #[.null, intV 2, intV 2]) #[.null, intV (-1)]
        expectOkStack "tail/false" (runQleqDirect #[.cell Cell.empty, intV 3, intV 2]) #[.cell Cell.empty, intV 0] }
    ,
    { name := "unit/dispatch/non-qleq-falls-through"
      run := do
        expectOkStack "dispatch/non-contExt" (runQleqDispatchFallback .add #[]) #[intV 31415]
        expectOkStack "dispatch/other-contExt" (runQleqDispatchFallback (.contExt .condSel) #[]) #[intV 31415] }
  ]
  oracle := #[
    mkCase "ok/order/zero-eq-zero" #[intV 0, intV 0],
    mkCase "ok/order/pos-lt-pos" #[intV 1, intV 2],
    mkCase "ok/order/pos-gt-pos" #[intV 2, intV 1],
    mkCase "ok/order/neg-eq-neg" #[intV (-7), intV (-7)],
    mkCase "ok/order/neg-lt-neg" #[intV (-8), intV (-7)],
    mkCase "ok/order/neg-gt-neg" #[intV (-7), intV (-8)],
    mkCase "ok/order/neg-lt-pos" #[intV (-1), intV 1],
    mkCase "ok/order/pos-gt-neg" #[intV 1, intV (-1)],
    mkCase "ok/edge/min-eq-min" #[intV minInt257, intV minInt257],
    mkCase "ok/edge/max-eq-max" #[intV maxInt257, intV maxInt257],
    mkCase "ok/edge/min-lt-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/edge/max-gt-min" #[intV maxInt257, intV minInt257],
    mkCase "ok/edge/max-minus-one-lt-max" #[intV (maxInt257 - 1), intV maxInt257],
    mkCase "ok/edge/min-plus-one-gt-min" #[intV (minInt257 + 1), intV minInt257],
    mkCase "ok/order/below-preserved-true" #[.null, intV 5, intV 5],
    mkCase "ok/order/below-preserved-false" #[.cell Cell.empty, intV 6, intV 5],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "quiet-nan/right-via-program" #[.num 42, .nan],
    mkCaseFromIntVals "quiet-nan/left-via-program" #[.nan, .num 42],
    mkCaseFromIntVals "quiet-nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-range-high-before-qleq" #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-low-before-qleq" #[.num (minInt257 - 1), .num 7],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qleqSetGasExact), .tonEnvOp .setGasLimit, qleqInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qleqSetGasExactMinusOne), .tonEnvOp .setGasLimit, qleqInstr]
  ]
  fuzz := #[
    { seed := 2026020823
      count := 700
      gen := genQleqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLEQ
