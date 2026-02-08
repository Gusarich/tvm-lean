import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMIN

/-!
QMIN branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qmin`)
  - `TvmLean/Model/Value/IntVal.lean` (`IntVal.min`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_minmax`, opcode wiring in `register_other_arith_ops` for `QMIN` mode=3)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 9 branch points / 8 terminal outcomes
  (outer dispatch, `.contExt` sub-dispatch, explicit `checkUnderflow 2`,
   two `popInt` type checks, `IntVal.min` finite-vs-NaN plus compare split,
   quiet `pushIntQuiet` finite-vs-NaN/out-of-range split).
- C++: 7 branch points / 8 aligned terminal outcomes
  (`QMIN` registration to `exec_minmax(mode=3)`, underflow guard,
   two `pop_int` checks, validity fold + compare/swap, quiet push behavior).

Key risk areas covered:
- singleton-stack error ordering must be `stkUnd` before any type check;
- top-pop order (first pop is stack top) controls which type path is hit first;
- quiet NaN propagation from either operand must succeed with NaN result;
- quiet range overflow must only affect selected minimum (unselected out-of-range is ignored);
- gas cliff determinism for `PUSHINT n; SETGASLIMIT; QMIN` exact vs exact-minus-one;
- serialization edge ordering where out-of-range `PUSHINT` can fail before `QMIN`.
-/

private def qminId : InstrId := { name := "QMIN" }

private def qminInstr : Instr := .contExt .qmin

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qminInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qminId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qminInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQminDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qminInstr stack

private def runQminDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 1337)) stack

private def qminSetGasExact : Int :=
  computeExactGasBudget qminInstr

private def qminSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qminInstr

private def genQminFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/random-random" #[.num x, .num y], r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/boundary-random" #[.num x, .num y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/random-boundary" #[.num x, .num y], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/boundary-boundary" #[.num x, .num y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/equal" #[.num x, .num x], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/right-zero" #[.num x, .num 0], r2)
    else if shape = 6 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/left-zero" #[.num 0, .num y], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/descending-order" #[.num x, .num (x - Int.natAbs y - 1)], r3)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/one-non-int" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-top-first" #[intV x, .null], r2)
    else if shape = 12 then
      let (y, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-second" #[.null, intV y], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/right-via-program" #[.num x, .nan], r2)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/left-via-program" #[.nan, .num y], r2)
    else if shape = 15 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/both-via-program" #[.nan, .nan], rng1)
    else if shape = 16 then
      let (hi, r2) := randBool rng1
      if hi then
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/high-pushint-overflow-before-qmin"
          #[.num (maxInt257 + 1), .num 0], r2)
      else
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/low-pushint-overflow-before-qmin"
          #[.num (minInt257 - 1), .num 0], r2)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qminId
  unit := #[
    { name := "unit/direct/finite-order-sign-and-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 3),
            (7, -3, -3),
            (-7, 3, -7),
            (-7, -3, -7),
            (123, 0, 0),
            (0, 123, 0),
            (maxInt257, minInt257, minInt257),
            (maxInt257 - 1, maxInt257, maxInt257 - 1),
            (minInt257 + 1, minInt257, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"qmin({x},{y})" (runQminDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-and-selected-range-overflow-yield-nan"
      run := do
        expectOkStack "nan/left" (runQminDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/right" (runQminDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "range/selected-low-out-of-range"
          (runQminDirect #[intV (minInt257 - 1), intV 0]) #[.int .nan]
        expectOkStack "range/both-high-out-of-range"
          (runQminDirect #[intV (maxInt257 + 2), intV (maxInt257 + 1)]) #[.int .nan]
        expectOkStack "range/unselected-high-out-of-range-keeps-finite"
          (runQminDirect #[intV (maxInt257 + 1), intV (-5)]) #[intV (-5)] }
    ,
    { name := "unit/error-order/underflow-before-type-and-top-pop-order"
      run := do
        expectErr "underflow/empty" (runQminDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQminDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQminDirect #[.null]) .stkUnd
        expectErr "type/pop-top-first" (runQminDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-second" (runQminDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-top-first" (runQminDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qmin-falls-through"
      run := do
        expectOkStack "fallback/non-contExt"
          (runQminDispatchFallback .add #[]) #[intV 1337]
        expectOkStack "fallback/other-contExt"
          (runQminDispatchFallback (.contExt .condSel) #[]) #[intV 1337] }
  ]
  oracle := #[
    mkCase "ok/zero/zero-zero" #[intV 0, intV 0],
    mkCase "ok/sign/pos-pos" #[intV 17, intV 5],
    mkCase "ok/sign/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/sign/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/sign/neg-neg" #[intV (-17), intV (-5)],
    mkCase "ok/equal/positive" #[intV 42, intV 42],
    mkCase "ok/equal/negative" #[intV (-42), intV (-42)],
    mkCase "ok/zero/right-zero" #[intV 222, intV 0],
    mkCase "ok/zero/left-zero" #[intV 0, intV 222],
    mkCase "boundary/in-range/max-min" #[intV maxInt257, intV minInt257],
    mkCase "boundary/in-range/min-max" #[intV minInt257, intV maxInt257],
    mkCase "boundary/in-range/max-near-max" #[intV maxInt257, intV (maxInt257 - 1)],
    mkCase "boundary/in-range/min-near-min" #[intV minInt257, intV (minInt257 + 1)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-top-null" #[intV 1, .null],
    mkCase "type/pop-second-null" #[.null, intV 1],
    mkCase "type/pop-top-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-top-first" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "nan/right-via-program" #[.num 42, .nan],
    mkCaseFromIntVals "nan/left-via-program" #[.nan, .num 42],
    mkCaseFromIntVals "nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-overflow-high-before-qmin" #[.num (maxInt257 + 1), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-low-before-qmin" #[.num (minInt257 - 1), .num 5],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qminSetGasExact), .tonEnvOp .setGasLimit, qminInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qminSetGasExactMinusOne), .tonEnvOp .setGasLimit, qminInstr]
  ]
  fuzz := #[
    { seed := 2026020818
      count := 600
      gen := genQminFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMIN
