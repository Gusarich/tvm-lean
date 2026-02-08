import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADD

/-
QADD branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Qadd.lean` (`execInstrArithQadd`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_add`, opcode wiring in `register_add_mul_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 7 branch points / 9 terminal outcomes
  (opcode dispatch; explicit underflow guard; two `popInt` type checks;
   `IntVal.add` finite-vs-NaN; quiet `pushIntQuiet` NaN-vs-num and signed-257 fit).
- C++: 6 branch points / 9 aligned terminal outcomes
  (`QADD` opcode binds `exec_add(..., quiet=true)`; `check_underflow(2)`;
   two `pop_int` type checks; `push_int_quiet` valid-vs-overflow-vs-NaN handling).

Key risk areas covered:
- quiet overflow must push NaN (not throw `intOv`);
- quiet NaN operand propagation must keep execution successful;
- stack error ordering: underflow must win over type-check for arity<2;
- operand pop order (`y` then `x`) determines first type-check site;
- signed-257 near-boundary behavior around `[-2^256, 2^256-1]`;
- gas threshold determinism for `PUSHINT n; SETGASLIMIT; QADD`.
-/

private def qaddId : InstrId := { name := "QADD" }

private def qaddInstr : Instr := .qadd

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qaddInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qaddId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qaddInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQaddDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQadd qaddInstr stack

private def runQaddDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQadd .add (VM.push (intV 904)) stack

private def qaddSetGasExact : Int :=
  computeExactGasBudget qaddInstr

private def qaddSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qaddInstr

private def genQaddFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-boundary" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-right-zero" #[intV x, intV 0], r2)
    else if shape = 5 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-left-zero" #[intV 0, intV y], r2)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow-max-plus-one"
        #[intV maxInt257, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow-min-minus-one"
        #[intV minInt257, intV (-1)], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow-one-non-int" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-first" #[intV x, .null], r2)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-second" #[.null, intV y], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-right-via-program"
        #[IntVal.num x, IntVal.nan], r2)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-left-via-program"
        #[IntVal.nan, IntVal.num y], r2)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow-empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qaddId
  unit := #[
    { name := "unit/direct/finite-sign-zero-and-near-boundary"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, -3, 4),
            (-7, 3, -4),
            (-9, -11, -20),
            (0, 123, 123),
            (123, 0, 123),
            (maxInt257, minInt257, -1),
            (maxInt257 - 1, 1, maxInt257),
            (minInt257 + 1, -1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}+{y}" (runQaddDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-overflow-pushes-nan"
      run := do
        expectOkStack "max+1->nan" (runQaddDirect #[intV maxInt257, intV 1]) #[.int .nan]
        expectOkStack "min-1->nan" (runQaddDirect #[intV minInt257, intV (-1)]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQaddDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQaddDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQaddDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQaddDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQaddDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-qadd-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQaddDispatchFallback #[]) #[intV 904] }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "ok/pos-pos" #[intV 17, intV 25],
    mkCase "ok/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/neg-neg" #[intV (-17), intV (-5)],
    mkCase "ok/zero-right" #[intV 222, intV 0],
    mkCase "ok/zero-left" #[intV 0, intV 222],
    mkCase "ok/max-plus-zero" #[intV maxInt257, intV 0],
    mkCase "ok/min-plus-zero" #[intV minInt257, intV 0],
    mkCase "ok/max-plus-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/min-plus-one" #[intV minInt257, intV 1],
    mkCase "ok/max-minus-one-plus-one" #[intV (maxInt257 - 1), intV 1],
    mkCase "ok/min-plus-one-plus-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/max-plus-min" #[intV maxInt257, intV minInt257],
    mkCase "quiet-overflow/max-plus-one-pushes-nan" #[intV maxInt257, intV 1],
    mkCase "quiet-overflow/min-minus-one-pushes-nan" #[intV minInt257, intV (-1)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "type/error-order-both-non-int" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "nan/right-operand-via-program" #[IntVal.num 42, IntVal.nan],
    mkCaseFromIntVals "nan/left-operand-via-program" #[IntVal.nan, IntVal.num 42],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qaddSetGasExact), .tonEnvOp .setGasLimit, qaddInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qaddSetGasExactMinusOne), .tonEnvOp .setGasLimit, qaddInstr]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 600
      gen := genQaddFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADD
