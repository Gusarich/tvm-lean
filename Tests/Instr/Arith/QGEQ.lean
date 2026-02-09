import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QGEQ

/-
QGEQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qgeq` arm)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp`, opcode registration in `register_int_cmp_ops` with mode `0x778`, quiet=true)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch map used for this suite:
- Lean: 6 branch points / 9 terminal outcomes
  (opcode dispatch; explicit two-arg underflow guard; two `popInt` failure points;
   `x/y` NaN-vs-finite split; finite compare split (`a ≥ b` true/false)).
- C++: 6 branch points / 9 aligned terminal outcomes
  (`QGEQ` registration to `exec_cmp(..., mode=0x778, quiet=true)`;
   `check_underflow(2)`; two `pop_int` type checks; invalid-int (NaN) path;
   compare result class `{<,=,>}` mapped by mode to `{0,-1,-1}`).

Terminal categories covered in oracle:
- finite success (`-1` for `x ≥ y`, `0` for `x < y`);
- quiet NaN propagation (result NaN, not `intOv`);
- `stkUnd` (empty/one-arg);
- `typeChk` at first (`y`) and second (`x`) pop;
- out-of-gas at exact-minus-one budget.

Key risk areas:
- comparator truth-table mapping (`=` and `>` both return `-1`);
- operand pop order (`y` then `x`) and corresponding error ordering;
- underflow-vs-type ordering for one-item stacks;
- quiet NaN handling must push NaN (not throw);
- deterministic gas threshold for `PUSHINT n; SETGASLIMIT; QGEQ`.
-/

private def qgeqId : InstrId := { name := "QGEQ" }

private def qgeqInstr : Instr := .contExt .qgeq

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qgeqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qgeqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qgeqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQgeqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qgeqInstr stack

private def runQgeqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt .add (VM.push (intV 778)) stack

private def qgeqSetGasExact : Int :=
  computeExactGasBudget qgeqInstr

private def qgeqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qgeqInstr

private def genQgeqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-boundary" #[intV x, intV y], r3)
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
      (mkCase s!"fuzz/shape-{shape}/ok/adjacent-boundary" #[intV base, intV y], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/one-non-int" #[.null], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, .null], r2)
    else if shape = 10 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[.null, intV y], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/right-via-program"
        #[IntVal.num x, IntVal.nan], r2)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/left-via-program"
        #[IntVal.nan, IntVal.num y], r2)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qgeqId
  unit := #[
    { name := "unit/direct/finite-ordering-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, -1),
            (2, 1, -1),
            (1, 2, 0),
            (-7, -7, -1),
            (-7, -8, -1),
            (-8, -7, 0),
            (1, -1, -1),
            (-1, 1, 0),
            (minInt257, minInt257, -1),
            (maxInt257, maxInt257, -1),
            (minInt257, maxInt257, 0),
            (maxInt257, minInt257, -1),
            (maxInt257 - 1, maxInt257, 0),
            (minInt257 + 1, minInt257, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"qgeq/{x}/{y}" (runQgeqDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-propagation-pushes-nan"
      run := do
        expectOkStack "nan/x" (runQgeqDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y" (runQgeqDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "nan/both" (runQgeqDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQgeqDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQgeqDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQgeqDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQgeqDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQgeqDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-pop-y-first" (runQgeqDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qgeq-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQgeqDispatchFallback #[]) #[intV 778] }
  ]
  oracle := #[
    mkCase "ok/order/zero-eq-zero" #[intV 0, intV 0],
    mkCase "ok/order/pos-gt-pos" #[intV 2, intV 1],
    mkCase "ok/order/pos-lt-pos" #[intV 1, intV 2],
    mkCase "ok/order/neg-eq-neg" #[intV (-7), intV (-7)],
    mkCase "ok/order/neg-gt-neg" #[intV (-7), intV (-8)],
    mkCase "ok/order/neg-lt-neg" #[intV (-8), intV (-7)],
    mkCase "ok/order/pos-gt-neg" #[intV 1, intV (-1)],
    mkCase "ok/order/neg-lt-pos" #[intV (-1), intV 1],
    mkCase "ok/edge/min-eq-min" #[intV minInt257, intV minInt257],
    mkCase "ok/edge/max-eq-max" #[intV maxInt257, intV maxInt257],
    mkCase "ok/edge/min-lt-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/edge/max-gt-min" #[intV maxInt257, intV minInt257],
    mkCase "ok/edge/max-minus-one-lt-max" #[intV (maxInt257 - 1), intV maxInt257],
    mkCase "ok/edge/min-plus-one-gt-min" #[intV (minInt257 + 1), intV minInt257],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "nan/right-via-program" #[IntVal.num 42, IntVal.nan],
    mkCaseFromIntVals "nan/left-via-program" #[IntVal.nan, IntVal.num 42],
    mkCaseFromIntVals "nan/both-via-program" #[IntVal.nan, IntVal.nan],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qgeqSetGasExact), .tonEnvOp .setGasLimit, qgeqInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qgeqSetGasExactMinusOne), .tonEnvOp .setGasLimit, qgeqInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 600
      gen := genQgeqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QGEQ
