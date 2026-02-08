import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.GREATER

/-
GREATER branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Greater.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_cmp`, opcode registration in `register_int_cmp_ops` with mode `0x788`).

Branch map used for this suite:
- Lean: 6 branch points / 9 terminal outcomes
  (opcode dispatch; explicit two-arg underflow guard; two `popInt` failure points;
   `x/y` NaN-vs-finite split; finite compare split (`a > b` true/false);
   non-quiet NaN push path).
- C++: 6 branch points / 9 aligned terminal outcomes
  (`GREATER` registration to `exec_cmp(..., mode=0x788, quiet=false)`;
   explicit `check_underflow(2)`; two `pop_int` type checks; invalid-int (NaN) path;
   compare result class `{<,=,>}` mapped by mode to `{0,0,-1}`).

Terminal categories covered in oracle:
- finite success (`-1` for `x > y`, `0` for `x ≤ y`);
- `stkUnd` (empty/one-arg);
- `typeChk` at first (`y`) and second (`x`) pop;
- `intOv` from NaN propagation in non-quiet GREATER;
- out-of-gas at exact-minus-one budget.

Key risk areas:
- comparator truth-table mapping (`>` returns `-1`; `<` and `=` return `0`);
- operand pop order (`y` then `x`) and corresponding error ordering;
- underflow-vs-type ordering for one-item stacks;
- NaN handling must throw `intOv` in non-quiet GREATER;
- deterministic gas threshold for `PUSHINT n; SETGASLIMIT; GREATER`.
-/

private def greaterId : InstrId := { name := "GREATER" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.greater])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := greaterId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runGreaterDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithGreater .greater stack

private def runGreaterDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithGreater .add (VM.push (intV 777)) stack

private def greaterSetGasExact : Int :=
  computeExactGasBudget .greater

private def greaterSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .greater

private def genGreaterFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  let ((x, y), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, x0), r2)
    else if shape = 5 then
      let (base, r2) := pickInt257Boundary rng1
      let (dir, r3) := randNat r2 0 1
      let y0 :=
        if base = minInt257 then minInt257 + 1
        else if base = maxInt257 then maxInt257 - 1
        else if dir = 0 then base - 1 else base + 1
      ((base, y0), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := greaterId
  unit := #[
    { name := "unit/finite-ordering-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (2, 1, -1),
            (1, 2, 0),
            (-7, -7, 0),
            (-7, -8, -1),
            (-8, -7, 0),
            (1, -1, -1),
            (-1, 1, 0),
            (minInt257, minInt257, 0),
            (maxInt257, maxInt257, 0),
            (minInt257, maxInt257, 0),
            (maxInt257, minInt257, -1),
            (maxInt257 - 1, maxInt257, 0),
            (minInt257 + 1, minInt257, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>{y}" (runGreaterDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/nan-propagation-throws-intov"
      run := do
        expectErr "x-nan" (runGreaterDirect #[.int .nan, intV 1]) .intOv
        expectErr "y-nan" (runGreaterDirect #[intV 1, .int .nan]) .intOv
        expectErr "both-nan" (runGreaterDirect #[.int .nan, .int .nan]) .intOv }
    ,
    { name := "unit/type-errors-follow-pop-order"
      run := do
        expectErr "pop-y-first-null" (runGreaterDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second-null" (runGreaterDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-first" (runGreaterDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/underflow-ordering-on-short-stacks"
      run := do
        expectErr "empty" (runGreaterDirect #[]) .stkUnd
        expectErr "one-int" (runGreaterDirect #[intV 1]) .stkUnd
        expectErr "one-non-int-underflow-first" (runGreaterDirect #[.null]) .stkUnd }
    ,
    { name := "unit/dispatch/non-greater-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runGreaterDispatchFallback #[]) #[intV 777] }
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
    mkCase "nan/y-via-pushnan-intov" #[intV 42] #[.pushInt .nan, .greater],
    mkCase "nan/x-via-pushnan-xchg-intov" #[intV 42] #[.pushInt .nan, .xchg0 1, .greater],
    mkCase "nan/both-via-double-pushnan-intov" #[] #[.pushInt .nan, .pushInt .nan, .greater],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num greaterSetGasExact), .tonEnvOp .setGasLimit, .greater],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num greaterSetGasExactMinusOne), .tonEnvOp .setGasLimit, .greater]
  ]
  fuzz := #[
    { seed := 2026020807
      count := 500
      gen := genGreaterFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.GREATER
