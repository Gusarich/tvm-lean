import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.EQUAL

/-
EQUAL branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Equal.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_cmp`, opcode registration in `register_int_cmp_ops` with mode `0x878`).

Branch map used for this suite:
- Lean: 6 branch points / 9 terminal outcomes
  (opcode dispatch; two `popInt` failure points; `x/y` NaN-vs-finite split;
   finite compare split (`a = b` true/false); non-quiet NaN push path).
- C++: 6 branch points / 9 aligned terminal outcomes
  (`EQUAL` registration to `exec_cmp(..., mode=0x878, quiet=false)`;
   explicit `check_underflow(2)`; two `pop_int` type checks; invalid-int (NaN) path;
   compare class `{<,=,>}` mapped by mode to `{0,-1,0}`).

Terminal categories covered in oracle:
- finite success (`-1` for `x = y`, `0` for `x ≠ y`);
- `stkUnd` (empty/one-arg);
- `typeChk` at first (`y`) and second (`x`) pop;
- `intOv` from NaN propagation in non-quiet EQUAL;
- out-of-gas at exact-minus-one budget.

Key risk areas:
- truth-table mapping for mode `0x878` (only equality maps to `-1`);
- operand pop order (`y` then `x`) and corresponding error ordering;
- underflow-vs-type ordering for one-item stacks;
- NaN handling must throw `intOv` in non-quiet EQUAL;
- deterministic gas threshold for `PUSHINT n; SETGASLIMIT; EQUAL`.
-/

private def equalId : InstrId := { name := "EQUAL" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.equal])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := equalId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runEqualDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithEqual .equal stack

private def runEqualDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithEqual .add (VM.push (intV 777)) stack

private def equalSetGasExact : Int :=
  computeExactGasBudget .equal

private def equalSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .equal

private def genEqualFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
  id := equalId
  unit := #[
    { name := "unit/finite-equality-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, -1),
            (1, 1, -1),
            (1, 2, 0),
            (-7, -7, -1),
            (-7, -8, 0),
            (-1, 1, 0),
            (1, -1, 0),
            (minInt257, minInt257, -1),
            (maxInt257, maxInt257, -1),
            (minInt257, maxInt257, 0),
            (maxInt257, minInt257, 0),
            (maxInt257 - 1, maxInt257, 0),
            (minInt257 + 1, minInt257, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}=={y}" (runEqualDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/nan-propagation-throws-intov"
      run := do
        expectErr "x-nan" (runEqualDirect #[.int .nan, intV 1]) .intOv
        expectErr "y-nan" (runEqualDirect #[intV 1, .int .nan]) .intOv
        expectErr "both-nan" (runEqualDirect #[.int .nan, .int .nan]) .intOv }
    ,
    { name := "unit/type-errors-follow-pop-order"
      run := do
        expectErr "pop-y-first-null" (runEqualDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second-null" (runEqualDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-first" (runEqualDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/underflow-ordering-on-short-stacks"
      run := do
        expectErr "empty" (runEqualDirect #[]) .stkUnd
        expectErr "one-int" (runEqualDirect #[intV 1]) .stkUnd
        expectErr "one-non-int-underflow-first" (runEqualDirect #[.null]) .stkUnd }
    ,
    { name := "unit/dispatch/non-equal-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runEqualDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/equal/zero-eq-zero" #[intV 0, intV 0],
    mkCase "ok/equal/pos-eq-pos" #[intV 17, intV 17],
    mkCase "ok/equal/neg-eq-neg" #[intV (-17), intV (-17)],
    mkCase "ok/not-equal/pos-ne-pos" #[intV 17, intV 25],
    mkCase "ok/not-equal/neg-ne-neg" #[intV (-17), intV (-25)],
    mkCase "ok/not-equal/neg-ne-pos" #[intV (-1), intV 1],
    mkCase "ok/not-equal/pos-ne-neg" #[intV 1, intV (-1)],
    mkCase "ok/edge/min-eq-min" #[intV minInt257, intV minInt257],
    mkCase "ok/edge/max-eq-max" #[intV maxInt257, intV maxInt257],
    mkCase "ok/edge/min-ne-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/edge/max-ne-min" #[intV maxInt257, intV minInt257],
    mkCase "ok/edge/max-minus-one-ne-max" #[intV (maxInt257 - 1), intV maxInt257],
    mkCase "ok/edge/min-plus-one-ne-min" #[intV (minInt257 + 1), intV minInt257],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "nan/y-via-pushnan-intov" #[intV 42] #[.pushInt .nan, .equal],
    mkCase "nan/x-via-pushnan-xchg-intov" #[intV 42] #[.pushInt .nan, .xchg0 1, .equal],
    mkCase "nan/both-via-double-pushnan-intov" #[] #[.pushInt .nan, .pushInt .nan, .equal],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num equalSetGasExact), .tonEnvOp .setGasLimit, .equal],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num equalSetGasExactMinusOne), .tonEnvOp .setGasLimit, .equal]
  ]
  fuzz := #[
    { seed := 2026020807
      count := 500
      gen := genEqualFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.EQUAL
