import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.SUBR

/-
SUBR branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Subr.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_subr`, opcode registration in `register_add_mul_ops`).

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (opcode dispatch; two `popInt` failure points; `IntVal.sub` finite-vs-NaN;
   `pushIntQuiet` NaN-vs-num and signed-257 fit check).
- C++: 5 branch points / 8 aligned terminal outcomes
  (registration binds SUBR to `exec_subr(..., quiet=false)`; underflow check;
   two `pop_int` type checks; `push_int_quiet` signed-257 fit check with non-quiet throw).

Key risk areas:
- Reverse operand order must remain `y - x` (not `x - y`).
- Signed 257-bit boundary off-by-one (`[-2^256, 2^256-1]`) on both overflow sides.
- NaN propagation must fail with `intOv` in non-quiet SUBR.
- Operand pop order (`y` then `x`) determines first-observed type error when both are non-int.
- Gas-boundary checks should be deterministic in both Lean and `runvmx`
  (`PUSHINT n; SETGASLIMIT; SUBR` with exact and exact-minus-one budgets).
-/

private def subrId : InstrId := { name := "SUBR" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.subr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := subrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSubrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithSubr .subr stack

private def subrSetGasExact : Int :=
  computeExactGasBudget .subr

private def subrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .subr

private def genSubrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  let ((x, y), rng3) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else
      let (y0, r2) := pickSigned257ish rng1
      ((0, y0), r2)
  (mkCase s!"fuzz/shape-{shape}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := subrId
  unit := #[
    { name := "unit/reverse-subtraction-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (3, 10, 7),
            (10, 3, -7),
            (-7, 3, 10),
            (7, -3, -10),
            (-9, -11, -2),
            (0, 123, 123),
            (123, 0, -123)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{y}-{x}" (runSubrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/near-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (1, maxInt257, maxInt257 - 1),
            (-1, minInt257, minInt257 + 1),
            (1, minInt257 + 1, minInt257),
            (-1, maxInt257 - 1, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{y}-{x}" (runSubrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/overflow-boundaries-throw-intov"
      run := do
        expectErr "max-(-1)" (runSubrDirect #[intV (-1), intV maxInt257]) .intOv
        expectErr "min-1" (runSubrDirect #[intV 1, intV minInt257]) .intOv }
    ,
    { name := "unit/nan-and-pop-order-type-errors"
      run := do
        expectErr "y=nan" (runSubrDirect #[intV 1, .int .nan]) .intOv
        expectErr "x=nan" (runSubrDirect #[.int .nan, intV 1]) .intOv
        expectErr "pop-y-first" (runSubrDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second" (runSubrDirect #[.null, intV 1]) .typeChk
        expectErr "underflow-before-type-single-non-int" (runSubrDirect #[.null]) .stkUnd }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "ok/pos-pos" #[intV 5, intV 17],
    mkCase "ok/pos-neg" #[intV 5, intV (-17)],
    mkCase "ok/neg-pos" #[intV (-5), intV 17],
    mkCase "ok/neg-neg" #[intV (-5), intV (-17)],
    mkCase "ok/zero-right" #[intV 222, intV 0],
    mkCase "ok/zero-left" #[intV 0, intV 222],
    mkCase "boundary/max-minus-zero" #[intV 0, intV maxInt257],
    mkCase "boundary/min-minus-zero" #[intV 0, intV minInt257],
    mkCase "near-boundary/max-minus-one" #[intV 1, intV maxInt257],
    mkCase "near-boundary/min-plus-one" #[intV (-1), intV minInt257],
    mkCase "near-boundary/min-plus-one-to-min" #[intV 1, intV (minInt257 + 1)],
    mkCase "near-boundary/max-minus-one-to-max" #[intV (-1), intV (maxInt257 - 1)],
    mkCase "overflow/max-minus-neg-one" #[intV (-1), intV maxInt257],
    mkCase "overflow/max-minus-min" #[intV minInt257, intV maxInt257],
    mkCase "underflow/min-minus-one" #[intV 1, intV minInt257],
    mkCase "underflow/min-minus-max" #[intV maxInt257, intV minInt257],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "nan/y-nan-via-program" #[intV 1] #[.pushInt .nan, .subr],
    mkCase "nan/x-nan-via-program" #[intV 1] #[.pushInt .nan, .xchg0 1, .subr],
    mkCase "nan/pushnan-propagates-intov" #[intV 42] #[.pushInt .nan, .subr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num subrSetGasExact), .tonEnvOp .setGasLimit, .subr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num subrSetGasExactMinusOne), .tonEnvOp .setGasLimit, .subr]
  ]
  fuzz := #[
    { seed := 2026020802
      count := 500
      gen := genSubrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.SUBR
