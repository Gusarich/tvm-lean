import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MUL

/-
MUL branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Mul.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_mul`, opcode registration in `register_add_mul_ops`);
  checked stack primitives in `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
  (`check_underflow`, `pop_int`, `push_int_quiet`).

Branch counts used for this suite:
- Lean: 7 branch points / 8 terminal outcomes
  (opcode dispatch; explicit `checkUnderflow(2)`; two `popInt` type checks;
   `IntVal.mul` finite-vs-NaN; `pushIntQuiet` NaN-vs-num and signed-257 fit check).
- C++: 6 branch points / 8 aligned terminal outcomes
  (registration binds MUL to `exec_mul(..., quiet=false)`; underflow check;
   two `pop_int` type checks; bigint result validity; `push_int_quiet` signed-257 fit check).

Key risk areas:
- Underflow-vs-type ordering for 1-element stacks (`check_underflow(2)` must win).
- Operand pop order (`y` then `x`) changes which type-check path is observed first.
- NaN propagation and 257-bit overflow/underflow both map to non-quiet `intOv`.
- Signed-257 edge cases near `[-2^256, 2^256 - 1]`, especially `min * -1`.
- Gas-boundary determinism under `PUSHINT n; SETGASLIMIT; MUL` for exact and exact-minus-one.
-/

private def mulId : InstrId := { name := "MUL" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.mul])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMul .mul stack

private def mulSetGasExact : Int :=
  computeExactGasBudget .mul

private def mulSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .mul

private def genMulFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  let ((x, y), rng3) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 1), r2)
    else if shape = 5 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, -1), r2)
    else if shape = 6 then
      let (y0, r2) := pickSigned257ish rng1
      ((0, y0), r2)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
  (mkCase s!"fuzz/shape-{shape}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := mulId
  unit := #[
    { name := "unit/finite-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 21),
            (7, -3, -21),
            (-7, 3, -21),
            (-7, -3, 21),
            (0, 123, 0),
            (123, 0, 0),
            (maxInt257, 1, maxInt257),
            (minInt257, 1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}*{y}" (runMulDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/near-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, -1, -maxInt257),
            (minInt257 + 1, -1, maxInt257),
            (maxInt257 - 1, 1, maxInt257 - 1),
            (minInt257 + 1, 1, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}*{y}" (runMulDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/overflow-boundaries-throw-intov"
      run := do
        expectErr "max*2" (runMulDirect #[intV maxInt257, intV 2]) .intOv
        expectErr "min*(-1)" (runMulDirect #[intV minInt257, intV (-1)]) .intOv
        expectErr "min*2" (runMulDirect #[intV minInt257, intV 2]) .intOv }
    ,
    { name := "unit/nan-and-pop-order-errors"
      run := do
        expectErr "nan*1" (runMulDirect #[.int .nan, intV 1]) .intOv
        expectErr "pop-y-first" (runMulDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second" (runMulDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-first" (runMulDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "single-non-int-underflow-first" (runMulDirect #[.null]) .stkUnd }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "ok/pos-pos" #[intV 17, intV 25],
    mkCase "ok/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/neg-neg" #[intV (-17), intV (-5)],
    mkCase "ok/zero-right" #[intV 222, intV 0],
    mkCase "ok/zero-left" #[intV 0, intV 222],
    mkCase "ok/max-times-zero" #[intV maxInt257, intV 0],
    mkCase "ok/min-times-zero" #[intV minInt257, intV 0],
    mkCase "ok/max-times-one" #[intV maxInt257, intV 1],
    mkCase "ok/min-times-one" #[intV minInt257, intV 1],
    mkCase "ok/max-times-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/min-plus-one-times-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/max-minus-one-times-one" #[intV (maxInt257 - 1), intV 1],
    mkCase "ok/min-plus-one-times-one" #[intV (minInt257 + 1), intV 1],
    mkCase "overflow/max-times-two" #[intV maxInt257, intV 2],
    mkCase "overflow/min-times-neg-one" #[intV minInt257, intV (-1)],
    mkCase "underflow/min-times-two" #[intV minInt257, intV 2],
    mkCase "underflow/max-times-neg-two" #[intV maxInt257, intV (-2)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/single-non-int-order" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num mulSetGasExact), .tonEnvOp .setGasLimit, .mul],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num mulSetGasExactMinusOne), .tonEnvOp .setGasLimit, .mul],
    mkCase "nan/y-via-pushnan" #[intV 42] #[.pushInt .nan, .mul],
    mkCase "nan/x-via-pushnan" #[intV 42] #[.pushInt .nan, .xchg0 1, .mul]
  ]
  fuzz := #[
    { seed := 2026020802
      count := 500
      gen := genMulFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MUL
