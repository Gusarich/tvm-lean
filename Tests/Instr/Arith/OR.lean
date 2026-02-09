import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.OR

/-
OR branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Or.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_or`, opcode registration in `register_shift_logic_ops`).

Terminal-path focus for this suite:
- opcode dispatch (`.or`) versus fallback `next`;
- stack-underflow before any type checks (`checkUnderflow 2`);
- pop/type ordering (`y` pop/type failure before `x`);
- NaN in either operand for non-quiet OR (`pushIntQuiet ... false` => `intOv`);
- 257-bit two's-complement conversion for both operands, including
  negative-bit-pattern cases around sign bit 256 / high bit 255;
- out-of-range numeric operands (`|x| > 2^256`) failing pop validation with `rangeChk`;
- exact gas threshold for `PUSHINT n; SETGASLIMIT; OR` (exact vs exact-1).
-/

private def orId : InstrId := { name := "OR" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.or])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := orId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runOrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithOr .or stack

private def orSetGasExact : Int :=
  computeExactGasBudget .or

private def orSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .or

private def genOrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (x, r2) := pickInt257Boundary rng1
    let (y, r3) := pickInt257Boundary r2
    (mkCase "fuzz/shape-0-boundary-boundary" #[intV x, intV y], r3)
  else if shape = 1 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickInt257Boundary r2
    (mkCase "fuzz/shape-1-signed-boundary" #[intV x, intV y], r3)
  else if shape = 2 then
    let (x, r2) := pickInt257Boundary rng1
    let (y, r3) := pickSigned257ish r2
    (mkCase "fuzz/shape-2-boundary-signed" #[intV x, intV y], r3)
  else if shape = 3 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickSigned257ish r2
    (mkCase "fuzz/shape-3-signed-signed" #[intV x, intV y], r3)
  else if shape = 4 then
    let (variant, r2) := randNat rng1 0 2
    let x :=
      if variant = 0 then
        -(pow2 255)
      else if variant = 1 then
        -(pow2 200)
      else
        -8
    let y :=
      if variant = 0 then
        (pow2 255) - 1
      else if variant = 1 then
        pow2 13
      else
        7
    (mkCase s!"fuzz/shape-4-neg-pattern-{variant}" #[intV x, intV y], r2)
  else if shape = 5 then
    let (mode, r2) := randNat rng1 0 2
    if mode = 0 then
      (mkCase "fuzz/shape-5-underflow-empty" #[], r2)
    else if mode = 1 then
      let (x, r3) := pickSigned257ish r2
      (mkCase "fuzz/shape-5-underflow-one-int" #[intV x], r3)
    else
      (mkCase "fuzz/shape-5-underflow-one-non-int" #[.null], r2)
  else if shape = 6 then
    let (x, r2) := pickSigned257ish rng1
    (mkCase "fuzz/shape-6-type-pop-y-first" #[intV x, .null], r2)
  else if shape = 7 then
    let (y, r2) := pickSigned257ish rng1
    (mkCase "fuzz/shape-7-type-pop-x-second" #[.null, intV y], r2)
  else if shape = 8 then
    (mkCase "fuzz/shape-8-error-order-both-non-int" #[.cell Cell.empty, .null], rng1)
  else
    let (x, r2) := pickSigned257ish rng1
    (mkCase "fuzz/shape-9-nan-propagation" #[intV x] #[.pushInt .nan, .or], r2)

def suite : InstrSuite where
  id := orId
  unit := #[
    { name := "unit/twos-complement-negative-bit-patterns"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (0, 137, 137),
            (-1, 0, -1),
            (-1, 137, -1),
            (-8, 3, -5),
            (-8, 7, -1),
            (-16, 7, -9),
            (-(pow2 255), (pow2 255) - 1, -1),
            (-(pow2 200), pow2 13, (-(pow2 200)) + (pow2 13))
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}|{y}" (runOrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/sign-bit-boundaries-and-extremes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (minInt257, 0, minInt257),
            (maxInt257, 0, maxInt257),
            (maxInt257, minInt257, -1),
            (minInt257, 1, minInt257 + 1),
            (minInt257, pow2 255, -(pow2 255)),
            (-(pow2 255), pow2 255, -(pow2 255))
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}|{y}" (runOrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/underflow-type-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runOrDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runOrDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runOrDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runOrDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runOrDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-y-first" (runOrDirect #[.cell Cell.empty, .null]) .typeChk
        expectOkStack "pop/top-two-leave-lower" (runOrDirect #[.null, intV (-8), intV 3]) #[.null, intV (-5)] }
    ,
    { name := "unit/nan-and-out-of-range-errors"
      run := do
        expectErr "nan/x" (runOrDirect #[.int .nan, intV 1]) .intOv
        expectErr "nan/y" (runOrDirect #[intV 1, .int .nan]) .intOv
        expectErr "range/x-out-of-range-positive" (runOrDirect #[intV (pow2 256), intV 0]) .rangeChk
        expectErr "range/y-out-of-range-negative" (runOrDirect #[intV 0, intV (-(pow2 256) - 1)]) .rangeChk }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "ok/zero-right" #[intV 137, intV 0],
    mkCase "ok/zero-left" #[intV 0, intV 137],
    mkCase "ok/min-or-zero" #[intV minInt257, intV 0],
    mkCase "ok/max-or-zero" #[intV maxInt257, intV 0],
    mkCase "ok/max-or-min-all-ones" #[intV maxInt257, intV minInt257],
    mkCase "ok/neg8-or-3" #[intV (-8), intV 3],
    mkCase "ok/neg8-or-7" #[intV (-8), intV 7],
    mkCase "ok/neg16-or-7" #[intV (-16), intV 7],
    mkCase "ok/min-or-one" #[intV minInt257, intV 1],
    mkCase "ok/min-or-2pow255" #[intV minInt257, intV (pow2 255)],
    mkCase "ok/neg2pow255-or-mask" #[intV (-(pow2 255)), intV ((pow2 255) - 1)],
    mkCase "ok/neg2pow200-or-bit13" #[intV (-(pow2 200)), intV (pow2 13)],
    mkCase "ok/minus-one-or-random" #[intV (-1), intV 424242],
    mkCase "error-order/top-int-lower-non-int-preserved" #[.null, intV (-8), intV 3],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "range/pop-x-out-of-range" #[]
      #[.pushInt (.num (pow2 256)), .pushInt (.num 0), .or],
    mkCase "range/pop-y-out-of-range" #[]
      #[.pushInt (.num 0), .pushInt (.num (-(pow2 256) - 1)), .or],
    mkCase "nan/init-x-nan" #[intV 7] #[.pushInt .nan, .xchg0 1, .or],
    mkCase "nan/init-y-nan" #[intV 7] #[.pushInt .nan, .or],
    mkCase "nan/pushnan-y-intov" #[intV 42] #[.pushInt .nan, .or],
    mkCase "nan/pushnan-x-intov" #[intV 42] #[.pushInt .nan, .xchg0 1, .or],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num orSetGasExact), .tonEnvOp .setGasLimit, .or],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num orSetGasExactMinusOne), .tonEnvOp .setGasLimit, .or]
  ]
  fuzz := #[
    { seed := 2026020808
      count := 500
      gen := genOrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.OR
