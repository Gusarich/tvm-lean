import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULDIVC

/-
MULDIVC branch-mapping notes (Lean + C++ analyzed sources):

- Lean:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa98` + args4 decode)
  - Generic `.mulDivMod` handler has 7 branch sites / 16 terminal outcomes
    (dispatch arm; add-mode pop path; operand-shape split; divisor-zero split;
     round-mode validity split; `d` switch; non-num `d=3` split).
  - MULDIVC specialization is `.mulDivMod 1 1 false false` (ceil), with
    reachable outcomes: `ok`, `stkUnd`, `typeChk`, `intOv` (divzero),
    `intOv` (NaN funnel), `intOv` (quotient overflow/range check).

- C++:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `exec_muldivmod` has 5 branch sites / 11 terminal outcomes
    (global-version add-mode remap gate, invalid-opcode guard, underflow guard,
     add/non-add path, `d` switch push-shape split).
  - MULDIVC wiring is opcode `0xa986` (`0xa98` args4=`0x6`), non-quiet.

Key risk areas covered:
- ceil quotient semantics across all sign combinations and near-zero products;
- pop/error ordering (`z`, then `y`, then `x`);
- non-quiet NaN/divzero funnel to `intOv`;
- signed-257 quotient boundary behavior and overflow;
- exact gas boundary via `PUSHINT n; SETGASLIMIT; MULDIVC`.
-/

private def muldivcId : InstrId := { name := "MULDIVC" }

private def muldivcInstr : Instr := .mulDivMod 1 1 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muldivcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muldivcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulDivCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod muldivcInstr stack

private def runMulDivCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 3302)) stack

private def muldivcSetGasExact : Int :=
  computeExactGasBudget muldivcInstr

private def muldivcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muldivcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def ceilFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def ceilDivisorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genMulDivCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let ((x, y, z), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, y0, z0), r4)
    else if shape = 1 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, y0, z0), r4)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, y0, z0), r4)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, y0, z0), r4)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0, 0), r3)
    else if shape = 5 then
      let (x0, r2) := pickFromPool ceilFactorPool rng1
      let (y0, r3) := pickFromPool ceilFactorPool r2
      let (z0, r4) := pickFromPool ceilDivisorPool r3
      ((x0, y0, z0), r4)
    else if shape = 6 then
      ((minInt257, -1, 1), rng1)
    else if shape = 7 then
      ((minInt257, -1, -1), rng1)
    else if shape = 8 then
      ((maxInt257, 1, 2), rng1)
    else if shape = 9 then
      ((maxInt257, -1, 2), rng1)
    else if shape = 10 then
      let (y0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickNonZeroInt r2
      ((0, y0, z0), r3)
    else if shape = 11 then
      let (x0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickNonZeroInt r2
      ((x0, 0, z0), r3)
    else if shape = 12 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0, 1), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0, -1), r3)
  let tmp : Int := x * y
  let kind :=
    if z = 0 then
      "divzero"
    else
      let (q, _) := divModRound tmp z 1
      if !intFitsSigned257 q then
        "overflow"
      else if tmp = 0 then
        "zero"
      else if tmp % z = 0 then
        "exact"
      else
        "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV z], rng3)

def suite : InstrSuite where
  id := muldivcId
  unit := #[
    { name := "unit/ok/ceil-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 11),
            (-7, 3, 2, -10),
            (7, -3, 2, -10),
            (-7, -3, 2, 11),
            (5, 5, 2, 13),
            (-5, 5, 2, -12),
            (5, -5, 2, -12),
            (-5, -5, 2, 13),
            (-1, 1, 2, 0),
            (1, -1, 2, 0),
            (-1, -1, 2, 1),
            (0, 9, 5, 0),
            (9, 0, 5, 0),
            (42, 6, 7, 36),
            (-42, 6, 7, -36),
            (42, -6, 7, -36),
            (-42, -6, 7, 36)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"({x}*{y})/{z}" (runMulDivCDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "unit/ok/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, maxInt257),
            (maxInt257, -1, 1, -maxInt257),
            (minInt257, 1, 1, minInt257),
            (minInt257, -1, -1, minInt257),
            (minInt257 + 1, -1, -1, minInt257 + 1),
            (maxInt257, 1, 2, pow2 255),
            (maxInt257, -1, 2, 1 - (pow2 255)),
            (minInt257, 1, 2, -(pow2 255)),
            (minInt257, 1, -2, pow2 255),
            (minInt257 + 1, -1, 2, pow2 255)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"({x}*{y})/{z}" (runMulDivCDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "unit/error/intov-from-divzero-and-overflow"
      run := do
        expectErr "divzero/nonzero-product-over-zero" (runMulDivCDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "divzero/zero-product-over-zero" (runMulDivCDirect #[intV 0, intV 7, intV 0]) .intOv
        expectErr "overflow/min-times-neg-one-div-one" (runMulDivCDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/max-times-max-div-one" (runMulDivCDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-times-min-div-one" (runMulDivCDirect #[intV minInt257, intV minInt257, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulDivCDirect #[]) .stkUnd
        expectErr "underflow/one-int-before-missing-y" (runMulDivCDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-ints-before-missing-x" (runMulDivCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type-with-two-items"
          (runMulDivCDirect #[.cell Cell.empty, .null]) .stkUnd
        expectErr "type/pop-z-first" (runMulDivCDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulDivCDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMulDivCDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-z-before-y-when-both-non-int"
          (runMulDivCDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-z-int"
          (runMulDivCDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulDivCDispatchFallback #[]) #[intV 3302] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "ok/ceil/sign/neg-pos-near-zero" #[intV (-1), intV 1, intV 2],
    mkCase "ok/ceil/sign/pos-neg-near-zero" #[intV 1, intV (-1), intV 2],
    mkCase "ok/ceil/sign/neg-neg-near-zero" #[intV (-1), intV (-1), intV 2],
    mkCase "ok/ceil/sign/pos-pos-half" #[intV 5, intV 5, intV 2],
    mkCase "ok/ceil/sign/neg-pos-half" #[intV (-5), intV 5, intV 2],
    mkCase "ok/ceil/sign/pos-neg-half" #[intV 5, intV (-5), intV 2],
    mkCase "ok/ceil/sign/neg-neg-half" #[intV (-5), intV (-5), intV 2],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 6, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 6, intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-6), intV 7],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-6), intV 7],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "ok/boundary/max-times-neg-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/boundary/min-times-neg-one-div-neg-one" #[intV minInt257, intV (-1), intV (-1)],
    mkCase "ok/boundary/min-plus-one-times-neg-one-div-neg-one" #[intV (minInt257 + 1), intV (-1), intV (-1)],
    mkCase "ok/boundary/max-times-one-div-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-times-neg-one-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "ok/boundary/min-times-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "ok/boundary/min-times-one-div-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "ok/boundary/min-plus-one-times-neg-one-div-two"
      #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "overflow/min-times-neg-one-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "overflow/max-times-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "overflow/max-times-max-div-neg-one" #[intV maxInt257, intV maxInt257, intV (-1)],
    mkCase "overflow/min-times-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int-before-missing-y" #[intV 1],
    mkCase "underflow/two-ints-before-missing-x" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-items" #[.cell Cell.empty, .null],
    mkCase "type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "nan/z-via-program" #[intV 5, intV 7] #[.pushInt .nan, muldivcInstr],
    mkCase "nan/y-via-program" #[intV 5, intV 7]
      #[.pushInt .nan, .xchg0 1, muldivcInstr],
    mkCase "nan/x-via-program" #[intV 5, intV 7]
      #[.pushInt .nan, .xchg0 2, .xchg0 1, muldivcInstr],
    mkCase "out-of-range/injected-positive-before-op" #[intV 5, intV 7]
      #[.pushInt (.num (maxInt257 + 1)), .xchg0 2, .xchg0 1, muldivcInstr],
    mkCase "out-of-range/injected-negative-before-op" #[intV 5, intV 7]
      #[.pushInt (.num (minInt257 - 1)), .xchg0 2, .xchg0 1, muldivcInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivcSetGasExact), .tonEnvOp .setGasLimit, muldivcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivcSetGasExactMinusOne), .tonEnvOp .setGasLimit, muldivcInstr]
  ]
  fuzz := #[
    { seed := 2026020810
      count := 700
      gen := genMulDivCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULDIVC
