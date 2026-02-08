import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODC

/-
MULMODC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa98` + args4 decode to `.mulDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, opcode registration in `register_div_ops`)

Branch counts used for this suite:
- Lean (generic `.mulDivMod`): 7 branch sites / 16 terminal outcomes
  (dispatch arm; underflow gate; add-mode `w` pop split; operand-shape match;
   divisor-zero split; round-mode validation split; `d` switch with `d=3` arity split).
- C++ (`exec_muldivmod`): 5 branch sites / 11 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add operand path; `d` result-shape split).

MULMODC specialization:
- opcode args4 = `0xA` under `0xa98`;
- fixed params: `d=2`, `roundMode=1` (ceil), `addMode=false`, `quiet=false`.

Key risk areas covered:
- ceil-remainder sign behavior for mixed-sign products;
- `d=2` must not spuriously fail when quotient is huge/out-of-range but remainder fits;
- pop/error ordering (`z`, then `y`, then `x`; underflow before type paths);
- non-quiet NaN and out-of-range inputs injected through program only;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; MULMODC`.
-/

private def mulmodcId : InstrId := { name := "MULMODC" }

private def mulmodcInstr : Instr := .mulDivMod 2 1 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push mulmodcInstr) gasLimits fuel

private def runMulmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod mulmodcInstr stack

private def runMulmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 4202)) stack

private def mulmodcSetGasExact : Int :=
  computeExactGasBudget mulmodcInstr

private def mulmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def mulmodcProductPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def mulmodcDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def mulmodcOutOfRangePool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1, pow2 257, -(pow2 257)]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genMulmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-left" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-right" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"fuzz/shape-{shape}/ok-random" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickFromPool mulmodcProductPool rng1
      let (y, r3) := pickFromPool mulmodcProductPool r2
      let (z, r4) := pickFromPool mulmodcDivisorPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-small-sign-mix" #[intV x, intV y, intV z], r4)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/divzero-boundary" #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/divzero-random" #[intV x, intV y, intV 0], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/ok-huge-quotient-max-max" #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/ok-huge-quotient-min-neg-one" #[intV minInt257, intV 1, intV (-1)], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/ok-huge-quotient-min-plus-one-neg-one"
        #[intV (minInt257 + 1), intV (-1), intV 1], rng1)
    else if shape = 9 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok-zero-left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok-zero-right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one" #[intV x], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two" #[intV x, intV y], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-z-first" #[intV x, intV y, .null], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-second" #[intV x, .cell Cell.empty, intV z], r3)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-third" #[.null, intV y, intV z], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-z-via-program" #[.num x, .num y, .nan], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-y-via-program" #[.num x, .nan, .num z], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickFromPool mulmodcOutOfRangePool r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-z-via-program" #[.num x, .num y, .num z], r4)
    else
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let (x, r4) := pickFromPool mulmodcOutOfRangePool r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-x-via-program" #[.num x, .num y, .num z], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulmodcId
  unit := #[
    { name := "unit/ok/ceil-mod-sign-and-exactness"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 5, -4),
            (-7, 3, 5, -1),
            (7, -3, 5, -1),
            (-7, -3, 5, -4),
            (-1, 1, 2, -1),
            (1, -1, 2, -1),
            (-1, -1, -2, 1),
            (1, 1, -2, 1),
            (6, 7, 3, 0),
            (5, -7, 3, -2),
            (-5, 7, -3, 1),
            (0, 9, 5, 0),
            (9, 0, -5, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})%{z}" (runMulmodcDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "unit/ok/boundary-and-huge-quotient-remainder"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, 0),
            (maxInt257, 1, -1, 0),
            (minInt257, 1, 1, 0),
            (minInt257, 1, -1, 0),
            (maxInt257, 1, 2, -1),
            (maxInt257, 1, -2, 1),
            (minInt257 + 1, 1, 2, -1),
            (minInt257 + 1, 1, -2, 1),
            (maxInt257, maxInt257, 1, 0),
            (minInt257, minInt257, 1, 0),
            (0, maxInt257, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})%{z}" (runMulmodcDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "unit/error/divzero-underflow-type-and-pop-order"
      run := do
        expectErr "divzero/nonzero-over-zero" (runMulmodcDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "divzero/zero-over-zero" (runMulmodcDirect #[intV 0, intV 0, intV 0]) .intOv
        expectErr "underflow/empty" (runMulmodcDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runMulmodcDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-ints" (runMulmodcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/two-non-int-underflow-before-type" (runMulmodcDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-z-first" (runMulmodcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulmodcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMulmodcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-z-before-y-when-both-non-int"
          (runMulmodcDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-z-int"
          (runMulmodcDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulmodcDispatchFallback #[]) #[intV 4202] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 5],
    mkCase "ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 5],
    mkCase "ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 5],
    mkCase "ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 5],
    mkCase "ok/ceil/sign/neg-pos-near-zero" #[intV (-1), intV 1, intV 2],
    mkCase "ok/ceil/sign/pos-neg-near-zero" #[intV 1, intV (-1), intV 2],
    mkCase "ok/ceil/sign/neg-neg-divisor-near-zero" #[intV (-1), intV (-1), intV (-2)],
    mkCase "ok/ceil/sign/pos-pos-neg-divisor-near-zero" #[intV 1, intV 1, intV (-2)],
    mkCase "ok/exact/positive-product" #[intV 6, intV 7, intV 3],
    mkCase "ok/exact/negative-product" #[intV (-6), intV 7, intV 3],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 33, intV 7],
    mkCase "ok/exact/zero-right-factor" #[intV 33, intV 0, intV (-7)],
    mkCase "ok/boundary/max-times-one-mod-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "ok/boundary/max-times-one-mod-neg-one" #[intV maxInt257, intV 1, intV (-1)],
    mkCase "ok/boundary/min-times-one-mod-one" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/boundary/min-times-one-mod-neg-one" #[intV minInt257, intV 1, intV (-1)],
    mkCase "ok/boundary/max-times-one-mod-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-times-one-mod-neg-two" #[intV maxInt257, intV 1, intV (-2)],
    mkCase "ok/boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 1, intV 2],
    mkCase "ok/boundary/min-plus-one-mod-neg-two" #[intV (minInt257 + 1), intV 1, intV (-2)],
    mkCase "ok/boundary/huge-quotient-max-max-remains-zero" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "ok/boundary/huge-quotient-min-min-remains-zero" #[intV minInt257, intV minInt257, intV 1],
    mkCase "ok/boundary/huge-quotient-min-neg-one-remains-zero" #[intV minInt257, intV 1, intV (-1)],
    mkCase "divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/two-non-int-underflow-before-type" #[.null, .cell Cell.empty],
    mkCase "type/pop-z-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-z-before-y-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-y-before-x-after-z-int" #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "nan/z-via-program" #[.num 5, .num 7, .nan],
    mkCaseFromIntVals "nan/y-via-program" #[.num 5, .nan, .num 7],
    mkCaseFromIntVals "nan/x-via-program" #[.nan, .num 5, .num 7],
    mkCaseFromIntVals "range/z-out-of-range-via-program" #[.num 5, .num 7, .num (pow2 257)],
    mkCaseFromIntVals "range/x-out-of-range-via-program" #[.num (-(pow2 257)), .num 5, .num 7],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodcSetGasExact), .tonEnvOp .setGasLimit, mulmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genMulmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODC
