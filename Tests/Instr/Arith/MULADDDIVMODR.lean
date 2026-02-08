import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULADDDIVMODR

/-
MULADDDIVMODR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `0` nearest/tie-to-+∞)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa98` args4 decode to `.mulDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (generic `.mulDivMod`): 8 branch sites / 18 terminal outcomes
  (dispatch arm; stack-arity guard; add-mode pop path; operand-shape split;
   divisor-zero split; round-mode validity split; `d` switch with 4 arms;
   non-num `d=3` split).
- C++ (`exec_muldivmod`): 5 branch sites / 11 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add vs non-add pop path; `d` switch with quotient/mod/both exits).

MULADDDIVMODR specialization:
- opcode args4=`0x1` under `0xa98` family;
- fixed params: `d=3`, `roundMode=0` (nearest), `addMode=true`, `quiet=false`.

Key risk areas covered:
- nearest rounding ties across sign combinations after `x*y + w`;
- overflow from large intermediate products pushed non-quiet (`intOv`);
- non-quiet NaN/divzero funnels (NaN injected via program only);
- pop order (`z`, `w`, `y`, `x`) and underflow-before-type ordering;
- exact gas boundary behavior via `SETGASLIMIT` fixed-point budgets.
-/

private def muladddivmodrId : InstrId := { name := "MULADDDIVMODR" }

private def muladddivmodrInstr : Instr := .mulDivMod 3 0 true false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muladddivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muladddivmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulAddDivModRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod muladddivmodrInstr stack

private def runMulAddDivModRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 4242)) stack

private def muladddivmodrSetGasExact : Int :=
  computeExactGasBudget muladddivmodrInstr

private def muladddivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muladddivmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genMulAddDivModRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let ((x, y, w, z), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let (w0, r4) := pickInt257Boundary r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      ((x0, y0, w0, 0), r4)
    else if shape = 3 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (z0, r3) := pickFromPool tieDenominatorPool r2
      ((t, 1, 0, z0), r3)
    else if shape = 4 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (z0, r3) := pickFromPool tieDenominatorPool r2
      ((t, 1, 1, z0), r3)
    else if shape = 5 then
      ((maxInt257, 2, 0, 1), rng1)
    else if shape = 6 then
      ((minInt257, 2, 0, 1), rng1)
    else if shape = 7 then
      ((minInt257, 1, 0, -1), rng1)
    else if shape = 8 then
      ((maxInt257, maxInt257, 0, 1), rng1)
    else if shape = 9 then
      ((minInt257, maxInt257, 0, 1), rng1)
    else if shape = 10 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, 0, w0, z0), r4)
    else if shape = 11 then
      let (y0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((0, y0, w0, z0), r4)
    else if shape = 12 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      ((x0, y0, w0, 1), r4)
    else if shape = 13 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      ((x0, y0, w0, -1), r4)
    else if shape = 14 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickFromPool roundDenominatorPool r4
      ((x0, y0, w0, z0), r5)
    else
      let (x0raw, r2) := pickSigned257ish rng1
      let x0 := if x0raw = minInt257 then minInt257 + 1 else x0raw
      let (z0, r3) := pickFromPool roundDenominatorPool r2
      ((x0, 1, -x0, z0), r3)
  let tmp : Int := x * y + w
  let kind :=
    if z = 0 then
      "divzero"
    else
      let (q, r) := divModRound tmp z 0
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else if (Int.natAbs r) * 2 = Int.natAbs z then
        "tie"
      else
        "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV w, intV z], rng3)

def suite : InstrSuite where
  id := muladddivmodrId
  unit := #[
    { name := "unit/ok/nearest-rounding-signs-and-ties"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 3, 4, 10, -2),
            (7, 5, 2, 4, 9, 1),
            (-7, 5, 0, 4, -9, 1),
            (7, -5, 0, 4, -9, 1),
            (-7, -5, 0, 4, 9, -1),
            (5, 1, 0, 2, 3, -1),
            (-5, 1, 0, 2, -2, -1),
            (5, 1, 0, -2, -2, 1),
            (-5, 1, 0, -2, 3, 1),
            (-1, 1, 0, 2, 0, -1),
            (1, 1, 0, -2, 0, 1),
            (4, 3, 1, 2, 7, -1)
          ]
        for c in checks do
          match c with
          | (x, y, w, z, q, r) =>
              expectOkStack s!"({x}*{y}+{w})/{z}"
                (runMulAddDivModRDirect #[intV x, intV y, intV w, intV z])
                #[intV q, intV r] }
    ,
    { name := "unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 1, maxInt257, 0),
            (maxInt257, 1, -1, 1, maxInt257 - 1, 0),
            (minInt257, 1, 1, 1, minInt257 + 1, 0),
            (minInt257 + 1, 1, 0, -1, maxInt257, 0),
            (maxInt257, 1, 0, 2, pow2 255, -1),
            (minInt257, 1, 0, 2, -(pow2 255), 0),
            (minInt257, 1, 0, -2, pow2 255, 0)
          ]
        for c in checks do
          match c with
          | (x, y, w, z, q, r) =>
              expectOkStack s!"({x}*{y}+{w})/{z}"
                (runMulAddDivModRDirect #[intV x, intV y, intV w, intV z])
                #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runMulAddDivModRDirect #[intV 5, intV 7, intV 1, intV 0]) .intOv
        expectErr "overflow/max-times-two-over-one"
          (runMulAddDivModRDirect #[intV maxInt257, intV 2, intV 0, intV 1]) .intOv
        expectErr "overflow/min-times-two-over-one"
          (runMulAddDivModRDirect #[intV minInt257, intV 2, intV 0, intV 1]) .intOv
        expectErr "overflow/min-over-negone"
          (runMulAddDivModRDirect #[intV minInt257, intV 1, intV 0, intV (-1)]) .intOv
        expectErr "overflow/max-times-max-over-one"
          (runMulAddDivModRDirect #[intV maxInt257, intV maxInt257, intV 0, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulAddDivModRDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runMulAddDivModRDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runMulAddDivModRDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/three-args" (runMulAddDivModRDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "error-order/underflow-before-type-with-three-items"
          (runMulAddDivModRDirect #[.null, .cell Cell.empty, intV 1]) .stkUnd
        expectErr "type/pop-z-first" (runMulAddDivModRDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "type/pop-w-second" (runMulAddDivModRDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "type/pop-y-third" (runMulAddDivModRDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "type/pop-x-fourth" (runMulAddDivModRDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "error-order/pop-z-before-w-when-both-non-int"
          (runMulAddDivModRDirect #[intV 1, intV 2, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/pop-w-before-y-when-z-int"
          (runMulAddDivModRDirect #[intV 1, .null, .cell Cell.empty, intV 2]) .typeChk
        expectErr "error-order/pop-y-before-x-when-zw-int"
          (runMulAddDivModRDirect #[.null, .cell Cell.empty, intV 1, intV 2]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runMulAddDivModRDispatchFallback #[]) #[intV 4242] }
  ]
  oracle := #[
    mkCase "ok/round/inexact-pos-pos" #[intV 7, intV 5, intV 2, intV 4],
    mkCase "ok/round/inexact-neg-pos" #[intV (-7), intV 5, intV 0, intV 4],
    mkCase "ok/round/inexact-pos-neg" #[intV 7, intV 5, intV 0, intV (-4)],
    mkCase "ok/round/inexact-neg-neg" #[intV (-7), intV 5, intV 0, intV (-4)],
    mkCase "ok/tie/pos-over-pos-two" #[intV 5, intV 1, intV 0, intV 2],
    mkCase "ok/tie/neg-over-pos-two" #[intV (-5), intV 1, intV 0, intV 2],
    mkCase "ok/tie/pos-over-neg-two" #[intV 5, intV 1, intV 0, intV (-2)],
    mkCase "ok/tie/neg-over-neg-two" #[intV (-5), intV 1, intV 0, intV (-2)],
    mkCase "ok/tie/near-zero-neg-pos" #[intV (-1), intV 1, intV 0, intV 2],
    mkCase "ok/tie/near-zero-pos-neg" #[intV 1, intV 1, intV 0, intV (-2)],
    mkCase "ok/exact/pos-product-over-two" #[intV 4, intV 3, intV 0, intV 2],
    mkCase "ok/exact/neg-product-over-two" #[intV (-4), intV 3, intV 0, intV 2],
    mkCase "ok/exact/zero-product-plus-w" #[intV 0, intV 99, intV 7, intV 7],
    mkCase "ok/exact/addend-cancels-product" #[intV 42, intV 1, intV (-42), intV 3],
    mkCase "ok/boundary/max-times-one-over-one" #[intV maxInt257, intV 1, intV 0, intV 1],
    mkCase "ok/boundary/max-times-one-plus-negone-over-one" #[intV maxInt257, intV 1, intV (-1), intV 1],
    mkCase "ok/boundary/min-times-one-plus-one-over-one" #[intV minInt257, intV 1, intV 1, intV 1],
    mkCase "ok/boundary/min-plus-one-over-negone" #[intV (minInt257 + 1), intV 1, intV 0, intV (-1)],
    mkCase "ok/boundary/max-over-two-rounds-up" #[intV maxInt257, intV 1, intV 0, intV 2],
    mkCase "ok/boundary/min-over-two-exact" #[intV minInt257, intV 1, intV 0, intV 2],
    mkCase "ok/boundary/min-over-neg-two-exact" #[intV minInt257, intV 1, intV 0, intV (-2)],
    mkCase "overflow/max-times-two-over-one" #[intV maxInt257, intV 2, intV 0, intV 1],
    mkCase "overflow/min-times-two-over-one" #[intV minInt257, intV 2, intV 0, intV 1],
    mkCase "overflow/min-over-negone" #[intV minInt257, intV 1, intV 0, intV (-1)],
    mkCase "overflow/max-times-max-over-one" #[intV maxInt257, intV maxInt257, intV 0, intV 1],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 7, intV 1, intV 0],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "type/pop-z-first" #[intV 1, intV 2, intV 3, .null],
    mkCase "type/pop-w-second" #[intV 1, intV 2, .null, intV 3],
    mkCase "type/pop-y-third" #[intV 1, .null, intV 2, intV 3],
    mkCase "type/pop-x-fourth" #[.null, intV 1, intV 2, intV 3],
    mkCase "error-order/underflow-before-type-with-three-items" #[.null, .cell Cell.empty, intV 1],
    mkCase "error-order/pop-z-before-w-when-both-non-int" #[intV 1, intV 2, .null, .cell Cell.empty],
    mkCase "error-order/pop-w-before-y-when-z-int" #[intV 1, .null, .cell Cell.empty, intV 2],
    mkCase "error-order/pop-y-before-x-when-zw-int" #[.null, .cell Cell.empty, intV 1, intV 2],
    mkCase "nan/z-via-program" #[intV 5, intV 7, intV 1]
      #[.pushInt .nan, muladddivmodrInstr],
    mkCase "nan/w-via-program" #[intV 5, intV 7, intV 1]
      #[.pushInt .nan, .xchg0 1, muladddivmodrInstr],
    mkCase "nan/y-via-program" #[intV 5, intV 3, intV 1]
      #[.pushInt .nan, .xchg0 2, .xchg0 1, muladddivmodrInstr],
    mkCase "nan/x-via-program" #[intV 7, intV 3, intV 1]
      #[.pushInt .nan, .xchg0 3, .xchg0 1, muladddivmodrInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3, intV 4]
      #[.pushInt (.num muladddivmodrSetGasExact), .tonEnvOp .setGasLimit, muladddivmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3, intV 4]
      #[.pushInt (.num muladddivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, muladddivmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 700
      gen := genMulAddDivModRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDDIVMODR
