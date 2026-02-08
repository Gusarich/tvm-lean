import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULADDDIVMODC

/-
MULADDDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `1` / ceil)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (0xa98 args4 decode to `.mulDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (generic `.mulDivMod`): 6 branch sites / 14 terminal outcomes
  (dispatch arm; add-mode pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with non-num `d=3` split).
- C++ (`exec_muldivmod`): 5 branch sites / 10 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add tmp-init split; `d` switch terminal split).

MULADDDIVMODC specialization:
- opcode args4=`0x2` under `0xa98`;
- fixed params: `d=3`, `roundMode=1` (ceil), `addMode=true`, `quiet=false`.

Key risk areas covered:
- ceil quotient/remainder sign behavior on mixed-sign products;
- add-mode operand pop order (`z`, then `w`, then `y`, then `x`) and error ordering;
- non-quiet NaN/divzero funnels to `intOv` (NaN injected via program only);
- signed 257-bit overflow on quotient push near `minInt257`/`maxInt257`;
- deterministic gas boundary via exact / exact-minus-one `SETGASLIMIT`.
-/

private def muladddivmodcId : InstrId := { name := "MULADDDIVMODC" }

private def muladddivmodcInstr : Instr := .mulDivMod 3 1 true false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muladddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muladddivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulAddDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod muladddivmodcInstr stack

private def runMulAddDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 5050)) stack

private def muladddivmodcSetGasExact : Int :=
  computeExactGasBudget muladddivmodcInstr

private def muladddivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muladddivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def ceilMulPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def ceilAddendPool : Array Int :=
  #[-4, -3, -2, -1, 0, 1, 2, 3, 4]

private def ceilDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genMulAddDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let ((x, y, w, z), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      ((x0, y0, w0, 0), r4)
    else if shape = 5 then
      let (x0, r2) := pickFromPool ceilMulPool rng1
      let (y0, r3) := pickFromPool ceilMulPool r2
      let (w0, r4) := pickFromPool ceilAddendPool r3
      let (z0, r5) := pickFromPool ceilDivisorPool r4
      ((x0, y0, w0, z0), r5)
    else if shape = 6 then
      ((minInt257, -1, 0, 1), rng1)
    else if shape = 7 then
      ((maxInt257, 2, 0, 1), rng1)
    else if shape = 8 then
      ((minInt257, 2, 0, 1), rng1)
    else if shape = 9 then
      ((maxInt257, 1, 1, 1), rng1)
    else if shape = 10 then
      ((minInt257, 1, -1, 1), rng1)
    else if shape = 11 then
      let (y0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((0, y0, w0, z0), r4)
    else if shape = 12 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, 0, w0, z0), r4)
    else if shape = 13 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickSigned257ish r2
      ((x0, 1, w0, 1), r3)
    else if shape = 14 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickSigned257ish r2
      ((x0, -1, w0, -1), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0, 0, 1), r3)
  let numer := x * y + w
  let kind :=
    if z = 0 then
      "divzero"
    else
      let (q, r) := divModRound numer z 1
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else
        "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV w, intV z], rng3)

def suite : InstrSuite where
  id := muladddivmodcId
  unit := #[
    { name := "unit/ok/ceil-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (3, 4, 5, 2, 9, -1),
            (3, -4, 5, 2, -3, -1),
            (-3, 4, 5, 2, -3, -1),
            (-3, -4, 5, 2, 9, -1),
            (7, 1, 0, 3, 3, -2),
            (7, 1, 0, -3, -2, 1),
            (-7, -1, 0, 3, 3, -2),
            (-7, -1, 0, -3, -2, 1),
            (5, -7, 0, 3, -11, -2),
            (-5, 7, 0, -3, 12, 1),
            (0, 100, 5, 7, 1, -2),
            (8, 9, -72, 5, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let w := c.2.2.1
          let z := c.2.2.2.1
          let q := c.2.2.2.2.1
          let r := c.2.2.2.2.2
          expectOkStack s!"(({x}*{y})+{w})/{z}"
            (runMulAddDivModCDirect #[intV x, intV y, intV w, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/ok/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 1, maxInt257, 0),
            (minInt257, 1, 0, 1, minInt257, 0),
            (maxInt257, -1, 0, -1, maxInt257, 0),
            (minInt257 + 1, -1, 0, 1, maxInt257, 0),
            (maxInt257, 1, -1, 2, (pow2 255) - 1, 0),
            (minInt257, 1, 1, 2, 1 - (pow2 255), -1),
            (maxInt257, 0, -1, -2, 1, 1),
            (minInt257, 0, 1, -2, 0, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let w := c.2.2.1
          let z := c.2.2.2.1
          let q := c.2.2.2.2.1
          let r := c.2.2.2.2.2
          expectOkStack s!"(({x}*{y})+{w})/{z}"
            (runMulAddDivModCDirect #[intV x, intV y, intV w, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runMulAddDivModCDirect #[intV 7, intV 9, intV 2, intV 0]) .intOv
        expectErr "overflow/min-times-neg1"
          (runMulAddDivModCDirect #[intV minInt257, intV (-1), intV 0, intV 1]) .intOv
        expectErr "overflow/max-times-two"
          (runMulAddDivModCDirect #[intV maxInt257, intV 2, intV 0, intV 1]) .intOv
        expectErr "overflow/min-times-two"
          (runMulAddDivModCDirect #[intV minInt257, intV 2, intV 0, intV 1]) .intOv
        expectErr "overflow/max-plus-one-after-mul"
          (runMulAddDivModCDirect #[intV maxInt257, intV 1, intV 1, intV 1]) .intOv
        expectErr "overflow/min-minus-one-after-mul"
          (runMulAddDivModCDirect #[intV minInt257, intV 1, intV (-1), intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulAddDivModCDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runMulAddDivModCDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runMulAddDivModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/three-args" (runMulAddDivModCDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "error-order/underflow-before-type-with-three-items"
          (runMulAddDivModCDirect #[.null, .cell Cell.empty, .null]) .stkUnd
        expectErr "type/pop-z-first"
          (runMulAddDivModCDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "type/pop-w-second"
          (runMulAddDivModCDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "type/pop-y-third"
          (runMulAddDivModCDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "type/pop-x-fourth"
          (runMulAddDivModCDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "error-order/pop-z-before-w-when-both-non-int"
          (runMulAddDivModCDirect #[intV 1, intV 2, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-w-before-y-when-z-int"
          (runMulAddDivModCDirect #[intV 1, .null, .cell Cell.empty, intV 3]) .typeChk
        expectErr "error-order/pop-y-before-x-when-zw-int"
          (runMulAddDivModCDirect #[.null, .cell Cell.empty, intV 2, intV 3]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulAddDivModCDispatchFallback #[]) #[intV 5050] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-pos-div-pos" #[intV 3, intV 4, intV 5, intV 2],
    mkCase "ok/ceil/sign/pos-neg-pos-div-pos" #[intV 3, intV (-4), intV 5, intV 2],
    mkCase "ok/ceil/sign/neg-pos-pos-div-pos" #[intV (-3), intV 4, intV 5, intV 2],
    mkCase "ok/ceil/sign/neg-neg-pos-div-pos" #[intV (-3), intV (-4), intV 5, intV 2],
    mkCase "ok/ceil/sign/pos-pos-div-neg" #[intV 7, intV 1, intV 0, intV (-3)],
    mkCase "ok/ceil/sign/neg-neg-div-neg" #[intV (-7), intV (-1), intV 0, intV (-3)],
    mkCase "ok/ceil/addend/negative-total" #[intV 5, intV (-7), intV 0, intV 3],
    mkCase "ok/ceil/addend/negative-total-neg-divisor" #[intV (-5), intV 7, intV 0, intV (-3)],
    mkCase "ok/exact/positive" #[intV 8, intV 9, intV (-72), intV 5],
    mkCase "ok/exact/negative" #[intV (-8), intV 9, intV 72, intV 5],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 100, intV 0, intV 7],
    mkCase "ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 0, intV 1],
    mkCase "ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 0, intV 1],
    mkCase "ok/boundary/max-times-neg-one-div-neg-one" #[intV maxInt257, intV (-1), intV 0, intV (-1)],
    mkCase "ok/boundary/min-plus-one-times-neg-one-div-one" #[intV (minInt257 + 1), intV (-1), intV 0, intV 1],
    mkCase "ok/boundary/max-minus-one-over-two" #[intV maxInt257, intV 1, intV (-1), intV 2],
    mkCase "ok/boundary/min-plus-one-over-two" #[intV minInt257, intV 1, intV 1, intV 2],
    mkCase "ok/boundary/w-only-div-neg-two" #[intV maxInt257, intV 0, intV (-1), intV (-2)],
    mkCase "ok/boundary/w-only-min-div-neg-two" #[intV minInt257, intV 0, intV 1, intV (-2)],
    mkCase "overflow/min-times-neg-one" #[intV minInt257, intV (-1), intV 0, intV 1],
    mkCase "overflow/max-times-two" #[intV maxInt257, intV 2, intV 0, intV 1],
    mkCase "overflow/min-times-two" #[intV minInt257, intV 2, intV 0, intV 1],
    mkCase "overflow/max-plus-one-after-mul" #[intV maxInt257, intV 1, intV 1, intV 1],
    mkCase "overflow/min-minus-one-after-mul" #[intV minInt257, intV 1, intV (-1), intV 1],
    mkCase "divzero/nonzero-over-zero" #[intV 7, intV 9, intV 2, intV 0],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 0],
    mkCase "nan/z-via-program" #[intV 11, intV 13, intV 17] #[.pushInt .nan, muladddivmodcInstr],
    mkCase "nan/w-via-program" #[intV 11, intV 13, intV 17] #[.pushInt .nan, .xchg0 1, muladddivmodcInstr],
    mkCase "nan/y-via-program" #[intV 11, intV 13, intV 17] #[.pushInt .nan, .xchg0 2, muladddivmodcInstr],
    mkCase "nan/x-via-program" #[intV 11, intV 13, intV 17] #[.pushInt .nan, .xchg0 3, muladddivmodcInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "error-order/underflow-before-type-with-three-items" #[.null, .cell Cell.empty, .null],
    mkCase "type/pop-z-first" #[intV 1, intV 2, intV 3, .null],
    mkCase "type/pop-w-second" #[intV 1, intV 2, .null, intV 3],
    mkCase "type/pop-y-third" #[intV 1, .null, intV 2, intV 3],
    mkCase "type/pop-x-fourth" #[.null, intV 1, intV 2, intV 3],
    mkCase "error-order/pop-z-before-w-when-both-non-int" #[intV 1, intV 2, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-y-when-z-int" #[intV 1, .null, .cell Cell.empty, intV 3],
    mkCase "error-order/pop-y-before-x-when-zw-int" #[.null, .cell Cell.empty, intV 2, intV 3],
    mkCase "gas/exact-cost-succeeds" #[intV 3, intV 4, intV 5, intV 2]
      #[.pushInt (.num muladddivmodcSetGasExact), .tonEnvOp .setGasLimit, muladddivmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 3, intV 4, intV 5, intV 2]
      #[.pushInt (.num muladddivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, muladddivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020809
      count := 700
      gen := genMulAddDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDDIVMODC
