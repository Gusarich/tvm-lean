import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDDIVMODC

/-
ADDDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `1` / ceil)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (0xa90 args4 decode to `.divMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `dump_divmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (generic `.divMod`): 6 branch sites / 14 terminal outcomes
  (dispatch arm; add-mode pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with non-num `d=3` split).
- C++ (`exec_divmod`): 4 branch sites / 10 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add vs non-add execution split with `d` handling).

ADDDIVMODC specialization:
- opcode args4=`0x2` under `0xa90`;
- fixed params: `d=3`, `roundMode=1` (ceil), `addMode=true`, `quiet=false`.

Key risk areas covered:
- ceil quotient/remainder sign behavior on mixed-sign inputs;
- add-mode pop order (`y`, then `w`, then `x`) and error ordering;
- non-quiet NaN/divzero funnels to `intOv` (NaN injected via program only);
- signed 257-bit overflow on quotient push near `minInt257`/`maxInt257`;
- deterministic gas boundary via exact / exact-minus-one `SETGASLIMIT`.
-/

private def adddivmodcId : InstrId := { name := "ADDDIVMODC" }

private def adddivmodcInstr : Instr := .divMod 3 1 true false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[adddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := adddivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAddDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod adddivmodcInstr stack

private def runAddDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 6060)) stack

private def adddivmodcSetGasExact : Int :=
  computeExactGasBudget adddivmodcInstr

private def adddivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne adddivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def ceilNumeratorPool : Array Int :=
  #[-9, -7, -5, -1, 0, 1, 5, 7, 9]

private def ceilDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def addendPool : Array Int :=
  #[-3, -2, -1, 0, 1, 2, 3]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genAddDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let ((x, w, y), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickSigned257ish r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickInt257Boundary r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickInt257Boundary r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      ((x0, w0, 0), r3)
    else if shape = 5 then
      let (x0, r2) := pickFromPool ceilNumeratorPool rng1
      let (w0, r3) := pickFromPool addendPool r2
      let (y0, r4) := pickFromPool ceilDenominatorPool r3
      ((x0, w0, y0), r4)
    else if shape = 6 then
      ((minInt257, 0, -1), rng1)
    else if shape = 7 then
      ((minInt257 + 1, 0, -1), rng1)
    else if shape = 8 then
      ((maxInt257, 0, 1), rng1)
    else if shape = 9 then
      ((maxInt257, 1, 1), rng1)
    else if shape = 10 then
      ((minInt257, -1, 1), rng1)
    else if shape = 11 then
      ((maxInt257, -1, 2), rng1)
    else if shape = 12 then
      let (w0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      ((0, w0, y0), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, 0, y0), r3)
  let numer := x + w
  let kind :=
    if y = 0 then
      "divzero"
    else
      let (q, r) := divModRound numer y 1
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else
        "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV w, intV y], rng3)

def suite : InstrSuite where
  id := adddivmodcId
  unit := #[
    { name := "unit/ok/ceil-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 1, 3, 3, -1),
            (-7, -1, 3, -2, -2),
            (7, 1, -3, -2, 2),
            (-7, -1, -3, 3, 1),
            (-1, 0, 2, 0, -1),
            (1, 0, -2, 0, 1),
            (5, -7, 3, 0, -2),
            (-5, 7, -3, 0, 2),
            (40, 2, 7, 6, 0),
            (-40, -2, 7, -6, 0),
            (4, 1, 2, 3, -1),
            (0, 0, 5, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let y := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}+{w})/{y}" (runAddDivModCDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/ok/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 1, maxInt257, 0),
            (minInt257, 0, 1, minInt257, 0),
            (minInt257 + 1, 0, -1, maxInt257, 0),
            (maxInt257, -1, 1, maxInt257 - 1, 0),
            (minInt257, 1, 2, 1 - (pow2 255), -1),
            (maxInt257, -1, 2, (pow2 255) - 1, 0),
            (maxInt257, 0, -2, 1 - (pow2 255), 1),
            (minInt257, 0, -2, pow2 255, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let y := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}+{w})/{y}" (runAddDivModCDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "divzero/nonzero-over-zero" (runAddDivModCDirect #[intV 5, intV 1, intV 0]) .intOv
        expectErr "overflow/min-plus-zero-div-neg-one"
          (runAddDivModCDirect #[intV minInt257, intV 0, intV (-1)]) .intOv
        expectErr "overflow/max-plus-one-div-one"
          (runAddDivModCDirect #[intV maxInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-minus-one-div-one"
          (runAddDivModCDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/max-plus-max-div-one"
          (runAddDivModCDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-plus-min-div-one"
          (runAddDivModCDirect #[intV minInt257, intV minInt257, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runAddDivModCDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runAddDivModCDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runAddDivModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type-with-two-items"
          (runAddDivModCDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-y-first" (runAddDivModCDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-w-second" (runAddDivModCDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runAddDivModCDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-y-before-w-when-both-non-int"
          (runAddDivModCDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-w-before-x-when-y-int"
          (runAddDivModCDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runAddDivModCDispatchFallback #[]) #[intV 6060] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 1, intV 3],
    mkCase "ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV (-1), intV 3],
    mkCase "ok/ceil/sign/pos-neg-inexact" #[intV 7, intV 1, intV (-3)],
    mkCase "ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-1), intV (-3)],
    mkCase "ok/ceil/sign/neg-near-zero" #[intV (-1), intV 0, intV 2],
    mkCase "ok/ceil/sign/pos-neg-near-zero" #[intV 1, intV 0, intV (-2)],
    mkCase "ok/ceil/addend/negative-total" #[intV 5, intV (-7), intV 3],
    mkCase "ok/ceil/addend/positive-total-neg-div" #[intV (-5), intV 7, intV (-3)],
    mkCase "ok/exact/pos" #[intV 40, intV 2, intV 7],
    mkCase "ok/exact/neg" #[intV (-40), intV (-2), intV 7],
    mkCase "ok/exact/zero-total" #[intV 5, intV (-5), intV 3],
    mkCase "ok/boundary/max-plus-zero-div-one" #[intV maxInt257, intV 0, intV 1],
    mkCase "ok/boundary/min-plus-zero-div-one" #[intV minInt257, intV 0, intV 1],
    mkCase "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV 0, intV (-1)],
    mkCase "ok/boundary/max-minus-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/boundary/min-plus-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-minus-one-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "ok/boundary/max-div-neg-two" #[intV maxInt257, intV 0, intV (-2)],
    mkCase "ok/boundary/min-div-neg-two" #[intV minInt257, intV 0, intV (-2)],
    mkCase "overflow/min-plus-zero-div-neg-one" #[intV minInt257, intV 0, intV (-1)],
    mkCase "overflow/max-plus-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "overflow/min-minus-one-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "overflow/max-plus-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "overflow/min-plus-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 1, intV 0],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 0],
    mkCase "nan/y-via-program" #[intV 5, intV 7] #[.pushInt .nan, adddivmodcInstr],
    mkCase "nan/w-via-program" #[intV 5, intV 7] #[.pushInt .nan, .xchg0 1, adddivmodcInstr],
    mkCase "nan/x-via-program" #[intV 5, intV 7] #[.pushInt .nan, .xchg0 2, adddivmodcInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "type/pop-y-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-w-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "error-order/pop-y-before-w-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-x-when-y-int" #[.null, .cell Cell.empty, intV 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num adddivmodcSetGasExact), .tonEnvOp .setGasLimit, adddivmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num adddivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, adddivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020808
      count := 700
      gen := genAddDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDDIVMODC
