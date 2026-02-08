import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDDIVMODR

/-
ADDDIVMODR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `0` nearest/ties-to-+∞)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `dump_divmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (generic `.divMod`): 6 branch sites / 14 terminal outcomes
  (dispatch arm; add-mode pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with 4 arms and non-num `d=3` split).
- C++ (`exec_divmod`): 4 branch sites / 10 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add vs non-add execution split with `d` switch).

ADDDIVMODR specialization:
- opcode args4=`0x1` under `0xa90` family;
- fixed parameters: `d=3`, `roundMode=0` (nearest), `addMode=true`, `quiet=false`.

Key risk areas covered:
- nearest rounding with ties toward `+∞` for all sign combinations;
- add-mode pop order (`y`, then `w`, then `x`) and error ordering;
- non-quiet NaN/div-by-zero funnels to `intOv`;
- signed 257-bit overflow when `(x + w)` or quotient exceeds range;
- exact gas boundary via `SETGASLIMIT` fixed-point budget.
-/

private def adddivmodrId : InstrId := { name := "ADDDIVMODR" }

private def adddivmodrInstr : Instr := .divMod 3 0 true false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[adddivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := adddivmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAddDivModRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod adddivmodrInstr stack

private def runAddDivModRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 5150)) stack

private def adddivmodrSetGasExact : Int :=
  computeExactGasBudget adddivmodrInstr

private def adddivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne adddivmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def nearestNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def nearestDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genAddDivModRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let ((x, w, y), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickInt257Boundary r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      ((x0, w0, 0), r3)
    else if shape = 3 then
      let (t, r2) := pickFromPool nearestNumeratorPool rng1
      let (y0, r3) := pickFromPool nearestDenominatorPool r2
      ((t, 0, y0), r3)
    else if shape = 4 then
      let (x0, r2) := pickFromPool nearestNumeratorPool rng1
      let (y0, r3) := pickFromPool nearestDenominatorPool r2
      ((x0, 1, y0), r3)
    else if shape = 5 then
      ((maxInt257, 1, 1), rng1)
    else if shape = 6 then
      ((minInt257, -1, 1), rng1)
    else if shape = 7 then
      ((minInt257, 0, -1), rng1)
    else if shape = 8 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool nearestDenominatorPool r2
      ((x0, 0, y0), r3)
    else if shape = 9 then
      let (x0raw, r2) := pickSigned257ish rng1
      let x0 := if x0raw = minInt257 then minInt257 + 1 else x0raw
      let (y0, r3) := pickNonZeroInt r2
      ((x0, -x0, y0), r3)
    else if shape = 10 then
      let (w0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      ((0, w0, y0), r3)
    else if shape = 11 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      ((x0, w0, 1), r3)
    else if shape = 12 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      ((x0, w0, -1), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickInt257Boundary r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
  let numer : Int := x + w
  let kind :=
    if y = 0 then
      "divzero"
    else if numer > maxInt257 || numer < minInt257 then
      "overflow"
    else if numer = 0 then
      "zero"
    else
      "nonzero"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV w, intV y], rng3)

def suite : InstrSuite where
  id := adddivmodrId
  unit := #[
    { name := "unit/ok/nearest-rounding-signs-and-ties"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 3, 4, 0),
            (7, 4, 3, 4, -1),
            (7, 0, 3, 2, 1),
            (-7, 0, 3, -2, -1),
            (7, 0, -3, -2, 1),
            (-7, 0, -3, 2, -1),
            (5, 0, 2, 3, -1),
            (-5, 0, 2, -2, -1),
            (5, 0, -2, -2, 1),
            (-5, 0, -2, 3, 1),
            (-1, 0, 2, 0, -1),
            (1, 0, -2, 0, 1),
            (4, 1, 2, 3, -1)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let y := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}+{w})/{y}" (runAddDivModRDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 1, maxInt257, 0),
            (maxInt257, -1, 1, maxInt257 - 1, 0),
            (minInt257, 1, 1, minInt257 + 1, 0),
            (minInt257 + 1, 0, -1, maxInt257, 0),
            (maxInt257, 0, 2, pow2 255, -1),
            (minInt257, 0, 2, -(pow2 255), 0),
            (minInt257, 0, -2, pow2 255, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let y := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}+{w})/{y}" (runAddDivModRDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/overflow-divzero-nan/intov"
      run := do
        expectErr "divzero" (runAddDivModRDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "overflow/max-plus-one-over-one" (runAddDivModRDirect #[intV maxInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-minus-one-over-one" (runAddDivModRDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/min-over-negone" (runAddDivModRDirect #[intV minInt257, intV 0, intV (-1)]) .intOv
        expectErr "nan/y" (runAddDivModRDirect #[intV 5, intV 7, .int .nan]) .intOv
        expectErr "nan/w" (runAddDivModRDirect #[intV 5, .int .nan, intV 7]) .intOv
        expectErr "nan/x" (runAddDivModRDirect #[.int .nan, intV 7, intV 5]) .intOv }
    ,
    { name := "unit/type-underflow/error-order-and-pop-order"
      run := do
        expectErr "underflow/empty" (runAddDivModRDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runAddDivModRDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runAddDivModRDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type" (runAddDivModRDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-y-first" (runAddDivModRDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-w-second" (runAddDivModRDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runAddDivModRDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-y-before-w" (runAddDivModRDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/pop-w-before-x" (runAddDivModRDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runAddDivModRDispatchFallback #[]) #[intV 5150] }
  ]
  oracle := #[
    mkCase "ok/round/exact-pos-pos" #[intV 7, intV 5, intV 3],
    mkCase "ok/round/inexact-pos-pos" #[intV 7, intV 4, intV 3],
    mkCase "ok/round/inexact-neg-pos" #[intV (-7), intV 0, intV 3],
    mkCase "ok/round/inexact-pos-neg" #[intV 7, intV 0, intV (-3)],
    mkCase "ok/round/inexact-neg-neg" #[intV (-7), intV 0, intV (-3)],
    mkCase "ok/round/tie-pos-pos" #[intV 5, intV 0, intV 2],
    mkCase "ok/round/tie-neg-pos" #[intV (-5), intV 0, intV 2],
    mkCase "ok/round/tie-pos-neg" #[intV 5, intV 0, intV (-2)],
    mkCase "ok/round/tie-neg-neg" #[intV (-5), intV 0, intV (-2)],
    mkCase "ok/round/tie-near-zero-neg-pos" #[intV (-1), intV 0, intV 2],
    mkCase "ok/round/tie-near-zero-pos-neg" #[intV 1, intV 0, intV (-2)],
    mkCase "ok/round/addend-shifts-result" #[intV 4, intV 1, intV 2],
    mkCase "ok/boundary/max-plus-negone-over-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/boundary/min-plus-one-over-one" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/boundary/min-plus-one-over-negone" #[intV (minInt257 + 1), intV 0, intV (-1)],
    mkCase "ok/boundary/max-over-two-tie" #[intV maxInt257, intV 0, intV 2],
    mkCase "ok/boundary/min-over-two" #[intV minInt257, intV 0, intV 2],
    mkCase "ok/boundary/min-over-neg-two" #[intV minInt257, intV 0, intV (-2)],
    mkCase "overflow/numerator-max-plus-one-over-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "overflow/numerator-min-minus-one-over-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "overflow/min-over-negone" #[intV minInt257, intV 0, intV (-1)],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "type/pop-y-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-w-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/underflow-before-type" #[.null, .cell Cell.empty],
    mkCase "error-order/pop-y-before-w" #[intV 1, .null, .cell Cell.empty],
    mkCase "error-order/pop-w-before-x" #[.null, .cell Cell.empty, intV 1],
    mkCase "nan/y-via-program" #[intV 5, intV 7] #[.pushInt .nan, adddivmodrInstr],
    mkCase "nan/w-via-program" #[intV 5, intV 7] #[.pushInt .nan, .xchg0 1, adddivmodrInstr],
    mkCase "nan/x-via-program" #[intV 5, intV 7] #[.pushInt .nan, .xchg0 2, adddivmodrInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num adddivmodrSetGasExact), .tonEnvOp .setGasLimit, adddivmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num adddivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, adddivmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020806
      count := 700
      gen := genAddDivModRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDDIVMODR
