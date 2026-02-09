import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.DIVR

/-
DIVR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, `roundMode = 0` path)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `dump_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest-rounding adjustment)

Branch/terminal counts used for this suite:
- Lean (`execInstrArithDivMod`): 6 branch sites / 14 terminal outcomes
  (dispatch arm; `addMode` pop arity; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with 4 arms; non-num `d=3` split).
- Lean (`divModRound` for `roundMode=0`): 4 branch sites / 7 terminal outcomes
  (zero-divisor guard; mode dispatch chain; nearest-round increment predicate
   split by divisor sign).
- C++ (`exec_divmod` + `mod_div_any`): 6 branch sites / 14 aligned outcomes
  (opcode remap/guard; underflow arity check; `d` switch; nearest-round
   remainder-threshold adjustments including half-tie direction).

DIVR specialization:
- opcode family `0xa90` args4 = `0x5`
- fixed params: `d=1`, `roundMode=0` (nearest), `addMode=false`, `quiet=false`.

Key risk areas covered:
- nearest rounding behavior across sign combinations, especially half ties;
- tie direction (`±0.5` cases) and near-zero quotients;
- non-quiet NaN funnel (`intOv`) via program-injected `PUSHINT .nan`;
- overflow edge (`minInt257 / -1`);
- pop-order / error-ordering (`y` pops before `x`);
- exact gas boundary via `SETGASLIMIT` exact vs exact-minus-one budgets.
-/

private def divrId : InstrId := { name := "DIVR" }

private def divrInstr : Instr := .divMod 1 0 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[divrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := divrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDivrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod divrInstr stack

private def runDivrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 808)) stack

private def divrSetGasExact : Int :=
  computeExactGasBudget divrInstr

private def divrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne divrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def roundDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def tieOddPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genDivrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let ((x, y), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else if shape = 3 then
      let (x0, r2) := pickFromPool tieOddPool rng1
      ((x0, 2), r2)
    else if shape = 4 then
      let (x0, r2) := pickFromPool tieOddPool rng1
      ((x0, -2), r2)
    else if shape = 5 then
      ((minInt257, -1), rng1)
    else if shape = 6 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool roundDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 7 then
      let (x0, r2) := pickFromPool roundNumeratorPool rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 8 then
      let (y0, r2) := pickNonZeroInt rng1
      ((0, y0), r2)
    else if shape = 9 then
      ((maxInt257, 1), rng1)
    else if shape = 10 then
      ((maxInt257, -1), rng1)
    else
      ((minInt257, 1), rng1)
  let kind :=
    if y = 0 then
      "divzero"
    else if x = minInt257 && y = -1 then
      "overflow"
    else if shape = 3 || shape = 4 then
      "tie"
    else if decide (x % y = 0) then
      "exact"
    else
      "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := divrId
  unit := #[
    { name := "unit/round/sign-combos-and-half-ties"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 2),
            (-7, 3, -2),
            (7, -3, -2),
            (-7, -3, 2),
            (5, 2, 3),
            (-5, 2, -2),
            (5, -2, -2),
            (-5, -2, 3),
            (1, 2, 1),
            (-1, 2, 0),
            (1, -2, 0),
            (-1, -2, 1),
            (42, 7, 6),
            (-42, 7, -6),
            (42, -7, -6),
            (-42, -7, 6)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runDivrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/round/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257),
            (maxInt257, -1, -maxInt257),
            (minInt257, 1, minInt257),
            (minInt257 + 1, -1, maxInt257),
            (maxInt257, 2, pow2 255),
            (minInt257, 2, -(pow2 255)),
            (minInt257, -2, pow2 255),
            (0, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runDivrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "div-by-zero" (runDivrDirect #[intV 5, intV 0]) .intOv
        expectErr "overflow/min-div-neg1" (runDivrDirect #[intV minInt257, intV (-1)]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "empty" (runDivrDirect #[]) .stkUnd
        expectErr "missing-x-after-y-pop" (runDivrDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow-before-type" (runDivrDirect #[.null]) .stkUnd
        expectErr "y-non-int-top" (runDivrDirect #[intV 1, .null]) .typeChk
        expectErr "x-non-int-second" (runDivrDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-pop-first" (runDivrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runDivrDispatchFallback #[]) #[intV 808] }
  ]
  oracle := #[
    mkCase "ok/round/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ok/round/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ok/round/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ok/round/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ok/tie/pos-pos-half" #[intV 5, intV 2],
    mkCase "ok/tie/neg-pos-half" #[intV (-5), intV 2],
    mkCase "ok/tie/pos-neg-half" #[intV 5, intV (-2)],
    mkCase "ok/tie/neg-neg-half" #[intV (-5), intV (-2)],
    mkCase "ok/tie/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "ok/tie/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "ok/tie/neg-neg-near-zero" #[intV (-1), intV (-2)],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV (-5)],
    mkCase "ok/boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/boundary/max-div-two-half-up" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/min-div-two" #[intV minInt257, intV 2],
    mkCase "ok/boundary/min-div-neg-two" #[intV minInt257, intV (-2)],
    mkCase "overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "nan/y-via-program" #[intV 5] #[.pushInt .nan, divrInstr],
    mkCase "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, divrInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num divrSetGasExact), .tonEnvOp .setGasLimit, divrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num divrSetGasExactMinusOne), .tonEnvOp .setGasLimit, divrInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 700
      gen := genDivrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.DIVR
