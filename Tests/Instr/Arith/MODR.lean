import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODR

/-
MODR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, roundMode = 0 rules)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest-round adjustment logic)

Branch/terminal counts used for this suite:
- Lean (`execInstrArithDivMod` generic): 6 branch sites / 14 terminal outcomes
  (dispatch arm; addMode pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with 4 outcomes; non-num fallback split).
- C++ (`exec_divmod` generic): 4 branch sites / 10 terminal outcomes
  (add-remap gate; invalid-opcode guard; underflow guard; add vs non-add + `d` switch).
- C++ nearest rounding (`mod_div_any`, `round_mode = 0`): 2 sign-dependent
  adjustment subpaths with tie boundary checks.

MODR specialization:
- opcode args4 = `0x9` in the `0xa90` family;
- fixed parameters are `d=2`, `roundMode=0` (nearest, ties to +∞),
  `addMode=false`, `quiet=false`.

Key risk areas covered:
- nearest tie-breaking for all sign combinations (`±1 / ±2`, odd/even edges);
- remainder sign/magnitude behavior under nearest rounding;
- division-by-zero / NaN funnels in non-quiet mode (`intOv`);
- pop/error ordering (`y` is popped and type-checked before `x`);
- `minInt257 / -1` for MODR must not overflow (remainder is zero);
- exact gas threshold (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def modrId : InstrId := { name := "MODR" }

private def modrInstr : Instr := .divMod 2 0 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := modrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runModrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod modrInstr stack

private def runModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 606)) stack

private def modrSetGasExact : Int :=
  computeExactGasBudget modrInstr

private def modrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def nearestNumeratorPool : Array Int :=
  #[-9, -8, -7, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 7, 8, 9]

private def nearestDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def tiePairPool : Array (Int × Int) :=
  #[(1, 2), (-1, 2), (1, -2), (-1, -2), (5, 2), (-5, 2), (5, -2), (-5, -2)]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickTiePair (rng : StdGen) : (Int × Int) × StdGen :=
  let (idx, rng') := randNat rng 0 (tiePairPool.size - 1)
  (tiePairPool[idx]!, rng')

private def genModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
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
      let ((x0, y0), r2) := pickTiePair rng1
      ((x0, y0), r2)
    else if shape = 4 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool nearestDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 5 then
      let (x0, r2) := pickFromPool nearestNumeratorPool rng1
      let (y0, r3) := pickFromPool nearestDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 6 then
      let (y0, r2) := pickNonZeroInt rng1
      ((0, y0), r2)
    else if shape = 7 then
      let (useMax, r2) := randBool rng1
      let x0 := if useMax then maxInt257 else minInt257
      let (y0, r3) := pickFromPool nearestDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 8 then
      ((minInt257, -1), rng1)
    else if shape = 9 then
      let (x0, r2) := pickSigned257ish rng1
      let (usePos, r3) := randBool r2
      ((x0, if usePos then 2 else -2), r3)
    else
      ((maxInt257, 1), rng1)
  let kind :=
    if y = 0 then
      "divzero"
    else if x = minInt257 && y = -1 then
      "boundary-min-neg1"
    else if x % y = 0 then
      "exact"
    else
      "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := modrId
  unit := #[
    { name := "unit/nearest/sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 1),
            (8, 3, -1),
            (-7, 3, -1),
            (-8, 3, 1),
            (7, -3, 1),
            (8, -3, -1),
            (-7, -3, -1),
            (-8, -3, 1),
            (1, 2, -1),
            (-1, 2, -1),
            (1, -2, 1),
            (-1, -2, 1),
            (5, 2, -1),
            (-5, 2, -1),
            (5, -2, 1),
            (-5, -2, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%{y}" (runModrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/nearest/boundary-and-no-overflow-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, 0),
            (maxInt257, -1, 0),
            (minInt257, 1, 0),
            (minInt257, -1, 0),
            (maxInt257, 2, -1),
            (minInt257, 2, 0),
            (minInt257, -2, 0),
            (minInt257 + 1, 2, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%{y}" (runModrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error/divzero-pop-order-and-type-ordering"
      run := do
        expectErr "divzero/nonzero-over-zero" (runModrDirect #[intV 5, intV 0]) .intOv
        expectErr "underflow/empty" (runModrDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runModrDirect #[intV 1]) .stkUnd
        expectErr "error-order/single-non-int-underflow-first" (runModrDirect #[.null]) .stkUnd
        expectErr "type/y-pop-first" (runModrDirect #[intV 1, .null]) .typeChk
        expectErr "type/x-pop-second" (runModrDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-y-first" (runModrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runModrDispatchFallback #[]) #[intV 606] }
  ]
  oracle := #[
    mkCase "ok/sign/pos-pos-inexact-low" #[intV 7, intV 3],
    mkCase "ok/sign/pos-pos-inexact-high" #[intV 8, intV 3],
    mkCase "ok/sign/neg-pos-inexact-low" #[intV (-7), intV 3],
    mkCase "ok/sign/neg-pos-inexact-high" #[intV (-8), intV 3],
    mkCase "ok/sign/pos-neg-inexact-low" #[intV 7, intV (-3)],
    mkCase "ok/sign/pos-neg-inexact-high" #[intV 8, intV (-3)],
    mkCase "ok/sign/neg-neg-inexact-low" #[intV (-7), intV (-3)],
    mkCase "ok/sign/neg-neg-inexact-high" #[intV (-8), intV (-3)],
    mkCase "ok/tie/pos-over-pos-half" #[intV 1, intV 2],
    mkCase "ok/tie/neg-over-pos-half" #[intV (-1), intV 2],
    mkCase "ok/tie/pos-over-neg-half" #[intV 1, intV (-2)],
    mkCase "ok/tie/neg-over-neg-half" #[intV (-1), intV (-2)],
    mkCase "ok/exact/multiple-pos-pos" #[intV 42, intV 7],
    mkCase "ok/exact/multiple-neg-pos" #[intV (-42), intV 7],
    mkCase "ok/exact/multiple-pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 5],
    mkCase "ok/boundary/max-mod-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-mod-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-mod-one" #[intV minInt257, intV 1],
    mkCase "overflow/min-div-neg-one-no-overflow" #[intV minInt257, intV (-1)],
    mkCase "ok/boundary/max-mod-two-tie" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/min-mod-two-even" #[intV minInt257, intV 2],
    mkCase "ok/boundary/min-mod-neg-two-even" #[intV minInt257, intV (-2)],
    mkCase "ok/boundary/min-plus-one-mod-two-tie" #[intV (minInt257 + 1), intV 2],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "nan/y-via-program" #[intV 5] #[.pushInt .nan, modrInstr],
    mkCase "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, modrInstr],
    mkCase "overflow/both-operands-nan-via-program" #[] #[.pushInt .nan, .pushInt .nan, modrInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num modrSetGasExact), .tonEnvOp .setGasLimit, modrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num modrSetGasExactMinusOne), .tonEnvOp .setGasLimit, modrInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 700
      gen := genModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODR
