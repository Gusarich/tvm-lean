import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.DIVMODR

/-
DIVMODR branch map (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest-mode tie handling)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp` (`exec_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp` (`mod_div_any` round_mode=0 path)

Branch/terminal counts used for this suite:
- Lean `execInstrArithDivMod`: 6 branch sites / 14 terminal outcomes
  (dispatch arm; `addMode` pop split; operand-shape split; divisor-zero split;
   round-mode validation split; `d` switch; non-num `d=3` split).
- C++ `exec_divmod`: 4 branch sites / 10 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add split with `d` switch).

DIVMODR specialization:
- opcode args4 = `0xd` in `0xa90` family;
- fixed parameters are `d=3`, `roundMode=0` (nearest with tie-to-+∞),
  `addMode=false`, `quiet=false`.

Key risk areas covered:
- nearest rounding tie behavior across sign combinations (`±1/±2`, `±5/±2`);
- quotient/remainder pairing for non-floor mode;
- division-by-zero and NaN funnels in non-quiet mode (`intOv`);
- pop/type error ordering (`y` pops before `x`);
- signed 257-bit overflow edge (`minInt257 / -1`);
- exact gas threshold around `SETGASLIMIT`.
-/

private def divmodrId : InstrId := { name := "DIVMODR" }

private def divmodrInstr : Instr := .divMod 3 0 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[divmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := divmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDivmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod divmodrInstr stack

private def runDivmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 808)) stack

private def divmodrSetGasExact : Int :=
  computeExactGasBudget divmodrInstr

private def divmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne divmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def roundDenominatorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genDivmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
      let (x0, r2) := pickFromPool roundNumeratorPool rng1
      let (y0, r3) := pickFromPool roundDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 4 then
      ((minInt257, -1), rng1)
    else if shape = 5 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool roundDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 6 then
      let (x0, r2) := pickFromPool roundNumeratorPool rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 7 then
      let (x0, r2) := pickFromPool tieNumeratorPool rng1
      let (y0, r3) := pickFromPool tieDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 8 then
      let (y0, r2) := pickNonZeroInt rng1
      ((0, y0), r2)
    else if shape = 9 then
      ((maxInt257, 2), rng1)
    else if shape = 10 then
      ((minInt257, 2), rng1)
    else
      ((minInt257, -2), rng1)
  let rem := if y = 0 then 0 else x % y
  let isTie : Bool := y != 0 && (Int.natAbs rem) * 2 = Int.natAbs y
  let kind :=
    if y = 0 then
      "divzero"
    else if x = minInt257 && y = -1 then
      "overflow"
    else if rem = 0 then
      "exact"
    else if isTie then
      "tie"
    else
      "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := divmodrId
  unit := #[
    { name := "unit/nearest/sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 1),
            (-7, 3, -2, -1),
            (7, -3, -2, 1),
            (-7, -3, 2, -1),
            (5, 2, 3, -1),
            (-5, 2, -2, -1),
            (5, -2, -2, 1),
            (-5, -2, 3, 1),
            (1, 2, 1, -1),
            (-1, 2, 0, -1),
            (1, -2, 0, 1),
            (-1, -2, 1, 1),
            (42, 7, 6, 0),
            (-42, -7, 6, 0),
            (0, 5, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"{x}/{y}" (runDivmodrDirect #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/nearest/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257, 0),
            (maxInt257, -1, -maxInt257, 0),
            (minInt257, 1, minInt257, 0),
            (minInt257 + 1, -1, maxInt257, 0),
            (maxInt257, 2, pow2 255, -1),
            (minInt257, 2, -(pow2 255), 0),
            (minInt257, -2, pow2 255, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"{x}/{y}" (runDivmodrDirect #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "div-by-zero" (runDivmodrDirect #[intV 5, intV 0]) .intOv
        expectErr "overflow/min-div-neg1" (runDivmodrDirect #[intV minInt257, intV (-1)]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "empty" (runDivmodrDirect #[]) .stkUnd
        expectErr "missing-x-after-y-pop" (runDivmodrDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow-first" (runDivmodrDirect #[.null]) .stkUnd
        expectErr "y-non-int-top" (runDivmodrDirect #[intV 1, .null]) .typeChk
        expectErr "x-non-int-second" (runDivmodrDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-pop-first" (runDivmodrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runDivmodrDispatchFallback #[]) #[intV 808] }
  ]
  oracle := #[
    mkCase "ok/round/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ok/round/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ok/round/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ok/round/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ok/tie/pos-over-pos-two" #[intV 5, intV 2],
    mkCase "ok/tie/neg-over-pos-two" #[intV (-5), intV 2],
    mkCase "ok/tie/pos-over-neg-two" #[intV 5, intV (-2)],
    mkCase "ok/tie/neg-over-neg-two" #[intV (-5), intV (-2)],
    mkCase "ok/tie/neg-one-over-two" #[intV (-1), intV 2],
    mkCase "ok/tie/one-over-neg-two" #[intV 1, intV (-2)],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 5],
    mkCase "ok/boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/boundary/max-div-two-rounds-up" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/min-div-two-exact" #[intV minInt257, intV 2],
    mkCase "ok/boundary/min-div-neg-two-exact" #[intV minInt257, intV (-2)],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "error-order/single-non-int-underflow-first" #[.null],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "error-order/nan-y-via-program" #[intV 5] #[.pushInt .nan, divmodrInstr],
    mkCase "error-order/nan-x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, divmodrInstr],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num divmodrSetGasExact), .tonEnvOp .setGasLimit, divmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num divmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, divmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020806
      count := 700
      gen := genDivmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.DIVMODR
