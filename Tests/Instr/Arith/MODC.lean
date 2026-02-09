import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODC

/-
MODC branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp` (`exec_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_int`, `Stack::push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean: 6 branch sites / 14 terminal outcomes
  (dispatch arm; `addMode` pop split; operand-shape split; divisor-zero split;
   round-mode validation split; `d` switch with 4 arms; non-num `d=3` split).
- C++: 4 branch sites / 10 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; stack underflow guard;
   add-vs-non-add execution path with `d` switch arms).

MODC specialization:
- opcode args4 = `0xA` under `0xa90` family;
- fixed parameters are `d=2`, `roundMode=1` (ceil), `addMode=false`, `quiet=false`.

Key risk areas covered:
- ceil-mod remainder sign behavior across all sign combinations;
- division-by-zero and NaN funnels in non-quiet mode (`intOv`);
- pop order / error ordering (`y` is popped before `x`);
- signed 257-bit boundary behavior (especially `minInt257`, `maxInt257`);
- exact gas and exact-minus-one gas boundaries via `SETGASLIMIT`.
-/

private def modcId : InstrId := { name := "MODC" }

private def modcInstr : Instr := .divMod 2 1 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := modcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runModcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod modcInstr stack

private def runModcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 808)) stack

private def modcSetGasExact : Int :=
  computeExactGasBudget modcInstr

private def modcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def modcNumeratorPool : Array Int :=
  #[-9, -7, -5, -1, 0, 1, 5, 7, 9]

private def modcDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genModcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
      let (x0, r2) := pickFromPool modcNumeratorPool rng1
      let (y0, r3) := pickFromPool modcDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 4 then
      ((maxInt257, 2), rng1)
    else if shape = 5 then
      ((maxInt257, -2), rng1)
    else if shape = 6 then
      ((minInt257, -1), rng1)
    else if shape = 7 then
      ((minInt257 + 1, 2), rng1)
    else if shape = 8 then
      ((minInt257 + 1, -2), rng1)
    else if shape = 9 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool modcDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 10 then
      let (x0, r2) := pickFromPool modcNumeratorPool rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else
      ((0, -1), rng1)
  let kind :=
    if y = 0 then
      "divzero"
    else if x = minInt257 && y = -1 then
      "boundary-min-neg1"
    else
      "nonzero"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := modcId
  unit := #[
    { name := "unit/ceil-mod/sign-combos-and-near-zero-fractions"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, -2),
            (-7, 3, -1),
            (7, -3, 1),
            (-7, -3, 2),
            (-1, 2, -1),
            (1, -2, 1),
            (5, 2, -1),
            (-5, 2, -1),
            (5, -2, 1),
            (-5, -2, 1),
            (42, 7, 0),
            (-42, 7, 0),
            (42, -7, 0),
            (-42, -7, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%{y}" (runModcDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/ceil-mod/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, 0),
            (maxInt257, -1, 0),
            (minInt257, 1, 0),
            (minInt257, -1, 0),
            (maxInt257, 2, -1),
            (maxInt257, -2, 1),
            (minInt257 + 1, 2, -1),
            (minInt257 + 1, -2, 1),
            (0, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%{y}" (runModcDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error/divzero-and-pop-ordering"
      run := do
        expectErr "div-by-zero" (runModcDirect #[intV 5, intV 0]) .intOv
        expectErr "empty" (runModcDirect #[]) .stkUnd
        expectErr "missing-x-after-y-pop" (runModcDirect #[intV 1]) .stkUnd
        expectErr "single-value-underflow-before-type" (runModcDirect #[.null]) .stkUnd
        expectErr "y-non-int-top" (runModcDirect #[intV 1, .null]) .typeChk
        expectErr "x-non-int-second" (runModcDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-pop-first" (runModcDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runModcDispatchFallback #[]) #[intV 808] }
  ]
  oracle := #[
    mkCase "ok/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ok/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ok/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ok/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ok/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "ok/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "ok/sign/pos-pos-half" #[intV 5, intV 2],
    mkCase "ok/sign/neg-pos-half" #[intV (-5), intV 2],
    mkCase "ok/sign/pos-neg-half" #[intV 5, intV (-2)],
    mkCase "ok/sign/neg-neg-half" #[intV (-5), intV (-2)],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV (-5)],
    mkCase "ok/boundary/max-mod-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-mod-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-mod-one" #[intV minInt257, intV 1],
    mkCase "ok/boundary/min-mod-neg-one" #[intV minInt257, intV (-1)],
    mkCase "ok/boundary/max-mod-two" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/max-mod-neg-two" #[intV maxInt257, intV (-2)],
    mkCase "ok/boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 2],
    mkCase "ok/boundary/min-plus-one-mod-neg-two" #[intV (minInt257 + 1), intV (-2)],
    mkCase "overflow/divzero-intov" #[intV 5, intV 0],
    mkCase "overflow/nan-y-via-program" #[intV 5] #[.pushInt .nan, modcInstr],
    mkCase "overflow/nan-x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, modcInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "error-order/single-value-underflow-before-type" #[.null],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num modcSetGasExact), .tonEnvOp .setGasLimit, modcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num modcSetGasExactMinusOne), .tonEnvOp .setGasLimit, modcInstr]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 700
      gen := genModcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODC
