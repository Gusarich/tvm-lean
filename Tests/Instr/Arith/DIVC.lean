import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.DIVC

/-
DIVC branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_divmod`, opcode mapping in `register_div_ops`).

Branch/terminal counts used for this suite:
- Lean: 6 branch sites / 14 terminal outcomes
  (dispatch arm; `addMode` pop split; operand-shape split; divisor-zero split;
   round-mode validation split; `d` switch with 4 arms; non-num `d=3` split).
- C++: 4 branch sites / 10 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; stack underflow guard;
   add vs non-add path with `d` switch arms).

DIVC specialization:
- opcode args4 = `0x6` under `0xa90` family;
- fixed parameters are `d=1`, `roundMode=1` (ceil), `addMode=false`, `quiet=false`.

Key risk areas covered:
- ceil rounding across sign combinations (including near-zero fractions);
- division-by-zero and NaN funnels in non-quiet mode (`intOv`);
- operand pop/error ordering (`y` before `x`);
- signed 257-bit boundary overflow (`minInt257 / -1`);
- exact gas vs exact-minus-one gas boundaries via `SETGASLIMIT`.
-/

private def divcId : InstrId := { name := "DIVC" }

private def divcInstr : Instr := .divMod 1 1 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[divcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := divcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDivcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod divcInstr stack

private def runDivcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 909)) stack

private def divcSetGasExact : Int :=
  computeExactGasBudget divcInstr

private def divcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne divcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def ceilNumeratorPool : Array Int :=
  #[-7, -5, -1, 0, 1, 5, 7]

private def ceilDenominatorPool : Array Int :=
  #[-3, -2, -1, 1, 2, 3]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genDivcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
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
      let (x0, r2) := pickFromPool ceilNumeratorPool rng1
      let (y0, r3) := pickFromPool ceilDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 4 then
      ((minInt257, -1), rng1)
    else if shape = 5 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool ceilDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 6 then
      let (x0, r2) := pickFromPool ceilNumeratorPool rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 7 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickFromPool ceilDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 8 then
      ((0, -1), rng1)
    else
      ((maxInt257, 1), rng1)
  let kind :=
    if y = 0 then
      "divzero"
    else if x = minInt257 && y = -1 then
      "overflow"
    else
      "nonzero"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := divcId
  unit := #[
    { name := "unit/ceil/sign-combos-and-near-zero-fractions"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 3),
            (-7, 3, -2),
            (7, -3, -2),
            (-7, -3, 3),
            (-1, 2, 0),
            (1, -2, 0),
            (5, 2, 3),
            (-5, 2, -2),
            (5, -2, -2),
            (-5, -2, 3),
            (42, 7, 6),
            (-42, 7, -6),
            (42, -7, -6),
            (-42, -7, 6)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runDivcDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/ceil/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257),
            (maxInt257, -1, -maxInt257),
            (minInt257, 1, minInt257),
            (minInt257 + 1, -1, maxInt257),
            (maxInt257, 2, pow2 255),
            (minInt257, 2, -(pow2 255)),
            (0, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runDivcDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error/divzero-nan-and-overflow-intov"
      run := do
        expectErr "div-by-zero" (runDivcDirect #[intV 5, intV 0]) .intOv
        expectErr "overflow/min-div-neg1" (runDivcDirect #[intV minInt257, intV (-1)]) .intOv
        expectErr "nan-as-y" (runDivcDirect #[intV 5, .int .nan]) .intOv
        expectErr "nan-as-x" (runDivcDirect #[.int .nan, intV 5]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "empty" (runDivcDirect #[]) .stkUnd
        expectErr "missing-x-after-y-pop" (runDivcDirect #[intV 1]) .stkUnd
        expectErr "single-value-underflow-before-type" (runDivcDirect #[.null]) .stkUnd
        expectErr "y-non-int-top" (runDivcDirect #[intV 1, .null]) .typeChk
        expectErr "x-non-int-second" (runDivcDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-pop-first" (runDivcDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runDivcDispatchFallback #[]) #[intV 909] }
  ]
  oracle := #[
    mkCase "ceil/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ceil/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ceil/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ceil/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "ceil/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "ceil/sign/pos-pos-half" #[intV 5, intV 2],
    mkCase "ceil/sign/neg-neg-half" #[intV (-5), intV (-2)],
    mkCase "ceil/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ceil/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ceil/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ceil/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ceil/exact/zero-numerator" #[intV 0, intV (-5)],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "nan/y-via-program" #[intV 5] #[.pushInt .nan, divcInstr],
    mkCase "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, divcInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "error-order/single-value-underflow-before-type" #[.null],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "boundary/max-div-two" #[intV maxInt257, intV 2],
    mkCase "boundary/min-div-two" #[intV minInt257, intV 2],
    mkCase "overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num divcSetGasExact), .tonEnvOp .setGasLimit, divcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num divcSetGasExactMinusOne), .tonEnvOp .setGasLimit, divcInstr]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 700
      gen := genDivcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.DIVC
