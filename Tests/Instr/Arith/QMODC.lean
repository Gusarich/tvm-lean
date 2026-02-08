import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMODC

/-
QMODC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, quiet NaN/overflow handling)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean: 6 branch sites / 14 terminal outcomes in `execInstrArithDivMod`
  (dispatch arm; arity split; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with `d=3` non-num split).
- C++: 4 branch sites / 10 aligned outcomes in `exec_divmod`
  (opcode remap/guard; underflow guard; add-vs-non-add path; `d` switch).

QMODC specialization:
- opcode args4 = `0xA` under quiet `0xb7a90` DIV/MOD family;
- fixed params: `d=2`, `roundMode=1` (ceil), `addMode=false`, `quiet=true`.

Key risk areas covered:
- ceil-mod sign behavior across all sign combinations and near-zero fractions;
- quiet handling for div-by-zero / NaN / result-overflow to stack NaN (no throw);
- pop order and error ordering (`y` before `x`, underflow before type on short stacks);
- precise gas boundary with `PUSHINT n; SETGASLIMIT; QMODC`;
- oracle serialization hygiene: NaN/out-of-range inputs use program injection only.
-/

private def qmodcId : InstrId := { name := "QMODC" }

private def qmodcInstr : Instr := .divMod 2 1 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programTail) gasLimits fuel

private def runQmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qmodcInstr stack

private def runQmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 2910)) stack

private def qmodcSetGasExact : Int :=
  computeExactGasBudget qmodcInstr

private def qmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmodcInstr

private def ceilNumeratorPool : Array Int :=
  #[-11, -9, -7, -5, -1, 0, 1, 5, 7, 9, 11]

private def ceilDenominatorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def qmodcOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng0 : StdGen) : Value × StdGen :=
  let (isNull, rng1) := randBool rng0
  (if isNull then .null else .cell Cell.empty, rng1)

private def pickQmodcOutOfRange (rng : StdGen) : Int × StdGen :=
  pickFromPool qmodcOutOfRangePool rng

private def classifyQmodc (x y : Int) : String :=
  if y = 0 then
    "quiet/divzero"
  else
    let (_, r) := divModRound x y 1
    if !intFitsSigned257 r then
      "quiet/overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQmodc x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQmodc x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero-random" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickFromPool ceilNumeratorPool rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      let kind := classifyQmodc x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/sign-pools" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/boundary/max-mod-two" #[intV maxInt257, intV 2], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/boundary/max-mod-neg-two" #[intV maxInt257, intV (-2)], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/boundary/min-plus-one-mod-two"
        #[intV (minInt257 + 1), intV 2], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/boundary/min-plus-one-mod-neg-two"
        #[intV (minInt257 + 1), intV (-2)], rng1)
    else if shape = 8 then
      let (y, r2) := pickNonZeroInt rng1
      let kind := classifyQmodc 0 y
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-numerator" #[intV 0, intV y], r2)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-before-type" #[.null], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (top, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, top], r3)
    else if shape = 13 then
      let (y, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[xLike, intV y], r3)
    else if shape = 14 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[xLike, yLike], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program" #[.num x, .nan], r2)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program" #[.nan, .num y], r2)
    else if shape = 17 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program" #[.nan, .nan], rng1)
    else if shape = 18 then
      let (x, r2) := pickQmodcOutOfRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-x-before-qmodc"
        #[.num x, .num 7], r2)
    else if shape = 19 then
      let (y, r2) := pickQmodcOutOfRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-y-before-qmodc"
        #[.num 7, .num y], r2)
    else if shape = 20 then
      let (x, r2) := pickQmodcOutOfRange rng1
      let (y, r3) := pickQmodcOutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-both-before-qmodc"
        #[.num x, .num y], r3)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      let kind := classifyQmodc x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-denominator-pool" #[intV x, intV y], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmodcId
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
          expectOkStack s!"ok/{x}/{y}" (runQmodcDirect #[intV x, intV y]) #[intV expected] }
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
          expectOkStack s!"ok/{x}/{y}" (runQmodcDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/quiet/divzero-nan-and-overflow-push-nan"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero" (runQmodcDirect #[intV 5, intV 0]) #[.int .nan]
        expectOkStack "quiet/divzero/zero-over-zero" (runQmodcDirect #[intV 0, intV 0]) #[.int .nan]
        expectOkStack "quiet/nan/y" (runQmodcDirect #[intV 5, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan/x" (runQmodcDirect #[.int .nan, intV 5]) #[.int .nan]
        expectOkStack "quiet/overflow-remainder-out-of-range"
          (runQmodcDirect #[intV (maxInt257 + 1), intV (-(pow2 257))])
          #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQmodcDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQmodcDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQmodcDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQmodcDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQmodcDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQmodcDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmodcDispatchFallback #[]) #[intV 2910] }
  ]
  oracle := #[
    mkCase "ceil/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ceil/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ceil/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ceil/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "ceil/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "ceil/sign/pos-pos-half" #[intV 5, intV 2],
    mkCase "ceil/sign/neg-pos-half" #[intV (-5), intV 2],
    mkCase "ceil/sign/pos-neg-half" #[intV 5, intV (-2)],
    mkCase "ceil/sign/neg-neg-half" #[intV (-5), intV (-2)],
    mkCase "ceil/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ceil/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ceil/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ceil/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ceil/exact/zero-numerator" #[intV 0, intV (-5)],
    mkCase "boundary/max-mod-one" #[intV maxInt257, intV 1],
    mkCase "boundary/max-mod-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "boundary/min-mod-one" #[intV minInt257, intV 1],
    mkCase "boundary/min-mod-neg-one" #[intV minInt257, intV (-1)],
    mkCase "boundary/max-mod-two" #[intV maxInt257, intV 2],
    mkCase "boundary/max-mod-neg-two" #[intV maxInt257, intV (-2)],
    mkCase "boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 2],
    mkCase "boundary/min-plus-one-mod-neg-two" #[intV (minInt257 + 1), intV (-2)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[.num 5, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 5],
    mkCaseFromIntVals "quiet/nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-range-x-before-qmodc" #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-y-before-qmodc" #[.num 7, .num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-range-x-pow2-257-before-qmodc" #[.num (pow2 257), .num 1],
    mkCaseFromIntVals "error-order/pushint-range-y-neg-pow2-257-before-qmodc" #[.num 1, .num (-(pow2 257))],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/error-order-both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qmodcSetGasExact), .tonEnvOp .setGasLimit, qmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020844
      count := 700
      gen := genQmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMODC
