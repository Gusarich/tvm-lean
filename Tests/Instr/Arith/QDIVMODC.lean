import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QDIVMODC

/-
QDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, ceil mode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (24-bit QDIV/MOD decode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `dump_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal coverage target for this suite:
- Lean `.divMod` handler: 6 branch sites / 14 terminal outcomes
  (dispatch, add-mode arity split, operand numeric-vs-NaN split,
   divisor-zero split, round-mode validity split, `d` result-shape split).
- C++ `exec_divmod`: 4 branch sites / 10 terminal outcomes
  (opcode-arg validity guard, underflow guard, add-vs-non-add split, `d` switch).

QDIVMODC specialization:
- fixed parameters: `d=3`, `roundMode=1` (ceil), `addMode=false`, `quiet=true`;
- opcode args4=`0xe` under quiet `0xb7a90` family.

Key risk areas covered:
- ceil-specific quotient+remainder pairs for all sign combinations and near-zero fractions;
- quiet arithmetic behavior: div-by-zero / NaN / overflow become stack NaN values (no throw);
- error ordering: underflow before type on short stack, and pop order (`y` then `x`);
- deterministic gas boundary (`SETGASLIMIT` exact vs exact-minus-one);
- oracle serialization hygiene: NaN/out-of-range operands are program-injected only.
-/

private def qdivmodcId : InstrId := { name := "QDIVMODC" }

private def qdivmodcInstr : Instr := .divMod 3 1 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qdivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qdivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qdivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programSuffix) gasLimits fuel

private def runQDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qdivmodcInstr stack

private def runQDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 31337)) stack

private def qdivmodcSetGasExact : Int :=
  computeExactGasBudget qdivmodcInstr

private def qdivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qdivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng0 : StdGen) : Value × StdGen :=
  let (isNull, rng1) := randBool rng0
  (if isNull then .null else .cell Cell.empty, rng1)

private def ceilNumeratorPool : Array Int :=
  #[-11, -7, -5, -1, 0, 1, 5, 7, 11]

private def ceilDenominatorPool : Array Int :=
  #[-5, -3, -2, -1, 1, 2, 3, 5]

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1, pow2 257, -(pow2 257)]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  pickFromPool outOfRangeProgramPool rng

private def classifyQDivModC (x y : Int) : String :=
  if y = 0 then
    "divzero"
  else
    let (q, r) := divModRound x y 1
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if q = 0 then
      "near-zero"
    else
      "inexact"

private def genQDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQDivModC x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQDivModC x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickFromPool ceilNumeratorPool rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      let kind := classifyQDivModC x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/ceil-pool" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-min-div-negone" #[intV minInt257, intV (-1)], rng1)
    else if shape = 5 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      let kind := classifyQDivModC x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-denominator-pool" #[intV x, intV y], r3)
    else if shape = 6 then
      let (x, r2) := pickFromPool ceilNumeratorPool rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQDivModC x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/numerator-pool" #[intV x, intV y], r3)
    else if shape = 7 then
      let (y, r2) := pickNonZeroInt rng1
      let kind := classifyQDivModC 0 y
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-numerator" #[intV 0, intV y], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/exact/max-div-one" #[intV maxInt257, intV 1], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/exact/min-div-one" #[intV minInt257, intV 1], rng1)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-before-type" #[.null], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, nonInt], r3)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[nonInt, intV y], r3)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[xLike, yLike], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet-nan/y-via-program" #[.num x, .nan], r2)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet-nan/x-via-program" #[.nan, .num y], r2)
    else if shape = 18 then
      let (huge, r2) := pickOutOfRangeProgramInt rng1
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-range-x-before-qdivmodc" #[.num huge, .num 7], r2)
    else if shape = 19 then
      let (huge, r2) := pickOutOfRangeProgramInt rng1
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-range-y-before-qdivmodc" #[.num 7, .num huge], r2)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      let kind := classifyQDivModC x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-denominator-pool" #[intV x, intV y], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qdivmodcId
  unit := #[
    { name := "unit/ok/ceil-rounding-quotient-and-remainder-sign-cases"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 3, -2),
            (-7, 3, -2, -1),
            (7, -3, -2, 1),
            (-7, -3, 3, 2),
            (-1, 2, 0, -1),
            (1, -2, 0, 1),
            (-5, 2, -2, -1),
            (5, -2, -2, 1),
            (11, 5, 3, -4),
            (-11, 5, -2, -1),
            (11, -5, -2, 1),
            (-11, -5, 3, 4),
            (42, 7, 6, 0),
            (-42, 7, -6, 0),
            (42, -7, -6, 0),
            (-42, -7, 6, 0),
            (0, 5, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, q, r) =>
              expectOkStack s!"ceil/{x}/{y}"
                (runQDivModCDirect #[intV x, intV y])
                #[intV q, intV r] }
    ,
    { name := "unit/ok/boundary-and-quiet-overflow-shapes"
      run := do
        let checks : Array (Int × Int × Value × Value) :=
          #[
            (maxInt257, 1, intV maxInt257, intV 0),
            (maxInt257, -1, intV (-maxInt257), intV 0),
            (minInt257, 1, intV minInt257, intV 0),
            (minInt257 + 1, -1, intV maxInt257, intV 0),
            (maxInt257, 2, intV (pow2 255), intV (-1)),
            (minInt257, 2, intV (-(pow2 255)), intV 0),
            (minInt257, -2, intV (pow2 255), intV 0),
            (maxInt257, -2, intV (1 - (pow2 255)), intV 1),
            (minInt257, -1, .int .nan, intV 0)
          ]
        for c in checks do
          match c with
          | (x, y, q, r) =>
              expectOkStack s!"boundary/{x}/{y}"
                (runQDivModCDirect #[intV x, intV y])
                #[q, r] }
    ,
    { name := "unit/quiet/divzero-and-nan-produce-nan-pairs"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQDivModCDirect #[intV 5, intV 0])
          #[.int .nan, .int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQDivModCDirect #[intV 0, intV 0])
          #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/y"
          (runQDivModCDirect #[intV 5, .int .nan])
          #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/x"
          (runQDivModCDirect #[.int .nan, intV 5])
          #[.int .nan, .int .nan]
        expectOkStack "quiet/below-stack-preserved"
          (runQDivModCDirect #[.null, intV 7, intV 3])
          #[.null, intV 3, intV (-2)] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQDivModCDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQDivModCDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQDivModCDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQDivModCDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQDivModCDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQDivModCDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQDivModCDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQDivModCDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQDivModCDispatchFallback #[]) #[intV 31337] }
  ]
  oracle := #[
    mkCase "ok/ceil/inexact/pos-pos" #[intV 7, intV 3],
    mkCase "ok/ceil/inexact/neg-pos" #[intV (-7), intV 3],
    mkCase "ok/ceil/inexact/pos-neg" #[intV 7, intV (-3)],
    mkCase "ok/ceil/inexact/neg-neg" #[intV (-7), intV (-3)],
    mkCase "ok/ceil/near-zero/neg-pos" #[intV (-1), intV 2],
    mkCase "ok/ceil/near-zero/pos-neg" #[intV 1, intV (-2)],
    mkCase "ok/ceil/inexact/neg-pos-half" #[intV (-5), intV 2],
    mkCase "ok/ceil/inexact/pos-neg-half" #[intV 5, intV (-2)],
    mkCase "ok/ceil/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ok/ceil/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ok/ceil/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/ceil/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ok/ceil/exact/zero-numerator" #[intV 0, intV 5],
    mkCase "ok/boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/boundary/max-div-two" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/min-div-two" #[intV minInt257, intV 2],
    mkCase "ok/boundary/min-div-neg-two" #[intV minInt257, intV (-2)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0],
    mkCase "quiet/overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkInputCase "quiet-nan/y-via-program" #[.num 5, .nan],
    mkInputCase "quiet-nan/x-via-program" #[.nan, .num 5],
    mkInputCase "error-order/pushint-range-x-before-qdivmodc" #[.num (maxInt257 + 1), .num 7],
    mkInputCase "error-order/pushint-range-y-before-qdivmodc" #[.num 7, .num (minInt257 - 1)],
    mkInputCase "error-order/pushint-range-x-pow2-257-before-qdivmodc" #[.num (pow2 257), .num 1],
    mkInputCase "error-order/pushint-range-y-neg-pow2-257-before-qdivmodc" #[.num 1, .num (-(pow2 257))],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qdivmodcSetGasExact), .tonEnvOp .setGasLimit, qdivmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qdivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qdivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020827
      count := 700
      gen := genQDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QDIVMODC
