import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTMODC

/-
QLSHIFTMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 2 1 false true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, pop/type ordering)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, ceil-mode remainder behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, quiet runtime-shift arm, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (QLSHIFTMODC specialization):
- Lean generic `.shlDivMod`: ~8 branch sites / ~16 terminal outcomes.
- Lean QLSHIFTMODC reachable specialization: ~8 branch sites / ~10 outcomes
  (dispatch/fallback; arity precheck; shift pop type; y pop type; x pop type;
   quiet range funnel; div-by-zero funnel; numeric success push; NaN-operand funnel).
- C++ `exec_shldivmod` (quiet runtime-shift): ~7 branch sites / ~12 aligned outcomes
  (opcode guard; underflow gate; runtime shift range gate; pop/type path;
   validity/range quiet funnel; `d` switch; quiet push terminal).

Key risk areas covered:
- ceil remainder sign behavior across mixed signs and near-zero numerators;
- runtime shift boundaries (`0`, `1`, `255`, `256`) and quiet range funnels;
- strict pop/error ordering (`shift → divisor → x`, with quiet range not masking type);
- quiet NaN funnels (NaN `x`/`y`/`shift`, divisor zero);
- oracle serialization hygiene (NaN/out-of-range injected via `PUSHINT` prelude only);
- deterministic gas boundary (`computeExactGasBudget` exact vs minus-one).
-/

private def qlshiftmodcId : InstrId := { name := "QLSHIFTMODC" }

private def qlshiftmodcInstr : Instr :=
  .arithExt (.shlDivMod 2 1 false true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qlshiftmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQlshiftmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftmodcInstr stack

private def runQlshiftmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4519)) stack

private def qlshiftmodcSetGasExact : Int :=
  computeExactGasBudget qlshiftmodcInstr

private def qlshiftmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftmodcInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300, 511]

private def smallDivisorPool : Array Int :=
  #[-17, -9, -7, -5, -3, -2, -1, 1, 2, 3, 5, 7, 9, 17]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickFromPool shiftBoundaryPool rng1
  else
    let (n, rng2) := randNat rng1 0 256
    (Int.ofNat n, rng2)

private def pickNonZeroSigned257ish (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQlshiftmodc (x y shift : Int) : String :=
  if shift < 0 || shift > 256 then
    "quiet-range-shift"
  else if y = 0 then
    "quiet-divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat
    let (_, r) := divModRound tmp y 1
    if r = 0 then
      "exact"
    else if x = maxInt257 || x = minInt257 then
      "boundary"
    else
      "inexact"

private def genQlshiftmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (yRaw, r3) := pickInt257Boundary r2
      let y := if yRaw = 0 then 1 else yRaw
      let (shift, r4) := pickFromPool shiftBoundaryPool r3
      let kind := classifyQlshiftmodc x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-all" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickFromPool shiftBoundaryPool r3
      let kind := classifyQlshiftmodc x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-boundary-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let kind := classifyQlshiftmodc x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-random-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let kind := classifyQlshiftmodc x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-all" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickFromPool smallDivisorPool r2
      let (shift, r4) := pickFromPool shiftBoundaryPool r3
      let kind := classifyQlshiftmodc x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/small-divisor-pool" #[intV x, intV y, intV shift], r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let kind := classifyQlshiftmodc x y 0
      (mkCase s!"fuzz/shape-{shape}/{kind}/shift0-rewrite" #[intV x, intV y, intV 0], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let kind := classifyQlshiftmodc x y 256
      (mkCase s!"fuzz/shape-{shape}/{kind}/shift256-boundary" #[intV x, intV y, intV 256], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCase s!"fuzz/shape-{shape}/quiet-divzero" #[intV x, intV 0, intV shift], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (badShift0, r4) := pickFromPool shiftInvalidPool r3
      let badShift := if badShift0 < 0 then badShift0 else -1
      (mkCase s!"fuzz/shape-{shape}/quiet-range-shift/negative" #[intV x, intV y, intV badShift], r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (badShift0, r4) := pickFromPool shiftInvalidPool r3
      let badShift := if badShift0 > 256 then badShift0 else 257
      (mkCase s!"fuzz/shape-{shape}/quiet-range-shift/over-256" #[intV x, intV y, intV badShift], r4)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-before-type" #[.null], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-top-non-int" #[intV x, intV y, shiftLike], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"fuzz/shape-{shape}/type/y-second-non-int" #[intV x, yLike, intV shift], r4)
    else if shape = 16 then
      let (xLike, r2) := pickNonInt rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"fuzz/shape-{shape}/type/x-third-non-int" #[xLike, intV y, intV shift], r4)
    else if shape = 17 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-shift-first"
        #[xLike, yLike, shiftLike], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (badShift0, r3) := pickFromPool shiftInvalidPool r2
      let badShift := if badShift0 > 256 then badShift0 else 257
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/quiet-range-does-not-mask-y-type"
        #[intV x, yLike, intV badShift], r4)
    else if shape = 19 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (badShift0, r3) := pickFromPool shiftInvalidPool r2
      let badShift := if badShift0 < 0 then badShift0 else -1
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/quiet-range-does-not-mask-x-type"
        #[xLike, intV y, intV badShift], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-shift-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 22 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 23 then
      let (shift, r2) := pickValidShift rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program"
        #[IntVal.nan, IntVal.nan, IntVal.num shift], r2)
    else if shape = 24 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num shift], r4)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num shift], r4)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shiftOut], r4)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        #[IntVal.num xOut, IntVal.num yOut, IntVal.num shiftOut], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftmodcId
  unit := #[
    { name := "unit/ceil-remainder/sign-and-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, -1),
            (-7, 3, 1, -2),
            (7, -3, 1, 2),
            (-7, -3, 1, 1),
            (1, 3, 1, -1),
            (-1, 3, 1, -2),
            (1, -3, 1, 2),
            (-1, -3, 1, 1),
            (5, 7, 2, -1),
            (-5, 7, 2, -6),
            (5, -7, 2, 6),
            (-5, -7, 2, 1),
            (6, 3, 1, 0),
            (37, 5, 0, -3),
            (-37, 5, 0, -2),
            (0, 5, 200, 0),
            (maxInt257, 1, 256, 0),
            (minInt257, 1, 256, 0),
            (maxInt257, 7, 256, -5),
            (maxInt257, -7, 256, 2),
            (minInt257, 7, 256, -4),
            (minInt257, -7, 256, 3),
            (minInt257 + 1, 7, 256, -2),
            (minInt257 + 1, -7, 256, 5)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"x={x}/y={y}/shift={shift}"
            (runQlshiftmodcDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/pop-order/top-three-consumed-below-preserved"
      run := do
        expectOkStack "below-null"
          (runQlshiftmodcDirect #[.null, intV 7, intV 3, intV 1]) #[.null, intV (-1)]
        expectOkStack "below-cell"
          (runQlshiftmodcDirect #[.cell Cell.empty, intV (-5), intV 7, intV 2])
          #[.cell Cell.empty, intV (-6)] }
    ,
    { name := "unit/quiet/nan-divzero-and-shift-range-funnels"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQlshiftmodcDirect #[intV 5, intV 0, intV 3]) #[.int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQlshiftmodcDirect #[intV 0, intV 0, intV 3]) #[.int .nan]
        expectOkStack "quiet/shift-negative"
          (runQlshiftmodcDirect #[intV 5, intV 7, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/shift-over-256"
          (runQlshiftmodcDirect #[intV 5, intV 7, intV 257]) #[.int .nan]
        expectOkStack "quiet/shift-nan"
          (runQlshiftmodcDirect #[intV 5, intV 7, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan-y"
          (runQlshiftmodcDirect #[intV 5, .int .nan, intV 3]) #[.int .nan]
        expectOkStack "quiet/nan-x"
          (runQlshiftmodcDirect #[.int .nan, intV 5, intV 3]) #[.int .nan]
        expectOkStack "quiet/nan-both"
          (runQlshiftmodcDirect #[.int .nan, .int .nan, intV 3]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-quiet-range-precedence"
      run := do
        expectErr "underflow/empty" (runQlshiftmodcDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runQlshiftmodcDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runQlshiftmodcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type"
          (runQlshiftmodcDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runQlshiftmodcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/shift-top-cell"
          (runQlshiftmodcDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "type/y-second-null" (runQlshiftmodcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/x-third-null" (runQlshiftmodcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/shift-type-before-y-type"
          (runQlshiftmodcDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/quiet-range-does-not-mask-y-type"
          (runQlshiftmodcDirect #[intV 5, .null, intV 257]) .typeChk
        expectErr "error-order/quiet-range-does-not-mask-x-type"
          (runQlshiftmodcDirect #[.null, intV 7, intV (-1)]) .typeChk
        expectErr "error-order/both-non-int-shift-first"
          (runQlshiftmodcDirect #[.null, .cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qlshiftmodc-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQlshiftmodcDispatchFallback #[]) #[intV 4519] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-shift1" #[intV 7, intV 3, intV 1],
    mkCase "ok/ceil/sign/neg-pos-shift1" #[intV (-7), intV 3, intV 1],
    mkCase "ok/ceil/sign/pos-neg-shift1" #[intV 7, intV (-3), intV 1],
    mkCase "ok/ceil/sign/neg-neg-shift1" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/ceil/sign/near-zero-pos-divisor" #[intV 1, intV 3, intV 1],
    mkCase "ok/ceil/sign/near-zero-neg-divisor" #[intV 1, intV (-3), intV 1],
    mkCase "ok/ceil/sign/near-zero-neg-numerator-pos-divisor" #[intV (-1), intV 3, intV 1],
    mkCase "ok/ceil/sign/near-zero-neg-numerator-neg-divisor" #[intV (-1), intV (-3), intV 1],
    mkCase "ok/exact/divisible-shift1" #[intV 6, intV 3, intV 1],
    mkCase "ok/exact/shift-zero-positive" #[intV 37, intV 5, intV 0],
    mkCase "ok/exact/zero-numerator-large-shift" #[intV 0, intV 5, intV 200],
    mkCase "ok/boundary/max-shift256-div1" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-shift256-div1" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/max-shift256-div7" #[intV maxInt257, intV 7, intV 256],
    mkCase "ok/boundary/max-shift256-div-neg7" #[intV maxInt257, intV (-7), intV 256],
    mkCase "ok/boundary/min-shift256-div7" #[intV minInt257, intV 7, intV 256],
    mkCase "ok/boundary/min-shift256-div-neg7" #[intV minInt257, intV (-7), intV 256],
    mkCase "ok/boundary/min-plus-one-shift256-div7" #[intV (minInt257 + 1), intV 7, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256-div-neg7" #[intV (minInt257 + 1), intV (-7), intV 256],
    mkCase "ok/order/below-null-preserved" #[.null, intV 7, intV 3, intV 1],
    mkCase "ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-5), intV 7, intV 2],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0, intV 3],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 3],
    mkCase "quiet/shift-negative" #[intV 5, intV 7, intV (-1)],
    mkCase "quiet/shift-over-256" #[intV 5, intV 7, intV 257],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "type/shift-top-null" #[intV 1, intV 2, .null],
    mkCase "type/shift-top-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/y-second-null" #[intV 1, .null, intV 2],
    mkCase "type/x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/both-non-int-shift-first" #[.null, .cell Cell.empty, .null],
    mkCase "error-order/quiet-range-does-not-mask-y-type" #[intV 5, .null, intV 257],
    mkCase "error-order/quiet-range-does-not-mask-x-type" #[.null, intV 7, intV (-1)],
    mkCaseFromIntVals "quiet/nan-shift-via-program"
      #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "quiet/nan-y-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 3],
    mkCaseFromIntVals "quiet/nan-x-via-program"
      #[IntVal.nan, IntVal.num 7, IntVal.num 3],
    mkCaseFromIntVals "quiet/nan-both-via-program"
      #[IntVal.nan, IntVal.nan, IntVal.num 3],
    mkCase "error-order/shift-nan-does-not-mask-y-type-via-program"
      #[intV 5, .null] #[.pushInt .nan, qlshiftmodcInstr],
    mkCase "error-order/shift-nan-does-not-mask-x-type-via-program"
      #[.null, intV 7] #[.pushInt .nan, qlshiftmodcInstr],
    mkCaseFromIntVals "error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 7, IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 7, IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-y-low-before-op"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-high-before-op"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-low-before-op"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-both-before-op"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (maxInt257 + 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftmodcSetGasExact), .tonEnvOp .setGasLimit, qlshiftmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020849
      count := 700
      gen := genQlshiftmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTMODC
