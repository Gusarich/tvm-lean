import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QRSHIFTMODR

/-
QRSHIFTMODR branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 3 0 true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popNatUpTo 256`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, nearest ties toward `+∞`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`, quiet `0xb7a92c..0xb7a92e`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`, `AnyIntView::mod_pow2_any`)

Branch counts used for this suite (QRSHIFTMODR specialization):
- Lean: ~8 branch sites / ~14 terminal outcomes
  (dispatch/fallback; depth precheck; shift pop type/range/ok; x-pop type/ok;
   shift=0 round-mode rewrite; numeric-vs-NaN x split; fixed `d=3` two-result push;
   quiet `pushIntQuiet` finite-vs-NaN terminals).
- C++: ~7 branch sites / ~13 aligned terminal outcomes
  (`check_underflow(2)`; `pop_smallint_range(256)` type/range split;
   `pop_int` x check; `y==0` round rewrite; `d` switch to `RSHIFTMOD`;
   two quiet pushes for q/r with NaN funnel).

Key risk areas covered:
- nearest rounding (`R`) ties must go toward `+∞` and preserve q/r invariant signs;
- runtime shift `0` must force floor-mode semantics before computing q/r;
- strict pop/error order (depth underflow first, then shift, then x);
- quiet NaN behavior (`x=NaN` yields two NaNs), while shift NaN/out-of-range remains `rangeChk`;
- boundary shifts (`0`, `256`) across `±2^256` edges;
- oracle serialization safety: NaN/out-of-range values injected via program only;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qrshiftmodrId : InstrId := { name := "QRSHIFTMODR" }

private def qrshiftmodrInstr : Instr :=
  .arithExt (.shrMod false false 3 0 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qrshiftmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qrshiftmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qrshiftmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQRshiftmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qrshiftmodrInstr stack

private def runQRshiftmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 939)) stack

private def expectQRshiftmodr
    (label : String)
    (x : Int)
    (shift : Nat)
    (q : Int)
    (r : Int) : IO Unit :=
  expectOkStack label (runQRshiftmodrDirect #[intV x, intV (Int.ofNat shift)]) #[intV q, intV r]

private def qrshiftmodrSetGasExact : Int :=
  computeExactGasBudget qrshiftmodrInstr

private def qrshiftmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qrshiftmodrInstr

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieShift1Pool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieShift2Pool : Array Int :=
  #[-14, -10, -6, -2, 2, 6, 10, 14]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftUniform rng1

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQRshiftmodr (x : Int) (shift : Nat) : String :=
  if shift = 0 then
    "shift0"
  else
    let p := pow2 shift
    let rem := Int.emod x p
    if rem = pow2 (shift - 1) then
      "tie"
    else if rem = 0 then
      "exact"
    else if x = maxInt257 || x = minInt257 then
      "boundary"
    else
      "inexact"

private def genQRshiftmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyQRshiftmodr x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyQRshiftmodr x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let kind := classifyQRshiftmodr x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftUniform r2
      let kind := classifyQRshiftmodr x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieShift1Pool rng1
      (mkCase s!"fuzz/shape-{shape}/tie/shift1" #[intV x, intV 1], r2)
    else if shape = 5 then
      let (x, r2) := pickFromPool tieShift2Pool rng1
      (mkCase s!"fuzz/shape-{shape}/tie/shift2" #[intV x, intV 2], r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftMixed rng1
      let kind := classifyQRshiftmodr 0 shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-x"
        #[intV 0, intV (Int.ofNat shift)], r2)
    else if shape = 7 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyQRshiftmodr x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/extreme-x"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/shift0/round-rewrite" #[intV x, intV 0], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/shift256/edge" #[intV x, intV 256], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-before-type" #[.null], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/shift-pop-first" #[intV x, nonInt], r3)
    else if shape = 14 then
      let (shift, r2) := pickShiftMixed rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/x-pop-second"
        #[nonInt, intV (Int.ofNat shift)], r3)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-shift-first" #[xLike, shiftLike], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative"
        #[intV x, intV (-1)], r2)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range/shift-over256"
        #[intV x, intV 257], r2)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/shift-nan-via-program" #[.num x, .nan], r2)
    else if shape = 19 then
      let (shift, r2) := pickShiftMixed rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num (Int.ofNat shift)], r2)
    else if shape = 20 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-shift0-via-program" #[.nan, .num 0], rng1)
    else if shape = 21 then
      let (huge, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-before-op"
        #[.num huge, .num (Int.ofNat shift)], r3)
    else if shape = 22 then
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-via-program"
        #[.null] #[.pushInt (.num (-1)), qrshiftmodrInstr], rng1)
    else if shape = 23 then
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num (-1)), qrshiftmodrInstr], rng1)
    else
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-over256-via-program"
        #[.null] #[.pushInt (.num 257), qrshiftmodrInstr], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qrshiftmodrId
  unit := #[
    { name := "unit/round/nearest-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Nat × (Int × Int)) :=
          #[
            (7, 1, (4, -1)),
            (-7, 1, (-3, -1)),
            (1, 1, (1, -1)),
            (-1, 1, (0, -1)),
            (3, 1, (2, -1)),
            (-3, 1, (-1, -1)),
            (9, 2, (2, 1)),
            (-9, 2, (-2, -1)),
            (7, 2, (2, -1)),
            (-7, 2, (-2, 1)),
            (6, 2, (2, -2)),
            (-6, 2, (-1, -2)),
            (5, 3, (1, -3)),
            (-5, 3, (-1, 3))
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectQRshiftmodr s!"{x}>>#{shift}" x shift q r }
    ,
    { name := "unit/boundary/shift0-shift256-and-extremes"
      run := do
        let checks : Array (Int × Nat × (Int × Int)) :=
          #[
            (maxInt257, 0, (maxInt257, 0)),
            (minInt257, 0, (minInt257, 0)),
            (maxInt257, 1, (pow2 255, -1)),
            (minInt257, 1, (-(pow2 255), 0)),
            (maxInt257, 256, (1, -1)),
            (maxInt257 - 1, 256, (1, -2)),
            (minInt257, 256, (-1, 0)),
            (minInt257 + 1, 256, (-1, 1)),
            (pow2 255, 256, (1, -(pow2 255))),
            (-(pow2 255), 256, (0, -(pow2 255)))
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectQRshiftmodr s!"boundary/{x}>>#{shift}" x shift q r }
    ,
    { name := "unit/quiet/nan-funnel-and-range-strictness"
      run := do
        expectOkStack "quiet/nan-x-shift1"
          (runQRshiftmodrDirect #[.int .nan, intV 1]) #[intV 0, .int .nan]
        expectOkStack "quiet/nan-x-shift0"
          (runQRshiftmodrDirect #[.int .nan, intV 0]) #[.int .nan, .int .nan]
        expectErr "range/shift-negative" (runQRshiftmodrDirect #[intV 5, intV (-1)]) .rangeChk
        expectErr "range/shift-over256" (runQRshiftmodrDirect #[intV 5, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runQRshiftmodrDirect #[intV 5, .int .nan]) .rangeChk
        expectErr "error-order/range-before-x-type-nan-shift"
          (runQRshiftmodrDirect #[.null, .int .nan]) .rangeChk
        expectErr "error-order/range-before-x-type-negative-shift"
          (runQRshiftmodrDirect #[.null, intV (-1)]) .rangeChk }
    ,
    { name := "unit/error-order/underflow-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runQRshiftmodrDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQRshiftmodrDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQRshiftmodrDirect #[.null]) .stkUnd
        expectErr "type/shift-pop-first-null" (runQRshiftmodrDirect #[intV 1, .null]) .typeChk
        expectErr "type/shift-pop-first-cell" (runQRshiftmodrDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/x-pop-second-null" (runQRshiftmodrDirect #[.null, intV 1]) .typeChk
        expectErr "type/x-pop-second-cell" (runQRshiftmodrDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-shift-first"
          (runQRshiftmodrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQRshiftmodrDispatchFallback #[]) #[intV 939] }
  ]
  oracle := #[
    mkCase "ok/shift0/zero" #[intV 0, intV 0],
    mkCase "ok/shift0/positive" #[intV 17, intV 0],
    mkCase "ok/shift0/negative" #[intV (-17), intV 0],
    mkCase "ok/round/tie-pos-shift1" #[intV 1, intV 1],
    mkCase "ok/round/tie-neg-shift1" #[intV (-1), intV 1],
    mkCase "ok/round/three-over-two-shift1" #[intV 3, intV 1],
    mkCase "ok/round/neg-three-over-two-shift1" #[intV (-3), intV 1],
    mkCase "ok/round/non-tie-pos-shift2" #[intV 9, intV 2],
    mkCase "ok/round/non-tie-neg-shift2" #[intV (-9), intV 2],
    mkCase "ok/round/high-rem-pos-shift2" #[intV 7, intV 2],
    mkCase "ok/round/high-rem-neg-shift2" #[intV (-7), intV 2],
    mkCase "ok/round/tie-pos-shift2" #[intV 6, intV 2],
    mkCase "ok/round/tie-neg-shift2" #[intV (-6), intV 2],
    mkCase "ok/round/non-tie-pos-shift3" #[intV 5, intV 3],
    mkCase "ok/round/non-tie-neg-shift3" #[intV (-5), intV 3],
    mkCase "ok/exact/divisible-pos" #[intV 1024, intV 5],
    mkCase "ok/exact/divisible-neg" #[intV (-1024), intV 5],
    mkCase "boundary/max-shift0" #[intV maxInt257, intV 0],
    mkCase "boundary/min-shift0" #[intV minInt257, intV 0],
    mkCase "boundary/max-shift1-tie" #[intV maxInt257, intV 1],
    mkCase "boundary/min-shift1-exact" #[intV minInt257, intV 1],
    mkCase "boundary/max-shift256-tie" #[intV maxInt257, intV 256],
    mkCase "boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 256],
    mkCase "boundary/min-shift256-exact" #[intV minInt257, intV 256],
    mkCase "boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "boundary/pow255-shift256-tie" #[intV (pow2 255), intV 256],
    mkCase "boundary/negpow255-shift256-tie" #[intV (-(pow2 255)), intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "type/shift-pop-first-null" #[intV 1, .null],
    mkCase "type/shift-pop-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/x-pop-second-null" #[.null, intV 1],
    mkCase "type/x-pop-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative" #[intV 5, intV (-1)],
    mkCase "range/shift-over256" #[intV 5, intV 257],
    mkCase "error-order/range-before-x-type-negative" #[.null, intV (-1)],
    mkCase "error-order/range-before-x-type-over256" #[.null, intV 257],
    mkCaseFromIntVals "range/shift-nan-via-program" #[.num 5, .nan],
    mkCaseFromIntVals "quiet/nan-x-via-program-shift1" #[.nan, .num 1],
    mkCaseFromIntVals "quiet/nan-x-via-program-shift0" #[.nan, .num 0],
    mkCaseFromIntVals "error-order/pushint-range-high-before-op"
      #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-low-before-op"
      #[.num (minInt257 - 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-both-before-op"
      #[.num (pow2 257), .num (-(pow2 257))],
    mkCase "error-order/range-before-x-type-via-program" #[.null]
      #[.pushInt (.num (-1)), qrshiftmodrInstr],
    mkCase "error-order/underflow-before-range-via-program" #[]
      #[.pushInt (.num (-1)), qrshiftmodrInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qrshiftmodrSetGasExact), .tonEnvOp .setGasLimit, qrshiftmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qrshiftmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qrshiftmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020830
      count := 700
      gen := genQRshiftmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFTMODR
