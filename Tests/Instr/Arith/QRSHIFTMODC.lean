import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QRSHIFTMODC

/-
QRSHIFTMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 3 1 true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popNatUpTo 256`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, ceil mode + `shift=0` rewrite to floor)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, quiet runtime-shift arm, `y==0` round rewrite)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`, `AnyIntView::mod_pow2_any`)

Branch counts used for this suite (QRSHIFTMODC specialization):
- Lean: ~8 branch sites / ~14 terminal outcomes
  (dispatch/fallback; explicit arity precheck; shift pop type/range/ok;
   x-pop type/ok; runtime `shift=0` floor rewrite; numeric-vs-NaN split;
   fixed `d=3` two-result quiet push path).
- C++: ~7 branch sites / ~13 aligned terminal outcomes
  (`check_underflow(2)`; `pop_smallint_range(256)` type/range split;
   `pop_int` x type gate; `y==0` floor rewrite; `d` switch to `RSHIFTMOD`;
   two `push_int_quiet` result terminals).

Key risk areas covered:
- ceil quotient/remainder semantics for mixed signs, plus `shift=0` floor rewrite;
- shift boundary handling (`0`, `1`, `255`, `256`) and strict range errors in quiet mode;
- pop/error ordering (underflow before type on short stacks; shift failures before x pop);
- quiet NaN behavior (`x=NaN` pushes NaN pair), with shift-NaN staying `rangeChk`;
- oracle serialization hygiene (NaN/out-of-range injected via program prelude only);
- exact gas boundary (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qrshiftmodcId : InstrId := { name := "QRSHIFTMODC" }

private def qrshiftmodcInstr : Instr :=
  .arithExt (.shrMod false false 3 1 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qrshiftmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qrshiftmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x shift : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, shift]
  mkCase name (below ++ stack) (progPrefix.push qrshiftmodcInstr) gasLimits fuel

private def runQrshiftmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qrshiftmodcInstr stack

private def runQrshiftmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 940)) stack

private def qrshiftmodcSetGasExact : Int :=
  computeExactGasBudget qrshiftmodcInstr

private def qrshiftmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qrshiftmodcInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-3, -1, 257, 258, 300, 511]

private def smallSignPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -1, 0, 1, 5, 7, 9, 13, 17, 33]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQrshiftmodc (x : Int) (shift : Nat) : String :=
  if shift = 0 then
    "shift0"
  else
    let (_, r) := divModRound x (pow2 shift) 1
    if r = 0 then
      "exact"
    else if x = maxInt257 || x = minInt257 then
      "boundary"
    else
      "inexact"

private def genQrshiftmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 25
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyQrshiftmodc x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyQrshiftmodc x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftMixed r2
      let kind := classifyQrshiftmodc x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let kind := classifyQrshiftmodc x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool smallSignPool rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyQrshiftmodc x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/small-sign-pool"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/shift0/floor-rewrite"
        #[intV x, intV 0], r2)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/boundary/shift256-edge"
        #[intV x, intV 256], r2)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-before-type" #[.null], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/shift-pop-first" #[intV x, shiftLike], r3)
    else if shape = 11 then
      let (shift, r2) := pickShiftMixed rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/x-pop-second"
        #[xLike, intV (Int.ofNat shift)], r3)
    else if shape = 12 then
      let (xLike, r2) := pickNonInt rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-shift-first" #[xLike, shiftLike], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative"
        #[intV x, intV (-1)], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range/shift-over256"
        #[intV x, intV 257], r2)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-negative"
        #[xLike, intV (-1)], r2)
    else if shape = 16 then
      let (xLike, r2) := pickNonInt rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-over256"
        #[xLike, intV 257], r2)
    else if shape = 17 then
      let (shift, r2) := pickShiftMixed rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        .nan (.num (Int.ofNat shift)), r2)
    else if shape = 18 then
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-x-shift0-via-program"
        .nan (.num 0), rng1)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/range/shift-nan-via-program"
        (.num x) .nan, r2)
    else if shape = 20 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num (Int.ofNat shift)), r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftOut, r3) := pickInt257OutOfRange r2
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        (.num x) (.num shiftOut), r3)
    else if shape = 22 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shiftOut, r3) := pickInt257OutOfRange r2
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        (.num xOut) (.num shiftOut), r3)
    else if shape = 23 then
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num 257), qrshiftmodcInstr], rng1)
    else if shape = 24 then
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-via-program"
        #[.null] #[.pushInt (.num 257), qrshiftmodcInstr], rng1)
    else
      let (x, r2) := pickSigned257ish rng1
      let (badShift, r3) := pickFromPool shiftInvalidPool r2
      let badShift := if badShift < 0 then badShift else 257
      (mkCase s!"fuzz/shape-{shape}/range/shift-invalid-from-pool"
        #[intV x, intV badShift], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qrshiftmodcId
  unit := #[
    { name := "unit/round/ceil-quot-rem-sign-and-boundaries"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (13, 2, 4, -3),
            (-13, 2, -3, -1),
            (7, 3, 1, -1),
            (-7, 3, 0, -7),
            (1, 1, 1, -1),
            (-1, 1, 0, -1),
            (0, 200, 0, 0),
            (9, 0, 9, 0),
            (-9, 0, -9, 0),
            (maxInt257, 1, pow2 255, -1),
            (minInt257, 1, -(pow2 255), 0),
            (maxInt257, 256, 1, -1),
            (minInt257, 256, -1, 0),
            (minInt257 + 1, 256, 0, minInt257 + 1),
            (-1, 256, 0, -1),
            (1, 256, 1, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"x={x}/shift={shift}"
            (runQrshiftmodcDirect #[intV x, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/pop-order/top-consumed-below-preserved"
      run := do
        expectOkStack "below-null"
          (runQrshiftmodcDirect #[.null, intV 13, intV 2])
          #[.null, intV 4, intV (-3)]
        expectOkStack "below-cell"
          (runQrshiftmodcDirect #[.cell Cell.empty, intV (-13), intV 2])
          #[.cell Cell.empty, intV (-3), intV (-1)] }
    ,
    { name := "unit/quiet/nan-pair-and-shift-range-strictness"
      run := do
        expectOkStack "quiet/nan-x-shift5"
          (runQrshiftmodcDirect #[.int .nan, intV 5]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan-x-shift0"
          (runQrshiftmodcDirect #[.int .nan, intV 0]) #[.int .nan, .int .nan]
        expectErr "range/shift-nan" (runQrshiftmodcDirect #[intV 5, .int .nan]) .rangeChk
        expectErr "error-order/shift-nan-before-x-type"
          (runQrshiftmodcDirect #[.null, .int .nan]) .rangeChk }
    ,
    { name := "unit/error-order/underflow-type-range-and-precedence"
      run := do
        expectErr "underflow/empty" (runQrshiftmodcDirect #[]) .stkUnd
        expectErr "underflow/missing-x-after-shift-pop" (runQrshiftmodcDirect #[intV 3]) .stkUnd
        expectErr "underflow/one-non-int" (runQrshiftmodcDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runQrshiftmodcDirect #[intV 9, .null]) .typeChk
        expectErr "type/shift-top-cell" (runQrshiftmodcDirect #[intV 9, .cell Cell.empty]) .typeChk
        expectErr "type/x-second-null" (runQrshiftmodcDirect #[.null, intV 3]) .typeChk
        expectErr "range/shift-negative" (runQrshiftmodcDirect #[intV 9, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runQrshiftmodcDirect #[intV 9, intV 257]) .rangeChk
        expectErr "error-order/range-before-x-type-neg"
          (runQrshiftmodcDirect #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-over"
          (runQrshiftmodcDirect #[.cell Cell.empty, intV 257]) .rangeChk
        expectErr "error-order/type-on-shift-before-x"
          (runQrshiftmodcDirect #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/dispatch/non-qrshiftmodc-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQrshiftmodcDispatchFallback #[]) #[intV 940] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-shift2" #[intV 13, intV 2],
    mkCase "ok/ceil/sign/neg-shift2" #[intV (-13), intV 2],
    mkCase "ok/ceil/sign/pos-shift3" #[intV 7, intV 3],
    mkCase "ok/ceil/sign/neg-shift3" #[intV (-7), intV 3],
    mkCase "ok/ceil/sign/pos-near-zero-shift1" #[intV 1, intV 1],
    mkCase "ok/ceil/sign/neg-near-zero-shift1" #[intV (-1), intV 1],
    mkCase "ok/exact/zero-large-shift" #[intV 0, intV 200],
    mkCase "ok/shift0/rewrite-positive" #[intV 9, intV 0],
    mkCase "ok/shift0/rewrite-negative" #[intV (-9), intV 0],
    mkCase "ok/boundary/max-shift1" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/min-shift1" #[intV minInt257, intV 1],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/neg-one-shift256" #[intV (-1), intV 256],
    mkCase "ok/boundary/one-shift256" #[intV 1, intV 256],
    mkCase "ok/order/below-null-preserved" #[.null, intV 13, intV 2],
    mkCase "ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-13), intV 2],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 3],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "error-order/one-arg-push257-underflow-first" #[]
      #[.pushInt (.num 257), qrshiftmodcInstr],
    mkCase "error-order/one-arg-pushnan-underflow-first" #[]
      #[.pushInt .nan, qrshiftmodcInstr],
    mkCase "type/shift-top-null" #[intV 9, .null],
    mkCase "type/shift-top-cell" #[intV 9, .cell Cell.empty],
    mkCase "type/x-second-null" #[.null, intV 3],
    mkCase "type/x-second-cell" #[.cell Cell.empty, intV 3],
    mkCase "error-order/both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative" #[intV 9, intV (-1)],
    mkCase "range/shift-over-256" #[intV 9, intV 257],
    mkCase "error-order/range-before-x-type-neg" #[.null, intV (-1)],
    mkCase "error-order/range-before-x-type-over" #[.cell Cell.empty, intV 257],
    mkInputCase "quiet/nan-x-via-program" .nan (.num 5),
    mkInputCase "quiet/nan-x-via-program-shift0" .nan (.num 0),
    mkInputCase "quiet/nan-x-via-program-shift256" .nan (.num 256),
    mkInputCase "range/shift-nan-via-program" (.num 5) .nan,
    mkInputCase "error-order/shift-nan-before-x-type-via-program" .nan .nan,
    mkInputCase "error-order/pushint-overflow-x-high-before-op" (.num (maxInt257 + 1)) (.num 5),
    mkInputCase "error-order/pushint-overflow-x-low-before-op" (.num (minInt257 - 1)) (.num 5),
    mkInputCase "error-order/pushint-overflow-shift-high-before-op" (.num 5) (.num (maxInt257 + 1)),
    mkInputCase "error-order/pushint-overflow-shift-low-before-op" (.num 5) (.num (minInt257 - 1)),
    mkInputCase "error-order/pushint-overflow-both-before-op" (.num (pow2 257)) (.num (-(pow2 257))),
    mkCase "error-order/range-before-x-type-via-program" #[.null]
      #[.pushInt (.num 257), qrshiftmodcInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 13, intV 2]
      #[.pushInt (.num qrshiftmodcSetGasExact), .tonEnvOp .setGasLimit, qrshiftmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 13, intV 2]
      #[.pushInt (.num qrshiftmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qrshiftmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020838
      count := 700
      gen := genQrshiftmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFTMODC
