import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QRSHIFTC

/-
QRSHIFTC branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false false 1 1 true none)` path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popNatUpTo 256`, `VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, quiet runtime-shift arm)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean QRSHIFTC specialization: 7 branch sites / 9 terminal outcomes
  (dispatch/fallback; underflow gate; shift pop type/range; `x` pop type;
   `shift==0` ceil override; numeric-vs-NaN split; quiet push-int finite-vs-NaN funnel).
- C++ `exec_shrmod` (quiet, runtime-shift): 7 branch sites / 9 aligned outcomes
  (invalid-op gate; explicit underflow guard; `pop_smallint_range(256)` checks;
   `y==0` round override; `pop_int` type gate; `rshift` finite-vs-NaN path;
   quiet `push_int_quiet` normalization).

Key risk areas covered:
- ceil right-shift behavior across sign combinations and tie-adjacent numerators;
- sign-extension boundaries near 257-bit edges (`min/max`, `±1`, high shifts);
- runtime shift-width boundaries (`0`, `1`, `255`, `256`) and strict range failures;
- quiet/error ordering: underflow before pop-type/range on short stacks; shift range
  before `x` type on full stacks; quiet NaN result paths (`shift=0` vs `shift>0`);
- program-injected NaN/out-of-range operands and exact gas boundary (`SETGASLIMIT`).
-/

private def qrshiftcId : InstrId := { name := "QRSHIFTC" }

private def qrshiftcInstr : Instr :=
  .arithExt (.shrMod false false 1 1 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qrshiftcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qrshiftcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qrshiftcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programTail) gasLimits fuel

private def runQrshiftcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qrshiftcInstr stack

private def runQrshiftcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4904)) stack

private def qrshiftcSetGasExact : Int :=
  computeExactGasBudget qrshiftcInstr

private def qrshiftcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qrshiftcInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOutOfRangePool : Array Int :=
  #[-7, -3, -1, 257, 258, 300, 511]

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftOutOfRangePool.size - 1)
  (shiftOutOfRangePool[idx]!, rng')

private def pickShiftUpTo256 (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (useCell, rng') := randBool rng
  ((if useCell then .cell Cell.empty else .null), rng')

private def genQrshiftcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-shift-boundary" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-shift-boundary" #[intV x, intV shift], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftUpTo256 r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-shift-uniform" #[intV x, intV shift], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUpTo256 r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-shift-uniform" #[intV x, intV shift], r3)
    else if shape = 4 then
      let (useMin, r2) := randBool rng1
      let x := if useMin then minInt257 else maxInt257
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-signext-extreme" #[intV x, intV shift], r3)
    else if shape = 5 then
      let (useNegOne, r2) := randBool rng1
      let x := if useNegOne then (-1) else 1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-signext-unit-values" #[intV x, intV shift], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-arg" #[intV x], r2)
    else if shape = 8 then
      let (xLike, r2) := pickNonInt rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-arg-non-int" #[xLike], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type-shift-top-non-int" #[intV x, shiftLike], r3)
    else if shape = 10 then
      let (xLike, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/type-x-second-non-int" #[xLike, intV shift], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftOutOfRange r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-out-of-range" #[intV x, intV shift], r3)
    else if shape = 12 then
      let (xLike, r2) := pickNonInt rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-x-type" #[xLike, intV 257], r2)
    else if shape = 13 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-x-shift0-via-program"
        #[IntVal.nan, IntVal.num 0], rng1)
    else if shape = 14 then
      let (shift, r2) := pickShiftBoundary rng1
      let shift' := if shift = 0 then 1 else shift
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-x-shift-pos-via-program"
        #[IntVal.nan, IntVal.num shift'], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-shift-nan-via-program"
        #[IntVal.num x, IntVal.nan], r2)
    else if shape = 16 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order-pushint-overflow-x-before-op"
        #[IntVal.num x, IntVal.num shift], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order-pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num (pow2 257)], r2)
    else
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-fallback-shape" #[intV x, intV shift], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qrshiftcId
  unit := #[
    { name := "unit/direct/ceil-rounding-sign-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 1, 4),
            (7, 2, 2),
            (15, 3, 2),
            (-7, 1, -3),
            (-7, 2, -1),
            (-15, 3, -1),
            (-1, 1, 0),
            (1, 1, 1)
          ]
        for c in checks do
          match c with
          | (x, shift, expected) =>
              expectOkStack s!"ceil/{x}/{shift}"
                (runQrshiftcDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/sign-extension-and-shift-width-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 0, maxInt257),
            (minInt257, 0, minInt257),
            (maxInt257, 255, 2),
            (minInt257, 255, -2),
            (maxInt257, 256, 1),
            (minInt257, 256, -1),
            (minInt257 + 1, 256, 0),
            (-1, 256, 0),
            (1, 256, 1),
            (0, 256, 0)
          ]
        for c in checks do
          match c with
          | (x, shift, expected) =>
              expectOkStack s!"boundary/{x}/{shift}"
                (runQrshiftcDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-result-cases"
      run := do
        expectOkStack "quiet/nan-shift0" (runQrshiftcDirect #[.int .nan, intV 0]) #[.int .nan]
        expectOkStack "quiet/nan-shift1" (runQrshiftcDirect #[.int .nan, intV 1]) #[intV 0]
        expectOkStack "quiet/nan-shift256" (runQrshiftcDirect #[.int .nan, intV 256]) #[intV 0] }
    ,
    { name := "unit/error-ordering/underflow-range-type-paths"
      run := do
        expectErr "underflow/empty" (runQrshiftcDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQrshiftcDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQrshiftcDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runQrshiftcDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second-null" (runQrshiftcDirect #[.null, intV 1]) .typeChk
        expectErr "range/shift-negative-before-x-type" (runQrshiftcDirect #[.null, intV (-1)]) .rangeChk
        expectErr "range/shift-257-before-x-type" (runQrshiftcDirect #[.null, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-qrshiftc-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQrshiftcDispatchFallback #[]) #[intV 4904] }
  ]
  oracle := #[
    mkCase "ok/ceil/pos-odd-shift1" #[intV 7, intV 1],
    mkCase "ok/ceil/pos-odd-shift2" #[intV 7, intV 2],
    mkCase "ok/ceil/neg-odd-shift1" #[intV (-7), intV 1],
    mkCase "ok/ceil/neg-odd-shift2" #[intV (-7), intV 2],
    mkCase "ok/ceil/neg-half-to-zero" #[intV (-1), intV 1],
    mkCase "ok/ceil/zero-shift-identity" #[intV 123, intV 0],
    mkCase "ok/ceil/zero-input-high-shift" #[intV 0, intV 200],
    mkCase "ok/signext/max-shift255" #[intV maxInt257, intV 255],
    mkCase "ok/signext/min-shift255" #[intV minInt257, intV 255],
    mkCase "ok/signext/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/signext/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/signext/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/signext/minus-one-shift256" #[intV (-1), intV 256],
    mkCase "ok/signext/one-shift256" #[intV 1, intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "error-order/one-arg-push257-underflow-first" #[]
      #[.pushInt (.num 257), qrshiftcInstr],
    mkCase "error-order/one-arg-pushnan-underflow-first" #[]
      #[.pushInt .nan, qrshiftcInstr],
    mkCase "type/shift-top-null" #[intV 5, .null],
    mkCase "type/x-second-null" #[.null, intV 1],
    mkCase "error-order/shift-range-before-x-type" #[.null]
      #[.pushInt (.num 257), qrshiftcInstr],
    mkCase "range/shift-negative-via-program" #[intV 5]
      #[.pushInt (.num (-1)), qrshiftcInstr],
    mkCase "range/shift-257-via-program" #[intV 5]
      #[.pushInt (.num 257), qrshiftcInstr],
    mkCaseFromIntVals "range/shift-nan-via-program"
      #[IntVal.num 5, IntVal.nan],
    mkCaseFromIntVals "quiet/nan-x-shift0-via-program"
      #[IntVal.nan, IntVal.num 0],
    mkCaseFromIntVals "quiet/nan-x-shift1-via-program"
      #[IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "quiet/nan-x-shift256-via-program"
      #[IntVal.nan, IntVal.num 256],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/x-high"
      #[IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/x-low"
      #[IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/shift-huge"
      #[IntVal.num 7, IntVal.num (pow2 257)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 1]
      #[.pushInt (.num qrshiftcSetGasExact), .tonEnvOp .setGasLimit, qrshiftcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 1]
      #[.pushInt (.num qrshiftcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qrshiftcInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 600
      gen := genQrshiftcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFTC
