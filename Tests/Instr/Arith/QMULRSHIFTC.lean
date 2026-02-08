import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULRSHIFTC

/-
QMULRSHIFTC branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 1 1 true none)` specialization)
  - `TvmLean/Model/Basics/Bytes.lean` (`rshiftPow2Round`, ceil/floor by power-of-two)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb7a9a6` decode to `.shrMod true false 1 1 true none`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode wiring in `register_div_ops`)

Branch counts used for this suite:
- Lean QMULRSHIFTC specialization:
  9 branch sites / 14 terminal outcomes
  (dispatch/fallback; explicit arity gate; shift pop/type path; quiet range funnel;
   `y` then `x` pop/type sequence; numeric-vs-invalid operand split;
   shift-zero round override; `d` arm; quiet push-int finite-vs-NaN normalization).
- C++ `exec_mulshrmod` (quiet runtime-shift arm):
  8 branch sites / 13 aligned outcomes
  (opcode arg remap, arity gate, runtime-shift range gate in quiet mode,
   `pop_int` type sequence, validity funnel, `d` switch, rounding path,
   quiet `push_int_quiet` normalization).

Key risk areas covered:
- ceil rounding semantics across mixed signs and odd products, plus `shift=0` floor override;
- runtime shift boundaries (`0`, `1`, `255`, `256`) and quiet NaN for invalid shifts (`<0`, `>256`);
- strict pop/error ordering (`stkUnd` before any pops; then `z → y → x` type checks);
- invalid shift does not mask `y`/`x` type errors in quiet mul-shr flow;
- NaN/out-of-range operand injection only through `PUSHINT` program prelude helpers;
- exact gas boundary for `PUSHINT n; SETGASLIMIT; QMULRSHIFTC`.
-/

private def qmulrshiftcId : InstrId := { name := "QMULRSHIFTC" }

private def qmulrshiftcInstr : Instr :=
  .arithExt (.shrMod true false 1 1 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulrshiftcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmulrshiftcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulrshiftcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQmulrshiftcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulrshiftcInstr stack

private def runQmulrshiftcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 8312)) stack

private def qmulrshiftcSetGasExact : Int :=
  computeExactGasBudget qmulrshiftcInstr

private def qmulrshiftcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulrshiftcInstr

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

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def genQmulrshiftcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/ok-random-boundary-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUpTo256 r3
      (mkCase s!"/fuzz/shape-{shape}/ok-x-boundary-uniform-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftUpTo256 r3
      (mkCase s!"/fuzz/shape-{shape}/ok-y-boundary-uniform-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"/fuzz/shape-{shape}/ok-zero-left-factor" #[intV 0, intV y, intV shift], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"/fuzz/shape-{shape}/ok-zero-right-factor" #[intV x, intV 0, intV shift], r3)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow-min-negone-shift0"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow-max-max-shift255"
        #[intV maxInt257, intV maxInt257, intV 255], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow-one-arg" #[intV x], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow-two-args" #[intV x, intV y], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zLike, r4) := pickNonIntLike r3
      (mkCase s!"/fuzz/shape-{shape}/type-pop-shift-first" #[intV x, intV y, zLike], r4)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/type-pop-y-second" #[intV x, yLike, intV shift], r4)
    else if shape = 13 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/type-pop-x-third" #[xLike, intV y, intV shift], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftOutOfRange r3
      (mkCase s!"/fuzz/shape-{shape}/quiet-range-invalid-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftOutOfRange r3
      (mkCase s!"/fuzz/shape-{shape}/error-order-bad-shift-does-not-mask-y-type"
        #[intV x, yLike, intV shift], r4)
    else if shape = 16 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftOutOfRange r3
      (mkCase s!"/fuzz/shape-{shape}/error-order-bad-shift-does-not-mask-x-type"
        #[xLike, intV y, intV shift], r4)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet-nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet-nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet-shift-nan-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 20 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order-pushint-overflow-x-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order-pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order-pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/ok-fallback-shape" #[intV x, intV y, intV shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulrshiftcId
  unit := #[
    { name := "/unit/direct/ceil-rounding-and-shift-zero-override"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 5, 1, 18),
            (-7, 5, 1, -17),
            (7, -5, 1, -17),
            (-7, -5, 1, 18),
            (7, 5, 2, 9),
            (-7, 5, 2, -8),
            (5, 5, 2, 7),
            (-5, 5, 2, -6),
            (7, 5, 0, 35),
            (-7, 5, 0, -35),
            (maxInt257, 1, 256, 1),
            (minInt257, 1, 256, -1),
            (maxInt257, -1, 256, 0),
            (-1, 1, 256, 0),
            (1, 1, 256, 1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/ceil/{x}/{y}/{shift}"
                (runQmulrshiftcDirect #[intV x, intV y, intV shift])
                #[intV expected] }
    ,
    { name := "/unit/direct/quiet-nan-on-overflow-and-invalid-shift"
      run := do
        expectOkStack "/unit/direct/quiet-overflow/max-times-two-shift0"
          (runQmulrshiftcDirect #[intV maxInt257, intV 2, intV 0]) #[.int .nan]
        expectOkStack "/unit/direct/quiet-overflow/min-times-negone-shift0"
          (runQmulrshiftcDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan]
        expectOkStack "/unit/direct/quiet-overflow/max-times-max-shift255"
          (runQmulrshiftcDirect #[intV maxInt257, intV maxInt257, intV 255]) #[.int .nan]
        expectOkStack "/unit/direct/quiet-range/shift-negative"
          (runQmulrshiftcDirect #[intV 3, intV 5, intV (-1)]) #[.int .nan]
        expectOkStack "/unit/direct/quiet-range/shift-257"
          (runQmulrshiftcDirect #[intV 3, intV 5, intV 257]) #[.int .nan]
        expectOkStack "/unit/direct/quiet-range/shift-300"
          (runQmulrshiftcDirect #[intV 3, intV 5, intV 300]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-type-and-pop-sequencing"
      run := do
        expectErr "/unit/error/underflow-empty"
          (runQmulrshiftcDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-one-arg"
          (runQmulrshiftcDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-args"
          (runQmulrshiftcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-shift-type-short-stack"
          (runQmulrshiftcDirect #[intV 1, .null]) .stkUnd
        expectErr "/unit/error/type-pop-shift-first"
          (runQmulrshiftcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type-pop-y-second"
          (runQmulrshiftcDirect #[intV 1, .null, intV 1]) .typeChk
        expectErr "/unit/error/type-pop-x-third"
          (runQmulrshiftcDirect #[.null, intV 1, intV 1]) .typeChk
        expectErr "/unit/error-order/bad-shift-does-not-mask-y-type"
          (runQmulrshiftcDirect #[intV 1, .null, intV 257]) .typeChk
        expectErr "/unit/error-order/bad-shift-does-not-mask-x-type"
          (runQmulrshiftcDirect #[.null, intV 1, intV 257]) .typeChk }
    ,
    { name := "/unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmulrshiftcDispatchFallback #[]) #[intV 8312] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign-pos-pos-shift1" #[intV 7, intV 5, intV 1],
    mkCase "/ok/ceil/sign-neg-pos-shift1" #[intV (-7), intV 5, intV 1],
    mkCase "/ok/ceil/sign-pos-neg-shift1" #[intV 7, intV (-5), intV 1],
    mkCase "/ok/ceil/sign-neg-neg-shift1" #[intV (-7), intV (-5), intV 1],
    mkCase "/ok/ceil/sign-pos-pos-shift2" #[intV 7, intV 5, intV 2],
    mkCase "/ok/ceil/sign-neg-pos-shift2" #[intV (-7), intV 5, intV 2],
    mkCase "/ok/ceil/sign-pos-neg-shift2" #[intV 7, intV (-5), intV 2],
    mkCase "/ok/ceil/sign-neg-neg-shift2" #[intV (-7), intV (-5), intV 2],
    mkCase "/ok/ceil/near-zero-neg-half" #[intV (-1), intV 1, intV 1],
    mkCase "/ok/ceil/near-zero-pos-half" #[intV 1, intV 1, intV 1],
    mkCase "/ok/floor-override/shift-zero-pos-neg" #[intV 7, intV (-5), intV 0],
    mkCase "/ok/floor-override/shift-zero-neg-pos" #[intV (-7), intV 5, intV 0],
    mkCase "/ok/exact/zero-left-factor" #[intV 0, intV 123, intV 17],
    mkCase "/ok/exact/zero-right-factor" #[intV 123, intV 0, intV 17],
    mkCase "/ok/boundary/max-times-one-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "/ok/boundary/min-times-one-shift0" #[intV minInt257, intV 1, intV 0],
    mkCase "/ok/boundary/max-times-one-shift255" #[intV maxInt257, intV 1, intV 255],
    mkCase "/ok/boundary/min-times-one-shift255" #[intV minInt257, intV 1, intV 255],
    mkCase "/ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "/ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "/ok/boundary/max-times-negone-shift256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "/ok/boundary/min-plus-one-times-negone-shift256" #[intV (minInt257 + 1), intV (-1), intV 256],
    mkCase "/ok/boundary/max-times-max-shift256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "/quiet/overflow/min-times-negone-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "/quiet/overflow/max-times-two-shift0" #[intV maxInt257, intV 2, intV 0],
    mkCase "/quiet/overflow/max-times-max-shift255" #[intV maxInt257, intV maxInt257, intV 255],
    mkCase "/quiet/range/shift-negative" #[intV 5, intV 7, intV (-1)],
    mkCase "/quiet/range/shift-257" #[intV 5, intV 7, intV 257],
    mkCase "/quiet/range/shift-300" #[intV 5, intV 7, intV 300],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-shift-type" #[intV 1, .null],
    mkCase "/type/pop-shift-first-non-int" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second-non-int" #[intV 1, .null, intV 1],
    mkCase "/type/pop-x-third-non-int" #[.null, intV 1, intV 1],
    mkCase "/error-order/type-y-before-invalid-shift-funnel" #[intV 5, .null, intV 257],
    mkCase "/error-order/type-x-before-invalid-shift-funnel" #[.null, intV 5, intV 257],
    mkCaseFromIntVals "/quiet/nan/x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "/quiet/nan/y-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "/quiet/range/shift-nan-via-program"
      #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/x"
      #[IntVal.num (pow2 257), IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/y"
      #[IntVal.num 5, IntVal.num (-(pow2 257)), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/shift"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num qmulrshiftcSetGasExact), .tonEnvOp .setGasLimit, qmulrshiftcInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num qmulrshiftcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulrshiftcInstr]
  ]
  fuzz := #[
    { seed := 2026020828
      count := 700
      gen := genQmulrshiftcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTC
