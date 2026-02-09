import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTC

/-
MULRSHIFTC branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod` mul-mode path)
  - `TvmLean/Model/Basics/Bytes.lean` (`rshiftPow2Round`, ceil/floor pow2 division)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa9a` decode to `.shrMod true false 1 1 false none`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode registration in `register_div_ops`)

Branch counts used for this suite:
- Lean mul-shr specialization (`.arithExt (.shrMod true false 1 1 false none)`):
  8 branch sites / 13 terminal outcomes
  (dispatch/fallback; underflow gate; shift pop/type path; shift range check;
   operand shape split; round-mode validity gate; `d` switch; non-quiet push success/intOv).
- C++ `exec_mulshrmod` (non-quiet runtime-shift):
  7 branch sites / 12 aligned terminal outcomes
  (opcode guard/remap, underflow gate, shift range gate, validity funnel, `d` switch,
   rounding path, non-quiet `push_int_quiet` overflow/NaN throw).

Key risk areas covered:
- ceil rounding semantics for mixed signs and odd products;
- runtime shift boundaries (`0`, `1`, `255`, `256`) and range errors (`<0`, `>256`);
- strict pop/error ordering (`stkUnd` before shift/type checks on short stacks; `z → y → x`);
- NaN and out-of-range integer injection via program-only `PUSHINT` helper path;
- signed-257 overflow cliffs (`minInt257 * (-1)`, large products with small shifts);
- exact gas boundary under `PUSHINT n; SETGASLIMIT; MULRSHIFTC`.
-/

private def mulrshiftcId : InstrId := { name := "MULRSHIFTC" }

private def mulrshiftcInstr : Instr :=
  .arithExt (.shrMod true false 1 1 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulrshiftcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[mulrshiftcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runMulrshiftcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftcInstr stack

private def runMulrshiftcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 3904)) stack

private def mulrshiftcSetGasExact : Int :=
  computeExactGasBudget mulrshiftcInstr

private def mulrshiftcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftcInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOutOfRangePool : Array Int :=
  #[-7, -3, -1, 257, 258, 300, 511]

private def outOfRangeOperandPool : Array Int :=
  #[maxInt257 + 1, maxInt257 + 2, minInt257 - 1, minInt257 - 2, pow2 257, -(pow2 257)]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftOutOfRange (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftOutOfRangePool rng

private def pickShiftUpTo256 (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def genMulrshiftcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-boundary-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUpTo256 r3
      (mkCase s!"fuzz/shape-{shape}/ok-mixed-uniform-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftUpTo256 r3
      (mkCase s!"fuzz/shape-{shape}/ok-signed-boundary-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-zero-left-factor" #[intV 0, intV y, intV shift], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-zero-right-factor" #[intV x, intV 0, intV shift], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/intov-overflow-min-negone-shift0"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/intov-overflow-max-max-shift255"
        #[intV maxInt257, intV maxInt257, intV 255], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-arg" #[intV x], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two-args" #[intV x, intV y], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-shift-first" #[intV x, intV y, zLike], r4)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-second" #[intV x, yLike, intV shift], r4)
    else if shape = 13 then
      let (xLike, r2) := pickNonInt rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-third" #[xLike, intV y, intV shift], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftOutOfRange r3
      (mkCase s!"fuzz/shape-{shape}/range-shift-out-of-range" #[intV x, intV y, intV shift], r4)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-x-type"
        #[xLike, intV y, intV 257], r3)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-shift-nan-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else
      let (oor, r2) := pickFromPool outOfRangeOperandPool rng1
      let (v, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      let (xSlot, r5) := randBool r4
      let vals :=
        if xSlot then
          #[IntVal.num oor, IntVal.num v, IntVal.num shift]
        else
          #[IntVal.num v, IntVal.num oor, IntVal.num shift]
      let slot := if xSlot then "x" else "y"
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-{slot}-out-of-range-via-program" vals, r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftcId
  unit := #[
    { name := "unit/direct/ceil-rounding-sign-cases"
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
            (1, 1, 1, 1),
            (-1, 1, 1, 0),
            (1, -1, 1, 0),
            (-1, -1, 1, 1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"({x}*{y})>>{shift}"
                (runMulrshiftcDirect #[intV x, intV y, intV shift])
                #[intV expected] }
    ,
    { name := "unit/direct/zero-shift-and-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257),
            (minInt257, 1, 0, minInt257),
            (maxInt257, -1, 0, -maxInt257),
            (maxInt257, 1, 256, 1),
            (minInt257, 1, 256, -1),
            (maxInt257, -1, 256, 0),
            (-1, 1, 256, 0),
            (1, 1, 256, 1),
            (maxInt257, maxInt257, 256, maxInt257),
            (0, maxInt257, 13, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"({x}*{y})>>{shift}"
                (runMulrshiftcDirect #[intV x, intV y, intV shift])
                #[intV expected] }
    ,
    { name := "unit/error/intov-range-type-and-ordering"
      run := do
        expectErr "intov/min-times-neg-one-shift0"
          (runMulrshiftcDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "intov/max-times-max-shift255"
          (runMulrshiftcDirect #[intV maxInt257, intV maxInt257, intV 255]) .intOv
        expectErr "underflow/empty" (runMulrshiftcDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runMulrshiftcDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runMulrshiftcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/non-int-short-stack-underflow-first"
          (runMulrshiftcDirect #[.null, intV 1]) .stkUnd
        expectErr "type/pop-shift-first" (runMulrshiftcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulrshiftcDirect #[intV 1, .null, intV 1]) .typeChk
        expectErr "type/pop-x-third" (runMulrshiftcDirect #[.null, intV 1, intV 1]) .typeChk
        expectErr "range/shift-negative" (runMulrshiftcDirect #[intV 1, intV 2, intV (-1)]) .rangeChk
        expectErr "range/shift-257-before-x-type"
          (runMulrshiftcDirect #[.null, intV 2, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulrshiftcDispatchFallback #[]) #[intV 3904] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-shift1" #[intV 7, intV 5, intV 1],
    mkCase "ok/ceil/sign/neg-pos-shift1" #[intV (-7), intV 5, intV 1],
    mkCase "ok/ceil/sign/pos-neg-shift1" #[intV 7, intV (-5), intV 1],
    mkCase "ok/ceil/sign/neg-neg-shift1" #[intV (-7), intV (-5), intV 1],
    mkCase "ok/ceil/sign/pos-pos-shift2" #[intV 7, intV 5, intV 2],
    mkCase "ok/ceil/sign/neg-pos-shift2" #[intV (-7), intV 5, intV 2],
    mkCase "ok/ceil/sign/pos-neg-shift2" #[intV 7, intV (-5), intV 2],
    mkCase "ok/ceil/sign/neg-neg-shift2" #[intV (-7), intV (-5), intV 2],
    mkCase "ok/ceil/near-zero/neg-half" #[intV (-1), intV 1, intV 1],
    mkCase "ok/ceil/near-zero/pos-half" #[intV 1, intV 1, intV 1],
    mkCase "ok/exact/shift-zero-floor-identity" #[intV (-7), intV 5, intV 0],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 123, intV 17],
    mkCase "ok/exact/zero-right-factor" #[intV 123, intV 0, intV 17],
    mkCase "ok/boundary/max-times-one-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-times-one-shift0" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/max-times-neg-one-shift256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "ok/boundary/max-times-max-shift256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/boundary/min-times-max-shift256" #[intV minInt257, intV maxInt257, intV 256],
    mkCase "overflow/min-times-neg-one-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "overflow/max-times-max-shift255" #[intV maxInt257, intV maxInt257, intV 255],
    mkCase "overflow/min-times-min-shift255" #[intV minInt257, intV minInt257, intV 255],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-shift-type" #[intV 1, .null],
    mkCase "type/pop-shift-first-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 1],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 1],
    mkCase "range/shift-negative" #[intV 5, intV 7, intV (-1)],
    mkCase "range/shift-257" #[intV 5, intV 7, intV 257],
    mkCase "error-order/range-before-y-type" #[intV 5, .null, intV 257],
    mkCase "error-order/range-before-x-type" #[.null, intV 5, intV 257],
    mkCaseFromIntVals "nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "range/shift-nan-via-program" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "range/program-x-out-of-range" #[IntVal.num (pow2 257), IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "range/program-y-out-of-range" #[IntVal.num 5, IntVal.num (-(pow2 257)), IntVal.num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftcSetGasExact), .tonEnvOp .setGasLimit, mulrshiftcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftcSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftcInstr]
  ]
  fuzz := #[
    { seed := 2026020821
      count := 700
      gen := genMulrshiftcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTC
