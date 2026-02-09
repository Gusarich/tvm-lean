import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTR

/-
MULRSHIFTR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod` mul path)
  - `TvmLean/Model/Basics/Bytes.lean` (`rshiftPow2Round`, nearest/tie behavior)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (opcode decode `0xa9a5`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, opcode wiring in `register_div_ops`)

Branch/terminal outcomes mapped by this suite
(`mul=true`, `add=false`, `d=1`, `roundMode=0`, `quiet=false`, `zOpt=none`):
- Lean: 9 branch sites / 13 terminal outcomes
  (dispatch/fallback; explicit underflow gate; shift pop num/nan/type;
   shift range guard; `x/y` pop type-vs-num paths; zero-shift round rewrite;
   round-mode validity guard; `d` switch; non-quiet `pushIntQuiet` fit check).
- C++: 8 branch sites / 13 aligned terminal outcomes
  (`check_underflow(3)`; runtime shift pop/range; pop order `y` then `x`;
   NaN/type funnel to non-quiet `int_ov`; result push signed-257 guard).

Key risk areas covered:
- nearest rounding ties must go toward `+∞` after multiply (`-1*1 >>R 1 = 0`);
- runtime shift range is strict `[0, 256]` in non-quiet mode;
- error ordering: underflow before shift parse, range before operand type checks;
- NaN/out-of-range integer inputs are injected via program (`PUSHINT`) only;
- signed-257 overflow on result push (large products / minimal shifts);
- deterministic gas threshold (`PUSHINT n; SETGASLIMIT; MULRSHIFTR`).
-/

private def mulrshiftrId : InstrId := { name := "MULRSHIFTR" }

private def mulrshiftrInstr : Instr :=
  .arithExt (.shrMod true false 1 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulrshiftrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[mulrshiftrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runMulRshiftrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftrInstr stack

private def runMulRshiftrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4257)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def mulrshiftrSetGasExact : Int :=
  computeExactGasBudget mulrshiftrInstr

private def mulrshiftrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftrInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOverflowPool : Array Int :=
  #[257, 258, 511, 1024]

private def tieFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def outOfRangePool : Array Int :=
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

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftOverflow (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftOverflowPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def genMulRshiftrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-random"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 2 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-tie-shift1"
        #[IntVal.num x, IntVal.num y, IntVal.num 1], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-shift-zero-floor"
        #[IntVal.num x, IntVal.num y, IntVal.num 0], r3)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      let (useNeg, r3) := randBool r2
      let y : Int := if useNeg then -1 else 1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-shift-256-boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num 256], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (negMag, r4) := randNat r3 1 4
      let shift : Int := -Int.ofNat negMag
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-negative-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftOverflow r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-overmax-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-nan-via-program"
        #[intV x, intV y] #[.pushInt .nan, mulrshiftrInstr], r3)
    else if shape = 8 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 10 then
      let (oor, r2) := pickFromPool outOfRangePool rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-x-via-program"
        #[IntVal.num oor, IntVal.num y, IntVal.num shift], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (oor, r3) := pickFromPool outOfRangePool r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-y-via-program"
        #[IntVal.num x, IntVal.num oor, IntVal.num shift], r4)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two-ints" #[intV x, intV y], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (useNull, r4) := randBool r3
      let shiftLike : Value := if useNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-shift-non-int" #[intV x, intV y, shiftLike], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (useNull, r4) := randBool r3
      let yLike : Value := if useNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-y-non-int" #[intV x, yLike, intV shift], r4)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (useNull, r4) := randBool r3
      let xLike : Value := if useNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, intV y, intV shift], r4)
    else if shape = 18 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/overflow-max-times-two-shift0"
        #[IntVal.num maxInt257, IntVal.num 2, IntVal.num 0], rng1)
    else
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/overflow-min-times-neg-one-shift0"
        #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftrId
  unit := #[
    { name := "unit/round/sign-and-half-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 11),
            (-7, 3, 1, -10),
            (7, -3, 1, -10),
            (-7, -3, 1, 11),
            (5, 5, 1, 13),
            (-5, 5, 1, -12),
            (5, -5, 1, -12),
            (-5, -5, 1, 13),
            (1, 1, 1, 1),
            (-1, 1, 1, 0),
            (3, 3, 2, 2),
            (-3, 3, 2, -2),
            (9, 5, 3, 6),
            (-9, 5, 3, -6),
            (9, -5, 3, -6),
            (-9, -5, 3, 6)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})>>R{shift}"
            (runMulRshiftrDirect #[intV x, intV y, intV shift])
            #[intV expected] }
    ,
    { name := "unit/round/shift-zero-and-high-shift-boundaries"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (123, 45, 0, 5535),
            (-123, 45, 0, -5535),
            (123, -45, 0, -5535),
            (-123, -45, 0, 5535),
            (maxInt257, 1, 0, maxInt257),
            (minInt257, 1, 0, minInt257),
            (maxInt257, 1, 256, 1),
            (maxInt257, -1, 256, -1),
            (minInt257, 1, 256, -1),
            (minInt257, -1, 256, 1),
            (pow2 255, 1, 256, 1),
            (-(pow2 255), 1, 256, 0),
            (maxInt257, 1, 255, 2),
            (minInt257, 1, 255, -2)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})>>R{shift}"
            (runMulRshiftrDirect #[intV x, intV y, intV shift])
            #[intV expected] }
    ,
    { name := "unit/error/intov-overflow-and-nan-operands"
      run := do
        expectErr "overflow/max-times-two-shift0"
          (runMulRshiftrDirect #[intV maxInt257, intV 2, intV 0]) .intOv
        expectErr "overflow/min-times-neg-one-shift0"
          (runMulRshiftrDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "overflow/max-times-max-shift1"
          (runMulRshiftrDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "nan/x"
          (runMulRshiftrDirect #[.int .nan, intV 7, intV 1]) .intOv
        expectErr "nan/y"
          (runMulRshiftrDirect #[intV 7, .int .nan, intV 1]) .intOv }
    ,
    { name := "unit/error/underflow-range-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runMulRshiftrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runMulRshiftrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items-before-shift-parse" (runMulRshiftrDirect #[intV 1, .null]) .stkUnd
        expectErr "range/shift-negative-before-y-type"
          (runMulRshiftrDirect #[intV 7, .null, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax-before-x-type"
          (runMulRshiftrDirect #[.null, intV 7, intV 257]) .rangeChk
        expectErr "type/shift-top-non-int"
          (runMulRshiftrDirect #[intV 7, intV 5, .null]) .typeChk
        expectErr "type/y-second-non-int"
          (runMulRshiftrDirect #[intV 7, .null, intV 1]) .typeChk
        expectErr "type/x-third-non-int"
          (runMulRshiftrDirect #[.null, intV 5, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[mulrshiftrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/mulrshiftr" s0 mulrshiftrInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-mulrshiftr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulRshiftrDispatchFallback #[]) #[intV 4257] }
  ]
  oracle := #[
    mkCaseFromIntVals "ok/round/sign/pos-pos-shift1-half-up"
      #[IntVal.num 7, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "ok/round/sign/neg-pos-shift1-half-up-to-plus-inf"
      #[IntVal.num (-7), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "ok/round/sign/pos-neg-shift1-half-up-to-plus-inf"
      #[IntVal.num 7, IntVal.num (-3), IntVal.num 1],
    mkCaseFromIntVals "ok/round/sign/neg-neg-shift1-half-up"
      #[IntVal.num (-7), IntVal.num (-3), IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/plus-half"
      #[IntVal.num 1, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/minus-half-to-plus-inf"
      #[IntVal.num (-1), IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/plus-three-halves"
      #[IntVal.num 3, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/minus-three-halves"
      #[IntVal.num (-3), IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/round/non-tie-shift2-pos"
      #[IntVal.num 7, IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "ok/round/non-tie-shift2-neg"
      #[IntVal.num (-7), IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "ok/shift-zero/product-pos-neg"
      #[IntVal.num 123, IntVal.num (-45), IntVal.num 0],
    mkCaseFromIntVals "ok/shift-zero/product-neg-neg"
      #[IntVal.num (-123), IntVal.num (-45), IntVal.num 0],
    mkCaseFromIntVals "ok/boundary/max-shift256"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/min-shift256"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/max-neg-shift256"
      #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/min-neg-shift256"
      #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/half-up-pos"
      #[IntVal.num (pow2 255), IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/half-up-neg-to-zero"
      #[IntVal.num (-(pow2 255)), IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/max-shift255"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 255],
    mkCaseFromIntVals "ok/boundary/min-shift255"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 255],
    mkCaseFromIntVals "overflow/max-times-two-shift0"
      #[IntVal.num maxInt257, IntVal.num 2, IntVal.num 0],
    mkCaseFromIntVals "overflow/min-times-neg-one-shift0"
      #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0],
    mkCaseFromIntVals "overflow/max-times-max-shift1"
      #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items" #[intV 1, intV 2],
    mkCase "regression/error-order/underflow-before-shift-type-two-items"
      #[intV 1, .null],
    mkCase "regression/error-order/underflow-before-shift-range-two-items"
      #[intV 1, intV 257],
    mkCase "type/shift-top-non-int" #[intV 7, intV 5, .null],
    mkCase "type/y-second-non-int" #[intV 7, .null, intV 1],
    mkCase "type/x-third-non-int" #[.null, intV 5, intV 1],
    mkCase "range/shift-negative" #[intV 7, intV 5, intV (-1)],
    mkCase "range/shift-overmax" #[intV 7, intV 5, intV 257],
    mkCase "error-order/range-before-y-type-negative"
      #[intV 7, .null, intV (-1)],
    mkCase "error-order/range-before-x-type-overmax"
      #[.null, intV 7, intV 257],
    mkCase "range/shift-nan-via-program" #[intV 7, intV 5]
      #[.pushInt .nan, mulrshiftrInstr],
    mkCaseFromIntVals "nan/x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "nan/y-via-program"
      #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "range/x-out-of-range-via-program"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "range/y-out-of-range-via-program"
      #[IntVal.num 7, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftrSetGasExact), .tonEnvOp .setGasLimit, mulrshiftrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftrSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftrInstr]
  ]
  fuzz := #[
    { seed := 2026020816
      count := 700
      gen := genMulRshiftrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTR
