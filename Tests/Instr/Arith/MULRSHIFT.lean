import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFT

/-
MULRSHIFT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 1 (-1) false none)` path)
  - `TvmLean/Model/Basics/Bytes.lean` (`rshiftPow2Round`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode wiring in `register_div_ops`)

Branch counts used for this suite (MULRSHIFT specialization):
- Lean: 9 branch points / 12 terminal outcomes
  (dispatch/fallback; pre-pop depth gate; runtime shift pop type/range;
   `y` then `x` pop type checks; numeric-vs-NaN operand split;
   `shift=0` round-mode override path; `d` arm; non-quiet push success/intOv).
- C++: 8 branch points / 12 aligned outcomes
  (`check_underflow`; runtime shift validation; `y`/`x` pop checks;
   finite-vs-invalid operand split; `d` switch; non-quiet push overflow/NaN throw path).

Key risk areas covered:
- floor right-shift semantics across sign combinations and shift edges (`0`, `255`, `256`);
- strict runtime shift bounds `[0, 256]` with precedence over `y`/`x` pops;
- pre-pop underflow gate ordering (`stkUnd` before shift/type/range for short stacks);
- NaN/out-of-range integer injection only via program (`PUSHINT` helpers), never init stack;
- signed-257 overflow funnel at non-quiet result push (especially `shift=0` large products);
- exact gas boundary via `PUSHINT n; SETGASLIMIT; MULRSHIFT` (exact vs exact-minus-one).
-/

private def mulrshiftId : InstrId := { name := "MULRSHIFT" }

private def mulrshiftInstr : Instr :=
  .arithExt (.shrMod true false 1 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulrshiftId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push mulrshiftInstr) gasLimits fuel

private def runMulrshiftDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftInstr stack

private def runMulrshiftDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6401)) stack

private def mulrshiftSetGasExact : Int :=
  computeExactGasBudget mulrshiftInstr

private def mulrshiftSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftInstr

private def mkShiftInjectedCase (name : String) (x y : Value) (shift : IntVal) : OracleCase :=
  mkCase name #[x, y] #[.pushInt shift, mulrshiftInstr]

private def mkXNanInjectedCase (name : String) (y shift : Int) : OracleCase :=
  mkCase name #[intV y, intV shift] #[.pushInt .nan, .xchg0 2, .xchg0 1, mulrshiftInstr]

private def mkYNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift] #[.pushInt .nan, .xchg0 1, mulrshiftInstr]

private def validShiftPool : Array Int :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300, 511]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def genMulrshiftFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromIntPool validShiftPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-inrange" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickFromIntPool validShiftPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-x-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromIntPool validShiftPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-y-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-x-zero" #[intV 0, intV y, intV shift], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-y-zero" #[intV x, intV 0, intV shift], r3)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let (ySel, r3) := randNat r2 0 2
      let y :=
        if ySel = 0 then
          (1 : Int)
        else if ySel = 1 then
          (-1 : Int)
        else
          (2 : Int)
      let (shift, r4) := pickFromIntPool validShiftPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-extreme-times-unit" #[intV x, intV y, intV shift], r4)
    else if shape = 7 then
      let (variant, r2) := randNat rng1 0 3
      let (x, y) :=
        if variant = 0 then
          (maxInt257, (2 : Int))
        else if variant = 1 then
          (minInt257, (2 : Int))
        else if variant = 2 then
          (minInt257, (-1 : Int))
        else
          (maxInt257, maxInt257)
      (mkCase s!"fuzz/shape-{shape}/overflow-shift-zero" #[intV x, intV y, intV 0], r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickFromIntPool invalidShiftPool r3
      (mkCase s!"fuzz/shape-{shape}/range-invalid-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonIntLike r3
      (mkCase s!"fuzz/shape-{shape}/type-shift-pop-first" #[intV x, intV y, shiftLike], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/type-y-pop-second" #[intV x, yLike, intV shift], r4)
    else if shape = 11 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/type-x-pop-third" #[xLike, intV y, intV shift], r4)
    else if shape = 12 then
      let (variant, r2) := randNat rng1 0 3
      if variant = 0 then
        (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], r2)
      else if variant = 1 then
        let (x, r3) := pickSigned257ish r2
        (mkCase s!"fuzz/shape-{shape}/underflow-single-int" #[intV x], r3)
      else if variant = 2 then
        let (x, r3) := pickSigned257ish r2
        let (shift, r4) := pickShiftInRange r3
        (mkCase s!"fuzz/shape-{shape}/underflow-two-items" #[intV x, intV shift], r4)
      else
        let (v, r3) := pickNonIntLike r2
        (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int" #[v], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-shift-via-program" #[.num x, .num y, .nan], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkYNanInjectedCase s!"fuzz/shape-{shape}/nan-y-via-program" x shift, r3)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkXNanInjectedCase s!"fuzz/shape-{shape}/nan-x-via-program" y shift, r3)
    else if shape = 16 then
      let (variant, r2) := randNat rng1 0 2
      let big : Int := pow2 256
      if variant = 0 then
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/pushint-overflow-x" #[.num big, .num 7, .num 5], r2)
      else if variant = 1 then
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/pushint-overflow-y" #[.num 7, .num big, .num 5], r2)
      else
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/pushint-overflow-shift" #[.num 7, .num 5, .num big], r2)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickFromIntPool invalidShiftPool r3
      (mkShiftInjectedCase
        s!"fuzz/shape-{shape}/error-order-range-before-y-type-via-program"
        (intV x) yLike (.num shift), r4)
    else if shape = 18 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickFromIntPool invalidShiftPool r3
      (mkShiftInjectedCase
        s!"fuzz/shape-{shape}/error-order-range-before-x-type-via-program"
        xLike (intV y) (.num shift), r4)
    else
      let (xLike, r2) := pickNonIntLike rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/error-order-y-before-x-both-non-int"
        #[xLike, yLike, intV shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftId
  unit := #[
    { name := "unit/direct/floor-rshift-sign-zero-and-shift-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 5, 0, 35),
            (7, 5, 1, 17),
            (-7, 5, 1, -18),
            (7, -5, 1, -18),
            (-7, -5, 1, 17),
            (13, 11, 3, 17),
            (-13, 11, 3, -18),
            (13, -11, 3, -18),
            (-13, -11, 3, 17),
            (maxInt257, 2, 1, maxInt257),
            (maxInt257, 1, 255, 1),
            (maxInt257, 1, 256, 0),
            (minInt257, 1, 255, -2),
            (minInt257, 1, 256, -1),
            (minInt257, -1, 256, 1),
            (maxInt257, -1, 256, -1),
            (minInt257 + 1, -1, 256, 0),
            (-1, 1, 256, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})>>{shift}"
            (runMulrshiftDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/error/underflow-range-pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulrshiftDirect #[]) .stkUnd
        expectErr "underflow/single-int" (runMulrshiftDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runMulrshiftDirect #[.null]) .stkUnd
        expectErr "underflow/two-items-before-shift-pop" (runMulrshiftDirect #[intV 7, intV 1]) .stkUnd
        expectErr "error-order/underflow-before-range-with-two-items"
          (runMulrshiftDirect #[intV 7, intV (-1)]) .stkUnd
        expectErr "error-order/underflow-before-shift-type-with-two-items"
          (runMulrshiftDirect #[intV 7, .null]) .stkUnd
        expectErr "type/pop-shift-first"
          (runMulrshiftDirect #[intV 7, intV 5, .null]) .typeChk
        expectErr "type/pop-y-second"
          (runMulrshiftDirect #[intV 7, .null, intV 1]) .typeChk
        expectErr "type/pop-x-third"
          (runMulrshiftDirect #[.null, intV 7, intV 1]) .typeChk
        expectErr "error-order/pop-shift-before-y-x-when-both-non-int"
          (runMulrshiftDirect #[.null, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-valid-shift"
          (runMulrshiftDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "range/shift-negative"
          (runMulrshiftDirect #[intV 7, intV 5, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax"
          (runMulrshiftDirect #[intV 7, intV 5, intV 257]) .rangeChk
        expectErr "error-order/range-before-y-type"
          (runMulrshiftDirect #[intV 7, .null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type"
          (runMulrshiftDirect #[.null, intV 7, intV 257]) .rangeChk }
    ,
    { name := "unit/overflow/shift-zero-intov-boundaries"
      run := do
        expectErr "overflow/max-times-two-shift-zero"
          (runMulrshiftDirect #[intV maxInt257, intV 2, intV 0]) .intOv
        expectErr "overflow/min-times-neg-one-shift-zero"
          (runMulrshiftDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "overflow/min-times-two-shift-zero"
          (runMulrshiftDirect #[intV minInt257, intV 2, intV 0]) .intOv
        expectErr "overflow/max-times-max-shift-zero"
          (runMulrshiftDirect #[intV maxInt257, intV maxInt257, intV 0]) .intOv }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runMulrshiftDispatchFallback #[]) #[intV 6401] }
  ]
  oracle := #[
    mkCase "ok/shift-zero/zero-product" #[intV 0, intV 7, intV 0],
    mkCase "ok/shift-zero/pos-pos" #[intV 7, intV 5, intV 0],
    mkCase "ok/shift-zero/neg-pos" #[intV (-7), intV 5, intV 0],
    mkCase "ok/shift-zero/pos-neg" #[intV 7, intV (-5), intV 0],
    mkCase "ok/shift-zero/neg-neg" #[intV (-7), intV (-5), intV 0],
    mkCase "ok/floor/pos-pos-inexact" #[intV 7, intV 5, intV 1],
    mkCase "ok/floor/neg-pos-inexact" #[intV (-7), intV 5, intV 1],
    mkCase "ok/floor/pos-neg-inexact" #[intV 7, intV (-5), intV 1],
    mkCase "ok/floor/neg-neg-inexact" #[intV (-7), intV (-5), intV 1],
    mkCase "ok/exact/divisible-pos" #[intV 24, intV 7, intV 3],
    mkCase "ok/exact/divisible-neg" #[intV (-24), intV 7, intV 3],
    mkCase "ok/boundary/max-times-two-shift-one" #[intV maxInt257, intV 2, intV 1],
    mkCase "ok/boundary/max-times-one-shift255" #[intV maxInt257, intV 1, intV 255],
    mkCase "ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-times-one-shift255" #[intV minInt257, intV 1, intV 255],
    mkCase "ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-times-negone-shift256" #[intV minInt257, intV (-1), intV 256],
    mkCase "ok/boundary/max-times-negone-shift256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "ok/boundary/min-plus-one-times-negone-shift256" #[intV (minInt257 + 1), intV (-1), intV 256],
    mkCase "ok/boundary/negone-times-one-shift256" #[intV (-1), intV 1, intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/single-int" #[intV 1],
    mkCase "underflow/single-non-int" #[.null],
    mkCase "underflow/two-items-before-shift-pop" #[intV 7, intV 1],
    mkCase "error-order/underflow-before-range-with-two-items" #[intV 7, intV (-1)],
    mkCase "error-order/underflow-before-shift-type-with-two-items" #[intV 7, .null],
    mkCase "type/pop-shift-first-null" #[intV 7, intV 5, .null],
    mkCase "type/pop-shift-first-cell" #[intV 7, intV 5, .cell Cell.empty],
    mkCase "type/pop-y-second-null" #[intV 7, .null, intV 1],
    mkCase "type/pop-x-third-null" #[.null, intV 7, intV 1],
    mkCase "error-order/y-pop-before-x-after-valid-shift" #[.null, .cell Cell.empty, intV 1],
    mkCase "error-order/shift-type-before-y-x" #[.null, .cell Cell.empty, .null],
    mkCase "range/shift-negative" #[intV 7, intV 5, intV (-1)],
    mkCase "range/shift-overmax" #[intV 7, intV 5, intV 257],
    mkCase "error-order/range-before-y-type" #[intV 7, .null, intV (-1)],
    mkCase "error-order/range-before-x-type" #[.null, intV 7, intV 257],
    mkCaseFromIntVals "range/shift-nan-via-program" #[.num 7, .num 5, .nan],
    mkYNanInjectedCase "nan/y-via-program-intov" 7 1,
    mkXNanInjectedCase "nan/x-via-program-intov" 5 1,
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/x"
      #[.num (pow2 256), .num 7, .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/y"
      #[.num 7, .num (pow2 256), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/shift"
      #[.num 7, .num 5, .num (pow2 256)],
    mkShiftInjectedCase "error-order/shift-range-before-y-type-via-program"
      (intV 7) .null (.num (-1)),
    mkShiftInjectedCase "error-order/shift-range-before-x-type-via-program"
      .null (intV 7) (.num 257),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulrshiftSetGasExact), .tonEnvOp .setGasLimit, mulrshiftInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulrshiftSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftInstr]
  ]
  fuzz := #[
    { seed := 2026020816
      count := 700
      gen := genMulrshiftFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFT
