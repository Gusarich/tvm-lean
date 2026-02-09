import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODPOW2C

/-
MULMODPOW2C branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 2 1 false none)` path)
  - `TvmLean/Model/Basics/Bytes.lean` (`modPow2Round`, `rshiftPow2Round`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (MULMODPOW2C specialization): 9 branch points / 12 terminal outcomes
  (dispatch/fallback; underflow gate; shift pop type/range; `y` then `x` pop type/underflow;
   finite-vs-NaN operand split; `shift = 0` floor override; non-quiet push success/error).
- C++ (`exec_mulshrmod`, args `0xa9aa`): 8 branch points / 12 aligned outcomes
  (invalid-op guard; underflow gate; `pop_long` range/type; `y`/`x` pop checks;
   `y = 0` mode override; finite-vs-invalid split; non-quiet `push_int_quiet` success/error).

Key risk areas covered:
- ceil-mod remainder sign/tie behavior for `x*y mod 2^z` (`C` mode);
- runtime `shift = 0` forced floor override (remainder must be `0`);
- strict shift bounds `[0, 256]` and `shift` pop precedence;
- error/pop ordering (`shift` before `y`, `y` before `x`, underflow before type/range);
- NaN and out-of-range shift scenarios injected via program only;
- exact gas boundary via `PUSHINT n; SETGASLIMIT; MULMODPOW2C`.
-/

private def mulmodpow2cId : InstrId := { name := "MULMODPOW2C" }

private def mulmodpow2cInstr : Instr :=
  .arithExt (.shrMod true false 2 1 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulmodpow2cInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulmodpow2cId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulmodpow2cDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulmodpow2cInstr stack

private def runMulmodpow2cDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6102)) stack

private def mulmodpow2cSetGasExact : Int :=
  computeExactGasBudget mulmodpow2cInstr

private def mulmodpow2cSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulmodpow2cInstr

private def mkShiftInjectedCase (name : String) (x y : Value) (shift : IntVal) : OracleCase :=
  mkCase name #[x, y] #[.pushInt shift, mulmodpow2cInstr]

private def mkXNanInjectedCase (name : String) (y shift : Int) : OracleCase :=
  mkCase name #[intV y, intV shift] #[.pushInt .nan, .xchg0 2, .xchg0 1, mulmodpow2cInstr]

private def mkYNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift] #[.pushInt .nan, .xchg0 1, mulmodpow2cInstr]

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftNegativePool : Array Int :=
  #[-3, -2, -1]

private def shiftOverMaxPool : Array Int :=
  #[257, 258, 300, 511]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromIntPool validShiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNegativeShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftNegativePool rng

private def pickOverMaxShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftOverMaxPool rng

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def genMulmodpow2cFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-inrange" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-shift-zero-floor-override" #[intV x, intV y, intV 0], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromIntPool #[-1, 0, 1] r2
      (mkCase s!"fuzz/shape-{shape}/ok-shift-256-boundary" #[intV x, intV y, intV 256], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickNegativeShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-negative-via-program" (intV x) (intV y) (.num shift), r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickOverMaxShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-overmax-via-program" (intV x) (intV y) (.num shift), r4)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" (intV x) (intV y) .nan, r3)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkXNanInjectedCase s!"fuzz/shape-{shape}/nan-x-via-program" y shift, r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkYNanInjectedCase s!"fuzz/shape-{shape}/nan-y-via-program" x shift, r3)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-int" #[intV x], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two-items" #[intV x, intV shift], r3)
    else if shape = 12 then
      let (v, r2) := pickNonIntLike rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int" #[v], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonIntLike r3
      (mkCase s!"fuzz/shape-{shape}/type-shift-non-int" #[intV x, intV y, shiftLike], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/type-y-non-int" #[intV x, yLike, intV shift], r4)
    else if shape = 15 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, intV y, intV shift], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (pickNeg, r4) := randBool r3
      let (shift, r5) := if pickNeg then pickNegativeShift r4 else pickOverMaxShift r4
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order-range-before-y-type-via-program" (intV x) yLike (.num shift), r5)
    else
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (pickNeg, r4) := randBool r3
      let (shift, r5) := if pickNeg then pickNegativeShift r4 else pickOverMaxShift r4
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order-range-before-x-type-via-program" xLike (intV y) (.num shift), r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulmodpow2cId
  unit := #[
    { name := "unit/direct/ceil-mod-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, -1),
            (7, 3, 2, -3),
            (-7, 3, 1, -1),
            (-7, 3, 2, -1),
            (7, -3, 2, -1),
            (-7, -3, 2, -3),
            (1, 1, 1, -1),
            (-1, 1, 1, -1),
            (42, 2, 1, 0),
            (-42, 2, 1, 0),
            (5, 5, 3, -7),
            (-5, 5, 3, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})%2^{shift}"
            (runMulmodpow2cDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/shift-zero-and-256-boundaries"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 0),
            (minInt257, 1, 0, 0),
            (maxInt257, 0, 0, 0),
            (minInt257, 0, 0, 0),
            (maxInt257, 1, 256, -1),
            (maxInt257 - 1, 1, 256, -2),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, 1, 256, minInt257 + 1),
            (1, 1, 256, minInt257 + 1),
            (-1, 1, 256, -1),
            (maxInt257, -1, 256, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"boundary/({x}*{y})%2^{shift}"
            (runMulmodpow2cDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/error/underflow-pop-order-and-range-type-ordering"
      run := do
        expectErr "underflow/empty" (runMulmodpow2cDirect #[]) .stkUnd
        expectErr "underflow/single-int" (runMulmodpow2cDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runMulmodpow2cDirect #[.null]) .stkUnd
        expectErr "underflow/two-items-before-y-pop" (runMulmodpow2cDirect #[intV 7, intV 1]) .stkUnd
        expectErr "error-order/underflow-before-range-with-two-items"
          (runMulmodpow2cDirect #[intV 7, intV (-1)]) .stkUnd
        expectErr "error-order/underflow-before-shift-type-with-two-items"
          (runMulmodpow2cDirect #[intV 7, .null]) .stkUnd
        expectErr "type/pop-shift-first"
          (runMulmodpow2cDirect #[intV 7, intV 3, .null]) .typeChk
        expectErr "type/pop-y-second"
          (runMulmodpow2cDirect #[intV 7, .null, intV 1]) .typeChk
        expectErr "type/pop-x-third"
          (runMulmodpow2cDirect #[.null, intV 7, intV 1]) .typeChk
        expectErr "error-order/pop-shift-before-y-when-both-non-int"
          (runMulmodpow2cDirect #[intV 7, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-when-shift-int"
          (runMulmodpow2cDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "range/shift-negative"
          (runMulmodpow2cDirect #[intV 7, intV 3, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax"
          (runMulmodpow2cDirect #[intV 7, intV 3, intV 257]) .rangeChk
        expectErr "error-order/range-before-y-type"
          (runMulmodpow2cDirect #[intV 7, .null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type"
          (runMulmodpow2cDirect #[.null, intV 7, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runMulmodpow2cDispatchFallback #[]) #[intV 6102] }
  ]
  oracle := #[
    mkCase "ok/ceil/pos-pos-shift1" #[intV 7, intV 3, intV 1],
    mkCase "ok/ceil/pos-pos-shift2" #[intV 7, intV 3, intV 2],
    mkCase "ok/ceil/neg-pos-shift1" #[intV (-7), intV 3, intV 1],
    mkCase "ok/ceil/neg-pos-shift2" #[intV (-7), intV 3, intV 2],
    mkCase "ok/ceil/pos-neg-shift2" #[intV 7, intV (-3), intV 2],
    mkCase "ok/ceil/neg-neg-shift2" #[intV (-7), intV (-3), intV 2],
    mkCase "ok/ceil/tie-pos-half-shift1" #[intV 1, intV 1, intV 1],
    mkCase "ok/ceil/tie-neg-half-shift1" #[intV (-1), intV 1, intV 1],
    mkCase "ok/ceil/exact-pos" #[intV 42, intV 2, intV 1],
    mkCase "ok/ceil/exact-neg" #[intV (-42), intV 2, intV 1],
    mkCase "ok/ceil/pos-small-shift3" #[intV 5, intV 5, intV 3],
    mkCase "ok/ceil/neg-small-shift3" #[intV (-5), intV 5, intV 3],
    mkCase "ok/shift0/max-times-one" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/shift0/min-times-one" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/shift0/max-times-zero" #[intV maxInt257, intV 0, intV 0],
    mkCase "ok/shift0/min-times-zero" #[intV minInt257, intV 0, intV 0],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 1, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 1, intV 256],
    mkCase "ok/boundary/one-shift256" #[intV 1, intV 1, intV 256],
    mkCase "ok/boundary/minus-one-shift256" #[intV (-1), intV 1, intV 256],
    mkCase "ok/boundary/max-times-negone-shift256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/single-int" #[intV 1],
    mkCase "underflow/single-non-int" #[.null],
    mkCase "underflow/two-items-before-y-pop" #[intV 7, intV 1],
    mkCase "error-order/underflow-before-range-with-two-items" #[intV 7, intV (-1)],
    mkCase "error-order/underflow-before-shift-type-with-two-items" #[intV 7, .null],
    mkCase "type/pop-shift-first-null" #[intV 7, intV 3, .null],
    mkCase "type/pop-y-second-null" #[intV 7, .null, intV 1],
    mkCase "type/pop-x-third-null" #[.null, intV 7, intV 1],
    mkCase "type/error-order-both-non-int-shift-first" #[intV 7, .cell Cell.empty, .null],
    mkCase "type/error-order-pop-y-before-x-after-valid-shift" #[.null, .cell Cell.empty, intV 1],
    mkShiftInjectedCase "range/shift-negative-via-program" (intV 7) (intV 3) (.num (-1)),
    mkShiftInjectedCase "range/shift-overmax-via-program" (intV 7) (intV 3) (.num 257),
    mkShiftInjectedCase "range/shift-nan-via-program" (intV 7) (intV 3) .nan,
    mkShiftInjectedCase "error-order/shift-range-before-y-type-via-program" (intV 7) .null (.num (-1)),
    mkShiftInjectedCase "error-order/shift-range-before-x-type-via-program" .null (intV 7) (.num 257),
    mkXNanInjectedCase "nan/x-via-program-intov" 3 1,
    mkYNanInjectedCase "nan/y-via-program-intov" 7 1,
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodpow2cSetGasExact), .tonEnvOp .setGasLimit, mulmodpow2cInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodpow2cSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulmodpow2cInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 700
      gen := genMulmodpow2cFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2C
