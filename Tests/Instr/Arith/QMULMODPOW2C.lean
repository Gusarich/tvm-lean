import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULMODPOW2C

/-
QMULMODPOW2C branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 2 1 true none)` path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`modPow2Round`, ceil-mod and `shift = 0` floor override behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, quiet runtime-shift path for `d = 2`, `round_mode = +1`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (QMULMODPOW2C specialization): 9 branch points / 11 terminal outcomes
  (dispatch/fallback; stack-depth gate; shift pop type; bad-shift classifier;
   `y` then `x` pop type order; bad-shift quiet-NaN funnel;
   finite-vs-NaN operand split; `shift = 0` round override;
   quiet push result path).
- C++ (`exec_mulshrmod`, quiet mode, runtime shift): 8 branch points / 11 aligned outcomes
  (invalid-op guard; underflow gate; `pop_long` + shift classifier;
   `y`/`x` pop order/type; global-v13 invalid-input quiet-NaN funnel;
   `z == 0` round remap; modulo push path).

Key risk areas covered:
- ceil-mod sign/tie behavior and power boundaries (`shift = 0`, `256`);
- quiet bad-shift behavior (`< 0`, `> 256`, NaN) returning NaN (not `rangeChk`);
- explicit pop/error ordering (`shift` before `y`, `y` before `x`, underflow first);
- bad-shift does not mask downstream `y/x` type errors;
- oracle/fuzz safety discipline: NaN/out-of-range ints injected via `PUSHINT` only;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qmulmodpow2cId : InstrId := { name := "QMULMODPOW2C" }

private def qmulmodpow2cInstr : Instr :=
  .arithExt (.shrMod true false 2 1 true none)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulmodpow2cInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulmodpow2cId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qmulmodpow2cInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programTail) gasLimits fuel

private def runQmulmodpow2cDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulmodpow2cInstr stack

private def runQmulmodpow2cDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6154)) stack

private def qmulmodpow2cSetGasExact : Int :=
  computeExactGasBudget qmulmodpow2cInstr

private def qmulmodpow2cSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulmodpow2cInstr

private def mkShiftInjectedCase (name : String) (x y : Value) (shift : IntVal) : OracleCase :=
  mkCase name #[x, y] #[.pushInt shift, qmulmodpow2cInstr]

private def mkXNanInjectedCase (name : String) (y shift : Int) : OracleCase :=
  mkCase name #[intV y, intV shift] #[.pushInt .nan, .xchg0 2, .xchg0 1, qmulmodpow2cInstr]

private def mkYNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift] #[.pushInt .nan, .xchg0 1, qmulmodpow2cInstr]

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-5, -2, -1, 257, 258, 300, 511]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromIntPool validShiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickInvalidShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool invalidShiftPool rng

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def genQmulmodpow2cFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/ok/boundary-triplet" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"/fuzz/shape-{shape}/ok/signed-triplet" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/ok/shift-zero-floor-override" #[intV x, intV y, intV 0], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromIntPool #[-1, 0, 1] r2
      (mkCase s!"/fuzz/shape-{shape}/ok/shift-256-boundary" #[intV x, intV y, intV 256], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInvalidShift r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/invalid-shift-via-program"
        (intV x) (intV y) (.num shift), r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/shift-nan-via-program"
        (intV x) (intV y) .nan, r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkYNanInjectedCase s!"/fuzz/shape-{shape}/quiet/nan-y-via-program" x shift, r3)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkXNanInjectedCase s!"/fuzz/shape-{shape}/quiet/nan-x-via-program" y shift, r3)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/single-int" #[intV x], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-items" #[intV x, intV shift], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickInvalidShift r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/underflow-before-bad-shift-via-program"
        #[intV x] #[.pushInt (.num shift), qmulmodpow2cInstr], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonIntLike r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-shift-first" #[intV x, intV y, shiftLike], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second" #[intV x, yLike, intV shift], r4)
    else if shape = 14 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xLike, intV y, intV shift], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickInvalidShift r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-does-not-mask-y-type"
        #[intV x, yLike] #[.pushInt (.num shift), qmulmodpow2cInstr], r4)
    else if shape = 16 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInvalidShift r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-does-not-mask-x-type"
        #[xLike, intV y] #[.pushInt (.num shift), qmulmodpow2cInstr], r4)
    else if shape = 17 then
      let (xLike, r2) := pickNonIntLike rng1
      let (yLike, r3) := pickNonIntLike r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-shift-before-y-when-both-non-int"
        #[xLike, yLike, .null], r3)
    else if shape = 18 then
      let (xLike, r2) := pickNonIntLike rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-after-valid-shift"
        #[xLike, yLike, intV shift], r4)
    else if shape = 19 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[.num xOut, .num y, .num shift], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[.num x, .num yOut, .num shift], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[.num x, .num y, .num shiftOut], r4)
    else
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromIntPool #[-1, 0, 1] r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/ok/extreme-times-small" #[intV x, intV y, intV shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulmodpow2cId
  unit := #[
    { name := "/unit/direct/ceil-mod-sign-and-tie-invariants"
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
          expectOkStack s!"/unit/direct/ceil/x={x}/y={y}/shift={shift}"
            (runQmulmodpow2cDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "/unit/direct/shift-zero-and-256-boundaries"
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
          expectOkStack s!"/unit/direct/boundary/x={x}/y={y}/shift={shift}"
            (runQmulmodpow2cDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "/unit/direct/quiet-invalid-shift-and-nan-funnels"
      run := do
        expectOkStack "/unit/quiet/shift-negative"
          (runQmulmodpow2cDirect #[intV 7, intV 3, intV (-1)]) #[.int .nan]
        expectOkStack "/unit/quiet/shift-overmax"
          (runQmulmodpow2cDirect #[intV 7, intV 3, intV 257]) #[.int .nan]
        expectOkStack "/unit/quiet/shift-nan"
          (runQmulmodpow2cDirect #[intV 7, intV 3, .int .nan]) #[.int .nan]
        expectOkStack "/unit/quiet/y-nan"
          (runQmulmodpow2cDirect #[intV 7, .int .nan, intV 1]) #[.int .nan]
        expectOkStack "/unit/quiet/x-nan"
          (runQmulmodpow2cDirect #[.int .nan, intV 7, intV 1]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-pop-and-type-precedence"
      run := do
        expectErr "/unit/error/underflow-empty" (runQmulmodpow2cDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-single-int" (runQmulmodpow2cDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-single-non-int" (runQmulmodpow2cDirect #[.null]) .stkUnd
        expectErr "/unit/error/underflow-two-items-before-y-pop"
          (runQmulmodpow2cDirect #[intV 7, intV 1]) .stkUnd
        expectErr "/unit/error/underflow-before-shift-type-with-two-items"
          (runQmulmodpow2cDirect #[intV 7, .null]) .stkUnd
        expectErr "/unit/error/type-pop-shift-first-null"
          (runQmulmodpow2cDirect #[intV 7, intV 3, .null]) .typeChk
        expectErr "/unit/error/type-pop-shift-first-cell"
          (runQmulmodpow2cDirect #[intV 7, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type-pop-y-second-null"
          (runQmulmodpow2cDirect #[intV 7, .null, intV 1]) .typeChk
        expectErr "/unit/error/type-pop-x-third-null"
          (runQmulmodpow2cDirect #[.null, intV 7, intV 1]) .typeChk
        expectErr "/unit/error/order-pop-shift-before-y-when-both-non-int"
          (runQmulmodpow2cDirect #[.null, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error/order-pop-y-before-x-after-valid-shift"
          (runQmulmodpow2cDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "/unit/error/order-bad-shift-does-not-mask-y-type"
          (runQmulmodpow2cDirect #[intV 7, .null, intV 300]) .typeChk
        expectErr "/unit/error/order-bad-shift-does-not-mask-x-type"
          (runQmulmodpow2cDirect #[.null, intV 7, intV (-1)]) .typeChk
        expectOkStack "/unit/quiet/order-bad-shift-valid-operands"
          (runQmulmodpow2cDirect #[intV 7, intV 3, intV 300]) #[.int .nan] }
    ,
    { name := "/unit/direct/pop-order-top-three-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-cell-valid-shift"
          (runQmulmodpow2cDirect #[.cell Cell.empty, intV 7, intV 3, intV 2])
          #[.cell Cell.empty, intV (-3)]
        expectOkStack "/unit/pop-order/below-null-bad-shift"
          (runQmulmodpow2cDirect #[.null, intV 7, intV 3, intV 300])
          #[.null, .int .nan] }
    ,
    { name := "/unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmulmodpow2cDispatchFallback #[]) #[intV 6154] }
  ]
  oracle := #[
    mkCase "/ok/ceil/pos-pos-shift1" #[intV 7, intV 3, intV 1],
    mkCase "/ok/ceil/pos-pos-shift2" #[intV 7, intV 3, intV 2],
    mkCase "/ok/ceil/neg-pos-shift1" #[intV (-7), intV 3, intV 1],
    mkCase "/ok/ceil/neg-pos-shift2" #[intV (-7), intV 3, intV 2],
    mkCase "/ok/ceil/pos-neg-shift2" #[intV 7, intV (-3), intV 2],
    mkCase "/ok/ceil/neg-neg-shift2" #[intV (-7), intV (-3), intV 2],
    mkCase "/ok/ceil/tie-pos-half-shift1" #[intV 1, intV 1, intV 1],
    mkCase "/ok/ceil/tie-neg-half-shift1" #[intV (-1), intV 1, intV 1],
    mkCase "/ok/ceil/exact-pos" #[intV 42, intV 2, intV 1],
    mkCase "/ok/ceil/exact-neg" #[intV (-42), intV 2, intV 1],
    mkCase "/ok/ceil/pos-small-shift3" #[intV 5, intV 5, intV 3],
    mkCase "/ok/ceil/neg-small-shift3" #[intV (-5), intV 5, intV 3],
    mkCase "/ok/shift0/max-times-one" #[intV maxInt257, intV 1, intV 0],
    mkCase "/ok/shift0/min-times-one" #[intV minInt257, intV 1, intV 0],
    mkCase "/ok/shift0/max-times-zero" #[intV maxInt257, intV 0, intV 0],
    mkCase "/ok/shift0/min-times-zero" #[intV minInt257, intV 0, intV 0],
    mkCase "/ok/boundary/max-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "/ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 1, intV 256],
    mkCase "/ok/boundary/min-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "/ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 1, intV 256],
    mkCase "/ok/boundary/one-shift256" #[intV 1, intV 1, intV 256],
    mkCase "/ok/boundary/minus-one-shift256" #[intV (-1), intV 1, intV 256],
    mkCase "/ok/boundary/max-times-negone-shift256" #[intV maxInt257, intV (-1), intV 256],
    mkShiftInjectedCase "/quiet/invalid-shift-negative-via-program" (intV 7) (intV 3) (.num (-1)),
    mkShiftInjectedCase "/quiet/invalid-shift-overmax-via-program" (intV 7) (intV 3) (.num 257),
    mkShiftInjectedCase "/quiet/invalid-shift-nan-via-program" (intV 7) (intV 3) .nan,
    mkYNanInjectedCase "/quiet/nan-y-via-program" 7 1,
    mkXNanInjectedCase "/quiet/nan-x-via-program" 3 1,
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/single-int" #[intV 1],
    mkCase "/underflow/single-non-int" #[.null],
    mkCase "/underflow/two-items-before-y-pop" #[intV 7, intV 1],
    mkCase "/error-order/underflow-before-bad-shift-via-program" #[intV 7]
      #[.pushInt (.num (-1)), qmulmodpow2cInstr],
    mkCase "/error-order/underflow-before-shift-type-with-two-items" #[intV 7, .null],
    mkCase "/type/pop-shift-first-null" #[intV 7, intV 3, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 7, intV 3, .cell Cell.empty],
    mkCase "/type/pop-y-second-null" #[intV 7, .null, intV 1],
    mkCase "/type/pop-x-third-null" #[.null, intV 7, intV 1],
    mkCase "/error-order/pop-shift-before-y-when-both-non-int" #[.null, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-valid-shift" #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/bad-shift-does-not-mask-y-type" #[intV 7, .null]
      #[.pushInt (.num 300), qmulmodpow2cInstr],
    mkCase "/error-order/bad-shift-does-not-mask-x-type" #[.null, intV 7]
      #[.pushInt (.num (-1)), qmulmodpow2cInstr],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-before-op"
      #[.num (maxInt257 + 1), .num 7, .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-before-op"
      #[.num (minInt257 - 1), .num 7, .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-before-op"
      #[.num 7, .num (maxInt257 + 1), .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-low-before-op"
      #[.num 7, .num (minInt257 - 1), .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-high-before-op"
      #[.num 7, .num 5, .num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-low-before-op"
      #[.num 7, .num 5, .num (minInt257 - 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-all-before-op"
      #[.num (pow2 257), .num (-(pow2 257)), .num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodpow2cSetGasExact), .tonEnvOp .setGasLimit, qmulmodpow2cInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodpow2cSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulmodpow2cInstr]
  ]
  fuzz := #[
    { seed := 2026020852
      count := 700
      gen := genQmulmodpow2cFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULMODPOW2C
