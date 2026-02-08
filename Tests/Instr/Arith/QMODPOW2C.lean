import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMODPOW2C

/-
QMODPOW2C branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false false 2 1 true none)` path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popNatUpTo`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean` (`modPow2Round`, `rshiftPow2Round`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (QMODPOW2C specialization): 7 branch points / 9 terminal outcomes
  (dispatch/fallback; stack-depth underflow guard; shift pop type/range/success;
   x pop type/success; finite-vs-NaN split; `shift = 0` floor override;
   quiet push path for numeric vs NaN result).
- C++ (`exec_shrmod`, quiet mode, `d=2`, `round_mode=+1`): 7 branch points / 9 aligned outcomes
  (invalid-op guard; underflow check; `pop_smallint_range(256)` type/range/success;
   `y = 0` round override; `pop_int` type/success; finite-vs-invalid x split;
   quiet `push_int_quiet` result path).

Lean/C++ outcome mapping used for this suite:
- `stkUnd`: stack precheck before any pop (`check_underflow(2)` / `need = 2`);
- `typeChk`: shift pop type first, then x-pop type after successful shift pop;
- `rangeChk`: runtime shift range is strict `[0, 256]` even in quiet mode;
- success finite: ceil-mod remainder `x - ceil(x / 2^y) * 2^y`;
- success NaN: quiet funnel for NaN `x` (program-injected in oracle);
- `shift = 0`: runtime override to floor mode (remainder forced to `0`);
- gas cliff: exact gas passes; exact-minus-one yields out-of-gas.

Key risk areas covered:
- ceil-mod sign/tie behavior and power boundaries (`shift = 0`, `256`);
- pop/error ordering (`shift` before `x`, range before `x` type);
- quiet-vs-strict split (quiet NaN result for invalid `x`, strict shift range errors);
- oracle safety: NaN/out-of-range values injected via program only.
-/

private def qmodpow2cId : InstrId := { name := "QMODPOW2C" }

private def qmodpow2cInstr : Instr :=
  .arithExt (.shrMod false false 2 1 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmodpow2cInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmodpow2cId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qmodpow2cInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programTail) gasLimits fuel

private def runQmodpow2cDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmodpow2cInstr stack

private def runQmodpow2cDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9223)) stack

private def qmodpow2cSetGasExact : Int :=
  computeExactGasBudget qmodpow2cInstr

private def qmodpow2cSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmodpow2cInstr

private def mkShiftInjectedCase (name : String) (x : Value) (shift : IntVal) : OracleCase :=
  mkCase name #[x] #[.pushInt shift, qmodpow2cInstr]

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftNegativePool : Array Int :=
  #[-3, -2, -1]

private def shiftOverMaxPool : Array Int :=
  #[257, 258, 300, 511]

private def qmodpow2cOutOfRangeXPool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

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

private def pickOutOfRangeX (rng : StdGen) : Int × StdGen :=
  pickFromIntPool qmodpow2cOutOfRangeXPool rng

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def genQmodpow2cFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-shift" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-inrange-shift" #[intV x, intV shift], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-shift-zero-floor-override" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-shift-256-boundary" #[intV x, intV 256], r2)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickNegativeShift r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-negative-via-program" (intV x) (.num shift), r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickOverMaxShift r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-overmax-via-program" (intV x) (.num shift), r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" (intV x) .nan, r2)
    else if shape = 7 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-x-via-program" #[.nan, .num shift], r2)
    else if shape = 8 then
      let (x, r2) := pickOutOfRangeX rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-out-of-range-x-high-via-program"
        #[.num x, .num shift], r3)
    else if shape = 9 then
      let (x, r2) := pickOutOfRangeX rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-out-of-range-x-shift256-via-program"
        #[.num x, .num 256], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-int" #[intV x], r2)
    else if shape = 12 then
      let (v, r2) := pickNonIntLike rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int" #[v], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftLike, r3) := pickNonIntLike r2
      (mkCase s!"fuzz/shape-{shape}/type-shift-non-int" #[intV x, shiftLike], r3)
    else if shape = 14 then
      let (shift, r2) := pickShiftInRange rng1
      let (xLike, r3) := pickNonIntLike r2
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, intV shift], r3)
    else if shape = 15 then
      let (xLike, r2) := pickNonIntLike rng1
      let (pickNeg, r3) := randBool r2
      let (shift, r4) :=
        if pickNeg then pickNegativeShift r3 else pickOverMaxShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order-range-before-x-type-via-program"
        xLike (.num shift), r4)
    else
      let (xLike, r2) := pickNonIntLike rng1
      let (shiftLike, r3) := pickNonIntLike r2
      (mkCase s!"fuzz/shape-{shape}/error-order-shift-type-before-x-pop"
        #[xLike, shiftLike], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmodpow2cId
  unit := #[
    { name := "unit/direct/ceil-mod-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 1, -1),
            (7, 2, -1),
            (9, 2, -3),
            (-7, 1, -1),
            (-7, 2, -3),
            (-9, 2, -1),
            (1, 1, -1),
            (-1, 1, -1),
            (42, 1, 0),
            (-42, 1, 0),
            (5, 3, -3),
            (-5, 3, -5)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%2^{shift}"
            (runQmodpow2cDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/shift-zero-and-256-power-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 0, 0),
            (minInt257, 0, 0),
            (maxInt257, 256, -1),
            (maxInt257 - 1, 256, -2),
            (minInt257, 256, 0),
            (minInt257 + 1, 256, minInt257 + 1),
            (0, 256, 0),
            (1, 256, minInt257 + 1),
            (-1, 256, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"boundary/{x}%2^{shift}"
            (runQmodpow2cDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-and-out-of-range-x-paths"
      run := do
        expectOkStack "quiet/nan-x"
          (runQmodpow2cDirect #[.int .nan, intV 3]) #[.int .nan]
        expectOkStack "quiet/out-of-range-x-high-shift256"
          (runQmodpow2cDirect #[intV (pow2 257), intV 256]) #[intV 0]
        expectOkStack "quiet/out-of-range-x-low-shift256"
          (runQmodpow2cDirect #[intV (minInt257 - 1), intV 256]) #[intV (-1)]
        expectOkStack "quiet/out-of-range-x-odd-shift1"
          (runQmodpow2cDirect #[intV (maxInt257 + 2), intV 1]) #[intV (-1)] }
    ,
    { name := "unit/error/underflow-pop-order-and-range-type-ordering"
      run := do
        expectErr "underflow/empty" (runQmodpow2cDirect #[]) .stkUnd
        expectErr "underflow/single-int" (runQmodpow2cDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runQmodpow2cDirect #[.null]) .stkUnd
        expectErr "type/pop-shift-first"
          (runQmodpow2cDirect #[intV 7, .null]) .typeChk
        expectErr "type/pop-x-second"
          (runQmodpow2cDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/pop-shift-before-x-when-both-non-int"
          (runQmodpow2cDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "range/shift-negative"
          (runQmodpow2cDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax"
          (runQmodpow2cDirect #[intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan"
          (runQmodpow2cDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "error-order/shift-range-before-x-type-negative"
          (runQmodpow2cDirect #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/shift-range-before-x-type-overmax"
          (runQmodpow2cDirect #[.cell Cell.empty, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQmodpow2cDispatchFallback #[]) #[intV 9223] }
  ]
  oracle := #[
    mkCase "ok/ceil/pos-shift1" #[intV 7, intV 1],
    mkCase "ok/ceil/pos-shift2" #[intV 7, intV 2],
    mkCase "ok/ceil/neg-shift1" #[intV (-7), intV 1],
    mkCase "ok/ceil/neg-shift2" #[intV (-7), intV 2],
    mkCase "ok/ceil/tie-pos-half" #[intV 1, intV 1],
    mkCase "ok/ceil/tie-neg-half" #[intV (-1), intV 1],
    mkCase "ok/ceil/exact-pos" #[intV 42, intV 1],
    mkCase "ok/ceil/exact-neg" #[intV (-42), intV 1],
    mkCase "ok/shift-zero/max" #[intV maxInt257, intV 0],
    mkCase "ok/shift-zero/min" #[intV minInt257, intV 0],
    mkCase "ok/shift-zero/arbitrary" #[intV 12345, intV 0],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/one-shift256" #[intV 1, intV 256],
    mkCase "ok/boundary/minus-one-shift256" #[intV (-1), intV 256],
    mkShiftInjectedCase "range/shift-negative-via-program" (intV 7) (.num (-1)),
    mkShiftInjectedCase "range/shift-overmax-via-program" (intV 7) (.num 257),
    mkShiftInjectedCase "range/shift-nan-via-program" (intV 7) .nan,
    mkCaseFromIntVals "quiet/nan-x-via-program" #[.nan, .num 3],
    mkCaseFromIntVals "quiet/out-of-range-x-high-via-program"
      #[.num (maxInt257 + 1), .num 256],
    mkCaseFromIntVals "quiet/out-of-range-x-low-via-program"
      #[.num (minInt257 - 1), .num 256],
    mkCaseFromIntVals "quiet/out-of-range-x-odd-via-program"
      #[.num (maxInt257 + 2), .num 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/single-int" #[intV 1],
    mkCase "underflow/single-non-int" #[.null],
    mkCase "type/shift-top-null" #[intV 5, .null],
    mkCase "type/x-second-null" #[.null, intV 1],
    mkCase "type/shift-top-cell" #[intV 5, .cell Cell.empty],
    mkCase "type/x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/pop-shift-before-x-when-both-non-int"
      #[.cell Cell.empty, .null],
    mkShiftInjectedCase "error-order/shift-range-before-x-type-negative-via-program"
      .null (.num (-1)),
    mkShiftInjectedCase "error-order/shift-range-before-x-type-overmax-via-program"
      (.cell Cell.empty) (.num 257),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qmodpow2cSetGasExact), .tonEnvOp .setGasLimit, qmodpow2cInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qmodpow2cSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmodpow2cInstr]
  ]
  fuzz := #[
    { seed := 2026020832
      count := 700
      gen := genQmodpow2cFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMODPOW2C
