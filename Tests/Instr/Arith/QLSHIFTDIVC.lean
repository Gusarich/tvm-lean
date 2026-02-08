import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTDIVC

/-
QLSHIFTDIVC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shlDivMod 1 1 false true none)` path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, arity/type/quiet-NaN funnels)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, quiet runtime-shift arm)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite (QLSHIFTDIVC specialization):
- Lean: 8 branch sites / 11 terminal outcomes
  (dispatch/fallback; arity precheck; shift pop type; bad-shift split;
   divisor pop type; numerator pop type; numeric-vs-NaN split;
   quiet push finite-vs-NaN split).
- C++: 7 branch sites / 10 aligned terminal outcomes
  (`check_underflow(3)`; shift pop/type + range split in quiet mode;
   divisor/numerator pop type gates; divisor-zero split;
   numeric-vs-NaN split; `push_int_quiet` finite-vs-NaN).

Key risk areas covered:
- ceil rounding after left shift for mixed signs and near-zero fractions;
- quiet behavior for invalid runtime shift (`<0`, `>256`, NaN shift) and divisor-zero;
- strict pop/error ordering (`shift`, then divisor, then numerator) even on bad shift;
- signed-257 overflow after shift/division must quiet to NaN (not throw);
- oracle serialization constraints: NaN/out-of-range values injected via program only;
- deterministic gas boundary (`SETGASLIMIT` exact and exact-minus-one).
-/

private def qlshiftdivcId : InstrId := { name := "QLSHIFTDIVC" }

private def qlshiftdivcInstr : Instr :=
  .arithExt (.shlDivMod 1 1 false true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftdivcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftdivcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x y shift : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x, y, shift]
  mkCase name (below ++ stack) (programPrefix.push qlshiftdivcInstr) gasLimits fuel

private def runQlshiftdivcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftdivcInstr stack

private def runQlshiftdivcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 2506)) stack

private def qlshiftdivcSetGasExact : Int :=
  computeExactGasBudget qlshiftdivcInstr

private def qlshiftdivcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftdivcInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-7, -3, -1, 257, 258, 300, 511]

private def smallNumeratorPool : Array Int :=
  #[-17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17]

private def smallDivisorPool : Array Int :=
  #[-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]

private def boundaryNumeratorPool : Array Int :=
  #[maxInt257, maxInt257 - 1, minInt257, minInt257 + 1, 1, -1, 0]

private def boundaryDivisorPool : Array Int :=
  #[maxInt257, -maxInt257, 2, -2, 1, -1]

private def boundaryShiftPool : Array Int :=
  #[0, 1, 255, 256]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftUpTo256 (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (useCell, rng') := randBool rng
  (if useCell then .cell Cell.empty else .null, rng')

private def classifyQlshiftdivc (x y shift : Int) : String :=
  if shift < 0 || shift > 256 then
    "quiet-range"
  else if y = 0 then
    "quiet-divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat
    let (q, r) := divModRound tmp y 1
    if !intFitsSigned257 q then
      "quiet-overflow"
    else if r = 0 then
      "ok-exact"
    else
      "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (tag : Nat) (x y shift : Int) : OracleCase :=
  let kind := classifyQlshiftdivc x y shift
  mkCase s!"fuzz/shape-{shape}/{kind}/{tag}" #[intV x, intV y, intV shift]

private def genQlshiftdivcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, r3) := pickInt257Boundary rng2
    let (y, r4) := pickNonZeroInt r3
    let (shift, r5) := pickShiftBoundary r4
    (mkFiniteFuzzCase shape tag x y shift, r5)
  else if shape = 1 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickNonZeroInt r3
    let (shift, r5) := pickShiftBoundary r4
    (mkFiniteFuzzCase shape tag x y shift, r5)
  else if shape = 2 then
    let (x, r3) := pickInt257Boundary rng2
    let (y, r4) := pickFromPool smallDivisorPool r3
    let (shift, r5) := pickShiftUpTo256 r4
    (mkFiniteFuzzCase shape tag x y shift, r5)
  else if shape = 3 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickFromPool smallDivisorPool r3
    let (shift, r5) := pickShiftUpTo256 r4
    (mkFiniteFuzzCase shape tag x y shift, r5)
  else if shape = 4 then
    let (x, r3) := pickSigned257ish rng2
    let (shift, r4) := pickShiftBoundary r3
    (mkFiniteFuzzCase shape tag x 0 shift, r4)
  else if shape = 5 then
    let (shift, r3) := pickFromPool #[1, 2, 3, 7, 8, 16, 64, 128, 255, 256] rng2
    (mkFiniteFuzzCase shape tag maxInt257 1 shift, r3)
  else if shape = 6 then
    let (shift, r3) := pickFromPool #[1, 2, 3, 7, 8, 16, 64, 128, 255, 256] rng2
    (mkFiniteFuzzCase shape tag minInt257 1 shift, r3)
  else if shape = 7 then
    let (x, r3) := pickFromPool boundaryNumeratorPool rng2
    let (y, r4) := pickFromPool boundaryDivisorPool r3
    let (shift, r5) := pickFromPool boundaryShiftPool r4
    (mkFiniteFuzzCase shape tag x y shift, r5)
  else if shape = 8 then
    let (x, r3) := pickFromPool smallNumeratorPool rng2
    let (y, r4) := pickFromPool smallDivisorPool r3
    let (shift, r5) := pickShiftBoundary r4
    (mkFiniteFuzzCase shape tag x y shift, r5)
  else if shape = 9 then
    (mkCase s!"fuzz/shape-{shape}/underflow/empty/{tag}" #[], rng2)
  else if shape = 10 then
    let (x, r3) := pickSigned257ish rng2
    (mkCase s!"fuzz/shape-{shape}/underflow/one-int/{tag}" #[intV x], r3)
  else if shape = 11 then
    let (v, r3) := pickNonInt rng2
    (mkCase s!"fuzz/shape-{shape}/underflow/one-non-int/{tag}" #[v], r3)
  else if shape = 12 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickSigned257ish r3
    let (sLike, r5) := pickNonInt r4
    (mkCase s!"fuzz/shape-{shape}/type/shift-top/{tag}" #[intV x, intV y, sLike], r5)
  else if shape = 13 then
    let (x, r3) := pickSigned257ish rng2
    let (shift, r4) := pickShiftUpTo256 r3
    let (yLike, r5) := pickNonInt r4
    (mkCase s!"fuzz/shape-{shape}/type/divisor-second/{tag}" #[intV x, yLike, intV shift], r5)
  else if shape = 14 then
    let (y, r3) := pickNonZeroInt rng2
    let (shift, r4) := pickShiftUpTo256 r3
    let (xLike, r5) := pickNonInt r4
    (mkCase s!"fuzz/shape-{shape}/type/x-third/{tag}" #[xLike, intV y, intV shift], r5)
  else if shape = 15 then
    let (x, r3) := pickSigned257ish rng2
    let (shift, r4) := pickFromPool shiftInvalidPool r3
    (mkCase s!"fuzz/shape-{shape}/quiet/bad-shift-invalid/{tag}" #[intV x, intV 3, intV shift], r4)
  else if shape = 16 then
    let (x, r3) := pickSigned257ish rng2
    (mkCase s!"fuzz/shape-{shape}/error-order/type-divisor-before-quiet-bad-shift/{tag}"
      #[intV x, .null, intV (-1)], r3)
  else if shape = 17 then
    let (y, r3) := pickNonZeroInt rng2
    (mkCase s!"fuzz/shape-{shape}/error-order/type-x-before-quiet-bad-shift/{tag}"
      #[.null, intV y, intV 257], r3)
  else if shape = 18 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickNonZeroInt r3
    (mkInputCase s!"fuzz/shape-{shape}/quiet/bad-shift-nan-via-program/{tag}"
      (.num x) (.num y) .nan, r4)
  else if shape = 19 then
    let (x, r3) := pickSigned257ish rng2
    let (shift, r4) := pickShiftUpTo256 r3
    (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-divisor-via-program/{tag}"
      (.num x) .nan (.num shift), r4)
  else if shape = 20 then
    let (y, r3) := pickNonZeroInt rng2
    let (shift, r4) := pickShiftUpTo256 r3
    (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-x-via-program/{tag}"
      .nan (.num y) (.num shift), r4)
  else if shape = 21 then
    let (x, r3) := pickInt257OutOfRange rng2
    let (y, r4) := pickNonZeroInt r3
    let (shift, r5) := pickShiftUpTo256 r4
    (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op/{tag}"
      (.num x) (.num y) (.num shift), r5)
  else if shape = 22 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickInt257OutOfRange r3
    let (shift, r5) := pickShiftUpTo256 r4
    (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op/{tag}"
      (.num x) (.num y) (.num shift), r5)
  else if shape = 23 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickNonZeroInt r3
    let (shift, r5) := pickInt257OutOfRange r4
    (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op/{tag}"
      (.num x) (.num y) (.num shift), r5)
  else if shape = 24 then
    let (x, r3) := pickInt257OutOfRange rng2
    let (y, r4) := pickInt257OutOfRange r3
    (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op/{tag}"
      (.num x) (.num y) (.num 1), r4)
  else if shape = 25 then
    let (x, r3) := pickSigned257ish rng2
    (mkCase s!"fuzz/shape-{shape}/underflow/one-arg-pushnan-shift/{tag}"
      #[intV x] #[.pushInt .nan, qlshiftdivcInstr], r3)
  else
    let (x, r3) := pickSigned257ish rng2
    (mkCase s!"fuzz/shape-{shape}/error-order/type-divisor-before-quiet-bad-shift-nan/{tag}"
      #[intV x, .null] #[.pushInt .nan, qlshiftdivcInstr], r3)

def suite : InstrSuite where
  id := qlshiftdivcId
  unit := #[
    { name := "unit/direct/ceil-rounding-sign-and-shift-cases"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 5),
            (-7, 3, 1, -4),
            (7, -3, 1, -4),
            (-7, -3, 1, 5),
            (-1, 3, 1, 0),
            (1, -3, 1, 0),
            (5, 2, 0, 3),
            (-5, 2, 0, -2),
            (5, -2, 0, -2),
            (-5, -2, 0, 3),
            (9, 3, 2, 12),
            (1, 3, 2, 2),
            (-1, 3, 2, -1),
            (0, 5, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}"
            (runQlshiftdivcDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 2, 1, maxInt257),
            (minInt257, 2, 1, minInt257),
            (minInt257 + 1, 2, 1, minInt257 + 1),
            (1, maxInt257, 256, 2),
            (-1, maxInt257, 256, -1),
            (1, -maxInt257, 256, -1),
            (0, -5, 200, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"boundary/({x}<<{shift})/{y}"
            (runQlshiftdivcDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-funnels"
      run := do
        expectOkStack "quiet/divzero"
          (runQlshiftdivcDirect #[intV 5, intV 0, intV 1]) #[.int .nan]
        expectOkStack "quiet/overflow-max"
          (runQlshiftdivcDirect #[intV maxInt257, intV 1, intV 1]) #[.int .nan]
        expectOkStack "quiet/overflow-min"
          (runQlshiftdivcDirect #[intV minInt257, intV 1, intV 1]) #[.int .nan]
        expectOkStack "quiet/overflow-shift256"
          (runQlshiftdivcDirect #[intV 1, intV 1, intV 256]) #[.int .nan]
        expectOkStack "quiet/range-negative"
          (runQlshiftdivcDirect #[intV 5, intV 3, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/range-overmax"
          (runQlshiftdivcDirect #[intV 5, intV 3, intV 257]) #[.int .nan]
        expectOkStack "quiet/range-nan-shift"
          (runQlshiftdivcDirect #[intV 5, intV 3, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan-divisor"
          (runQlshiftdivcDirect #[intV 5, .int .nan, intV 1]) #[.int .nan]
        expectOkStack "quiet/nan-x"
          (runQlshiftdivcDirect #[.int .nan, intV 3, intV 1]) #[.int .nan]
        expectOkStack "quiet/out-of-range-x-direct"
          (runQlshiftdivcDirect #[intV (maxInt257 + 1), intV 1, intV 0]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-bad-shift-precedence"
      run := do
        expectErr "underflow/empty" (runQlshiftdivcDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQlshiftdivcDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQlshiftdivcDirect #[.null]) .stkUnd
        expectErr "underflow/two-args" (runQlshiftdivcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/two-args-top-non-int" (runQlshiftdivcDirect #[intV 1, .null]) .stkUnd
        expectErr "type/shift-top-null" (runQlshiftdivcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/shift-top-cell" (runQlshiftdivcDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "type/divisor-second" (runQlshiftdivcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/x-third" (runQlshiftdivcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/type-divisor-before-quiet-bad-shift"
          (runQlshiftdivcDirect #[intV 1, .null, intV (-1)]) .typeChk
        expectErr "error-order/type-x-before-quiet-bad-shift"
          (runQlshiftdivcDirect #[.null, intV 1, intV 257]) .typeChk }
    ,
    { name := "unit/dispatch/non-shldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQlshiftdivcDispatchFallback #[]) #[intV 2506] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-shift1" #[intV 7, intV 3, intV 1],
    mkCase "ok/ceil/sign/neg-pos-shift1" #[intV (-7), intV 3, intV 1],
    mkCase "ok/ceil/sign/pos-neg-shift1" #[intV 7, intV (-3), intV 1],
    mkCase "ok/ceil/sign/neg-neg-shift1" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/ceil/sign/neg-pos-near-zero" #[intV (-1), intV 3, intV 1],
    mkCase "ok/ceil/sign/pos-neg-near-zero" #[intV 1, intV (-3), intV 1],
    mkCase "ok/ceil/shift0-reduces-to-divc" #[intV 5, intV 2, intV 0],
    mkCase "ok/ceil/shift2-inexact" #[intV 1, intV 3, intV 2],
    mkCase "ok/ceil/shift2-negative" #[intV (-1), intV 3, intV 2],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 5, intV 200],
    mkCase "ok/boundary/max-shift1-div2" #[intV maxInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-shift1-div2" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-plus-one-shift1-div2" #[intV (minInt257 + 1), intV 2, intV 1],
    mkCase "ok/boundary/one-shift256-div-max" #[intV 1, intV maxInt257, intV 256],
    mkCase "ok/boundary/neg-one-shift256-div-max" #[intV (-1), intV maxInt257, intV 256],
    mkCase "ok/boundary/one-shift256-div-neg-max" #[intV 1, intV (-maxInt257), intV 256],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0, intV 1],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 200],
    mkCase "quiet/overflow/max-shift1-div1" #[intV maxInt257, intV 1, intV 1],
    mkCase "quiet/overflow/min-shift1-div1" #[intV minInt257, intV 1, intV 1],
    mkCase "quiet/overflow/one-shift256-div1" #[intV 1, intV 1, intV 256],
    mkCase "quiet/bad-shift-negative" #[intV 5, intV 3, intV (-1)],
    mkCase "quiet/bad-shift-overmax" #[intV 5, intV 3, intV 257],
    mkInputCase "quiet/bad-shift-nan-via-program" (.num 5) (.num 3) .nan,
    mkInputCase "quiet/nan-divisor-via-program" (.num 5) .nan (.num 1),
    mkInputCase "quiet/nan-x-via-program" .nan (.num 5) (.num 1),
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/two-args-shift-non-int-underflow-before-type" #[intV 1, .null],
    mkCase "underflow/one-arg-pushnan-shift-underflow-first" #[intV 1]
      #[.pushInt .nan, qlshiftdivcInstr],
    mkCase "type/shift-top-null" #[intV 1, intV 2, .null],
    mkCase "type/shift-top-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/divisor-second-null" #[intV 1, .null, intV 2],
    mkCase "type/x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/type-divisor-before-quiet-bad-shift-neg" #[intV 1, .null, intV (-1)],
    mkCase "error-order/type-x-before-quiet-bad-shift-overmax" #[.null, intV 1, intV 257],
    mkCase "error-order/type-shift-before-any-pop" #[.null, intV 1, .cell Cell.empty],
    mkCase "error-order/type-divisor-before-quiet-bad-shift-nan-via-program" #[intV 1, .null]
      #[.pushInt .nan, qlshiftdivcInstr],
    mkInputCase "error-order/pushint-overflow-x-high-before-op"
      (.num (maxInt257 + 1)) (.num 1) (.num 1),
    mkInputCase "error-order/pushint-overflow-x-low-before-op"
      (.num (minInt257 - 1)) (.num 1) (.num 1),
    mkInputCase "error-order/pushint-overflow-y-high-before-op"
      (.num 1) (.num (maxInt257 + 1)) (.num 1),
    mkInputCase "error-order/pushint-overflow-y-low-before-op"
      (.num 1) (.num (minInt257 - 1)) (.num 1),
    mkInputCase "error-order/pushint-overflow-shift-high-before-op"
      (.num 1) (.num 1) (.num (maxInt257 + 1)),
    mkInputCase "error-order/pushint-overflow-shift-low-before-op"
      (.num 1) (.num 1) (.num (minInt257 - 1)),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftdivcSetGasExact), .tonEnvOp .setGasLimit, qlshiftdivcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftdivcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftdivcInstr]
  ]
  fuzz := #[
    { seed := 2026020844
      count := 700
      gen := genQlshiftdivcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTDIVC
