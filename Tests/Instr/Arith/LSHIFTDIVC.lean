import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTDIVC

/-
LSHIFTDIVC branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Ext.lean`
  (the `.arithExt (.shlDivMod 1 1 false false none)` path).
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_shldivmod`, opcode wiring in `register_div_ops`).

Branch/terminal counts used for this suite:
- Lean (`.shlDivMod` generic path): 8 branch sites / 15 terminal outcomes
  (runtime-vs-const shift source; shift range gate; bad-shift NaN branch;
   operand-shape split; divisor-zero split; round-mode validity split; `d` switch;
   NaN single-vs-double push split when `d=3`).
- C++ (`exec_shldivmod`): 7 branch sites / 12 aligned terminal outcomes
  (`y_in_args` split; add-mode remap gate; invalid-opcode guard;
   explicit underflow guard; runtime shift range guard; gv>=13 invalid-int guard;
   `d` switch for DIV/MOD/DIVMOD).

Key risk areas covered:
- runtime pop order and error ordering (`shift`, then divisor, then numerator);
- ceil rounding semantics for mixed signs after left shift;
- shift boundary behavior at `0` and `256`, with range errors outside `[0,256]`;
- NaN / out-of-range literal injection via `PUSHINT` (never via `initStack`);
- signed 257-bit overflow after shift/division (`intOv`);
- deterministic gas boundary (`exact` vs `exact-minus-one`) with `SETGASLIMIT`.
-/

private def lshiftdivcId : InstrId := { name := "LSHIFTDIVC" }

private def lshiftdivcInstr : Instr :=
  .arithExt (.shlDivMod 1 1 false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftdivcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftdivcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInjectedCase
    (name : String)
    (vals : Array IntVal)
    (suffix : Array Instr := #[lshiftdivcInstr]) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ suffix)

private def runLshiftDivcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftdivcInstr stack

private def runLshiftDivcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 2026)) stack

private def lshiftdivcSetGasExact : Int :=
  computeExactGasBudget lshiftdivcInstr

private def lshiftdivcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftdivcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftPositivePool : Array Int :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def smallDenominatorPool : Array Int :=
  #[-7, -3, -2, -1, 1, 2, 3, 7]

private def boundaryNumeratorPool : Array Int :=
  #[maxInt257, minInt257, minInt257 + 1, 1, -1]

private def boundaryDivisorPool : Array Int :=
  #[2, -2, maxInt257, -maxInt257]

private def boundaryShiftPool : Array Int :=
  #[0, 1, 256]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftPositive (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftPositivePool rng

private def pickShiftUpTo256 (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def mkFiniteFuzzCase (shape : Nat) (tag : Nat) (x y shift : Int) : OracleCase :=
  let kind :=
    if shift < 0 || shift > 256 then
      "range"
    else if y = 0 then
      "divzero"
    else
      let shiftNat := shift.toNat
      let tmp := x * intPow2 shiftNat
      let (q, r) := divModRound tmp y 1
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else
        "inexact"
  mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV shift]

private def genLshiftDivCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x0, r3) := pickInt257Boundary rng2
    let (y0, r4) := pickNonZeroInt r3
    let (s0, r5) := pickShiftBoundary r4
    (mkFiniteFuzzCase shape tag x0 y0 s0, r5)
  else if shape = 1 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    let (s0, r5) := pickShiftBoundary r4
    (mkFiniteFuzzCase shape tag x0 y0 s0, r5)
  else if shape = 2 then
    let (x0, r3) := pickInt257Boundary rng2
    let (y0, r4) := pickNonZeroInt r3
    let (s0, r5) := pickShiftUpTo256 r4
    (mkFiniteFuzzCase shape tag x0 y0 s0, r5)
  else if shape = 3 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickFromPool smallDenominatorPool r3
    let (s0, r5) := pickShiftUpTo256 r4
    (mkFiniteFuzzCase shape tag x0 y0 s0, r5)
  else if shape = 4 then
    let (x0, r3) := pickSigned257ish rng2
    let (s0, r4) := pickShiftBoundary r3
    (mkFiniteFuzzCase shape tag x0 0 s0, r4)
  else if shape = 5 then
    let (s0, r3) := pickShiftPositive rng2
    (mkFiniteFuzzCase shape tag maxInt257 1 s0, r3)
  else if shape = 6 then
    let (s0, r3) := pickShiftPositive rng2
    (mkFiniteFuzzCase shape tag minInt257 1 s0, r3)
  else if shape = 7 then
    let (x0, r3) := pickFromPool boundaryNumeratorPool rng2
    let (y0, r4) := pickFromPool boundaryDivisorPool r3
    let (s0, r5) := pickFromPool boundaryShiftPool r4
    (mkFiniteFuzzCase shape tag x0 y0 s0, r5)
  else if shape = 8 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    (mkFiniteFuzzCase shape tag x0 y0 257, r4)
  else if shape = 9 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    (mkFiniteFuzzCase shape tag x0 y0 (-1), r4)
  else if shape = 10 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-shift-{tag}"
      #[IntVal.num x0, IntVal.num y0, IntVal.nan], r4)
  else if shape = 11 then
    let (x0, r3) := pickSigned257ish rng2
    let (s0, r4) := pickShiftBoundary r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-divisor-{tag}"
      #[IntVal.num x0, IntVal.nan, IntVal.num s0], r4)
  else if shape = 12 then
    let (y0, r3) := pickNonZeroInt rng2
    let (s0, r4) := pickShiftBoundary r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-x-{tag}"
      #[IntVal.nan, IntVal.num y0, IntVal.num s0], r4)
  else if shape = 13 then
    let (slot, r3) := randNat rng2 0 2
    let (delta, r4) := randNat r3 1 4096
    let hi := maxInt257 + Int.ofNat delta
    let vals :=
      if slot = 0 then
        #[IntVal.num hi, IntVal.num 1, IntVal.num 1]
      else if slot = 1 then
        #[IntVal.num 1, IntVal.num hi, IntVal.num 1]
      else
        #[IntVal.num 1, IntVal.num 1, IntVal.num hi]
    (mkInjectedCase s!"fuzz/shape-{shape}/out-of-range-high-slot-{slot}-{tag}" vals, r4)
  else if shape = 14 then
    let (slot, r3) := randNat rng2 0 2
    let (delta, r4) := randNat r3 1 4096
    let lo := minInt257 - Int.ofNat delta
    let vals :=
      if slot = 0 then
        #[IntVal.num lo, IntVal.num 1, IntVal.num 1]
      else if slot = 1 then
        #[IntVal.num 1, IntVal.num lo, IntVal.num 1]
      else
        #[IntVal.num 1, IntVal.num 1, IntVal.num lo]
    (mkInjectedCase s!"fuzz/shape-{shape}/out-of-range-low-slot-{slot}-{tag}" vals, r4)
  else if shape = 15 then
    let (x0, r3) := pickFromPool smallNumeratorPool rng2
    let (y0, r4) := pickFromPool smallDenominatorPool r3
    let (s0, r5) := pickShiftBoundary r4
    (mkFiniteFuzzCase shape tag x0 y0 s0, r5)
  else if shape = 16 then
    let (x0, r3) := pickSigned257ish rng2
    let (signPos, r4) := randBool r3
    let y0 := if signPos then 1 else -1
    let (s0, r5) := pickShiftPositive r4
    (mkFiniteFuzzCase shape tag x0 y0 s0, r5)
  else
    let (y0, r3) := pickNonZeroInt rng2
    let (s0, r4) := pickShiftBoundary r3
    (mkFiniteFuzzCase shape tag 0 y0 s0, r4)

def suite : InstrSuite where
  id := lshiftdivcId
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
            (-1, 3, 2, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}"
            (runLshiftDivcDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 2, 1, maxInt257),
            (minInt257, 2, 1, minInt257),
            (minInt257 + 1, 2, 1, minInt257 + 1),
            (1, maxInt257, 256, 2),
            (-1, maxInt257, 256, -1),
            (1, -maxInt257, 256, -1),
            (0, 5, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"boundary/({x}<<{shift})/{y}"
            (runLshiftDivcDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/error-ordering-underflow-range-and-types"
      run := do
        expectErr "underflow/empty" (runLshiftDivcDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runLshiftDivcDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-arg-non-int" (runLshiftDivcDirect #[.null]) .stkUnd
        expectErr "underflow/two-args" (runLshiftDivcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/two-args-shift-non-int" (runLshiftDivcDirect #[intV 1, .null]) .stkUnd
        expectErr "type/shift-top" (runLshiftDivcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/divisor-second" (runLshiftDivcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/x-third" (runLshiftDivcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/range-before-x-type"
          (runLshiftDivcDirect #[.null, intV 5, intV 257]) .rangeChk
        expectErr "error-order/range-before-divisor-type"
          (runLshiftDivcDirect #[intV 1, .null, intV (-1)]) .rangeChk }
    ,
    { name := "unit/direct/intov-divzero-overflow-and-nan"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runLshiftDivcDirect #[intV 5, intV 0, intV 1]) .intOv
        expectErr "overflow/max-shift1-div1"
          (runLshiftDivcDirect #[intV maxInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-shift1-div1"
          (runLshiftDivcDirect #[intV minInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-div-neg-one-shift0"
          (runLshiftDivcDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "overflow/one-shift256-div1"
          (runLshiftDivcDirect #[intV 1, intV 1, intV 256]) .intOv
        expectErr "range/nan-shift"
          (runLshiftDivcDirect #[intV 5, intV 3, .int .nan]) .rangeChk
        expectErr "intov/nan-divisor"
          (runLshiftDivcDirect #[intV 5, .int .nan, intV 1]) .intOv
        expectErr "intov/nan-x"
          (runLshiftDivcDirect #[.int .nan, intV 3, intV 1]) .intOv }
    ,
    { name := "unit/dispatch/non-shldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLshiftDivcDispatchFallback #[]) #[intV 2026] }
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
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/two-args-shift-non-int-underflow-before-type" #[intV 1, .null],
    mkCase "type/shift-top-null" #[intV 1, intV 2, .null],
    mkCase "type/divisor-second-null" #[intV 1, .null, intV 2],
    mkCase "type/x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/range-before-x-type" #[.null, intV 5, intV 257],
    mkCase "error-order/range-before-divisor-type" #[intV 1, .null, intV (-1)],
    mkCase "range/shift-negative" #[intV 5, intV 3, intV (-1)],
    mkCase "range/shift-257" #[intV 5, intV 3, intV 257],
    mkInjectedCase "range/shift-nan-via-program"
      #[IntVal.num 5, IntVal.num 3, IntVal.nan],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0, intV 1],
    mkCase "overflow/max-shift1-div1" #[intV maxInt257, intV 1, intV 1],
    mkCase "overflow/min-shift1-div1" #[intV minInt257, intV 1, intV 1],
    mkCase "overflow/min-div-neg-one-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "overflow/one-shift256-div1" #[intV 1, intV 1, intV 256],
    mkInjectedCase "nan/divisor-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkInjectedCase "nan/x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkInjectedCase "error-order/pushint-out-of-range-high-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (maxInt257 + 1)],
    mkInjectedCase "error-order/pushint-out-of-range-low-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftdivcSetGasExact), .tonEnvOp .setGasLimit, lshiftdivcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftdivcSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftdivcInstr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 700
      gen := genLshiftDivCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTDIVC
