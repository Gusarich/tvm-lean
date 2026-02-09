import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTDIVMOD

/-
LSHIFTDIVMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shlDivMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xa9cc..0xa9ce` decode to `.arithExt (.shlDivMod 3 ... false none)`).
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`).

Branch counts used for this suite:
- Lean (`.shlDivMod` generic path): 9 branch sites / 17 terminal outcomes
  (runtime-vs-immediate shift source; stack pre-underflow guard; shift-range gate;
   add-mode pop path; bad-shift NaN fanout; operand numeric-vs-NaN split;
   divisor-zero split; round-mode validity split; `d` switch with non-num fanout).
- C++ (`exec_shldivmod`, mode=0): 7 branch sites / 13 terminal outcomes
  (d/add remap + invalid-op guard; underflow guard; runtime shift pop/range gate;
   global-version fallback gate; add-vs-non-add split; `d` switch; push funnel).

LSHIFTDIVMOD specialization:
- fixed params: `d=3`, `roundMode=-1`, `addMode=false`, `quiet=false`, runtime shift.

Key risk areas covered:
- strict pop/error order (`shift`, then `y`, then `x`) and short-stack underflow precedence;
- shift range boundaries (`0..256`) vs later type checks (`rangeChk` precedence when arity suffices);
- floor quotient/remainder sign invariants on shifted numerators;
- signed-257 overflow from large shifted numerators;
- NaN / out-of-range integer injection via program only (`PUSHINT`), not via `initStack`;
- exact gas boundary (`SETGASLIMIT`) and exact-minus-one out-of-gas behavior.
-/

private def lshiftdivmodId : InstrId := { name := "LSHIFTDIVMOD" }

private def lshiftdivmodInstr : Instr :=
  .arithExt (.shlDivMod 3 (-1) false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftdivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftdivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[lshiftdivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runLshiftdivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftdivmodInstr stack

private def runLshiftdivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5150)) stack

private def lshiftdivmodSetGasExact : Int :=
  computeExactGasBudget lshiftdivmodInstr

private def lshiftdivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftdivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-3, -2, -1, 257, 258, 512]

private def outOfRangePool : Array Int :=
  #[pow2 256, pow2 256 + 1, -(pow2 256) - 1]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftValidMixed (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    let (shiftNat, rng2) := randNat rng1 0 256
    (Int.ofNat shiftNat, rng2)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def pickOutOfRangeInt (rng : StdGen) : Int × StdGen :=
  pickFromPool outOfRangePool rng

private def genLshiftdivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftValidMixed r3
      (mkCase s!"fuzz/shape-{shape}/ok-random" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok-shift-zero" #[intV x, intV y, intV 0], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftValidMixed r2
      (mkCase s!"fuzz/shape-{shape}/divzero" #[intV x, intV 0, intV shift], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/overflow-high" #[intV maxInt257, intV 1, intV 1], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/overflow-low" #[intV minInt257, intV 1, intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (shift, r2) := pickShiftValidMixed rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-arg" #[intV shift], r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftValidMixed r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two-args" #[intV x, intV shift], r3)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/regression-underflow-before-range-one-arg" #[intV 257], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/regression-underflow-before-range-two-args"
        #[intV x, intV 257], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type-shift-first" #[intV x, intV y, shiftLike], r4)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftValidMixed r3
      (mkCase s!"fuzz/shape-{shape}/type-y-second" #[intV x, yLike, intV shift], r4)
    else if shape = 13 then
      let (xLike, r2) := pickNonInt rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftValidMixed r3
      (mkCase s!"fuzz/shape-{shape}/type-x-third" #[xLike, intV y, intV shift], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickFromPool shiftInvalidPool r3
      (mkCase s!"fuzz/shape-{shape}/range-invalid-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (valsPos, r3) := randNat r2 0 2
      let vals : Array IntVal :=
        if valsPos = 0 then
          #[.num x, .num 5, .nan]
        else if valsPos = 1 then
          #[.num x, .nan, .num 1]
        else
          #[.nan, .num 5, .num 1]
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-via-program-pos-{valsPos}" vals, r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (huge, r4) := pickOutOfRangeInt r3
      let (pos, r5) := randNat r4 0 2
      let vals : Array IntVal :=
        if pos = 0 then
          #[.num huge, .num y, .num 1]
        else if pos = 1 then
          #[.num x, .num huge, .num 1]
        else
          #[.num x, .num y, .num huge]
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/out-of-range-via-program-pos-{pos}" vals, r5)
    else
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-y-type"
        #[intV x, .null, intV 257], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftdivmodId
  unit := #[
    { name := "unit/direct/floor-sign-shift-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (13, 3, 2, 17, 1),
            (-13, 3, 1, -9, 1),
            (13, -3, 2, -18, -2),
            (-13, -3, 2, 17, -1),
            (7, 3, 0, 2, 1),
            (-7, 3, 0, -3, 2),
            (7, -3, 0, -3, -2),
            (-7, -3, 0, 2, -1),
            (1, 5, 8, 51, 1),
            (0, 3, 256, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}" (runLshiftdivmodDirect #[intV x, intV y, intV shift])
            #[intV q, intV r] }
    ,
    { name := "unit/direct/boundary-successes-at-shift-0-and-256"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257, 0),
            (minInt257, 1, 0, minInt257, 0),
            (minInt257 + 1, -1, 0, maxInt257, 0),
            (1, maxInt257, 256, 1, 1),
            (-1, maxInt257, 256, -2, maxInt257 - 1),
            (maxInt257, 2, 1, maxInt257, 0),
            (minInt257, 2, 1, minInt257, 0),
            (minInt257 + 1, 2, 1, minInt257 + 1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}" (runLshiftdivmodDirect #[intV x, intV y, intV shift])
            #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-overflow-range-and-ordering"
      run := do
        expectErr "divzero/nonzero-over-zero" (runLshiftdivmodDirect #[intV 5, intV 0, intV 1]) .intOv
        expectErr "overflow/max-shift1-div1" (runLshiftdivmodDirect #[intV maxInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-shift1-div1" (runLshiftdivmodDirect #[intV minInt257, intV 1, intV 1]) .intOv
        expectErr "range/negative-shift" (runLshiftdivmodDirect #[intV 5, intV 3, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runLshiftdivmodDirect #[intV 5, intV 3, intV 257]) .rangeChk
        expectErr "error-order/range-before-y-type"
          (runLshiftdivmodDirect #[intV 5, .null, intV 257]) .rangeChk
        expectErr "error-order/range-before-x-type"
          (runLshiftdivmodDirect #[.null, intV 3, intV 257]) .rangeChk }
    ,
    { name := "unit/error/underflow-and-type-pop-ordering"
      run := do
        expectErr "underflow/empty" (runLshiftdivmodDirect #[]) .stkUnd
        expectErr "underflow/one-arg-valid-shift" (runLshiftdivmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runLshiftdivmodDirect #[intV 5, intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-first" (runLshiftdivmodDirect #[.null]) .stkUnd
        expectErr "regression/underflow-before-range-one-arg-bad-shift"
          (runLshiftdivmodDirect #[intV 257]) .stkUnd
        expectErr "regression/underflow-before-range-two-args-bad-shift"
          (runLshiftdivmodDirect #[intV 5, intV 257]) .stkUnd
        expectErr "type/pop-shift-first-null" (runLshiftdivmodDirect #[intV 5, intV 3, .null]) .typeChk
        expectErr "type/pop-y-second-null" (runLshiftdivmodDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/pop-x-third-null" (runLshiftdivmodDirect #[.null, intV 3, intV 1]) .typeChk
        expectErr "error-order/shift-type-before-y-type"
          (runLshiftdivmodDirect #[intV 5, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/y-before-x-when-both-non-int"
          (runLshiftdivmodDirect #[.cell Cell.empty, .null, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLshiftdivmodDispatchFallback #[]) #[intV 5150] }
  ]
  oracle := #[
    mkCase "ok/sign/pos-pos-inexact-shift2" #[intV 13, intV 3, intV 2],
    mkCase "ok/sign/neg-pos-inexact-shift1" #[intV (-13), intV 3, intV 1],
    mkCase "ok/sign/pos-neg-inexact-shift2" #[intV 13, intV (-3), intV 2],
    mkCase "ok/sign/neg-neg-inexact-shift2" #[intV (-13), intV (-3), intV 2],
    mkCase "ok/shift-zero/pos" #[intV 7, intV 3, intV 0],
    mkCase "ok/shift-zero/neg" #[intV (-7), intV 3, intV 0],
    mkCase "ok/shift-zero/mixed-sign" #[intV 7, intV (-3), intV 0],
    mkCase "ok/zero-x/high-shift" #[intV 0, intV 3, intV 256],
    mkCase "ok/boundary/max-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-shift0" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-plus-one-div-neg1-shift0" #[intV (minInt257 + 1), intV (-1), intV 0],
    mkCase "ok/boundary/one-over-max-shift256" #[intV 1, intV maxInt257, intV 256],
    mkCase "ok/boundary/negone-over-max-shift256" #[intV (-1), intV maxInt257, intV 256],
    mkCase "ok/boundary/max-shift1-div2" #[intV maxInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-shift1-div2" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-plus-one-shift1-div2" #[intV (minInt257 + 1), intV 2, intV 1],
    mkCase "overflow/max-shift1-div1" #[intV maxInt257, intV 1, intV 1],
    mkCase "overflow/min-shift1-div1" #[intV minInt257, intV 1, intV 1],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0, intV 1],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 7],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-valid-shift" #[intV 1],
    mkCase "underflow/two-args" #[intV 5, intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "regression/underflow-before-range-one-arg-bad-shift" #[intV 257],
    mkCase "regression/underflow-before-range-two-args-bad-shift" #[intV 5, intV 257],
    mkCase "type/pop-shift-first-null" #[intV 5, intV 3, .null],
    mkCase "type/pop-y-second-null" #[intV 5, .null, intV 1],
    mkCase "type/pop-x-third-null" #[.null, intV 3, intV 1],
    mkCase "type/error-order-both-non-int-y-before-x" #[.cell Cell.empty, .null, intV 1],
    mkCase "range/shift-negative" #[intV 5, intV 3, intV (-1)],
    mkCase "range/shift-over-256" #[intV 5, intV 3, intV 257],
    mkCase "error-order/range-before-y-type" #[intV 5, .null, intV 257],
    mkCase "error-order/range-before-x-type" #[.null, intV 3, intV 257],
    mkCaseFromIntVals "nan/shift-via-program" #[.num 5, .num 3, .nan],
    mkCaseFromIntVals "nan/y-via-program" #[.num 5, .nan, .num 1],
    mkCaseFromIntVals "nan/x-via-program" #[.nan, .num 3, .num 1],
    mkCaseFromIntVals "overflow/input-x-out-of-range-via-program"
      #[.num (pow2 256), .num 3, .num 1],
    mkCaseFromIntVals "overflow/input-y-out-of-range-via-program"
      #[.num 5, .num (-(pow2 256) - 1), .num 1],
    mkCaseFromIntVals "overflow/input-shift-out-of-range-via-program"
      #[.num 5, .num 3, .num (pow2 256 + 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 13, intV 3, intV 2]
      #[.pushInt (.num lshiftdivmodSetGasExact), .tonEnvOp .setGasLimit, lshiftdivmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 13, intV 3, intV 2]
      #[.pushInt (.num lshiftdivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftdivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020816
      count := 700
      gen := genLshiftdivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTDIVMOD
