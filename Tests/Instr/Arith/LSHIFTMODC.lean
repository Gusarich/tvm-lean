import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTMODC

/-
LSHIFTMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shlDivMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa9ca` decode path)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (`LSHIFTMODC` specialization): 7 branch sites / 10 terminal outcomes
  (dispatch/fallback; arity gate; shift-range gate; pop/type path `shift→z→x`;
   numeric-vs-NaN split; div-by-zero split; non-quiet push success vs `intOv`).
- C++ (`exec_shldivmod`, non-quiet, runtime-shift): 6 branch sites / 10 outcomes
  (opcode validity guard; underflow guard; runtime-shift range gate; pop/type path;
   numeric validity gate; `d`-mode result branch).

Key risk areas covered:
- ceil-remainder sign behavior for mixed signs and near-zero numerators;
- huge-quotient remainder stability (`d=2` must not overflow when quotient is unused);
- strict pop/error ordering (`stkUnd` on short stacks before type/range paths);
- NaN/out-of-range injection through program-only `PUSHINT` helpers;
- deterministic gas cliff (`PUSHINT n; SETGASLIMIT; LSHIFTMODC`).
-/

private def lshiftmodcId : InstrId := { name := "LSHIFTMODC" }

private def lshiftmodcInstr : Instr := .arithExt (.shlDivMod 2 1 false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[lshiftmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runLshiftmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftmodcInstr stack

private def runLshiftmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5151)) stack

private def lshiftmodcSetGasExact : Int :=
  computeExactGasBudget lshiftmodcInstr

private def lshiftmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftmodcInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNonZeroDivisor (rng0 : StdGen) : Int × StdGen :=
  let (z, rng1) := pickSigned257ish rng0
  (if z = 0 then 1 else z, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1]

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (outOfRangeProgramPool.size - 1)
  (outOfRangeProgramPool[idx]!, rng')

private def genLshiftmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (zRaw, r3) := pickInt257Boundary r2
      let z := if zRaw = 0 then 1 else zRaw
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-all" #[intV x, intV z, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroDivisor r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-boundary-shift" #[intV x, intV z, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroDivisor r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-all" #[intV x, intV z, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/divzero" #[intV x, intV 0, intV shift], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-arg" #[intV x], r2)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroDivisor r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two-args" #[intV x, intV z], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroDivisor r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-shift-first" #[intV x, intV z, shiftLike], r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (zLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-divisor-second" #[intV x, zLike, intV shift], r4)
    else if shape = 9 then
      let (xLike, r2) := pickNonInt rng1
      let (z, r3) := pickNonZeroDivisor r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-third" #[xLike, intV z, intV shift], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroDivisor r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-negative" #[intV x, intV z, intV (-1)], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroDivisor r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-over-256" #[intV x, intV z, intV 257], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroDivisor r2
      (mkInputCase s!"fuzz/shape-{shape}/nan-shift-via-program"
        #[IntVal.num x, IntVal.num z, IntVal.nan], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkInputCase s!"fuzz/shape-{shape}/nan-divisor-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 14 then
      let (z, r2) := pickNonZeroDivisor rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkInputCase s!"fuzz/shape-{shape}/nan-x-via-program"
        #[IntVal.nan, IntVal.num z, IntVal.num shift], r3)
    else if shape = 15 then
      let (huge, r2) := pickOutOfRangeProgramInt rng1
      let (z, r3) := pickNonZeroDivisor r2
      let (shift, r4) := pickShiftBoundary r3
      (mkInputCase s!"fuzz/shape-{shape}/overflow-x-via-program"
        #[IntVal.num huge, IntVal.num z, IntVal.num shift], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (huge, r3) := pickOutOfRangeProgramInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkInputCase s!"fuzz/shape-{shape}/overflow-divisor-via-program"
        #[IntVal.num x, IntVal.num huge, IntVal.num shift], r4)
    else if shape = 17 then
      let (below, r2) := pickNonInt rng1
      let (x, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroDivisor r3
      let (shift, r5) := pickShiftInRange r4
      (mkCase s!"fuzz/shape-{shape}/ok-below-preserved"
        #[below, intV x, intV z, intV shift], r5)
    else
      let (pickX, r2) := randNat rng1 0 2
      let x :=
        if pickX = 0 then maxInt257
        else if pickX = 1 then minInt257
        else minInt257 + 1
      let (negDiv, r3) := randBool r2
      let z : Int := if negDiv then -7 else 7
      (mkCase s!"fuzz/shape-{shape}/ok-huge-quotient" #[intV x, intV z, intV 256], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftmodcId
  unit := #[
    { name := "unit/direct/ceil-remainder-sign-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, -1),
            (-7, 3, 1, -2),
            (7, -3, 1, 2),
            (-7, -3, 1, 1),
            (1, 3, 1, -1),
            (-1, 3, 1, -2),
            (1, -3, 1, 2),
            (-1, -3, 1, 1),
            (5, 7, 2, -1),
            (-5, 7, 2, -6),
            (5, -7, 2, 6),
            (-5, -7, 2, 1),
            (6, 3, 1, 0),
            (0, 5, 200, 0)
          ]
        for c in checks do
          let x := c.1
          let z := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"(x={x},z={z},s={shift})"
            (runLshiftmodcDirect #[intV x, intV z, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/boundary-huge-quotient-and-pop-discipline"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 256, 0),
            (minInt257, 1, 256, 0),
            (maxInt257, 7, 256, -5),
            (maxInt257, -7, 256, 2),
            (minInt257, 7, 256, -4),
            (minInt257, -7, 256, 3),
            (minInt257 + 1, 7, 256, -2),
            (minInt257 + 1, -7, 256, 5)
          ]
        for c in checks do
          let x := c.1
          let z := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"(x={x},z={z},s={shift})"
            (runLshiftmodcDirect #[intV x, intV z, intV shift]) #[intV expected]
        expectOkStack "below-null-preserved"
          (runLshiftmodcDirect #[.null, intV 7, intV 3, intV 1]) #[.null, intV (-1)]
        expectOkStack "below-cell-preserved"
          (runLshiftmodcDirect #[.cell Cell.empty, intV (-5), intV 7, intV 2])
          #[.cell Cell.empty, intV (-6)] }
    ,
    { name := "unit/error/range-divzero-underflow-type-ordering"
      run := do
        expectErr "range/shift-neg-one" (runLshiftmodcDirect #[intV 5, intV 3, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runLshiftmodcDirect #[intV 5, intV 3, intV 257]) .rangeChk
        expectErr "divzero/nonzero-over-zero" (runLshiftmodcDirect #[intV 5, intV 0, intV 1]) .intOv
        expectErr "divzero/zero-over-zero" (runLshiftmodcDirect #[intV 0, intV 0, intV 1]) .intOv
        expectErr "underflow/empty" (runLshiftmodcDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runLshiftmodcDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runLshiftmodcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/non-int-singleton-underflow-before-type"
          (runLshiftmodcDirect #[.null]) .stkUnd
        expectErr "error-order/two-items-underflow-before-range"
          (runLshiftmodcDirect #[intV 5, intV 257]) .stkUnd
        expectErr "type/pop-shift-first" (runLshiftmodcDirect #[intV 5, intV 3, .null]) .typeChk
        expectErr "type/pop-divisor-second" (runLshiftmodcDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/pop-x-third" (runLshiftmodcDirect #[.null, intV 3, intV 1]) .typeChk
        expectErr "error-order/pop-shift-before-divisor-when-both-non-int"
          (runLshiftmodcDirect #[intV 5, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-divisor-before-x-after-shift-int"
          (runLshiftmodcDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-lshiftmodc-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runLshiftmodcDispatchFallback #[]) #[intV 5151] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-shift1-inexact" #[intV 7, intV 3, intV 1],
    mkCase "ok/ceil/sign/neg-pos-shift1-inexact" #[intV (-7), intV 3, intV 1],
    mkCase "ok/ceil/sign/pos-neg-shift1-inexact" #[intV 7, intV (-3), intV 1],
    mkCase "ok/ceil/sign/neg-neg-shift1-inexact" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/ceil/sign/near-zero-pos-divisor" #[intV 1, intV 3, intV 1],
    mkCase "ok/ceil/sign/near-zero-neg-divisor" #[intV 1, intV (-3), intV 1],
    mkCase "ok/ceil/sign/near-zero-neg-numerator-pos-divisor" #[intV (-1), intV 3, intV 1],
    mkCase "ok/ceil/sign/near-zero-neg-numerator-neg-divisor" #[intV (-1), intV (-3), intV 1],
    mkCase "ok/exact/divisible-shift1" #[intV 6, intV 3, intV 1],
    mkCase "ok/exact/divisible-neg" #[intV (-6), intV 3, intV 1],
    mkCase "ok/exact/zero-numerator-large-shift" #[intV 0, intV 5, intV 256],
    mkCase "ok/exact/shift-zero-noop-shift" #[intV 37, intV 5, intV 0],
    mkCase "ok/boundary/huge-quotient-max-shift256-div1" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/huge-quotient-min-shift256-div1" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/huge-quotient-max-shift256-div7" #[intV maxInt257, intV 7, intV 256],
    mkCase "ok/boundary/huge-quotient-max-shift256-div-neg7" #[intV maxInt257, intV (-7), intV 256],
    mkCase "ok/boundary/huge-quotient-min-shift256-div7" #[intV minInt257, intV 7, intV 256],
    mkCase "ok/boundary/huge-quotient-min-shift256-div-neg7" #[intV minInt257, intV (-7), intV 256],
    mkCase "ok/boundary/huge-quotient-min-plus-one-shift256-div7" #[intV (minInt257 + 1), intV 7, intV 256],
    mkCase "ok/boundary/huge-quotient-min-plus-one-shift256-div-neg7" #[intV (minInt257 + 1), intV (-7), intV 256],
    mkCase "pop-order/below-preserved-null" #[.null, intV 7, intV 3, intV 1],
    mkCase "pop-order/below-preserved-cell" #[.cell Cell.empty, intV (-5), intV 7, intV 2],
    mkCase "range/shift-neg-one" #[intV 5, intV 3, intV (-1)],
    mkCase "range/shift-over-256" #[intV 5, intV 3, intV 257],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0, intV 1],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/non-int-singleton-underflow-before-type" #[.null],
    mkCase "error-order/two-items-underflow-before-range" #[intV 5, intV 257],
    mkCase "type/pop-shift-first" #[intV 5, intV 3, .null],
    mkCase "type/pop-divisor-second" #[intV 5, .null, intV 1],
    mkCase "type/pop-x-third" #[.null, intV 3, intV 1],
    mkCase "error-order/pop-shift-before-divisor-when-both-non-int"
      #[intV 5, .cell Cell.empty, .null],
    mkCase "error-order/pop-divisor-before-x-after-shift-int"
      #[.null, .cell Cell.empty, intV 1],
    mkInputCase "nan/shift-via-program" #[IntVal.num 5, IntVal.num 3, IntVal.nan],
    mkInputCase "nan/divisor-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkInputCase "nan/x-via-program" #[IntVal.nan, IntVal.num 3, IntVal.num 1],
    mkInputCase "overflow/pushint-x-out-of-range-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 1],
    mkInputCase "overflow/pushint-divisor-out-of-range-before-op"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftmodcSetGasExact), .tonEnvOp .setGasLimit, lshiftmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020819
      count := 700
      gen := genLshiftmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTMODC
