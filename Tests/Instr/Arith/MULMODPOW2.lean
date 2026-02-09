import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODPOW2

/-
MULMODPOW2 branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 2 (-1) false none` path)
  - `TvmLean/Model/Basics/Bytes.lean` (`modPow2Round`, `rshiftPow2Round`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xa9a8..0xa9aa` decode to `MULMODPOW2`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, `register_div_ops`)

Branch counts used for this suite:
- Lean (MULMODPOW2 specialization): 8 branch sites / 12 terminal outcomes
  (dispatch; runtime shift pop/type/underflow; shift range gate; `y` and `x`
   pop/type/underflow paths; numeric-vs-NaN operand split; non-quiet
   `pushIntQuiet` success vs `intOv`).
- C++ (`exec_mulshrmod`, non-add mode): 7 branch sites / 12 aligned outcomes
  (invalid-opcode guard; underflow gate; runtime shift range check; `y`/`x`
   type checks; global-v13 NaN/invalid funnel; `d` switch with non-quiet
   push overflow/NaN throw funnel).

Key risk areas covered:
- floor mod-2^z behavior across sign combinations and `z = 0`/`z = 256`;
- strict runtime shift validation (`0..256`) before `y`/`x` pops;
- pop/error ordering (`z` first, then `y`, then `x`);
- NaN/out-of-range inputs injected via program only (never direct init stack);
- exact gas and exact-minus-one boundaries under `SETGASLIMIT`.
-/

private def mulmodpow2Id : InstrId := { name := "MULMODPOW2" }

private def mulmodpow2Instr : Instr :=
  .arithExt (.shrMod true false 2 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulmodpow2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulmodpow2Id
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
  mkCase name stack (progPrefix.push mulmodpow2Instr) gasLimits fuel

private def runMulmodpow2Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulmodpow2Instr stack

private def runMulmodpow2DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6602)) stack

private def mulmodpow2SetGasExact : Int :=
  computeExactGasBudget mulmodpow2Instr

private def mulmodpow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulmodpow2Instr

private def validShiftPool : Array Int :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genMulmodpow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (caseOut, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromPool validShiftPool r3
      (mkCase "tmp" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftNat, r4) := randNat r3 0 256
      (mkCase "tmp" #[intV x, intV y, intV (Int.ofNat shiftNat)], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickFromPool validShiftPool r3
      (mkCase "tmp" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromPool validShiftPool r3
      (mkCase "tmp" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickFromPool invalidShiftPool r3
      (mkCase "tmp" #[intV x, intV y, intV shift], r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (useCell, r4) := randBool r3
      let shiftVal : Value := if useCell then .cell Cell.empty else .null
      (mkCase "tmp" #[intV x, intV y, shiftVal], r4)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool validShiftPool r2
      let (useCell, r4) := randBool r3
      let yVal : Value := if useCell then .cell Cell.empty else .null
      (mkCase "tmp" #[intV x, yVal, intV shift], r4)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool validShiftPool r2
      let (useCell, r4) := randBool r3
      let xVal : Value := if useCell then .cell Cell.empty else .null
      (mkCase "tmp" #[xVal, intV y, intV shift], r4)
    else if shape = 8 then
      let (variant, r2) := randNat rng1 0 2
      if variant = 0 then
        (mkCase "tmp" #[], r2)
      else if variant = 1 then
        let (shift, r3) := pickFromPool validShiftPool r2
        (mkCase "tmp" #[intV shift], r3)
      else
        let (x, r3) := pickSigned257ish r2
        let (shift, r4) := pickFromPool validShiftPool r3
        (mkCase "tmp" #[intV x, intV shift], r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals "tmp" #[.num x, .num y, .nan], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftNat, r3) := randNat r2 0 256
      (mkCaseFromIntVals "tmp" #[.num x, .nan, .num (Int.ofNat shiftNat)], r3)
    else if shape = 11 then
      let (y, r2) := pickSigned257ish rng1
      let (shiftNat, r3) := randNat r2 0 256
      (mkCaseFromIntVals "tmp" #[.nan, .num y, .num (Int.ofNat shiftNat)], r3)
    else if shape = 12 then
      let (variant, r2) := randNat rng1 0 2
      let big : Int := pow2 256
      if variant = 0 then
        (mkCaseFromIntVals "tmp" #[.num big, .num 7, .num 5], r2)
      else if variant = 1 then
        (mkCaseFromIntVals "tmp" #[.num 7, .num big, .num 5], r2)
      else
        (mkCaseFromIntVals "tmp" #[.num 7, .num 5, .num big], r2)
    else
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let (flipY, r3) := randBool r2
      let y := if flipY then (-1 : Int) else 1
      let (shift, r4) := pickFromPool validShiftPool r3
      (mkCase "tmp" #[intV x, intV y, intV shift], r4)
  let kind :=
    if shape = 4 then
      "range"
    else if shape = 5 || shape = 6 || shape = 7 then
      "type"
    else if shape = 8 then
      "underflow"
    else if shape = 9 || shape = 10 || shape = 11 then
      "nan-program"
    else if shape = 12 then
      "program-overflow"
    else
      "ok"
  let (tag, rng3) := randNat rng2 0 999_999
  ({ caseOut with name := s!"fuzz/shape-{shape}/{kind}-{tag}" }, rng3)

def suite : InstrSuite where
  id := mulmodpow2Id
  unit := #[
    { name := "unit/direct/floor-modpow2-sign-zero-and-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 3, 0, 0),
            (-7, 3, 0, 0),
            (7, 3, 2, 1),
            (-7, 3, 2, 3),
            (7, -3, 2, 3),
            (-7, -3, 2, 1),
            (13, 11, 4, 15),
            (-13, 11, 4, 1),
            (13, -11, 4, 1),
            (-13, -11, 4, 15),
            (5, 0, 7, 0),
            (0, 5, 7, 0),
            (maxInt257, 1, 1, 1),
            (maxInt257, 1, 255, (pow2 255) - 1),
            (maxInt257, 1, 256, maxInt257),
            (minInt257, 1, 1, 0),
            (minInt257, -1, 1, 0),
            (minInt257, 1, 255, 0),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, 1, 256, 1),
            (minInt257 + 1, -1, 256, maxInt257),
            (-1, 1, 256, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})%2^{shift}"
            (runMulmodpow2Direct #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/error/range-pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulmodpow2Direct #[]) .stkUnd
        expectErr "underflow/one-arg-shift-only" (runMulmodpow2Direct #[intV 4]) .stkUnd
        expectErr "underflow/two-args-missing-x" (runMulmodpow2Direct #[intV 5, intV 4]) .stkUnd
        expectErr "type/pop-shift-first-null" (runMulmodpow2Direct #[intV 5, intV 7, .null]) .typeChk
        expectErr "type/pop-shift-first-cell" (runMulmodpow2Direct #[intV 5, intV 7, .cell Cell.empty]) .typeChk
        expectErr "type/pop-y-second-null" (runMulmodpow2Direct #[intV 5, .null, intV 4]) .typeChk
        expectErr "type/pop-x-third-null" (runMulmodpow2Direct #[.null, intV 5, intV 4]) .typeChk
        expectErr "range/shift-negative" (runMulmodpow2Direct #[intV 5, intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runMulmodpow2Direct #[intV 5, intV 7, intV 257]) .rangeChk
        expectErr "error-order/range-before-y-type"
          (runMulmodpow2Direct #[intV 5, .null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type"
          (runMulmodpow2Direct #[.cell Cell.empty, intV 7, intV 257]) .rangeChk
        expectErr "error-order/type-on-shift-before-y-x"
          (runMulmodpow2Direct #[.null, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-valid-shift"
          (runMulmodpow2Direct #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulmodpow2DispatchFallback #[]) #[intV 6602] }
  ]
  oracle := #[
    mkCase "ok/shift-zero/pos-pos" #[intV 7, intV 3, intV 0],
    mkCase "ok/shift-zero/neg-pos" #[intV (-7), intV 3, intV 0],
    mkCase "ok/floor/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "ok/floor/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "ok/floor/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "ok/floor/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "ok/exact/divisible-pos" #[intV 8, intV 4, intV 3],
    mkCase "ok/exact/divisible-neg" #[intV (-8), intV 4, intV 3],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 19, intV 7],
    mkCase "ok/exact/zero-right-factor" #[intV 19, intV 0, intV 7],
    mkCase "ok/boundary/max-times-one-shift1" #[intV maxInt257, intV 1, intV 1],
    mkCase "ok/boundary/max-times-one-shift255" #[intV maxInt257, intV 1, intV 255],
    mkCase "ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-times-one-shift1" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/boundary/min-times-one-shift255" #[intV minInt257, intV 1, intV 255],
    mkCase "ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-plus-one-times-neg-one-shift256"
      #[intV (minInt257 + 1), intV (-1), intV 256],
    mkCase "ok/boundary/neg-one-times-one-shift256" #[intV (-1), intV 1, intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-shift-only" #[intV 4],
    mkCase "underflow/two-args-missing-x" #[intV 5, intV 4],
    mkCase "type/pop-shift-first-null" #[intV 5, intV 7, .null],
    mkCase "type/pop-shift-first-cell" #[intV 5, intV 7, .cell Cell.empty],
    mkCase "type/pop-y-second-null" #[intV 5, .null, intV 4],
    mkCase "type/pop-x-third-null" #[.null, intV 5, intV 4],
    mkCase "error-order/pop-y-before-x-after-valid-shift"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "range/shift-neg-one" #[intV 5, intV 7, intV (-1)],
    mkCase "range/shift-neg-two" #[intV 5, intV 7, intV (-2)],
    mkCase "range/shift-over-256" #[intV 5, intV 7, intV 257],
    mkCase "range/shift-over-258" #[intV 5, intV 7, intV 258],
    mkCase "error-order/range-before-y-type" #[intV 5, .null, intV (-1)],
    mkCase "error-order/range-before-x-type" #[.cell Cell.empty, intV 7, intV 257],
    mkCase "error-order/type-on-shift-before-y-x" #[.null, .cell Cell.empty, .null],
    mkCaseFromIntVals "nan/shift-via-program" #[.num 5, .num 7, .nan],
    mkCaseFromIntVals "nan/y-via-program" #[.num 5, .nan, .num 7],
    mkCaseFromIntVals "nan/x-via-program" #[.nan, .num 5, .num 7],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/x"
      #[.num (pow2 256), .num 7, .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/y"
      #[.num 7, .num (pow2 256), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op/shift"
      #[.num 7, .num 5, .num (pow2 256)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodpow2SetGasExact), .tonEnvOp .setGasLimit, mulmodpow2Instr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodpow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, mulmodpow2Instr]
  ]
  fuzz := #[
    { seed := 2026020814
      count := 700
      gen := genMulmodpow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2
