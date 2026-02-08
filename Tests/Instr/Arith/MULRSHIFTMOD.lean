import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTMOD

/-
MULRSHIFTMOD branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (opcode family decode around `0xa9ac`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, `register_div_ops`)

Branch counts used for this suite:
- Lean (`.shrMod` mul-path specialization): 9 branch sites / 17 terminal outcomes
  (mul-vs-nonmul split; underflow gate; runtime shift source; shift range gate;
   operand-shape split; `shift==0` floor override; round-mode validity gate;
   fixed `d=3` push path; non-quiet `pushIntQuiet` fit checks).
- C++ (`exec_mulshrmod`): 8 branch sites / 15 aligned outcomes
  (const-vs-stack shift source; add-remap gate; invalid-op guard; underflow gate;
   non-quiet range gate; zero-shift round override; global-version invalid-input gate;
   `d` switch with `MULRSHIFTMOD` fixed to `d=3`).

Key risk areas covered:
- pop/error ordering (`shift` first, then `y`, then `x`);
- range-check precedence over later operand-type checks (non-quiet);
- signed-257 overflow cliffs (`z=0`, plus `min*min` at `z=256`);
- floor quotient/remainder invariants for negative products;
- NaN propagation to non-quiet `intOv` (injected via `PUSHINT`);
- deterministic gas boundary (`PUSHINT n; SETGASLIMIT; MULRSHIFTMOD`).
-/

private def mulrshiftmodId : InstrId := { name := "MULRSHIFTMOD" }

private def mulrshiftmodInstr : Instr :=
  .arithExt (.shrMod true false 3 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulrshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulRShiftModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftmodInstr stack

private def runMulRShiftModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 1901)) stack

private def mulrshiftmodSetGasExact : Int :=
  computeExactGasBudget mulrshiftmodInstr

private def mulrshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftmodInstr

private def mkShiftInjectedCase (name : String) (x y : Int) (shift : IntVal) : OracleCase :=
  mkCase name #[intV x, intV y] #[.pushInt shift, mulrshiftmodInstr]

private def mkYNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift] #[.pushInt .nan, .xchg0 1, mulrshiftmodInstr]

private def mkXNanInjectedCase (name : String) (y shift : Int) : OracleCase :=
  mkCase name #[intV y, intV shift] #[.pushInt .nan, .xchg0 2, .xchg0 1, mulrshiftmodInstr]

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def outOfRangeShiftPool : Array Int :=
  #[-5, -1, 257, 258, 300]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickFromIntPool validShiftBoundaryPool rng1
  else
    let (z, rng2) := randNat rng1 0 256
    (Int.ofNat z, rng2)

private def pickOutOfRangeShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool outOfRangeShiftPool rng

private def genMulRShiftModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromIntPool validShiftBoundaryPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"fuzz/shape-{shape}/ok-signed" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"fuzz/shape-{shape}/ok-x-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"fuzz/shape-{shape}/ok-y-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/overflow-max-times-two-shift0" #[intV maxInt257, intV 2, intV 0], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/overflow-min-times-neg1-shift0" #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/overflow-min-times-min-shift256" #[intV minInt257, intV minInt257, intV 256], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickOutOfRangeShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-out-of-range-via-program" x y (.num shift), r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" x y .nan, r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (pick, r4) := randNat r3 0 1
      let shiftLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-shift-non-int" #[intV x, intV y, shiftLike], r4)
    else if shape = 10 then
      let (pick, r2) := randNat rng1 0 3
      let stack : Array Value :=
        if pick = 0 then
          #[]
        else if pick = 1 then
          #[intV 1]
        else if pick = 2 then
          #[intV 1, intV 2]
        else
          #[.null, intV 2]
      (mkCase s!"fuzz/shape-{shape}/underflow" stack, r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkYNanInjectedCase s!"fuzz/shape-{shape}/nan-y-via-program" x shift, r3)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkXNanInjectedCase s!"fuzz/shape-{shape}/nan-x-via-program" y shift, r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (pick, r4) := randNat r3 0 1
      let yLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-y-non-int" #[intV x, yLike, intV shift], r4)
    else
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (pick, r4) := randNat r3 0 1
      let xLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, intV y, intV shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftmodId
  unit := #[
    { name := "unit/ok/floor-quot-rem-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 2, 8, 3),
            (-7, 5, 2, -9, 1),
            (7, -5, 2, -9, 1),
            (-7, -5, 2, 8, 3),
            (1, -2, 1, -1, 0),
            (-1, 2, 1, -1, 0),
            (9, 0, 5, 0, 0),
            (0, 9, 5, 0, 0),
            (5, 3, 0, 15, 0),
            (-5, 3, 0, -15, 0),
            (1, 1, 256, 0, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})>>{shift}"
            (runMulRShiftModDirect #[intV x, intV y, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/ok/boundary-and-large-shift-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257, 0),
            (minInt257, 1, 0, minInt257, 0),
            (maxInt257, -1, 0, -maxInt257, 0),
            (minInt257, -1, 256, 1, 0),
            (maxInt257, maxInt257, 256, maxInt257 - 1, 1),
            (minInt257 + 1, minInt257 + 1, 256, maxInt257 - 1, 1),
            (minInt257, 1, 256, -1, 0),
            (maxInt257, minInt257, 256, -maxInt257, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"boundary/({x}*{y})>>{shift}"
            (runMulRShiftModDirect #[intV x, intV y, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/error/overflow-range-and-nan-paths"
      run := do
        expectErr "overflow/max-times-two-shift0"
          (runMulRShiftModDirect #[intV maxInt257, intV 2, intV 0]) .intOv
        expectErr "overflow/min-times-neg1-shift0"
          (runMulRShiftModDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "overflow/min-times-min-shift256"
          (runMulRShiftModDirect #[intV minInt257, intV minInt257, intV 256]) .intOv
        expectErr "range/shift-negative"
          (runMulRShiftModDirect #[intV 5, intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax"
          (runMulRShiftModDirect #[intV 5, intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan"
          (runMulRShiftModDirect #[intV 5, intV 7, .int .nan]) .rangeChk
        expectErr "nan/y"
          (runMulRShiftModDirect #[intV 5, .int .nan, intV 4]) .intOv
        expectErr "nan/x"
          (runMulRShiftModDirect #[.int .nan, intV 5, intV 4]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runMulRShiftModDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runMulRShiftModDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args-int" (runMulRShiftModDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/two-args-non-int" (runMulRShiftModDirect #[.null, intV 2]) .stkUnd
        expectErr "type/pop-shift-first" (runMulRShiftModDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulRShiftModDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMulRShiftModDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-shift-before-y-when-both-non-int"
          (runMulRShiftModDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/range-before-y-type"
          (runMulRShiftModDirect #[intV 1, .null, intV 300]) .rangeChk
        expectErr "error-order/pop-y-before-x-when-shift-valid"
          (runMulRShiftModDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runMulRShiftModDispatchFallback #[]) #[intV 1901] }
  ]
  oracle := #[
    mkCase "ok/floor/basic/pos-pos" #[intV 7, intV 5, intV 2],
    mkCase "ok/floor/basic/neg-pos" #[intV (-7), intV 5, intV 2],
    mkCase "ok/floor/basic/pos-neg" #[intV 7, intV (-5), intV 2],
    mkCase "ok/floor/basic/neg-neg" #[intV (-7), intV (-5), intV 2],
    mkCase "ok/floor/basic/shift-zero-pos" #[intV 5, intV 3, intV 0],
    mkCase "ok/floor/basic/shift-zero-neg" #[intV (-5), intV 3, intV 0],
    mkCase "ok/floor/basic/y-zero" #[intV 9, intV 0, intV 5],
    mkCase "ok/floor/basic/x-zero" #[intV 0, intV 9, intV 5],
    mkCase "ok/floor/basic/shift-256-small" #[intV 1, intV 1, intV 256],
    mkCase "ok/boundary/max-times-one-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-times-one-shift0" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/max-times-neg1-shift0" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/boundary/min-times-neg1-shift256" #[intV minInt257, intV (-1), intV 256],
    mkCase "ok/boundary/max-times-max-shift256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/boundary/min-plus1-times-min-plus1-shift256" #[intV (minInt257 + 1), intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/max-times-min-shift256" #[intV maxInt257, intV minInt257, intV 256],
    mkCase "overflow/max-times-two-shift0" #[intV maxInt257, intV 2, intV 0],
    mkCase "overflow/min-times-neg1-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "overflow/min-times-min-shift256" #[intV minInt257, intV minInt257, intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args-int" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-args" #[.null, intV 2],
    mkCase "type/pop-shift-first-null" #[intV 1, intV 2, .null],
    mkCase "type/pop-shift-first-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/pop-y-second-null" #[intV 1, .null, intV 1],
    mkCase "type/pop-x-third-null" #[.null, intV 1, intV 1],
    mkCase "error-order/pop-shift-before-y-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-y-before-x-when-shift-valid" #[.null, .cell Cell.empty, intV 1],
    mkShiftInjectedCase "range/shift-negative-via-program" 5 7 (.num (-1)),
    mkShiftInjectedCase "range/shift-overmax-via-program" 5 7 (.num 257),
    mkShiftInjectedCase "range/shift-nan-via-program" 5 7 .nan,
    mkShiftInjectedCase "error-order/range-before-y-type-via-program" 9 0 (.num 300),
    mkYNanInjectedCase "nan/y-via-program" 5 4,
    mkXNanInjectedCase "nan/x-via-program" 5 4,
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulrshiftmodSetGasExact), .tonEnvOp .setGasLimit, mulrshiftmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulrshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020816
      count := 700
      gen := genMulRShiftModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTMOD
