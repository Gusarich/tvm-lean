import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDRSHIFTMOD

/-
ADDRSHIFTMOD branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (0xa920 decoding)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)

Branch counts used for this suite:
- Lean (`.shrMod` generic path): 8 branch sites / 16 terminal outcomes
  (mul-vs-nonmul split; stack underflow gate; runtime-shift source;
   shift range/type checks; operand-shape split; round-mode validity;
   `d` switch; NaN non-quiet push behavior).
- C++ (`exec_shrmod`): 7 branch sites / 14 terminal outcomes
  (const-vs-stack shift source; add remap gate; invalid-op guard;
   underflow gate; `y=0` round override; add-vs-nonadd split;
   nonadd `d` switch with ADDR* fixed to add+`d=3`).

ADDRSHIFTMOD specialization:
- opcode `0xa920`;
- parameters fixed to `.arithExt (.shrMod false true 3 (-1) false none)`
  (non-quiet, add-mode, floor semantics, stack shift).

Key risk areas covered:
- stack underflow before any type/range checks (`add ? 3 : 2`);
- pop order (`y` first, then `w`, then `x`);
- shift range (`0..256`) and `y`-path range/type ordering;
- non-quiet NaN propagation to `intOv` for `x`/`w`;
- signed-257 overflow cliff when `y = 0` and `x + w` escapes bounds;
- exact vs exact-minus-one gas boundary with `SETGASLIMIT`.
-/

private def addrshiftmodId : InstrId := { name := "ADDRSHIFTMOD" }

private def addrshiftmodInstr : Instr :=
  .arithExt (.shrMod false true 3 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[addrshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := addrshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAddrShiftModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt addrshiftmodInstr stack

private def runAddrShiftModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4310)) stack

private def addrshiftmodSetGasExact : Int :=
  computeExactGasBudget addrshiftmodInstr

private def addrshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne addrshiftmodInstr

private def mkShiftInjectedCase (name : String) (x w : Int) (shift : IntVal) : OracleCase :=
  mkCase name #[intV x, intV w] #[.pushInt shift, addrshiftmodInstr]

private def mkXNanInjectedCase (name : String) (w y : Int) : OracleCase :=
  mkCase name #[intV w, intV y] #[.pushInt .nan, .xchg0 2, .xchg0 1, addrshiftmodInstr]

private def mkWNanInjectedCase (name : String) (x y : Int) : OracleCase :=
  mkCase name #[intV x, intV y] #[.pushInt .nan, .xchg0 1, addrshiftmodInstr]

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def outOfRangeShiftPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromIntPool validShiftBoundaryPool rng1
  else
    let (v, rng2) := randNat rng1 0 256
    (Int.ofNat v, rng2)

private def pickOutOfRangeShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool outOfRangeShiftPool rng

private def genAddrShiftModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickFromIntPool validShiftBoundaryPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x, intV w, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"fuzz/shape-{shape}/ok-mixed" #[intV x, intV w, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/overflow-shift-zero" #[intV x, intV w, intV 0], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-shift-256" #[intV x, intV w, intV 256], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickOutOfRangeShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-out-of-range" x w (.num shift), r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan" x w .nan, r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (pick, r4) := randNat r3 0 1
      let yLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-y-non-int" #[intV x, intV w, yLike], r4)
    else if shape = 7 then
      let (pick, r2) := randNat rng1 0 2
      let stack : Array Value :=
        if pick = 0 then
          #[]
        else if pick = 1 then
          #[intV 1]
        else
          #[.null, intV 1]
      (mkCase s!"fuzz/shape-{shape}/underflow" stack, r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkWNanInjectedCase s!"fuzz/shape-{shape}/nan-w-via-program" x shift, r3)
    else if shape = 9 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkXNanInjectedCase s!"fuzz/shape-{shape}/nan-x-via-program" w shift, r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (pick, r4) := randNat r3 0 1
      let wLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-w-non-int" #[intV x, wLike, intV shift], r4)
    else if shape = 11 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (pick, r4) := randNat r3 0 1
      let xLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, intV w, intV shift], r4)
    else
      let (x0, r2) := pickInt257Boundary rng1
      let x := if x0 = minInt257 then minInt257 + 1 else x0
      let (shift, r3) := pickValidShift r2
      (mkCase s!"fuzz/shape-{shape}/ok-canceling-addend" #[intV x, intV (-x), intV shift], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := addrshiftmodId
  unit := #[
    { name := "unit/ok/floor-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 2, 3, 0),
            (-7, 1, 2, -2, 2),
            (7, -8, 2, -1, 3),
            (-7, -1, 2, -2, 0),
            (1, -2, 1, -1, 1),
            (-1, 2, 1, 0, 1),
            (9, -9, 5, 0, 0),
            (5, 3, 0, 8, 0),
            (-5, -3, 0, -8, 0),
            (0, 0, 9, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"(x={x},w={w},y={shift})"
            (runAddrShiftModDirect #[intV x, intV w, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/ok/boundary-and-large-shift-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 0, maxInt257, 0),
            (minInt257, 0, 0, minInt257, 0),
            (maxInt257, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 0, minInt257 + 1, 0),
            (maxInt257, maxInt257, 256, 1, (pow2 256) - 2),
            (minInt257, minInt257, 256, -2, 0),
            (minInt257, 1, 256, -1, 1),
            (maxInt257, -1, 256, 0, (pow2 256) - 2)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"(x={x},w={w},y={shift})"
            (runAddrShiftModDirect #[intV x, intV w, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/error/overflow-range-and-nan"
      run := do
        expectErr "overflow/max-plus-one-shift-zero"
          (runAddrShiftModDirect #[intV maxInt257, intV 1, intV 0]) .intOv
        expectErr "overflow/min-minus-one-shift-zero"
          (runAddrShiftModDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "range/shift-negative" (runAddrShiftModDirect #[intV 5, intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax" (runAddrShiftModDirect #[intV 5, intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runAddrShiftModDirect #[intV 5, intV 7, .int .nan]) .rangeChk
        expectErr "nan/w" (runAddrShiftModDirect #[intV 5, .int .nan, intV 4]) .intOv
        expectErr "nan/x" (runAddrShiftModDirect #[.int .nan, intV 5, intV 4]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runAddrShiftModDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runAddrShiftModDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args-int" (runAddrShiftModDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/two-args-non-int" (runAddrShiftModDirect #[.null, intV 2]) .stkUnd
        expectErr "type/pop-y-first" (runAddrShiftModDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-w-second" (runAddrShiftModDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runAddrShiftModDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-y-before-w-when-both-non-int"
          (runAddrShiftModDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-w-before-x-when-y-valid"
          (runAddrShiftModDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runAddrShiftModDispatchFallback #[]) #[intV 4310] }
  ]
  oracle := #[
    mkCase "ok/floor/basic/pos-pos" #[intV 7, intV 5, intV 2],
    mkCase "ok/floor/basic/neg-pos" #[intV (-7), intV 1, intV 2],
    mkCase "ok/floor/basic/pos-neg" #[intV 7, intV (-8), intV 2],
    mkCase "ok/floor/basic/neg-neg" #[intV (-7), intV (-1), intV 2],
    mkCase "ok/floor/basic/shift-zero-pos" #[intV 5, intV 3, intV 0],
    mkCase "ok/floor/basic/shift-zero-neg" #[intV (-5), intV (-3), intV 0],
    mkCase "ok/floor/basic/shift-one-neg" #[intV 1, intV (-2), intV 1],
    mkCase "ok/floor/basic/shift-one-pos" #[intV (-1), intV 2, intV 1],
    mkCase "ok/floor/boundary/max-plus-zero-shift-zero" #[intV maxInt257, intV 0, intV 0],
    mkCase "ok/floor/boundary/min-plus-zero-shift-zero" #[intV minInt257, intV 0, intV 0],
    mkCase "ok/floor/boundary/max-plus-neg-one-shift-zero" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/floor/boundary/min-plus-one-shift-zero" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/floor/boundary/max-plus-max-shift-256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/floor/boundary/min-plus-min-shift-256" #[intV minInt257, intV minInt257, intV 256],
    mkCase "ok/floor/boundary/min-plus-one-shift-256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/floor/boundary/max-plus-neg-one-shift-256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "overflow/shift-zero/max-plus-one" #[intV maxInt257, intV 1, intV 0],
    mkCase "overflow/shift-zero/min-minus-one" #[intV minInt257, intV (-1), intV 0],
    mkShiftInjectedCase "range/shift-negative-via-program" 5 7 (.num (-1)),
    mkShiftInjectedCase "range/shift-overmax-via-program" 5 7 (.num 257),
    mkShiftInjectedCase "range/shift-nan-via-program" 5 7 .nan,
    mkWNanInjectedCase "nan/w-via-program" 5 4,
    mkXNanInjectedCase "nan/x-via-program" 5 4,
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args-int" #[intV 1, intV 2],
    mkCase "regression/error-order/underflow-before-type-two-args" #[.null, intV 2],
    mkCase "type/pop-y-first-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-w-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-y-before-w-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-x-when-y-valid" #[.null, .cell Cell.empty, intV 1],
    mkShiftInjectedCase "error-order/range-before-w-type-via-program" 9 0 (.num 300),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num addrshiftmodSetGasExact), .tonEnvOp .setGasLimit, addrshiftmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num addrshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, addrshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 700
      gen := genAddrShiftModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTMOD
