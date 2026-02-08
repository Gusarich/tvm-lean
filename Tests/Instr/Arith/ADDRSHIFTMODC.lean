import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDRSHIFTMODC

/-
ADDRSHIFTMODC branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Ext.lean`
  (the `.arithExt (.shrMod false true 3 1 false none)` specialization, including
   `rshiftPow2RoundAddCompat` for add-path compatibility at large shifts).
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_shrmod`, `dump_shrmod`, `register_div_ops`; opcode args `0x2` under `0xa92`).

Branch counts used for this suite:
- Lean specialization: 9 branch points / 13 terminal outcomes
  (dispatch path; `mulMode` split; depth gate; shift pop/type/range;
   `w`/`x` pop type checks; numeric-vs-NaN operand split; `shift==0` mode override;
   fixed `d=3` double-push with non-quiet fit checks).
- C++ specialization: 8 branch points / 12 aligned outcomes
  (global-version add-remap; invalid-op guard; underflow gate;
   `pop_smallint_range(256)` type/range; `y==0` mode override;
   `w`/`x` `pop_int` checks; add-path quotient/remainder pushes with non-quiet overflow).

Key risk areas covered:
- ceil rounding + remainder sign invariants across mixed signs;
- `shift=0` forced-floor override (`C` suffix suppressed at runtime);
- pop/error ordering (`shift` before `w`, `w` before `x`, underflow before type/range);
- NaN propagation from `x`/`w` through non-quiet push (`intOv`);
- signed-257 overflow at `shift=0` when `x+w` exceeds range;
- deterministic gas boundary (`PUSHINT n; SETGASLIMIT; ADDRSHIFTMODC` exact / minus-one).
-/

private def addrshiftmodcId : InstrId := { name := "ADDRSHIFTMODC" }

private def addrshiftmodcInstr : Instr :=
  .arithExt (.shrMod false true 3 1 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[addrshiftmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := addrshiftmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAddrShiftModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt addrshiftmodcInstr stack

private def runAddrShiftModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 8080)) stack

private def addrshiftmodcSetGasExact : Int :=
  computeExactGasBudget addrshiftmodcInstr

private def addrshiftmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne addrshiftmodcInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallSignedPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftUpTo256 (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def mkFuzzDataCase (shape : Nat) (kind : String) (x w shift : Int)
    (rng : StdGen) : OracleCase × StdGen :=
  let (tag, rng') := randNat rng 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV w, intV shift], rng')

private def genAddrShiftModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    let (x, r2) := pickInt257Boundary rng1
    let (w, r3) := pickInt257Boundary r2
    let (shift, r4) := pickShiftBoundary r3
    let sum := x + w
    let kind :=
      if shift = 0 && !intFitsSigned257 sum then "overflow-shift0" else "boundary"
    mkFuzzDataCase 0 kind x w shift r4
  else if shape = 1 then
    let (x, r2) := pickSigned257ish rng1
    let (w, r3) := pickSigned257ish r2
    let (shift, r4) := pickShiftBoundary r3
    let sum := x + w
    let kind :=
      if shift = 0 && !intFitsSigned257 sum then "overflow-shift0" else "signed"
    mkFuzzDataCase 1 kind x w shift r4
  else if shape = 2 then
    let (x, r2) := pickInt257Boundary rng1
    let (w, r3) := pickSigned257ish r2
    let (shift, r4) := pickShiftUpTo256 r3
    mkFuzzDataCase 2 "mix-x-boundary" x w shift r4
  else if shape = 3 then
    let (x, r2) := pickSigned257ish rng1
    let (w, r3) := pickInt257Boundary r2
    let (shift, r4) := pickShiftUpTo256 r3
    mkFuzzDataCase 3 "mix-w-boundary" x w shift r4
  else if shape = 4 then
    let (x, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftUpTo256 r2
    mkFuzzDataCase 4 "w-zero" x 0 shift r3
  else if shape = 5 then
    let (w, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftUpTo256 r2
    mkFuzzDataCase 5 "x-zero" 0 w shift r3
  else if shape = 6 then
    mkFuzzDataCase 6 "overflow-max-plus-one-shift0" maxInt257 1 0 rng1
  else if shape = 7 then
    mkFuzzDataCase 7 "overflow-min-minus-one-shift0" minInt257 (-1) 0 rng1
  else if shape = 8 then
    let (useMax, r2) := randBool rng1
    let x := if useMax then maxInt257 else minInt257
    let w := if useMax then 0 else 0
    mkFuzzDataCase 8 "shift256-boundary" x w 256 r2
  else if shape = 9 then
    let (x, r2) := pickFromPool smallSignedPool rng1
    let (w, r3) := pickFromPool smallSignedPool r2
    let (shift, r4) := pickFromPool #[0, 1, 2, 3, 4, 5, 6, 7, 8] r3
    mkFuzzDataCase 9 "small-signed" x w shift r4
  else if shape = 10 then
    let (x, r2) := pickSigned257ish rng1
    let (w, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-10/range-shift-neg-one-{tag}" #[intV x, intV w]
      #[.pushInt (.num (-1)), addrshiftmodcInstr], r4)
  else if shape = 11 then
    let (x, r2) := pickSigned257ish rng1
    let (w, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-11/range-shift-257-{tag}" #[intV x, intV w]
      #[.pushInt (.num 257), addrshiftmodcInstr], r4)
  else if shape = 12 then
    let (x, r2) := pickSigned257ish rng1
    let (w, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-12/range-shift-nan-{tag}" #[intV x, intV w]
      #[.pushInt .nan, addrshiftmodcInstr], r4)
  else
    let (nanInX, r2) := randBool rng1
    let (v, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    if nanInX then
      (mkCase s!"fuzz/shape-13/nan-x-{tag}" #[intV v]
        #[.pushInt .nan, .xchg0 1, .pushInt (.num 1), addrshiftmodcInstr], r4)
    else
      (mkCase s!"fuzz/shape-13/nan-w-{tag}" #[intV v]
        #[.pushInt .nan, .pushInt (.num 1), addrshiftmodcInstr], r4)

def suite : InstrSuite where
  id := addrshiftmodcId
  unit := #[
    { name := "unit/ok/ceil-rounding-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 0, 1, 4, -1),
            (7, 1, 1, 4, 0),
            (-7, 0, 1, -3, -1),
            (-7, -1, 1, -4, 0),
            (5, -7, 1, -1, 0),
            (-5, 7, 1, 1, 0),
            (5, 1, 2, 2, -2),
            (-5, -1, 2, -1, -2),
            (1, 0, 2, 1, -3),
            (-1, 0, 2, 0, -1),
            (0, 0, 3, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}+{w})>>{shift}"
            (runAddrShiftModCDirect #[intV x, intV w, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/ok/shift-zero-and-boundaries"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 0, maxInt257, 0),
            (minInt257, 0, 0, minInt257, 0),
            (maxInt257, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 0, minInt257 + 1, 0),
            (maxInt257, 0, 256, 1, -1),
            (minInt257, 0, 256, -1, 0),
            (-1, 0, 256, 0, -1),
            (1, 0, 256, 1, minInt257 + 1),
            (maxInt257, minInt257, 1, 0, -1)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"boundary/({x}+{w})>>{shift}"
            (runAddrShiftModCDirect #[intV x, intV w, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/error/overflow-and-range-checks"
      run := do
        expectErr "overflow/max-plus-one-shift0"
          (runAddrShiftModCDirect #[intV maxInt257, intV 1, intV 0]) .intOv
        expectErr "overflow/min-minus-one-shift0"
          (runAddrShiftModCDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "range/shift-neg-one"
          (runAddrShiftModCDirect #[intV 7, intV 5, intV (-1)]) .rangeChk
        expectErr "range/shift-257"
          (runAddrShiftModCDirect #[intV 7, intV 5, intV 257]) .rangeChk }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runAddrShiftModCDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runAddrShiftModCDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runAddrShiftModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type-with-two-items"
          (runAddrShiftModCDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-shift-first"
          (runAddrShiftModCDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-w-second"
          (runAddrShiftModCDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third"
          (runAddrShiftModCDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/range-before-w-type"
          (runAddrShiftModCDirect #[intV 1, .null, intV 257]) .rangeChk
        expectErr "error-order/pop-shift-before-w-when-both-non-int"
          (runAddrShiftModCDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-w-before-x-when-shift-int"
          (runAddrShiftModCDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runAddrShiftModCDispatchFallback #[]) #[intV 8080] }
  ]
  oracle := #[
    mkCase "ok/ceil/pos-pos-inexact" #[intV 7, intV 0, intV 1],
    mkCase "ok/ceil/pos-pos-exact" #[intV 7, intV 1, intV 1],
    mkCase "ok/ceil/neg-pos-inexact" #[intV (-7), intV 0, intV 1],
    mkCase "ok/ceil/neg-pos-exact" #[intV (-7), intV (-1), intV 1],
    mkCase "ok/ceil/add-cancel-neg" #[intV 5, intV (-7), intV 1],
    mkCase "ok/ceil/add-cancel-pos" #[intV (-5), intV 7, intV 1],
    mkCase "ok/ceil/small-pos-shift2" #[intV 1, intV 0, intV 2],
    mkCase "ok/ceil/small-neg-shift2" #[intV (-1), intV 0, intV 2],
    mkCase "ok/shift0/max-plus-zero" #[intV maxInt257, intV 0, intV 0],
    mkCase "ok/shift0/min-plus-zero" #[intV minInt257, intV 0, intV 0],
    mkCase "ok/shift0/max-minus-one" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/shift0/min-plus-one" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/shift256/max" #[intV maxInt257, intV 0, intV 256],
    mkCase "ok/shift256/min" #[intV minInt257, intV 0, intV 256],
    mkCase "ok/shift256/neg-one" #[intV (-1), intV 0, intV 256],
    mkCase "ok/shift256/pos-one" #[intV 1, intV 0, intV 256],
    mkCase "ok/boundary/max-plus-min-shift1" #[intV maxInt257, intV minInt257, intV 1],
    mkCase "ok/boundary/min-plus-max-shift256" #[intV minInt257, intV maxInt257, intV 256],
    mkCase "overflow/max-plus-one-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "overflow/min-minus-one-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "type/pop-shift-first-null" #[intV 1, intV 2, .null],
    mkCase "type/pop-shift-first-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/pop-w-second-null" #[intV 1, .null, intV 1],
    mkCase "type/pop-x-third-null" #[.null, intV 1, intV 1],
    mkCase "error-order/pop-shift-before-w-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-x-when-shift-int" #[.null, .cell Cell.empty, intV 1],
    mkCase "error-order/range-before-w-type-via-program" #[intV 1, .null]
      #[.pushInt (.num 257), addrshiftmodcInstr],
    mkCase "range/shift-neg-via-program" #[intV 7, intV 5]
      #[.pushInt (.num (-1)), addrshiftmodcInstr],
    mkCase "range/shift-257-via-program" #[intV 7, intV 5]
      #[.pushInt (.num 257), addrshiftmodcInstr],
    mkCase "range/shift-nan-via-program" #[intV 7, intV 5]
      #[.pushInt .nan, addrshiftmodcInstr],
    mkCase "nan/w-via-program-intov" #[intV 7]
      #[.pushInt .nan, .pushInt (.num 1), addrshiftmodcInstr],
    mkCase "nan/x-via-program-intov" #[intV 5]
      #[.pushInt .nan, .xchg0 1, .pushInt (.num 1), addrshiftmodcInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num addrshiftmodcSetGasExact), .tonEnvOp .setGasLimit, addrshiftmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num addrshiftmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, addrshiftmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020809
      count := 700
      gen := genAddrShiftModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTMODC
