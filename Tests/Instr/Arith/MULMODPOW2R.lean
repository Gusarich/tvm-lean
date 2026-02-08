import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODPOW2R

/-
MULMODPOW2R branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Ext.lean`
  (`execInstrArithExt`, `.arithExt (.shrMod true false 2 0 false none)` path).
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_shrmod`, opcode wiring in `register_div_ops`).

Branch counts used for this suite (specialized path):
- Lean: ~8 branch sites / ~11 terminal outcomes
  (dispatch; pre-pop depth gate; shift pop `typeChk`; shift range gate; `y` pop;
   `x` pop; numeric-vs-NaN operand split; non-quiet push result).
- C++: ~6 branch sites / ~9 aligned terminal outcomes
  (`check_underflow`; `pop_smallint_range(256)` type/range split;
   `y==0` round remap; `pop_int` order (`y` then `x`); `d=2` remainder push).

Key risk areas covered:
- runtime shift pop/range ordering (`shift` checked before `y`/`x`);
- pre-pop underflow gate (`stkUnd`) before shift/type/range in runtime-shift mode;
- strict shift bounds (`0..256`) and NaN shift handling (`rangeChk`), via program injection only;
- `shift=0` round-mode remap and deterministic modulo result (`0`);
- non-quiet NaN propagation from operands (`intOv`), injected via program only;
- signed 257-bit boundary behavior around `±2^256` with large products;
- exact gas boundary determinism (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def mulModPow2RId : InstrId := { name := "MULMODPOW2R" }

private def mulModPow2RInstr : Instr :=
  .arithExt (.shrMod true false 2 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulModPow2RInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulModPow2RId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulModPow2RDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulModPow2RInstr stack

private def runMulModPow2RDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 606)) stack

private def mulModPow2RSetGasExact : Int :=
  computeExactGasBudget mulModPow2RInstr

private def mulModPow2RSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulModPow2RInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftUniform rng1

private def mkFuzzDataCase
    (shape : Nat)
    (kind : String)
    (x : Int)
    (y : Int)
    (shift : Nat)
    (rng : StdGen) : OracleCase × StdGen :=
  let (tag, rng') := randNat rng 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV (Int.ofNat shift)], rng')

private def genMulModPow2RFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (x, r2) := pickInt257Boundary rng1
    let (y, r3) := pickInt257Boundary r2
    let (shift, r4) := pickShiftBoundary r3
    mkFuzzDataCase 0 "boundary-boundary" x y shift r4
  else if shape = 1 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickSigned257ish r2
    let (shift, r4) := pickShiftBoundary r3
    mkFuzzDataCase 1 "signed-boundary-shift" x y shift r4
  else if shape = 2 then
    let (x, r2) := pickInt257Boundary rng1
    let (y, r3) := pickSigned257ish r2
    let (shift, r4) := pickShiftMixed r3
    mkFuzzDataCase 2 "x-boundary" x y shift r4
  else if shape = 3 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickInt257Boundary r2
    let (shift, r4) := pickShiftMixed r3
    mkFuzzDataCase 3 "y-boundary" x y shift r4
  else if shape = 4 then
    let (y, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftMixed r2
    mkFuzzDataCase 4 "x-zero" 0 y shift r3
  else if shape = 5 then
    let (x, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftMixed r2
    mkFuzzDataCase 5 "y-zero" x 0 shift r3
  else if shape = 6 then
    let (useMax, r2) := randBool rng1
    let x := if useMax then maxInt257 else minInt257
    let y := if useMax then 1 else (-1)
    let (shift, r3) := pickShiftBoundary r2
    mkFuzzDataCase 6 "extreme-times-unit" x y shift r3
  else if shape = 7 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-7/range-shift-neg-one-via-program-{tag}" #[intV x, intV y]
      #[.pushInt (.num (-1)), mulModPow2RInstr], r4)
  else if shape = 8 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-8/range-shift-257-via-program-{tag}" #[intV x, intV y]
      #[.pushInt (.num 257), mulModPow2RInstr], r4)
  else if shape = 9 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-9/range-shift-nan-via-program-{tag}" #[intV x, intV y]
      #[.pushInt .nan, mulModPow2RInstr], r4)
  else if shape = 10 then
    let (y, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftMixed r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-10/nan-x-via-program-{tag}" #[intV (Int.ofNat shift), intV y]
      #[.pushInt .nan, .xchg0 2, mulModPow2RInstr], r4)
  else if shape = 11 then
    let (x, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftMixed r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-11/nan-y-via-program-{tag}" #[intV x, intV (Int.ofNat shift)]
      #[.pushInt .nan, .xchg0 1, mulModPow2RInstr], r4)
  else if shape = 12 then
    let (x, r2) := pickSigned257ish rng1
    let (y, r3) := pickSigned257ish r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-12/type-shift-pop-first-{tag}" #[intV x, intV y, .null], r4)
  else if shape = 13 then
    let (x, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftMixed r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-13/type-y-pop-second-{tag}" #[intV x, .null, intV (Int.ofNat shift)], r4)
  else if shape = 14 then
    let (y, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftMixed r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-14/type-x-pop-third-{tag}" #[.null, intV y, intV (Int.ofNat shift)], r4)
  else if shape = 15 then
    let (x, r2) := pickSigned257ish rng1
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/shape-15/range-before-y-type-via-program-{tag}" #[intV x, .null]
      #[.pushInt (.num (-1)), mulModPow2RInstr], r3)
  else if shape = 16 then
    let (x, r2) := pickSigned257ish rng1
    let (shift, r3) := pickShiftMixed r2
    let (tag, r4) := randNat r3 0 999_999
    (mkCase s!"fuzz/shape-16/underflow-missing-x-{tag}" #[intV x, intV (Int.ofNat shift)], r4)
  else
    let (shift, r2) := pickShiftMixed rng1
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/shape-17/underflow-missing-y-{tag}" #[intV (Int.ofNat shift)], r3)

def suite : InstrSuite where
  id := mulModPow2RId
  unit := #[
    { name := "unit/ok/nearest-mod-product-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 5, 1, -1),
            (-7, 5, 1, -1),
            (7, -5, 1, -1),
            (-7, -5, 1, -1),
            (3, 2, 2, -2),
            (-3, 2, 2, -2),
            (3, -2, 2, -2),
            (5, 1, 3, -3),
            (-5, 1, 3, 3),
            (9, 1, 2, 1),
            (-9, 1, 2, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"{x}*{y} modPow2R {shift}"
            (runMulModPow2RDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/ok/boundary-extremes-and-shift-edges"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 256, -1),
            (maxInt257 - 1, 1, 256, -2),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, 1, 256, 1),
            (maxInt257, -1, 256, 1),
            (minInt257, -1, 256, 0),
            (maxInt257, 2, 0, 0),
            (minInt257, -1, 0, 0),
            (maxInt257, 0, 255, 0),
            (minInt257, 0, 255, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"boundary/{x}*{y} modPow2R {shift}"
            (runMulModPow2RDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulModPow2RDirect #[]) .stkUnd
        expectErr "underflow/missing-y" (runMulModPow2RDirect #[intV 3]) .stkUnd
        expectErr "underflow/missing-x" (runMulModPow2RDirect #[intV 9, intV 2]) .stkUnd
        expectErr "type/shift-pop-first" (runMulModPow2RDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/y-pop-second" (runMulModPow2RDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/x-pop-third" (runMulModPow2RDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/depth-underflow-before-y-type"
          (runMulModPow2RDirect #[.null, intV 2]) .stkUnd
        expectErr "error-order/depth-underflow-before-shift-type"
          (runMulModPow2RDirect #[.null]) .stkUnd
        expectErr "error-order/y-pop-before-x-when-both-non-int"
          (runMulModPow2RDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulModPow2RDispatchFallback #[]) #[intV 606] }
  ]
  oracle := #[
    mkCase "ok/shift0/zero-product" #[intV 0, intV 17, intV 0],
    mkCase "ok/shift0/nonzero-product" #[intV 9, intV (-11), intV 0],
    mkCase "ok/sign/pos-pos-shift1" #[intV 7, intV 5, intV 1],
    mkCase "ok/sign/neg-pos-shift1" #[intV (-7), intV 5, intV 1],
    mkCase "ok/sign/pos-neg-shift1" #[intV 7, intV (-5), intV 1],
    mkCase "ok/sign/neg-neg-shift1" #[intV (-7), intV (-5), intV 1],
    mkCase "ok/nearest/tie-pos-shift2" #[intV 3, intV 2, intV 2],
    mkCase "ok/nearest/tie-neg-shift2" #[intV (-3), intV 2, intV 2],
    mkCase "ok/general/pos-shift3" #[intV 5, intV 1, intV 3],
    mkCase "ok/general/neg-shift3" #[intV (-5), intV 1, intV 3],
    mkCase "ok/general/pos-neg-shift3" #[intV 5, intV (-1), intV 3],
    mkCase "ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/max-minus-one-times-one-shift256" #[intV (maxInt257 - 1), intV 1, intV 256],
    mkCase "ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-plus-one-times-one-shift256" #[intV (minInt257 + 1), intV 1, intV 256],
    mkCase "ok/boundary/max-times-neg1-shift256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "ok/boundary/min-times-neg1-shift256" #[intV minInt257, intV (-1), intV 256],
    mkCase "ok/boundary/shift255" #[intV maxInt257, intV 1, intV 255],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-y-after-shift-pop" #[intV 1],
    mkCase "underflow/missing-x-after-y-pop" #[intV 7, intV 1],
    mkCase "type/shift-pop-first-null" #[intV 1, intV 2, .null],
    mkCase "type/y-pop-second-null" #[intV 1, .null, intV 2],
    mkCase "type/x-pop-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/depth-underflow-before-y-type" #[.null, intV 2],
    mkCase "error-order/y-pop-before-x-when-both-non-int" #[.null, .cell Cell.empty, intV 1],
    mkCase "range/shift-negative-via-program" #[intV 7, intV 5]
      #[.pushInt (.num (-1)), mulModPow2RInstr],
    mkCase "range/shift-257-via-program" #[intV 7, intV 5]
      #[.pushInt (.num 257), mulModPow2RInstr],
    mkCase "range/shift-nan-via-program" #[intV 7, intV 5]
      #[.pushInt .nan, mulModPow2RInstr],
    mkCase "error-order/range-before-y-type-via-program" #[intV 7, .null]
      #[.pushInt (.num (-1)), mulModPow2RInstr],
    mkCase "error-order/underflow-before-range-via-program" #[]
      #[.pushInt (.num (-1)), mulModPow2RInstr],
    mkCase "nan/x-via-program-intov" #[intV 5, intV 3]
      #[.pushInt .nan, .xchg0 2, mulModPow2RInstr],
    mkCase "nan/y-via-program-intov" #[intV 7, intV 5]
      #[.pushInt .nan, .xchg0 1, mulModPow2RInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulModPow2RSetGasExact), .tonEnvOp .setGasLimit, mulModPow2RInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulModPow2RSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulModPow2RInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genMulModPow2RFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2R
