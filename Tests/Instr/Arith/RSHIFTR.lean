import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTR

/-
RSHIFTR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod` non-mul path)
  - `TvmLean/Model/Basics/Bytes.lean` (`rshiftPow2Round`, nearest/tie behavior)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`)

Branch/terminal outcomes mapped by this suite:
- Lean (`.shrMod` with `mul=false`, `add=false`, `d=1`, `roundMode=0`):
  dispatch/fallback; explicit underflow gate; shift pop range/type/success;
  operand pop type/success; numeric-vs-NaN split; non-quiet push (`ok` vs `intOv`).
- C++ (`exec_shrmod` specialization for `RSHIFTR`):
  opcode args decode (`0xa925`); `check_underflow(2)`; `pop_smallint_range(256)`
  range/type/success; `pop_int` type/success; non-quiet `push_int_quiet` NaN funnel.

Key risk areas covered:
- nearest rounding ties must go toward `+∞` (e.g. `-1 >>R 1 = 0`);
- runtime `shift=0` forces floor mode (`roundMode := -1`) in this family;
- strict runtime shift bounds `[0, 256]`;
- error ordering: underflow must happen before shift type/range for single-item stacks;
- NaN must be program-injected for oracle/fuzz serialization paths.
-/

private def rshiftrId : InstrId := { name := "RSHIFTR" }

private def rshiftrInstr : Instr :=
  .arithExt (.shrMod false false 1 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rshiftrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRshiftrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt rshiftrInstr stack

private def runRshiftrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 909)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def rshiftrSetGasExact : Int :=
  computeExactGasBudget rshiftrInstr

private def rshiftrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftrInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOverflowPool : Array Int :=
  #[257, 258, 511, 1024]

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftBoundaryPool rng

private def pickShiftOverflow (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftOverflowPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def genRshiftrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
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
      let (x, r2) := pickFromIntPool tieNumeratorPool rng1
      (mkCase s!"fuzz/shape-{shape}/ok-tie-shift1" #[intV x, intV 1], r2)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-shift-zero-floor" #[intV x, intV 0], r2)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-shift-256-boundary" #[intV x, intV 256], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (negMag, r3) := randNat r2 1 4
      let shift : Int := -Int.ofNat negMag
      (mkCase s!"fuzz/shape-{shape}/range-negative-shift" #[intV x, intV shift], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftOverflow r2
      (mkCase s!"fuzz/shape-{shape}/range-overmax-shift" #[intV x, intV shift], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" #[intV x]
        #[.pushInt .nan, rshiftrInstr], r2)
    else if shape = 8 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCase s!"fuzz/shape-{shape}/nan-x-via-program" #[intV shift]
        #[.pushInt .nan, .xchg0 1, rshiftrInstr], r2)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 10 then
      let (pickRangeVal, r2) := randBool rng1
      let stack : Array Value := if pickRangeVal then #[intV 1] else #[intV 257]
      let kind : String := if pickRangeVal then "underflow-single-int" else "underflow-single-range-int"
      (mkCase s!"fuzz/shape-{shape}/{kind}" stack, r2)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int-regression" #[.null], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (pickNull, r3) := randBool r2
      let shiftLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-shift-non-int" #[intV x, shiftLike], r3)
    else
      let (shift, r2) := pickShiftInRange rng1
      let (pickNull, r3) := randBool r2
      let xLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, intV shift], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftrId
  unit := #[
    { name := "unit/round/sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 1, 4),
            (-7, 1, -3),
            (5, 1, 3),
            (-5, 1, -2),
            (1, 1, 1),
            (-1, 1, 0),
            (3, 1, 2),
            (-3, 1, -1),
            (7, 2, 2),
            (-7, 2, -2),
            (9, 3, 1),
            (-9, 3, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>R{shift}" (runRshiftrDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/round/shift-zero-and-boundary-high-shifts"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (12345, 0, 12345),
            (-12345, 0, -12345),
            (maxInt257, 256, 1),
            (maxInt257 - 1, 256, 1),
            (minInt257, 256, -1),
            (minInt257 + 1, 256, -1),
            (pow2 255, 256, 1),
            (-(pow2 255), 256, 0),
            (maxInt257, 255, 2),
            (minInt257, 255, -2)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>R{shift}" (runRshiftrDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/error/underflow-range-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runRshiftrDirect #[]) .stkUnd
        expectErr "underflow/single-int-before-range" (runRshiftrDirect #[intV 257]) .stkUnd
        expectErr "regression/single-non-int-underflow-before-type" (runRshiftrDirect #[.null]) .stkUnd
        expectErr "range/shift-negative-before-x-type" (runRshiftrDirect #[.null, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax-before-x-type" (runRshiftrDirect #[.cell Cell.empty, intV 257]) .rangeChk
        expectErr "type/shift-top-non-int" (runRshiftrDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second-non-int" (runRshiftrDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[rshiftrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/rshiftr" s0 rshiftrInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-rshiftr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runRshiftrDispatchFallback #[]) #[intV 909] }
  ]
  oracle := #[
    mkCase "ok/round/pos-shift1-half-up" #[intV 7, intV 1],
    mkCase "ok/round/neg-shift1-half-up-to-plus-inf" #[intV (-7), intV 1],
    mkCase "ok/round/pos-shift2-inexact" #[intV 7, intV 2],
    mkCase "ok/round/neg-shift2-inexact" #[intV (-7), intV 2],
    mkCase "ok/tie/plus-half" #[intV 1, intV 1],
    mkCase "ok/tie/minus-half" #[intV (-1), intV 1],
    mkCase "ok/tie/plus-three-halves" #[intV 3, intV 1],
    mkCase "ok/tie/minus-three-halves" #[intV (-3), intV 1],
    mkCase "ok/shift-zero/identity-pos" #[intV 12345, intV 0],
    mkCase "ok/shift-zero/identity-neg" #[intV (-12345), intV 0],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/half-up-pos" #[intV (pow2 255), intV 256],
    mkCase "ok/boundary/half-up-neg-to-zero" #[intV (-(pow2 255)), intV 256],
    mkCase "ok/boundary/max-shift255" #[intV maxInt257, intV 255],
    mkCase "ok/boundary/min-shift255" #[intV minInt257, intV 255],
    mkCase "range/shift-negative" #[intV 7, intV (-1)],
    mkCase "range/shift-overmax" #[intV 7, intV 257],
    mkCase "range/shift-nan-via-program" #[intV 7] #[.pushInt .nan, rshiftrInstr],
    mkCase "nan/x-via-program" #[intV 1] #[.pushInt .nan, .xchg0 1, rshiftrInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/single-int" #[intV 1],
    mkCase "regression/error-order/underflow-before-range-single-int257" #[intV 257],
    mkCase "regression/error-order/underflow-before-shift-type-single-non-int" #[.null],
    mkCase "type/shift-top-non-int" #[intV 7, .null],
    mkCase "type/x-second-non-int" #[.null, intV 1],
    mkCase "error-order/range-before-x-type-negative" #[.null, intV (-1)],
    mkCase "error-order/range-before-x-type-overmax" #[.cell Cell.empty, intV 257],
    mkCase "gas/exact-succeeds" #[intV 7, intV 1]
      #[.pushInt (.num rshiftrSetGasExact), .tonEnvOp .setGasLimit, rshiftrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 1]
      #[.pushInt (.num rshiftrSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftrInstr]
  ]
  fuzz := #[
    { seed := 2026020808
      count := 700
      gen := genRshiftrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTR
