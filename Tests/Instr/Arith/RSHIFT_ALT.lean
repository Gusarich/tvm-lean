import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFT_ALT

/-
RSHIFT_ALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false false 1 (-1) false none)`).
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`).

Branch/terminal outcomes covered by this suite:
- Lean specialization (`mul=false`, `add=false`, `d=1`, `round=-1`, `quiet=false`):
  dispatch/fallback; explicit underflow precheck; shift pop
  (`typeChk`/`rangeChk`/ok); x pop (`typeChk`/ok); numeric-vs-NaN x split;
  non-quiet push (`ok` vs `intOv`).
- C++ specialization (`RSHIFT_ALT`, opcode `0xa924`):
  underflow gate (`check_underflow`), `pop_smallint_range(256)` checks,
  second-pop type check, floor right-shift + invalid-int compatibility funnel,
  non-quiet `push_int_quiet` overflow behavior.

Key risk areas covered:
- floor rounding for mixed signs at `shift ∈ [0, 256]`;
- pop/error order (`shift` is consumed and validated before `x`);
- underflow precedence over shift type/range with single-item stacks;
- out-of-range and NaN shift injection via program only;
- invalid-int compatibility for `x=NaN` (`shift=0` => `intOv`,
  small shifts => `0`, very large shifts => `-1`);
- exact gas threshold (`SETGASLIMIT`) exact vs exact-minus-one.
-/

private def rshiftAltId : InstrId := { name := "RSHIFT_ALT" }

private def rshiftAltInstr : Instr :=
  .arithExt (.shrMod false false 1 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rshiftAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRshiftAltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt rshiftAltInstr stack

private def runRshiftAltDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 808)) stack

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

private def rshiftAltSetGasExact : Int :=
  computeExactGasBudget rshiftAltInstr

private def rshiftAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftAltInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def nanCompatShiftPool : Array Nat :=
  #[0, 1, 2, 12, 13, 64, 128, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickNanCompatShift (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (nanCompatShiftPool.size - 1)
  (nanCompatShiftPool[idx]!, rng')

private def genRshiftAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty-stack" #[], rng1)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-missing-x-after-shift-pop" #[intV x], r2)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int" #[.null], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (useCell, r3) := randBool r2
      let shiftLike : Value := if useCell then .cell Cell.empty else .null
      (mkCase s!"fuzz/shape-{shape}/type-shift-pop-first" #[intV x, shiftLike], r3)
    else if shape = 8 then
      let (shift, r2) := pickShiftInRange rng1
      let (useCell, r3) := randBool r2
      let xLike : Value := if useCell then .cell Cell.empty else .null
      (mkCase s!"fuzz/shape-{shape}/type-x-pop-second" #[xLike, intV (Int.ofNat shift)], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range-shift-negative-via-program"
        #[intV x] #[.pushInt (.num (-1)), rshiftAltInstr], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range-shift-overmax-via-program"
        #[intV x] #[.pushInt (.num 257), rshiftAltInstr], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range-shift-nan-via-program"
        #[intV x] #[.pushInt .nan, rshiftAltInstr], r2)
    else if shape = 12 then
      let (shift, r2) := pickNanCompatShift rng1
      (mkCase s!"fuzz/shape-{shape}/nan-x-invalid-int-compat-via-program"
        #[] #[.pushInt .nan, .pushInt (.num (Int.ofNat shift)), rshiftAltInstr], r2)
    else
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-x-type-via-program"
        #[.null] #[.pushInt (.num 257), rshiftAltInstr], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftAltId
  unit := #[
    { name := "unit/direct/floor-rounding-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (0, 0, 0),
            (7, 1, 3),
            (7, 2, 1),
            (15, 3, 1),
            (-7, 1, -4),
            (-7, 2, -2),
            (-15, 3, -2),
            (1, 1, 0),
            (-1, 1, -1),
            (12345, 8, floorDivPow2 12345 8),
            (-12345, 8, floorDivPow2 (-12345) 8)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>{shift}" (runRshiftAltDirect #[intV x, intV (Int.ofNat shift)]) #[intV expected] }
    ,
    { name := "unit/direct/shift-boundaries-and-extreme-values"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (maxInt257, 0, maxInt257),
            (minInt257, 0, minInt257),
            (maxInt257, 1, (pow2 255) - 1),
            (minInt257, 1, -(pow2 255)),
            (maxInt257, 255, 1),
            (minInt257, 255, -2),
            (maxInt257, 256, 0),
            (maxInt257 - 1, 256, 0),
            (minInt257, 256, -1),
            (minInt257 + 1, 256, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"boundary/{x}>>{shift}" (runRshiftAltDirect #[intV x, intV (Int.ofNat shift)]) #[intV expected] }
    ,
    { name := "unit/error/underflow-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runRshiftAltDirect #[]) .stkUnd
        expectErr "underflow/one-arg-int" (runRshiftAltDirect #[intV 7]) .stkUnd
        expectErr "underflow/one-arg-non-int" (runRshiftAltDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runRshiftAltDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second-null" (runRshiftAltDirect #[.null, intV 7]) .typeChk
        expectErr "type/error-order-both-non-int-shift-first"
          (runRshiftAltDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-rshift-alt-sequence"
      run := do
        let program : Array Instr := #[rshiftAltInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/rshift-alt" s0 rshiftAltInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runRshiftAltDispatchFallback #[]) #[intV 808] }
  ]
  oracle := #[
    mkCase "ok/floor/pos-shift1" #[intV 7, intV 1],
    mkCase "ok/floor/neg-shift1" #[intV (-7), intV 1],
    mkCase "ok/floor/pos-shift2" #[intV 7, intV 2],
    mkCase "ok/floor/neg-shift2" #[intV (-7), intV 2],
    mkCase "ok/floor/shift-zero-pos" #[intV 12345, intV 0],
    mkCase "ok/floor/shift-zero-neg" #[intV (-12345), intV 0],
    mkCase "ok/floor/zero-numerator" #[intV 0, intV 200],
    mkCase "ok/boundary/max-shift1" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/min-shift1" #[intV minInt257, intV 1],
    mkCase "ok/boundary/max-shift255" #[intV maxInt257, intV 255],
    mkCase "ok/boundary/min-shift255" #[intV minInt257, intV 255],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "type/shift-top-non-int" #[intV 7, .null],
    mkCase "type/x-second-non-int" #[.null, intV 1],
    mkCase "type/error-order-both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative-via-program" #[intV 5]
      #[.pushInt (.num (-1)), rshiftAltInstr],
    mkCase "range/shift-overmax-via-program" #[intV 5]
      #[.pushInt (.num 257), rshiftAltInstr],
    mkCase "range/shift-nan-via-program" #[intV 5]
      #[.pushInt .nan, rshiftAltInstr],
    mkCase "error-order/range-before-x-type-via-program" #[.null]
      #[.pushInt (.num 257), rshiftAltInstr],
    mkCase "nan/x-via-program-shift0-intov" #[]
      #[.pushInt .nan, .pushInt (.num 0), rshiftAltInstr],
    mkCase "nan/x-via-program-shift1-zero" #[]
      #[.pushInt .nan, .pushInt (.num 1), rshiftAltInstr],
    mkCase "nan/x-via-program-shift13-minus-one" #[]
      #[.pushInt .nan, .pushInt (.num 13), rshiftAltInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num rshiftAltSetGasExact), .tonEnvOp .setGasLimit, rshiftAltInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num rshiftAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftAltInstr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 700
      gen := genRshiftAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFT_ALT
