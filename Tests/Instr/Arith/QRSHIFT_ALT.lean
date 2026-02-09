import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QRSHIFT_ALT

/-
QRSHIFT_ALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false false 1 (-1) true none)`).
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (24-bit quiet SHR/MOD decode family: `0xb7a924..0xb7a926`).
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet SHR/MOD encoding through 24-bit `0xb7 || p16` form).
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, quiet wiring in `register_div_ops`).

Branch/terminal counts used for this suite:
- Lean specialization: 7 branch sites / 13 terminal outcomes
  (dispatch/fallback; underflow gate; `popNatUpTo 256` split
  `typeChk`/`rangeChk`/ok; `popInt` split `typeChk`/ok; shift-zero round remap;
  finite-vs-NaN `x` split; quiet push funnel `ok`/`NaN`).
- C++ specialization: 5 branch sites / 11 aligned terminal outcomes
  (`check_underflow`; `pop_smallint_range(256)` checks; `pop_int` type check;
  `y == 0` round remap; `rshift + push_int_quiet` quiet result funnel).

Key risk areas covered:
- alt-encoding semantics (`QRSHIFT_ALT` 24-bit `0xb7a924 + round_ofs`)
  vs non-alt `QRSHIFT` (`0xb7ab imm8`) and `QRSHIFT_VAR` (`0xb7ad`);
- floor shift boundaries (`shift ∈ [0, 256]`) for `maxInt257/minInt257`;
- strict shift validation even in quiet mode (`NaN`, negative, `>256` => `rangeChk`);
- pop/error ordering (shift is consumed/validated before `x`, underflow first);
- quiet invalid-int compatibility for `x = NaN`
  (`shift=0 => NaN`, `1..12 => 0`, `>=13 => -1`);
- oracle NaN/out-of-range injection via program (`PUSHINT` prelude);
- exact gas cliff (`SETGASLIMIT`) exact vs exact-minus-one.
-/

private def qrshiftAltId : InstrId := { name := "QRSHIFT_ALT" }

private def qrshiftAltInstr : Instr :=
  .arithExt (.shrMod false false 1 (-1) true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qrshiftAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qrshiftAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qrshiftAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQrshiftAltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qrshiftAltInstr stack

private def runQrshiftAltDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
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

private def qrshiftAltSetGasExact : Int :=
  computeExactGasBudget qrshiftAltInstr

private def qrshiftAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qrshiftAltInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 11, 12, 13, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

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

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genQrshiftAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 4 then
      let (variant, r2) := randNat rng1 0 3
      if variant = 0 then
        (mkCase s!"fuzz/shape-{shape}/ok/extreme/max-shift256"
          #[intV maxInt257, intV 256], r2)
      else if variant = 1 then
        (mkCase s!"fuzz/shape-{shape}/ok/extreme/min-shift256"
          #[intV minInt257, intV 256], r2)
      else if variant = 2 then
        (mkCase s!"fuzz/shape-{shape}/ok/extreme/max-shift255"
          #[intV maxInt257, intV 255], r2)
      else
        (mkCase s!"fuzz/shape-{shape}/ok/extreme/min-shift255"
          #[intV minInt257, intV 255], r2)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/missing-x-after-shift-pop" #[intV x], r2)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/underflow/single-non-int" #[.null], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/shift-pop-first" #[intV x, shiftLike], r3)
    else if shape = 9 then
      let (shift, r2) := pickShiftInRange rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/x-pop-second" #[xLike, intV (Int.ofNat shift)], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative-via-program"
        #[intV x] #[.pushInt (.num (-1)), qrshiftAltInstr], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range/shift-overmax-via-program"
        #[intV x] #[.pushInt (.num 257), qrshiftAltInstr], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/range/shift-nan-via-program"
        #[intV x] #[.pushInt .nan, qrshiftAltInstr], r2)
    else if shape = 13 then
      let (shift, r2) := pickNanCompatShift rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-invalid-int-compat-via-program"
        #[.nan, .num (Int.ofNat shift)], r2)
    else if shape = 14 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-random-shift-via-program"
        #[.nan, .num (Int.ofNat shift)], r2)
    else if shape = 15 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-qrshift-alt"
        #[.num xOut, .num (Int.ofNat shift)], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftOut, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-qrshift-alt"
        #[.num x, .num shiftOut], r3)
    else if shape = 17 then
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-via-program"
        #[.null] #[.pushInt (.num 257), qrshiftAltInstr], rng1)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shiftOut, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-qrshift-alt"
        #[.num xOut, .num shiftOut], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qrshiftAltId
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
          expectOkStack s!"{x}>>{shift}" (runQrshiftAltDirect #[intV x, intV (Int.ofNat shift)]) #[intV expected] }
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
          expectOkStack s!"boundary/{x}>>{shift}" (runQrshiftAltDirect #[intV x, intV (Int.ofNat shift)]) #[intV expected] }
    ,
    { name := "unit/quiet/nan-invalid-int-compat-and-range-funnel"
      run := do
        let nanChecks : Array (Nat × IntVal) :=
          #[
            (0, .nan),
            (1, .num 0),
            (2, .num 0),
            (12, .num 0),
            (13, .num (-1)),
            (256, .num (-1))
          ]
        for c in nanChecks do
          let shift := c.1
          let expected := c.2
          expectOkStack s!"quiet/nan-x/shift-{shift}"
            (runQrshiftAltDirect #[.int .nan, intV (Int.ofNat shift)])
            #[.int expected]
        expectOkStack "quiet/out-of-range-x/high-shift0"
          (runQrshiftAltDirect #[intV (maxInt257 + 1), intV 0]) #[.int .nan]
        expectOkStack "quiet/out-of-range-x/low-shift0"
          (runQrshiftAltDirect #[intV (minInt257 - 1), intV 0]) #[.int .nan]
        expectOkStack "quiet/out-of-range-x/high-shift1-becomes-finite"
          (runQrshiftAltDirect #[intV (maxInt257 + 1), intV 1]) #[intV (pow2 255)] }
    ,
    { name := "unit/error/underflow-range-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runQrshiftAltDirect #[]) .stkUnd
        expectErr "underflow/one-arg-int" (runQrshiftAltDirect #[intV 7]) .stkUnd
        expectErr "underflow/one-arg-non-int" (runQrshiftAltDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runQrshiftAltDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second-null" (runQrshiftAltDirect #[.null, intV 7]) .typeChk
        expectErr "range/shift-negative" (runQrshiftAltDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax" (runQrshiftAltDirect #[intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runQrshiftAltDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "error-order/range-before-x-type"
          (runQrshiftAltDirect #[.null, intV 257]) .rangeChk }
    ,
    { name := "unit/opcode/alt-encoding-and-neighbor-family-decode"
      run := do
        let qrshiftImmInstr : Instr := .rshiftConst true 1
        let qrshiftVarInstr : Instr := .arithExt (.rshiftVar true)
        let program : Array Instr := #[qrshiftAltInstr, qrshiftImmInstr, qrshiftVarInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qrshift-alt" s0 qrshiftAltInstr 24
        let s2 ← expectDecodeStep "decode/qrshift-imm" s1 qrshiftImmInstr 24
        let s3 ← expectDecodeStep "decode/qrshift-var" s2 qrshiftVarInstr 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQrshiftAltDispatchFallback #[]) #[intV 909] }
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
    mkCase "type/error-order/both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative-via-program" #[intV 5]
      #[.pushInt (.num (-1)), qrshiftAltInstr],
    mkCase "range/shift-overmax-via-program" #[intV 5]
      #[.pushInt (.num 257), qrshiftAltInstr],
    mkCase "range/shift-nan-via-program" #[intV 5]
      #[.pushInt .nan, qrshiftAltInstr],
    mkCase "error-order/range-before-x-type-via-program" #[.null]
      #[.pushInt (.num 257), qrshiftAltInstr],
    mkCaseFromIntVals "quiet/nan-x-via-program/shift0-nan" #[.nan, .num 0],
    mkCaseFromIntVals "quiet/nan-x-via-program/shift1-zero" #[.nan, .num 1],
    mkCaseFromIntVals "quiet/nan-x-via-program/shift12-zero" #[.nan, .num 12],
    mkCaseFromIntVals "quiet/nan-x-via-program/shift13-minus-one" #[.nan, .num 13],
    mkCaseFromIntVals "quiet/nan-x-via-program/shift256-minus-one" #[.nan, .num 256],
    mkCaseFromIntVals "error-order/pushint-overflow-high-x-before-qrshift-alt"
      #[.num (maxInt257 + 1), .num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-low-x-before-qrshift-alt"
      #[.num (minInt257 - 1), .num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-before-qrshift-alt"
      #[.num 5, .num (maxInt257 + 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qrshiftAltSetGasExact), .tonEnvOp .setGasLimit, qrshiftAltInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qrshiftAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, qrshiftAltInstr]
  ]
  fuzz := #[
    { seed := 2026020830
      count := 700
      gen := genQrshiftAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFT_ALT
