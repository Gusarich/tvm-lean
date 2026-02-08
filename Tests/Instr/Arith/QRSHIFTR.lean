import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QRSHIFTR

/-
QRSHIFTR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod` non-mul path for `d=1`, `quiet=true`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, nearest/tie behavior used by this rounding variant)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`, quiet map `0xb7a925`)

Branch counts used for this suite:
- Lean: 7 branch points / 10 terminal outcomes
  (dispatch/fallback; explicit underflow gate; `popNatUpTo 256` shift pop
   success/type/range; `popInt` on `x`; `shift=0` round-mode override;
   `x` numeric-vs-NaN split; quiet push path).
- C++: 6 branch points / 10 aligned terminal outcomes
  (opcode decode to quiet mode; `check_underflow(2)`; `pop_smallint_range(256)`;
   `y==0` round-mode override; `pop_int` on `x`; `push_int_quiet` quiet behavior).

Key risk areas covered:
- nearest rounding ties toward `+∞` (`-1 >>R 1 = 0`, not `-1`);
- runtime `shift=0` override to floor mode (`roundMode := -1`);
- arithmetic sign-extension boundaries (`shift=255/256` near `±2^255`, `±2^256`);
- quiet NaN handling quirk for this opcode (`x=NaN`: `shift>0 -> 0`, `shift=0 -> NaN`);
- quiet mode does not silence shift range/type failures (`popNatUpTo 256`);
- deterministic gas boundary for `PUSHINT n; SETGASLIMIT; QRSHIFTR`.
-/

private def qrshiftrId : InstrId := { name := "QRSHIFTR" }

private def qrshiftrInstr : Instr :=
  .arithExt (.shrMod false false 1 0 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qrshiftrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qrshiftrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def shiftFitsQrshiftrRange (v : IntVal) : Bool :=
  match v with
  | .nan => false
  | .num n => decide (0 ≤ n ∧ n ≤ 256)

private def mkInputCase
    (name : String)
    (x shift : IntVal)
    (below : Array Value := #[])
    (programSuffix : Array Instr := #[qrshiftrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let forceProgramInject : Bool :=
    !(intValOracleSerializable x) || !(shiftFitsQrshiftrRange shift)
  let (stack, progPrefix) :=
    if forceProgramInject then
      (#[], #[.pushInt x, .pushInt shift])
    else
      oracleIntInputsToStackOrProgram #[x, shift]
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def runQrshiftrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qrshiftrInstr stack

private def runQrshiftrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 911)) stack

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

private def qrshiftrSetGasExact : Int :=
  computeExactGasBudget qrshiftrInstr

private def qrshiftrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qrshiftrInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickTieNumerator (rng : StdGen) : Int × StdGen :=
  pickFromIntPool tieNumeratorPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (isNull, rng') := randBool rng
  ((if isNull then .null else .cell Cell.empty), rng')

private def genQrshiftrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkInputCase s!"fuzz/shape-{shape}/ok-boundary-x-shift" (.num x) (.num shift), r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/ok-random-inrange" (.num x) (.num shift), r3)
    else if shape = 2 then
      let (x, r2) := pickTieNumerator rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok-tie-shift1" (.num x) (.num 1), r2)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok-shift0-floor-override" (.num x) (.num 0), r2)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok-shift256-boundary" (.num x) (.num 256), r2)
    else if shape = 5 then
      let (shift, r2) := pickShiftBoundary rng1
      let shift' := if shift = 0 then (1 : Int) else shift
      (mkInputCase s!"fuzz/shape-{shape}/nan-x-shift-positive" .nan (.num shift'), r2)
    else if shape = 6 then
      (mkInputCase s!"fuzz/shape-{shape}/nan-x-shift0" .nan (.num 0), rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" (.num x) .nan, r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (negMag, r3) := randNat r2 1 16
      let shift : Int := -Int.ofNat negMag
      (mkInputCase s!"fuzz/shape-{shape}/range-shift-negative-via-program" (.num x) (.num shift), r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromIntPool #[257, 258, 511, 1024] r2
      (mkInputCase s!"fuzz/shape-{shape}/range-shift-overmax-via-program" (.num x) (.num shift), r3)
    else if shape = 10 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/range-x-out-of-257-via-program" (.num x) (.num shift), r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-int" #[intV x], r2)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int" #[.null], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type-shift-top-non-int" #[intV x, nonInt], r3)
    else if shape = 15 then
      let (shift, r2) := pickShiftInRange rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type-x-second-non-int" #[nonInt, intV shift], r3)
    else
      let (xNonInt, r2) := pickNonInt rng1
      let (useNegative, r3) := randBool r2
      let shift : Int := if useNegative then -1 else 257
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-x-type"
        #[xNonInt] #[.pushInt (.num shift), qrshiftrInstr], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qrshiftrId
  unit := #[
    { name := "unit/round/nearest-ties-and-sign-behavior"
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
            (15, 2, 4),
            (-15, 2, -4),
            (9, 3, 1),
            (-9, 3, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>QR{shift}" (runQrshiftrDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/round/shift-zero-override-and-boundary-256"
      run := do
        let checks : Array (Int × Int × IntVal) :=
          #[
            (12345, 0, .num 12345),
            (-12345, 0, .num (-12345)),
            (maxInt257, 256, .num 1),
            (maxInt257 - 1, 256, .num 1),
            (minInt257, 256, .num (-1)),
            (minInt257 + 1, 256, .num (-1)),
            (pow2 255, 256, .num 1),
            (-(pow2 255), 256, .num 0),
            (-(pow2 255) - 1, 256, .num (-1)),
            (-1, 256, .num 0)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>QR{shift}" (runQrshiftrDirect #[intV x, intV shift]) #[.int expected] }
    ,
    { name := "unit/quiet/nan-and-range-behavior"
      run := do
        expectOkStack "nan/x-shift-positive-pushes-zero"
          (runQrshiftrDirect #[.int .nan, intV 1]) #[intV 0]
        expectOkStack "nan/x-shift-zero-pushes-nan"
          (runQrshiftrDirect #[.int .nan, intV 0]) #[.int .nan]
        expectErr "range/shift-nan-even-in-quiet-mode"
          (runQrshiftrDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "range/shift-negative-even-in-quiet-mode"
          (runQrshiftrDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax-even-in-quiet-mode"
          (runQrshiftrDirect #[intV 7, intV 257]) .rangeChk }
    ,
    { name := "unit/error/underflow-type-range-ordering"
      run := do
        expectErr "underflow/empty" (runQrshiftrDirect #[]) .stkUnd
        expectErr "underflow/single-int-before-range-check" (runQrshiftrDirect #[intV 257]) .stkUnd
        expectErr "underflow/single-non-int-before-type-check" (runQrshiftrDirect #[.null]) .stkUnd
        expectErr "type/shift-top-non-int" (runQrshiftrDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second-non-int" (runQrshiftrDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/range-before-x-type-negative-shift"
          (runQrshiftrDirect #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-overmax-shift"
          (runQrshiftrDirect #[.cell Cell.empty, intV 257]) .rangeChk }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[qrshiftrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qrshiftr" s0 qrshiftrInstr 24
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-qrshiftr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQrshiftrDispatchFallback #[]) #[intV 911] }
  ]
  oracle := #[
    mkInputCase "ok/round/pos-shift1-half-up" (.num 7) (.num 1),
    mkInputCase "ok/round/neg-shift1-half-up-to-plus-inf" (.num (-7)) (.num 1),
    mkInputCase "ok/tie/plus-half" (.num 1) (.num 1),
    mkInputCase "ok/tie/minus-half" (.num (-1)) (.num 1),
    mkInputCase "ok/tie/plus-three-halves" (.num 3) (.num 1),
    mkInputCase "ok/tie/minus-three-halves" (.num (-3)) (.num 1),
    mkInputCase "ok/shift-zero/identity-pos" (.num 12345) (.num 0),
    mkInputCase "ok/shift-zero/identity-neg" (.num (-12345)) (.num 0),
    mkInputCase "ok/boundary/max-shift256" (.num maxInt257) (.num 256),
    mkInputCase "ok/boundary/max-minus-one-shift256" (.num (maxInt257 - 1)) (.num 256),
    mkInputCase "ok/boundary/min-shift256" (.num minInt257) (.num 256),
    mkInputCase "ok/boundary/min-plus-one-shift256" (.num (minInt257 + 1)) (.num 256),
    mkInputCase "ok/boundary/plus-half-at-2^255" (.num (pow2 255)) (.num 256),
    mkInputCase "ok/boundary/minus-half-at-2^255" (.num (-(pow2 255))) (.num 256),
    mkInputCase "ok/boundary/below-minus-half-at-2^255" (.num (-(pow2 255) - 1)) (.num 256),
    mkInputCase "ok/boundary/max-shift255" (.num maxInt257) (.num 255),
    mkInputCase "ok/boundary/min-shift255" (.num minInt257) (.num 255),
    mkInputCase "ok/sign-extension/minus-one-shift256-to-zero" (.num (-1)) (.num 256),
    mkInputCase "nan/x-shift-positive-via-program" .nan (.num 1),
    mkInputCase "nan/x-shift-zero-via-program" .nan (.num 0),
    mkInputCase "range/shift-nan-via-program" (.num 7) .nan,
    mkInputCase "range/shift-negative-via-program" (.num 7) (.num (-1)),
    mkInputCase "range/shift-overmax-via-program" (.num 7) (.num 257),
    mkInputCase "range/x-high-via-program" (.num (maxInt257 + 1)) (.num 1),
    mkInputCase "range/x-low-via-program" (.num (minInt257 - 1)) (.num 1),
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/single-int-stack" #[intV 1],
    mkCase "underflow/single-non-int-stack" #[.null],
    mkCase "type/shift-top-non-int" #[intV 7, .null],
    mkCase "type/x-second-non-int" #[.null, intV 1],
    mkCase "error-order/range-before-x-type-negative"
      #[.null] #[.pushInt (.num (-1)), qrshiftrInstr],
    mkCase "error-order/range-before-x-type-overmax"
      #[.cell Cell.empty] #[.pushInt (.num 257), qrshiftrInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 1]
      #[.pushInt (.num qrshiftrSetGasExact), .tonEnvOp .setGasLimit, qrshiftrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 1]
      #[.pushInt (.num qrshiftrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qrshiftrInstr]
  ]
  fuzz := #[
    { seed := 2026020817
      count := 700
      gen := genQrshiftrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFTR
