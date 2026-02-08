import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULRSHIFTR

/-
QMULRSHIFTR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 1 0 true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, quiet `pushIntQuiet` overflow funnel)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (24-bit decode family `0xb7a9a4..0xb7a9a6`, `QMULRSHIFTR` at `0xb7a9a5`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `register_div_ops`, quiet opcode `0xb7a9a`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/outcome mapping covered by this suite (`mul=true`, `add=false`, `d=1`, `round=0`, `quiet=true`):
- Lean: 9 branch sites / 12 terminal outcomes
  (dispatch/fallback; explicit arity gate; shift pop type path; bad-shift vs in-range path;
   `y` pop type path; `x` pop type path; `shift=0` round rewrite; numeric-vs-NaN operand split;
   quiet result push fit-vs-NaN funnel).
- C++: 8 aligned branch sites / 12 terminal outcomes
  (`check_underflow(3)`; runtime shift pop; type checks on `y` then `x`;
   global-v13 quiet bad-shift NaN path; multiply+round; quiet `push_int_quiet` overflow behavior).

Key risk areas covered:
- nearest rounding ties to `+∞` after multiply (`-1*1 >>R 1 = 0`);
- quiet runtime-shift handling (`shift<0`, `shift>256`, `shift=NaN`) pushes NaN, not `range_chk`;
- pop/error ordering with bad shift: type errors on `y`/`x` occur before quiet bad-shift NaN funnel;
- underflow precedence before any shift/type work;
- NaN/out-of-range integer inputs for oracle/fuzz are injected via `PUSHINT` prelude only;
- exact gas cliff with `PUSHINT n; SETGASLIMIT; QMULRSHIFTR` (exact vs exact-minus-one).
-/

private def qmulrshiftrId : InstrId := { name := "QMULRSHIFTR" }

private def qmulrshiftrInstr : Instr :=
  .arithExt (.shrMod true false 1 0 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulrshiftrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmulrshiftrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def shiftFitsQmulrshiftrRange (v : IntVal) : Bool :=
  match v with
  | .nan => false
  | .num n => decide (0 ≤ n ∧ n ≤ 256)

private def mkInputCase
    (name : String)
    (x y shift : IntVal)
    (below : Array Value := #[])
    (programSuffix : Array Instr := #[qmulrshiftrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let forceProgramInject : Bool :=
    !(intValOracleSerializable x) || !(intValOracleSerializable y) || !(shiftFitsQmulrshiftrRange shift)
  let (stack, progPrefix) :=
    if forceProgramInject then
      (#[], #[.pushInt x, .pushInt y, .pushInt shift])
    else
      oracleIntInputsToStackOrProgram #[x, y, shift]
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def runQmulrshiftrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulrshiftrInstr stack

private def runQmulrshiftrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 913)) stack

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

private def qmulrshiftrSetGasExact : Int :=
  computeExactGasBudget qmulrshiftrInstr

private def qmulrshiftrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulrshiftrInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOverflowPool : Array Int :=
  #[257, 258, 511, 1024]

private def tieFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftOverflow (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftOverflowPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (isNull, rng') := randBool rng
  ((if isNull then .null else .cell Cell.empty), rng')

private def genQmulrshiftrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkInputCase s!"fuzz/shape-{shape}/ok/boundary"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/ok/random"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 2 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/tie-shift1"
        (.num x) (.num y) (.num 1), r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/shift-zero-floor"
        (.num x) (.num y) (.num 0), r3)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      let (useNeg, r3) := randBool r2
      let y : Int := if useNeg then -1 else 1
      (mkInputCase s!"fuzz/shape-{shape}/ok/shift-256-boundary"
        (.num x) (.num y) (.num 256), r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (negMag, r4) := randNat r3 1 8
      let shift : Int := -Int.ofNat negMag
      (mkInputCase s!"fuzz/shape-{shape}/quiet/bad-shift-negative-via-program"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftOverflow r3
      (mkInputCase s!"fuzz/shape-{shape}/quiet/bad-shift-overmax-via-program"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/bad-shift-nan-via-program"
        (.num x) (.num y) .nan, r3)
    else if shape = 8 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        .nan (.num y) (.num shift), r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        (.num x) .nan (.num shift), r3)
    else if shape = 10 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-range-x-before-op"
        (.num xOut) (.num y) (.num shift), r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-range-y-before-op"
        (.num x) (.num yOut) (.num shift), r4)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-item" #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-items" #[intV x, intV y], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/y-second-non-int"
        #[intV x, yLike, intV shift], r4)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/x-third-non-int"
        #[xLike, intV y, intV shift], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/type-y-before-bad-shift-via-program"
        #[intV x, yLike] #[.pushInt (.num (-1)), qmulrshiftrInstr], r3)
    else if shape = 19 then
      let (y, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/type-x-before-bad-shift-via-program"
        #[xLike, intV y] #[.pushInt (.num 257), qmulrshiftrInstr], r3)
    else if shape = 20 then
      (mkInputCase s!"fuzz/shape-{shape}/quiet/overflow-max-times-two-shift0"
        (.num maxInt257) (.num 2) (.num 0), rng1)
    else
      (mkInputCase s!"fuzz/shape-{shape}/quiet/overflow-min-times-neg-one-shift0"
        (.num minInt257) (.num (-1)) (.num 0), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulrshiftrId
  unit := #[
    { name := "unit/round/sign-and-half-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 11),
            (-7, 3, 1, -10),
            (7, -3, 1, -10),
            (-7, -3, 1, 11),
            (5, 5, 1, 13),
            (-5, 5, 1, -12),
            (5, -5, 1, -12),
            (-5, -5, 1, 13),
            (1, 1, 1, 1),
            (-1, 1, 1, 0),
            (3, 3, 2, 2),
            (-3, 3, 2, -2),
            (9, 5, 3, 6),
            (-9, 5, 3, -6),
            (9, -5, 3, -6),
            (-9, -5, 3, 6)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})>>R{shift}"
            (runQmulrshiftrDirect #[intV x, intV y, intV shift])
            #[intV expected] }
    ,
    { name := "unit/round/shift-zero-and-high-shift-boundaries"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (123, 45, 0, 5535),
            (-123, 45, 0, -5535),
            (123, -45, 0, -5535),
            (-123, -45, 0, 5535),
            (maxInt257, 1, 0, maxInt257),
            (minInt257, 1, 0, minInt257),
            (maxInt257, 1, 256, 1),
            (maxInt257, -1, 256, -1),
            (minInt257, 1, 256, -1),
            (minInt257, -1, 256, 1),
            (pow2 255, 1, 256, 1),
            (-(pow2 255), 1, 256, 0),
            (maxInt257, 1, 255, 2),
            (minInt257, 1, 255, -2)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})>>R{shift}"
            (runQmulrshiftrDirect #[intV x, intV y, intV shift])
            #[intV expected] }
    ,
    { name := "unit/quiet/nan-range-and-overflow-funnels"
      run := do
        expectOkStack "quiet/bad-shift-negative"
          (runQmulrshiftrDirect #[intV 7, intV 5, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/bad-shift-overmax"
          (runQmulrshiftrDirect #[intV 7, intV 5, intV 257]) #[.int .nan]
        expectOkStack "quiet/bad-shift-nan"
          (runQmulrshiftrDirect #[intV 7, intV 5, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan-x"
          (runQmulrshiftrDirect #[.int .nan, intV 5, intV 1]) #[.int .nan]
        expectOkStack "quiet/nan-y"
          (runQmulrshiftrDirect #[intV 7, .int .nan, intV 1]) #[.int .nan]
        expectOkStack "quiet/overflow-max-times-two-shift0"
          (runQmulrshiftrDirect #[intV maxInt257, intV 2, intV 0]) #[.int .nan]
        expectOkStack "quiet/overflow-min-times-neg-one-shift0"
          (runQmulrshiftrDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-and-type-precedence"
      run := do
        expectErr "underflow/empty" (runQmulrshiftrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runQmulrshiftrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items-before-shift-parse" (runQmulrshiftrDirect #[intV 1, .null]) .stkUnd
        expectErr "type/shift-top-non-int"
          (runQmulrshiftrDirect #[intV 7, intV 5, .null]) .typeChk
        expectErr "type/y-second-non-int"
          (runQmulrshiftrDirect #[intV 7, .null, intV 1]) .typeChk
        expectErr "type/x-third-non-int"
          (runQmulrshiftrDirect #[.null, intV 5, intV 1]) .typeChk
        expectErr "error-order/type-y-before-bad-shift-negative"
          (runQmulrshiftrDirect #[intV 7, .null, intV (-1)]) .typeChk
        expectErr "error-order/type-x-before-bad-shift-overmax"
          (runQmulrshiftrDirect #[.null, intV 7, intV 257]) .typeChk }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[qmulrshiftrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qmulrshiftr" s0 qmulrshiftrInstr 24
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-qmulrshiftr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmulrshiftrDispatchFallback #[]) #[intV 913] }
  ]
  oracle := #[
    mkInputCase "ok/round/sign/pos-pos-shift1-half-up" (.num 7) (.num 3) (.num 1),
    mkInputCase "ok/round/sign/neg-pos-shift1-half-up-to-plus-inf" (.num (-7)) (.num 3) (.num 1),
    mkInputCase "ok/round/sign/pos-neg-shift1-half-up-to-plus-inf" (.num 7) (.num (-3)) (.num 1),
    mkInputCase "ok/round/sign/neg-neg-shift1-half-up" (.num (-7)) (.num (-3)) (.num 1),
    mkInputCase "ok/round/tie/plus-half" (.num 1) (.num 1) (.num 1),
    mkInputCase "ok/round/tie/minus-half-to-plus-inf" (.num (-1)) (.num 1) (.num 1),
    mkInputCase "ok/round/tie/plus-three-halves" (.num 3) (.num 1) (.num 1),
    mkInputCase "ok/round/tie/minus-three-halves" (.num (-3)) (.num 1) (.num 1),
    mkInputCase "ok/round/non-tie-shift2-pos" (.num 7) (.num 3) (.num 2),
    mkInputCase "ok/round/non-tie-shift2-neg" (.num (-7)) (.num 3) (.num 2),
    mkInputCase "ok/shift-zero/product-pos-neg" (.num 123) (.num (-45)) (.num 0),
    mkInputCase "ok/shift-zero/product-neg-neg" (.num (-123)) (.num (-45)) (.num 0),
    mkInputCase "ok/boundary/max-shift256" (.num maxInt257) (.num 1) (.num 256),
    mkInputCase "ok/boundary/min-shift256" (.num minInt257) (.num 1) (.num 256),
    mkInputCase "ok/boundary/max-neg-shift256" (.num maxInt257) (.num (-1)) (.num 256),
    mkInputCase "ok/boundary/min-neg-shift256" (.num minInt257) (.num (-1)) (.num 256),
    mkInputCase "ok/boundary/half-up-pos" (.num (pow2 255)) (.num 1) (.num 256),
    mkInputCase "ok/boundary/half-up-neg-to-zero" (.num (-(pow2 255))) (.num 1) (.num 256),
    mkInputCase "ok/boundary/max-shift255" (.num maxInt257) (.num 1) (.num 255),
    mkInputCase "ok/boundary/min-shift255" (.num minInt257) (.num 1) (.num 255),
    mkInputCase "quiet/bad-shift-negative-via-program" (.num 7) (.num 5) (.num (-1)),
    mkInputCase "quiet/bad-shift-overmax-via-program" (.num 7) (.num 5) (.num 257),
    mkInputCase "quiet/bad-shift-nan-via-program" (.num 7) (.num 5) .nan,
    mkInputCase "quiet/nan/x-via-program" .nan (.num 5) (.num 1),
    mkInputCase "quiet/nan/y-via-program" (.num 7) .nan (.num 1),
    mkInputCase "error-order/pushint-range-x-high-before-op" (.num (maxInt257 + 1)) (.num 5) (.num 1),
    mkInputCase "error-order/pushint-range-y-low-before-op" (.num 7) (.num (minInt257 - 1)) (.num 1),
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-shift-type-two-items"
      #[intV 1, .null],
    mkCase "type/shift-top-non-int" #[intV 7, intV 5, .null],
    mkCase "type/y-second-non-int" #[intV 7, .null, intV 1],
    mkCase "type/x-third-non-int" #[.null, intV 5, intV 1],
    mkCase "error-order/type-y-before-bad-shift-via-program" #[intV 7, .null]
      #[.pushInt (.num (-1)), qmulrshiftrInstr],
    mkCase "error-order/type-x-before-bad-shift-via-program" #[.null, intV 7]
      #[.pushInt (.num 257), qmulrshiftrInstr],
    mkInputCase "quiet/overflow/max-times-two-shift0" (.num maxInt257) (.num 2) (.num 0),
    mkInputCase "quiet/overflow/min-times-neg-one-shift0" (.num minInt257) (.num (-1)) (.num 0),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num qmulrshiftrSetGasExact), .tonEnvOp .setGasLimit, qmulrshiftrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num qmulrshiftrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulrshiftrInstr]
  ]
  fuzz := #[
    { seed := 2026020829
      count := 700
      gen := genQmulrshiftrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTR
