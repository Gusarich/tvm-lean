import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULRSHIFT

/-
QMULRSHIFT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 1 (-1) true none)` path).
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet SHR/MOD family encoding via 24-bit `0xb7 || p16` opcodes).
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode family `0xb7a9a4..0xb7a9a6` -> `QMULRSHIFT{,R,C}`).
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet` type/quiet-result behavior).
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, `register_div_ops` quiet opcode wiring).
  - `/Users/daniil/Coding/ton/crypto/vm/stack.hpp`
    (`check_underflow`).
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_int`, `pop_long`, `push_int_quiet`).

Branch counts used for this suite (QMULRSHIFT specialization):
- Lean: 10 branch points / 14 terminal outcomes
  (dispatch/fallback; pre-pop depth gate; runtime shift pop type/range-class;
   `y` then `x` pop type checks; bad-shift quiet funnel;
   finite-vs-NaN operand split; `shift=0` round-mode override;
   `d` arm; quiet push finite-vs-NaN result split).
- C++: 9 branch points / 14 aligned outcomes
  (`check_underflow`; `pop_long` shift parse; quiet range suppression for `z`;
   `pop_int` for `y`/`x`; invalid bigint-or-z quiet NaN funnel;
   `z==0` round remap; `d` switch; `push_int_quiet` fit-vs-NaN).

Key risk areas covered:
- quiet invalid-shift behavior for runtime `z` (`<0`, `>256`, `NaN`) => NaN, not `rangeChk`;
- error ordering with invalid shift: shift parse precedes `y/x` pops, but quiet mode still surfaces `typeChk` on bad `y/x`;
- floor right-shift semantics across sign combinations and edges (`0`, `255`, `256`);
- quiet overflow funnel at result push (`shift=0` large products -> NaN, never `intOv`);
- opcode-family boundary (`QMULRSHIFT` 24-bit quiet form vs `MULRSHIFT` 16-bit non-quiet);
- pre-pop underflow gating and exact gas cliff (`PUSHINT n; SETGASLIMIT; QMULRSHIFT`).
-/

private def qmulrshiftId : InstrId := { name := "QMULRSHIFT" }

private def qmulrshiftInstr : Instr :=
  .arithExt (.shrMod true false 1 (-1) true none)

private def mulrshiftInstr : Instr :=
  .arithExt (.shrMod true false 1 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulrshiftInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmulrshiftId
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
  mkCase name stack (progPrefix.push qmulrshiftInstr) gasLimits fuel

private def mkShiftInjectedCase (name : String) (x y : Value) (shift : IntVal) : OracleCase :=
  mkCase name #[x, y] #[.pushInt shift, qmulrshiftInstr]

private def mkXNanInjectedCase (name : String) (y shift : Int) : OracleCase :=
  mkCase name #[intV y, intV shift] #[.pushInt .nan, .xchg0 2, .xchg0 1, qmulrshiftInstr]

private def mkYNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift] #[.pushInt .nan, .xchg0 1, qmulrshiftInstr]

private def runQmulrshiftDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulrshiftInstr stack

private def runQmulrshiftDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6419)) stack

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

private def qmulrshiftSetGasExact : Int :=
  computeExactGasBudget qmulrshiftInstr

private def qmulrshiftSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulrshiftInstr

private def validShiftPool : Array Int :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300, 511]

private def pickValidShift (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (validShiftPool.size - 1)
  (validShiftPool[idx]!, rng')

private def pickInvalidShift (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (invalidShiftPool.size - 1)
  (invalidShiftPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def genQmulrshiftFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/ok/boundary-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"/fuzz/shape-{shape}/ok/random-inrange" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/ok/x-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/ok/y-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"/fuzz/shape-{shape}/ok/x-zero" #[intV 0, intV y, intV shift], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"/fuzz/shape-{shape}/ok/y-zero" #[intV x, intV 0, intV shift], r3)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let (ySel, r3) := randNat r2 0 2
      let y :=
        if ySel = 0 then
          (1 : Int)
        else if ySel = 1 then
          (-1 : Int)
        else
          (2 : Int)
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/ok/extreme-times-unit" #[intV x, intV y, intV shift], r4)
    else if shape = 7 then
      let (variant, r2) := randNat rng1 0 3
      let (x, y) :=
        if variant = 0 then
          (maxInt257, (2 : Int))
        else if variant = 1 then
          (minInt257, (2 : Int))
        else if variant = 2 then
          (minInt257, (-1 : Int))
        else
          (maxInt257, maxInt257)
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-shift-zero" #[intV x, intV y, intV 0], r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInvalidShift r3
      (mkShiftInjectedCase
        s!"/fuzz/shape-{shape}/quiet/invalid-shift-via-program"
        (intV x) (intV y) (.num shift), r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonIntLike r3
      (mkCase s!"/fuzz/shape-{shape}/type/shift-pop-first" #[intV x, intV y, shiftLike], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"/fuzz/shape-{shape}/type/y-pop-second" #[intV x, yLike, intV shift], r4)
    else if shape = 11 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase s!"/fuzz/shape-{shape}/type/x-pop-third" #[xLike, intV y, intV shift], r4)
    else if shape = 12 then
      let (variant, r2) := randNat rng1 0 4
      if variant = 0 then
        (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], r2)
      else if variant = 1 then
        let (x, r3) := pickSigned257ish r2
        (mkCase s!"/fuzz/shape-{shape}/underflow/single-int" #[intV x], r3)
      else if variant = 2 then
        let (x, r3) := pickSigned257ish r2
        let (shift, r4) := pickShiftInRange r3
        (mkCase s!"/fuzz/shape-{shape}/underflow/two-items" #[intV x, intV shift], r4)
      else if variant = 3 then
        let (x, r3) := pickSigned257ish r2
        let (shift, r4) := pickInvalidShift r3
        (mkCase
          s!"/fuzz/shape-{shape}/underflow/invalid-shift-injected-before-pop-order"
          #[intV x] #[.pushInt (.num shift), qmulrshiftInstr], r4)
      else
        let (v, r3) := pickNonIntLike r2
        (mkCase s!"/fuzz/shape-{shape}/underflow/single-non-int" #[v], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/shift-nan-via-program" #[.num x, .num y, .nan], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkYNanInjectedCase s!"/fuzz/shape-{shape}/quiet/y-nan-via-program" x shift, r3)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkXNanInjectedCase s!"/fuzz/shape-{shape}/quiet/x-nan-via-program" y shift, r3)
    else if shape = 16 then
      let (variant, r2) := randNat rng1 0 2
      let big : Int := pow2 256
      if variant = 0 then
        (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x"
          #[.num big, .num 7, .num 5], r2)
      else if variant = 1 then
        (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y"
          #[.num 7, .num big, .num 5], r2)
      else
        (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift"
          #[.num 7, .num 5, .num big], r2)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickInvalidShift r3
      (mkShiftInjectedCase
        s!"/fuzz/shape-{shape}/error-order/invalid-shift-before-y-type-via-program"
        (intV x) yLike (.num shift), r4)
    else if shape = 18 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInvalidShift r3
      (mkShiftInjectedCase
        s!"/fuzz/shape-{shape}/error-order/invalid-shift-before-x-type-via-program"
        xLike (intV y) (.num shift), r4)
    else
      let (xLike, r2) := pickNonIntLike rng1
      let (yLike, r3) := pickNonIntLike r2
      let (shift, r4) := pickShiftInRange r3
      (mkCase
        s!"/fuzz/shape-{shape}/error-order/y-before-x-both-non-int"
        #[xLike, yLike, intV shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulrshiftId
  unit := #[
    { name := "/unit/direct/floor-rshift-sign-zero-and-shift-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 5, 0, 35),
            (7, 5, 1, 17),
            (-7, 5, 1, -18),
            (7, -5, 1, -18),
            (-7, -5, 1, 17),
            (13, 11, 3, 17),
            (-13, 11, 3, -18),
            (13, -11, 3, -18),
            (-13, -11, 3, 17),
            (maxInt257, 2, 1, maxInt257),
            (maxInt257, 1, 255, 1),
            (maxInt257, 1, 256, 0),
            (minInt257, 1, 255, -2),
            (minInt257, 1, 256, -1),
            (minInt257, -1, 256, 1),
            (maxInt257, -1, 256, -1),
            (minInt257 + 1, -1, 256, 0),
            (-1, 1, 256, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})>>{shift}"
            (runQmulrshiftDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "/unit/direct/quiet-invalid-shift-nan-and-overflow-funnel"
      run := do
        expectOkStack "quiet/shift-negative-to-nan"
          (runQmulrshiftDirect #[intV 7, intV 5, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/shift-overmax-to-nan"
          (runQmulrshiftDirect #[intV 7, intV 5, intV 257]) #[.int .nan]
        expectOkStack "quiet/shift-nan-to-nan"
          (runQmulrshiftDirect #[intV 7, intV 5, .int .nan]) #[.int .nan]
        expectOkStack "quiet/y-nan-to-nan"
          (runQmulrshiftDirect #[intV 7, .int .nan, intV 1]) #[.int .nan]
        expectOkStack "quiet/x-nan-to-nan"
          (runQmulrshiftDirect #[.int .nan, intV 7, intV 1]) #[.int .nan]
        expectOkStack "quiet/overflow/max-times-two-shift-zero"
          (runQmulrshiftDirect #[intV maxInt257, intV 2, intV 0]) #[.int .nan]
        expectOkStack "quiet/overflow/min-times-neg-one-shift-zero"
          (runQmulrshiftDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan]
        expectOkStack "quiet/overflow/max-times-max-shift-zero"
          (runQmulrshiftDirect #[intV maxInt257, intV maxInt257, intV 0]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-type-and-invalid-shift-ordering"
      run := do
        expectErr "underflow/empty" (runQmulrshiftDirect #[]) .stkUnd
        expectErr "underflow/single-int" (runQmulrshiftDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runQmulrshiftDirect #[.null]) .stkUnd
        expectErr "underflow/two-items-before-shift-pop" (runQmulrshiftDirect #[intV 7, intV 1]) .stkUnd
        expectErr "underflow/before-invalid-shift-interpretation"
          (runQmulrshiftDirect #[intV 7, intV (-1)]) .stkUnd
        expectErr "type/shift-pop-first-null"
          (runQmulrshiftDirect #[intV 7, intV 5, .null]) .typeChk
        expectErr "type/shift-pop-first-cell"
          (runQmulrshiftDirect #[intV 7, intV 5, .cell Cell.empty]) .typeChk
        expectErr "type/y-pop-second-after-invalid-shift"
          (runQmulrshiftDirect #[intV 7, .null, intV (-1)]) .typeChk
        expectErr "type/x-pop-third-after-invalid-shift"
          (runQmulrshiftDirect #[.null, intV 7, intV 257]) .typeChk
        expectErr "type/y-before-x-both-non-int"
          (runQmulrshiftDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectOkStack "quiet/invalid-shift-with-valid-operands-still-nan"
          (runQmulrshiftDirect #[intV 9, intV (-4), intV 258]) #[.int .nan] }
    ,
    { name := "/unit/opcode/quiet-vs-nonquiet-mulrshift-decode-boundary"
      run := do
        let program : Array Instr := #[qmulrshiftInstr, mulrshiftInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qmulrshift" s0 qmulrshiftInstr 24
        let s2 ← expectDecodeStep "decode/mulrshift" s1 mulrshiftInstr 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQmulrshiftDispatchFallback #[]) #[intV 6419] }
  ]
  oracle := #[
    mkCase "/ok/shift-zero/zero-product" #[intV 0, intV 7, intV 0],
    mkCase "/ok/shift-zero/pos-pos" #[intV 7, intV 5, intV 0],
    mkCase "/ok/shift-zero/neg-pos" #[intV (-7), intV 5, intV 0],
    mkCase "/ok/shift-zero/pos-neg" #[intV 7, intV (-5), intV 0],
    mkCase "/ok/shift-zero/neg-neg" #[intV (-7), intV (-5), intV 0],
    mkCase "/ok/floor/pos-pos-inexact" #[intV 7, intV 5, intV 1],
    mkCase "/ok/floor/neg-pos-inexact" #[intV (-7), intV 5, intV 1],
    mkCase "/ok/floor/pos-neg-inexact" #[intV 7, intV (-5), intV 1],
    mkCase "/ok/floor/neg-neg-inexact" #[intV (-7), intV (-5), intV 1],
    mkCase "/ok/exact/divisible-pos" #[intV 24, intV 7, intV 3],
    mkCase "/ok/exact/divisible-neg" #[intV (-24), intV 7, intV 3],
    mkCase "/ok/boundary/max-times-two-shift-one" #[intV maxInt257, intV 2, intV 1],
    mkCase "/ok/boundary/max-times-one-shift255" #[intV maxInt257, intV 1, intV 255],
    mkCase "/ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "/ok/boundary/min-times-one-shift255" #[intV minInt257, intV 1, intV 255],
    mkCase "/ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "/ok/boundary/min-times-negone-shift256" #[intV minInt257, intV (-1), intV 256],
    mkCase "/ok/boundary/max-times-negone-shift256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "/ok/boundary/min-plus-one-times-negone-shift256" #[intV (minInt257 + 1), intV (-1), intV 256],
    mkCase "/ok/boundary/negone-times-one-shift256" #[intV (-1), intV 1, intV 256],
    mkCase "/quiet/overflow/max-times-two-shift-zero" #[intV maxInt257, intV 2, intV 0],
    mkCase "/quiet/overflow/min-times-negone-shift-zero" #[intV minInt257, intV (-1), intV 0],
    mkCase "/quiet/overflow/min-times-two-shift-zero" #[intV minInt257, intV 2, intV 0],
    mkCase "/quiet/overflow/max-times-max-shift-zero" #[intV maxInt257, intV maxInt257, intV 0],
    mkShiftInjectedCase "/quiet/invalid-shift-negative-via-program" (intV 7) (intV 5) (.num (-1)),
    mkShiftInjectedCase "/quiet/invalid-shift-overmax-via-program" (intV 7) (intV 5) (.num 257),
    mkCaseFromIntVals "/quiet/shift-nan-via-program" #[.num 7, .num 5, .nan],
    mkYNanInjectedCase "/quiet/y-nan-via-program" 7 1,
    mkXNanInjectedCase "/quiet/x-nan-via-program" 5 1,
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/single-int" #[intV 1],
    mkCase "/underflow/single-non-int" #[.null],
    mkCase "/underflow/two-items-before-shift-pop" #[intV 7, intV 1],
    mkCase "/underflow/invalid-shift-injected-before-pop-order" #[intV 7]
      #[.pushInt (.num (-1)), qmulrshiftInstr],
    mkCase "/type/pop-shift-first-null" #[intV 7, intV 5, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 7, intV 5, .cell Cell.empty],
    mkCase "/type/pop-y-second-after-invalid-shift" #[intV 7, .null]
      #[.pushInt (.num (-1)), qmulrshiftInstr],
    mkCase "/type/pop-x-third-after-invalid-shift" #[.null, intV 7]
      #[.pushInt (.num 257), qmulrshiftInstr],
    mkCase "/error-order/y-pop-before-x-after-valid-shift" #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/x"
      #[.num (pow2 256), .num 7, .num 5],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/y"
      #[.num 7, .num (pow2 256), .num 5],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/shift"
      #[.num 7, .num 5, .num (pow2 256)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulrshiftSetGasExact), .tonEnvOp .setGasLimit, qmulrshiftInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulrshiftSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulrshiftInstr]
  ]
  fuzz := #[
    { seed := 2026020834
      count := 700
      gen := genQmulrshiftFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFT
