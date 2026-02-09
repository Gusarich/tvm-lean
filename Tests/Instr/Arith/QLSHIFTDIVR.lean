import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTDIVR

/-
QLSHIFTDIVR branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 1 0 false true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, nearest mode `roundMode = 0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode family `0xb7a9c4..0xb7a9c6`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest rounding behavior)

Branch counts used for this suite (`d=1`, `roundMode=0`, `add=false`,
`quiet=true`, `zOpt=none` specialization):
- Lean: 9 branch sites / 12 terminal outcomes
  (dispatch/fallback; arity precheck; shift pop type/range split; `y`/`x` pop
   type checks; quiet invalid-input funnel; divisor-zero split; quotient push
   fit-vs-overflow to quiet NaN).
- C++: 8 branch sites / 12 aligned outcomes
  (`check_underflow(3)`; `pop_long`; `pop_int` for divisor/numerator;
   v13 quiet invalid-input funnel; `mod_div_any`; `push_int_quiet` fit-vs-NaN).

Key risk areas covered:
- nearest rounding ties toward `+∞` for `(x << z) / y` across sign combinations;
- quiet range handling for runtime shift (`z < 0`, `z > 256`, `z = NaN`);
- error ordering in quiet mode: bad shift must not mask later `y/x` type errors;
- underflow must dominate malformed top values when depth < 3;
- quiet NaN funnels for divzero, overflow, and NaN operands;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QLSHIFTDIVR`.
-/

private def qlshiftdivrId : InstrId := { name := "QLSHIFTDIVR" }

private def qlshiftdivrInstr : Instr :=
  .arithExt (.shlDivMod 1 0 false true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftdivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftdivrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qlshiftdivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQlshiftdivrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftdivrInstr stack

private def runQlshiftdivrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 2419)) stack

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

private def qlshiftdivrSetGasExact : Int :=
  computeExactGasBudget qlshiftdivrInstr

private def qlshiftdivrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftdivrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOverflowPool : Array Int :=
  #[257, 258, 511, 1024]

private def tieNumeratorPool : Array Int :=
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
  let (useNull, rng') := randBool rng
  ((if useNull then .null else .cell Cell.empty), rng')

private def genQlshiftdivrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkInputCase s!"fuzz/shape-{shape}/ok/boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/ok/random"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/divzero"
        #[IntVal.num x, IntVal.num 0, IntVal.num shift], r3)
    else if shape = 3 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/tie-pos-den"
        #[IntVal.num x, IntVal.num 4, IntVal.num 1], r2)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/tie-neg-den"
        #[IntVal.num x, IntVal.num (-4), IntVal.num 1], r2)
    else if shape = 5 then
      (mkInputCase s!"fuzz/shape-{shape}/quiet/overflow-max-shift1-div1"
        #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1], rng1)
    else if shape = 6 then
      (mkInputCase s!"fuzz/shape-{shape}/quiet/overflow-min-shift0-div-neg1"
        #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (mag, r3) := randNat r2 1 8
      let shift : Int := -Int.ofNat mag
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-negative-shift"
        #[IntVal.num x, IntVal.num 3, IntVal.num shift], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftOverflow r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-overmax-shift"
        #[IntVal.num x, IntVal.num 3, IntVal.num shift], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-shift-nan-via-program"
        #[IntVal.num x, IntVal.num 3, IntVal.nan], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 11 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 12 then
      let (shift, r2) := pickShiftInRange rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-both-via-program"
        #[IntVal.nan, IntVal.nan, IntVal.num shift], r2)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-item" #[intV x], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/two-items-top-non-int" #[intV x, .null], r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/y-second-non-int"
        #[intV x, yLike, intV shift], r4)
    else if shape = 18 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/x-third-non-int"
        #[xLike, intV y, intV shift], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/quiet-range-does-not-mask-y-type-negative"
        #[intV x, .null, intV (-1)], r2)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/quiet-range-does-not-mask-y-type-overmax"
        #[intV x, .null, intV 257], r2)
    else if shape = 21 then
      let (y, r2) := pickNonZeroInt rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/quiet-range-does-not-mask-x-type-overmax"
        #[.null, intV y, intV 257], r2)
    else if shape = 22 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else
      let (y, r2) := pickInt257OutOfRange rng1
      let (x, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftdivrId
  unit := #[
    { name := "unit/round/nearest-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 5),
            (-7, 3, 1, -5),
            (7, -3, 1, -5),
            (-7, -3, 1, 5),
            (5, 4, 1, 3),
            (-5, 4, 1, -2),
            (5, -4, 1, -2),
            (-5, -4, 1, 3),
            (1, 4, 1, 1),
            (-1, 4, 1, 0),
            (1, -4, 1, 0),
            (-1, -4, 1, 1),
            (7, 2, 0, 4),
            (-7, 2, 0, -3)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}"
            (runQlshiftdivrDirect #[intV x, intV y, intV shift]) #[intV q] }
    ,
    { name := "unit/round/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257),
            (maxInt257, -1, 0, -maxInt257),
            (minInt257, 1, 0, minInt257),
            (minInt257 + 1, -1, 0, maxInt257),
            (maxInt257, 2, 0, pow2 255),
            (minInt257, 2, 0, -(pow2 255)),
            (minInt257, -2, 0, pow2 255),
            (1, 2, 256, pow2 255),
            (-1, 2, 256, -(pow2 255)),
            (0, 5, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}"
            (runQlshiftdivrDirect #[intV x, intV y, intV shift]) #[intV q] }
    ,
    { name := "unit/quiet/nan-divzero-overflow-and-shift-range-funnel"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQlshiftdivrDirect #[intV 5, intV 0, intV 1]) #[.int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQlshiftdivrDirect #[intV 0, intV 0, intV 200]) #[.int .nan]
        expectOkStack "quiet/overflow/max-shift1-div1"
          (runQlshiftdivrDirect #[intV maxInt257, intV 1, intV 1]) #[.int .nan]
        expectOkStack "quiet/overflow/min-shift1-div1"
          (runQlshiftdivrDirect #[intV minInt257, intV 1, intV 1]) #[.int .nan]
        expectOkStack "quiet/overflow/min-shift0-div-neg1"
          (runQlshiftdivrDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan]
        expectOkStack "quiet/range/shift-negative"
          (runQlshiftdivrDirect #[intV 5, intV 7, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/range/shift-overmax"
          (runQlshiftdivrDirect #[intV 5, intV 7, intV 257]) #[.int .nan]
        expectOkStack "quiet/range/shift-nan"
          (runQlshiftdivrDirect #[intV 5, intV 7, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan/y"
          (runQlshiftdivrDirect #[intV 5, .int .nan, intV 3]) #[.int .nan]
        expectOkStack "quiet/nan/x"
          (runQlshiftdivrDirect #[.int .nan, intV 5, intV 3]) #[.int .nan]
        expectOkStack "quiet/nan/both"
          (runQlshiftdivrDirect #[.int .nan, .int .nan, intV 3]) #[.int .nan]
        expectOkStack "quiet/pop-order/lower-preserved"
          (runQlshiftdivrDirect #[.cell Cell.empty, intV 7, intV 3, intV 1])
          #[.cell Cell.empty, intV 5]
        expectOkStack "quiet/pop-order/lower-preserved-range-shift"
          (runQlshiftdivrDirect #[.cell Cell.empty, intV 7, intV 3, intV 257])
          #[.cell Cell.empty, .int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-quiet-range-precedence"
      run := do
        expectErr "underflow/empty" (runQlshiftdivrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runQlshiftdivrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items-top-non-int" (runQlshiftdivrDirect #[intV 1, .null]) .stkUnd
        expectErr "type/shift-top-non-int" (runQlshiftdivrDirect #[intV 5, intV 6, .null]) .typeChk
        expectErr "type/y-second-non-int" (runQlshiftdivrDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/x-third-non-int" (runQlshiftdivrDirect #[.null, intV 6, intV 1]) .typeChk
        expectErr "error-order/quiet-range-does-not-mask-y-type-negative-shift"
          (runQlshiftdivrDirect #[intV 7, .null, intV (-1)]) .typeChk
        expectErr "error-order/quiet-range-does-not-mask-y-type-overmax-shift"
          (runQlshiftdivrDirect #[intV 7, .null, intV 257]) .typeChk
        expectErr "error-order/quiet-range-does-not-mask-x-type-overmax-shift"
          (runQlshiftdivrDirect #[.null, intV 7, intV 257]) .typeChk
        expectErr "error-order/quiet-range-does-not-mask-y-type-nan-shift"
          (runQlshiftdivrDirect #[intV 7, .null, .int .nan]) .typeChk }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[qlshiftdivrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qlshiftdivr" s0 qlshiftdivrInstr 24
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-qlshiftdivr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQlshiftdivrDispatchFallback #[]) #[intV 2419] }
  ]
  oracle := #[
    mkInputCase "ok/round/sign/pos-pos-inexact" #[IntVal.num 7, IntVal.num 3, IntVal.num 1],
    mkInputCase "ok/round/sign/neg-pos-inexact" #[IntVal.num (-7), IntVal.num 3, IntVal.num 1],
    mkInputCase "ok/round/sign/pos-neg-inexact" #[IntVal.num 7, IntVal.num (-3), IntVal.num 1],
    mkInputCase "ok/round/sign/neg-neg-inexact" #[IntVal.num (-7), IntVal.num (-3), IntVal.num 1],
    mkInputCase "ok/round/tie/pos-pos-half" #[IntVal.num 5, IntVal.num 4, IntVal.num 1],
    mkInputCase "ok/round/tie/neg-pos-half" #[IntVal.num (-5), IntVal.num 4, IntVal.num 1],
    mkInputCase "ok/round/tie/pos-neg-half" #[IntVal.num 5, IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/round/tie/neg-neg-half" #[IntVal.num (-5), IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/round/tie/neg-pos-near-zero" #[IntVal.num (-1), IntVal.num 4, IntVal.num 1],
    mkInputCase "ok/round/tie/pos-neg-near-zero" #[IntVal.num 1, IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/round/tie/neg-neg-near-zero" #[IntVal.num (-1), IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/exact/shift0-pos-pos" #[IntVal.num 42, IntVal.num 7, IntVal.num 0],
    mkInputCase "ok/exact/shift0-neg-pos" #[IntVal.num (-42), IntVal.num 7, IntVal.num 0],
    mkInputCase "ok/exact/shift0-pos-neg" #[IntVal.num 42, IntVal.num (-7), IntVal.num 0],
    mkInputCase "ok/exact/shift0-neg-neg" #[IntVal.num (-42), IntVal.num (-7), IntVal.num 0],
    mkInputCase "ok/exact/zero-numerator" #[IntVal.num 0, IntVal.num 5, IntVal.num 1],
    mkInputCase "ok/boundary/max-shift0-div1" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 0],
    mkInputCase "ok/boundary/max-shift0-div-neg1" #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 0],
    mkInputCase "ok/boundary/min-shift0-div1" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 0],
    mkInputCase "ok/boundary/min-plus-one-shift0-div-neg1"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num 0],
    mkInputCase "ok/boundary/max-shift0-div2-half-up"
      #[IntVal.num maxInt257, IntVal.num 2, IntVal.num 0],
    mkInputCase "ok/boundary/min-shift0-div2"
      #[IntVal.num minInt257, IntVal.num 2, IntVal.num 0],
    mkInputCase "ok/boundary/min-shift0-div-neg2"
      #[IntVal.num minInt257, IntVal.num (-2), IntVal.num 0],
    mkInputCase "ok/boundary/one-shift256-div2"
      #[IntVal.num 1, IntVal.num 2, IntVal.num 256],
    mkInputCase "ok/boundary/neg-one-shift256-div2"
      #[IntVal.num (-1), IntVal.num 2, IntVal.num 256],
    mkInputCase "quiet/divzero/nonzero-over-zero" #[IntVal.num 5, IntVal.num 0, IntVal.num 1],
    mkInputCase "quiet/divzero/zero-over-zero" #[IntVal.num 0, IntVal.num 0, IntVal.num 200],
    mkInputCase "quiet/overflow/max-shift1-div1" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1],
    mkInputCase "quiet/overflow/min-shift1-div1" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1],
    mkInputCase "quiet/overflow/min-shift0-div-neg1" #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0],
    mkInputCase "quiet/range/shift-negative" #[IntVal.num 7, IntVal.num 5, IntVal.num (-1)],
    mkInputCase "quiet/range/shift-overmax" #[IntVal.num 7, IntVal.num 5, IntVal.num 257],
    mkInputCase "quiet/range/shift-nan-via-program" #[IntVal.num 7, IntVal.num 5, IntVal.nan],
    mkInputCase "quiet/nan/y-via-program" #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkInputCase "quiet/nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkInputCase "quiet/nan/both-via-program" #[IntVal.nan, IntVal.nan, IntVal.num 1],
    mkInputCase "error-order/pushint-overflow-x-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 1],
    mkInputCase "error-order/pushint-overflow-y-before-op"
      #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkInputCase "error-order/pushint-overflow-shift-before-op"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items-top-non-int" #[intV 9, .null],
    mkCase "type/shift-top-non-int" #[intV 5, intV 6, .null],
    mkCase "type/y-second-non-int" #[intV 5, .null, intV 1],
    mkCase "type/x-third-non-int" #[.null, intV 6, intV 1],
    mkCase "error-order/quiet-range-does-not-mask-y-type-negative"
      #[intV 7, .null, intV (-1)],
    mkCase "error-order/quiet-range-does-not-mask-y-type-overmax"
      #[intV 7, .null, intV 257],
    mkCase "error-order/quiet-range-does-not-mask-x-type-overmax"
      #[.null, intV 7, intV 257],
    mkCase "error-order/quiet-shift-nan-does-not-mask-y-type"
      #[intV 7, .null] #[.pushInt .nan, qlshiftdivrInstr],
    mkCase "ok/pop-order/lower-preserved"
      #[.cell Cell.empty, intV 7, intV 3, intV 1],
    mkCase "quiet/range/lower-preserved"
      #[.cell Cell.empty, intV 7, intV 3, intV 257],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftdivrSetGasExact), .tonEnvOp .setGasLimit, qlshiftdivrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftdivrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftdivrInstr]
  ]
  fuzz := #[
    { seed := 2026020853
      count := 700
      gen := genQlshiftdivrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTDIVR
