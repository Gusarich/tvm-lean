import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTDIVR

/-
LSHIFTDIVR branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shlDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest mode `roundMode = 0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (16-bit decode family `0xa9c4..0xa9c6`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite (`d=1`, `roundMode=0`, `add=false`,
`quiet=false`, `zOpt=none` specialization):
- Lean: 8 branch sites / 10 terminal outcomes
  (dispatch/fallback; pre-underflow gate; shift pop type/range; y/x pop type;
   divisor-zero split; result push fit check success vs `intOv`).
- C++: 8 branch sites / 10 aligned outcomes
  (`check_underflow(3)`; `pop_long` shift checks; `pop_int` for divisor/numerator;
   division path and `push_int_quiet` overflow/NaN behavior).

Key risk areas covered:
- nearest rounding for `(x << z) / y` across sign combinations and half ties;
- runtime shift bounds `[0, 256]`, including NaN shift behavior (`rangeChk`);
- strict pop/error ordering (`shift`, then `y`, then `x`);
- underflow must dominate malformed shift when stack depth < 3 (C++ parity);
- non-quiet NaN funnel (`intOv`) via program-injected `PUSHINT .nan`;
- exact gas boundary with `PUSHINT n; SETGASLIMIT; LSHIFTDIVR`.
-/

private def lshiftdivrId : InstrId := { name := "LSHIFTDIVR" }

private def lshiftdivrInstr : Instr :=
  .arithExt (.shlDivMod 1 0 false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftdivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftdivrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[lshiftdivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runLshiftdivrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftdivrInstr stack

private def runLshiftdivrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 1409)) stack

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

private def lshiftdivrSetGasExact : Int :=
  computeExactGasBudget lshiftdivrInstr

private def lshiftdivrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftdivrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOverflowPool : Array Int :=
  #[257, 258, 511, 1024]

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def outOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

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

private def genLshiftdivrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkInputCase s!"fuzz/shape-{shape}/ok-boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/ok-random"
        #[IntVal.num x, IntVal.num y, IntVal.num shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/divzero"
        #[IntVal.num x, IntVal.num 0, IntVal.num shift], r3)
    else if shape = 3 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      (mkInputCase s!"fuzz/shape-{shape}/tie-pos-den"
        #[IntVal.num x, IntVal.num 4, IntVal.num 1], r2)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      (mkInputCase s!"fuzz/shape-{shape}/tie-neg-den"
        #[IntVal.num x, IntVal.num (-4), IntVal.num 1], r2)
    else if shape = 5 then
      (mkInputCase s!"fuzz/shape-{shape}/overflow-max-shift1-div1"
        #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1], rng1)
    else if shape = 6 then
      (mkInputCase s!"fuzz/shape-{shape}/overflow-min-shift1-div1"
        #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1], rng1)
    else if shape = 7 then
      (mkInputCase s!"fuzz/shape-{shape}/overflow-min-shift0-div-neg1"
        #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (mag, r3) := randNat r2 1 4
      let shift : Int := -Int.ofNat mag
      (mkInputCase s!"fuzz/shape-{shape}/range-negative-shift"
        #[IntVal.num x, IntVal.num 3, IntVal.num shift], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftOverflow r2
      (mkInputCase s!"fuzz/shape-{shape}/range-overmax-shift"
        #[IntVal.num x, IntVal.num 3, IntVal.num shift], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/range-shift-nan-via-program"
        #[IntVal.num x, IntVal.num 3, IntVal.nan], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 12 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-item" #[intV x], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/regression-underflow-two-before-shift-type"
        #[intV x, .null], r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/type-shift-non-int"
        #[intV x, intV y, .null], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/type-y-non-int"
        #[intV x, .cell Cell.empty, intV shift], r3)
    else if shape = 18 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int"
        #[.null, intV y, intV shift], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-y-type"
        #[intV x, .null, intV (-1)], r2)
    else
      let (oor, r2) := pickFromPool outOfRangePool rng1
      (mkInputCase s!"fuzz/shape-{shape}/range-out-of-range-x-via-program"
        #[IntVal.num oor, IntVal.num 3, IntVal.num 1], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftdivrId
  unit := #[
    { name := "unit/round/sign-and-tie-invariants"
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
            (runLshiftdivrDirect #[intV x, intV y, intV shift]) #[intV q] }
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
            (runLshiftdivrDirect #[intV x, intV y, intV shift]) #[intV q] }
    ,
    { name := "unit/error/intov-divzero-and-overflow"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runLshiftdivrDirect #[intV 5, intV 0, intV 1]) .intOv
        expectErr "overflow/max-shift1-div1"
          (runLshiftdivrDirect #[intV maxInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-shift1-div1"
          (runLshiftdivrDirect #[intV minInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-shift0-div-neg1"
          (runLshiftdivrDirect #[intV minInt257, intV (-1), intV 0]) .intOv }
    ,
    { name := "unit/error/shift-range-pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runLshiftdivrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runLshiftdivrDirect #[intV 1]) .stkUnd
        expectErr "regression/underflow-before-shift-type-two-items"
          (runLshiftdivrDirect #[intV 1, .null]) .stkUnd
        expectErr "regression/underflow-before-shift-type-single-non-int"
          (runLshiftdivrDirect #[.null]) .stkUnd
        expectErr "range/shift-negative-before-y-type"
          (runLshiftdivrDirect #[.null, intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax-before-y-type"
          (runLshiftdivrDirect #[.cell Cell.empty, intV 7, intV 257]) .rangeChk
        expectErr "type/shift-top-non-int"
          (runLshiftdivrDirect #[intV 5, intV 6, .null]) .typeChk
        expectErr "type/y-second-non-int"
          (runLshiftdivrDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/x-third-non-int"
          (runLshiftdivrDirect #[.null, intV 6, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[lshiftdivrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/lshiftdivr" s0 lshiftdivrInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-lshiftdivr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runLshiftdivrDispatchFallback #[]) #[intV 1409] }
  ]
  oracle := #[
    mkInputCase "ok/round/pos-pos-inexact" #[IntVal.num 7, IntVal.num 3, IntVal.num 1],
    mkInputCase "ok/round/neg-pos-inexact" #[IntVal.num (-7), IntVal.num 3, IntVal.num 1],
    mkInputCase "ok/round/pos-neg-inexact" #[IntVal.num 7, IntVal.num (-3), IntVal.num 1],
    mkInputCase "ok/round/neg-neg-inexact" #[IntVal.num (-7), IntVal.num (-3), IntVal.num 1],
    mkInputCase "ok/tie/pos-pos-half" #[IntVal.num 5, IntVal.num 4, IntVal.num 1],
    mkInputCase "ok/tie/neg-pos-half" #[IntVal.num (-5), IntVal.num 4, IntVal.num 1],
    mkInputCase "ok/tie/pos-neg-half" #[IntVal.num 5, IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/tie/neg-neg-half" #[IntVal.num (-5), IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/tie/neg-pos-near-zero" #[IntVal.num (-1), IntVal.num 4, IntVal.num 1],
    mkInputCase "ok/tie/pos-neg-near-zero" #[IntVal.num 1, IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/tie/neg-neg-near-zero" #[IntVal.num (-1), IntVal.num (-4), IntVal.num 1],
    mkInputCase "ok/exact/shift0-pos-pos" #[IntVal.num 42, IntVal.num 7, IntVal.num 0],
    mkInputCase "ok/exact/shift0-neg-pos" #[IntVal.num (-42), IntVal.num 7, IntVal.num 0],
    mkInputCase "ok/exact/shift0-pos-neg" #[IntVal.num 42, IntVal.num (-7), IntVal.num 0],
    mkInputCase "ok/exact/shift0-neg-neg" #[IntVal.num (-42), IntVal.num (-7), IntVal.num 0],
    mkInputCase "ok/exact/zero-numerator" #[IntVal.num 0, IntVal.num 5, IntVal.num 1],
    mkInputCase "ok/boundary/max-shift0-div-one" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 0],
    mkInputCase "ok/boundary/max-shift0-div-neg-one" #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 0],
    mkInputCase "ok/boundary/min-shift0-div-one" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 0],
    mkInputCase "ok/boundary/min-plus-one-shift0-div-neg-one"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num 0],
    mkInputCase "ok/boundary/max-shift0-div-two-round-up"
      #[IntVal.num maxInt257, IntVal.num 2, IntVal.num 0],
    mkInputCase "ok/boundary/min-shift0-div-two"
      #[IntVal.num minInt257, IntVal.num 2, IntVal.num 0],
    mkInputCase "ok/boundary/min-shift0-div-neg-two"
      #[IntVal.num minInt257, IntVal.num (-2), IntVal.num 0],
    mkInputCase "ok/boundary/one-shift256-div-two"
      #[IntVal.num 1, IntVal.num 2, IntVal.num 256],
    mkInputCase "ok/boundary/neg-one-shift256-div-two"
      #[IntVal.num (-1), IntVal.num 2, IntVal.num 256],
    mkInputCase "divzero/nonzero-over-zero" #[IntVal.num 5, IntVal.num 0, IntVal.num 1],
    mkInputCase "overflow/max-shift1-div1" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1],
    mkInputCase "overflow/min-shift1-div1" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1],
    mkInputCase "overflow/min-shift0-div-neg1" #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0],
    mkInputCase "range/shift-negative" #[IntVal.num 7, IntVal.num 5, IntVal.num (-1)],
    mkInputCase "range/shift-overmax" #[IntVal.num 7, IntVal.num 5, IntVal.num 257],
    mkInputCase "range/shift-nan-via-program" #[IntVal.num 7, IntVal.num 5, IntVal.nan],
    mkInputCase "nan/y-via-program" #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkInputCase "nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkInputCase "range/x-out-of-range-via-program"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "regression/error-order/underflow-before-shift-type-single-non-int" #[.null],
    mkCase "regression/error-order/underflow-before-shift-type-two-items" #[intV 9, .null],
    mkCase "type/shift-top-non-int" #[intV 5, intV 6, .null],
    mkCase "type/y-second-non-int" #[intV 5, .null, intV 1],
    mkCase "type/x-third-non-int" #[.null, intV 6, intV 1],
    mkCase "error-order/range-before-y-type-negative"
      #[.null, .cell Cell.empty, intV (-1)],
    mkCase "error-order/range-before-y-type-overmax"
      #[.cell Cell.empty, .null, intV 257],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftdivrSetGasExact), .tonEnvOp .setGasLimit, lshiftdivrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftdivrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftdivrInstr]
  ]
  fuzz := #[
    { seed := 2026020821
      count := 700
      gen := genLshiftdivrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTDIVR
