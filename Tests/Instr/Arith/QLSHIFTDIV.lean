import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTDIV

/-
QLSHIFTDIV branch-mapping notes (Lean + C++ analyzed sources):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 1 (-1) false true none`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet `.shlDivMod` encoding via `0xb7 ++ 0xa9c4..0xa9c6`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-shldiv decode for `0xb7a9c4..0xb7a9c6`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, quiet `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops` Q wiring)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (`execInstrArithExt` `.shlDivMod` generic helper): 8 branch sites / 16 terminal outcomes.
- Lean (QLSHIFTDIV specialization): 7 branch sites / 6 reachable terminal outcomes
  (`ok` finite quotient, `ok` quiet-NaN quotient, `stkUnd`,
   shift `typeChk`, y `typeChk`, x `typeChk`).
- C++ (`exec_shldivmod` runtime-shift + Q registration): 7 branch sites / 14 terminal outcomes.

Key risk areas covered:
- floor quotient semantics for sign-mixed operands and shift boundaries (`0..256`);
- strict pop/error order (`shift`, then `y`, then `x`) including quiet bad-shift precedence;
- quiet NaN funnels for divisor-zero, NaN operands, and signed-257 overflow on quotient push;
- oracle serialization constraints (NaN / out-of-range ints only via `PUSHINT` prelude);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QLSHIFTDIV`.
-/

private def qlshiftdivId : InstrId := { name := "QLSHIFTDIV" }

private def qlshiftdivInstr : Instr :=
  .arithExt (.shlDivMod 1 (-1) false true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftdivInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftdivId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qlshiftdivInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def mkShiftInjectedCase
    (name : String)
    (x : Int)
    (y : Int)
    (shift : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x, intV y] #[.pushInt shift, qlshiftdivInstr] gasLimits fuel

private def runQlshiftdivDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftdivInstr stack

private def runQlshiftdivDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 8137)) stack

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

private def qlshiftdivSetGasExact : Int :=
  computeExactGasBudget qlshiftdivInstr

private def qlshiftdivSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftdivInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOutOfRangePool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromPool shiftBoundaryPool rng1
  else
    let (n, rng2) := randNat rng1 0 256
    (Int.ofNat n, rng2)

private def pickOutOfRangeShift (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftOutOfRangePool rng

private def pickNonZeroSigned257ish (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQlshiftdiv (x y shift : Int) : String :=
  if shift < 0 || shift > 256 then
    "quiet-range-shift"
  else if y = 0 then
    "quiet-divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat
    let (q, r) := divModRound tmp y (-1)
    if !intFitsSigned257 q then
      "quiet-overflow"
    else if tmp = 0 then
      "zero"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQlshiftdivFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let y := if y0 = 0 then 1 else y0
      let (shift, r4) := pickFromPool shiftBoundaryPool r3
      let kind := classifyQlshiftdiv x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-boundary-shift"
        #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickFromPool shiftBoundaryPool r3
      let kind := classifyQlshiftdiv x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/random-boundary-shift"
        #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let kind := classifyQlshiftdiv x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/random-random-shift"
        #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let y := if y0 = 0 then 1 else y0
      let kind := classifyQlshiftdiv x y 256
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-shift-256"
        #[intV x, intV y, intV 256], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero-random"
        #[intV x, intV 0, intV shift], r3)
    else if shape = 5 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero-boundary-shift0"
        #[intV x, intV 0, intV 0], r2)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-max-shift1-div1"
        #[intV maxInt257, intV 1, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-min-shift1-div1"
        #[intV minInt257, intV 1, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-min-div-neg1"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/y-second-non-int"
        #[intV x, yLike, intV shift], r4)
    else if shape = 11 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/x-third-non-int"
        #[xLike, intV y, intV shift], r4)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 13 then
      let (shift, r2) := pickValidShift rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-arg"
        #[intV shift], r2)
    else if shape = 14 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-args"
        #[intV y, intV shift], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 16 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-shift-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (badShift, r4) := pickOutOfRangeShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/quiet/shift-range-via-program"
        x y (.num badShift), r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-does-not-mask-y-type"
        #[intV x, .null] #[.pushInt (.num 257), qlshiftdivInstr], r2)
    else if shape = 20 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-does-not-mask-x-type"
        #[.null, intV y] #[.pushInt (.num 257), qlshiftdivInstr], r2)
    else if shape = 21 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xo, IntVal.num y, IntVal.num shift], r4)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num yo, IntVal.num shift], r4)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shiftOut], r4)
    else
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (so, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        #[IntVal.num xo, IntVal.num yo, IntVal.num so], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftdivId
  unit := #[
    { name := "unit/direct/floor-sign-zero-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 4),
            (-7, 3, 1, -5),
            (7, -3, 1, -5),
            (-7, -3, 1, 4),
            (1, 2, 0, 0),
            (-1, 2, 0, -1),
            (5, 1, 0, 5),
            (5, -1, 0, -5),
            (0, 5, 200, 0),
            (13, 3, 2, 17),
            (-13, 3, 2, -18),
            (maxInt257, 2, 1, maxInt257),
            (minInt257, 2, 1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"unit/direct/x={x}/y={y}/shift={shift}"
            (runQlshiftdivDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-funnels-divzero-range-and-overflow"
      run := do
        expectOkStack "unit/quiet/divzero/nonzero-over-zero"
          (runQlshiftdivDirect #[intV 7, intV 0, intV 1]) #[.int .nan]
        expectOkStack "unit/quiet/divzero/zero-over-zero"
          (runQlshiftdivDirect #[intV 0, intV 0, intV 200]) #[.int .nan]
        expectOkStack "unit/quiet/shift-negative"
          (runQlshiftdivDirect #[intV 7, intV 3, intV (-1)]) #[.int .nan]
        expectOkStack "unit/quiet/shift-overmax"
          (runQlshiftdivDirect #[intV 7, intV 3, intV 257]) #[.int .nan]
        expectOkStack "unit/quiet/shift-nan"
          (runQlshiftdivDirect #[intV 7, intV 3, .int .nan]) #[.int .nan]
        expectOkStack "unit/quiet/nan-y"
          (runQlshiftdivDirect #[intV 7, .int .nan, intV 1]) #[.int .nan]
        expectOkStack "unit/quiet/nan-x"
          (runQlshiftdivDirect #[.int .nan, intV 3, intV 1]) #[.int .nan]
        expectOkStack "unit/quiet/overflow/max-shift1-div1"
          (runQlshiftdivDirect #[intV maxInt257, intV 1, intV 1]) #[.int .nan]
        expectOkStack "unit/quiet/overflow/min-shift1-div1"
          (runQlshiftdivDirect #[intV minInt257, intV 1, intV 1]) #[.int .nan]
        expectOkStack "unit/quiet/overflow/min-div-neg1"
          (runQlshiftdivDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan]
        expectOkStack "unit/quiet/overflow-x-out-of-range-direct"
          (runQlshiftdivDirect #[intV (pow2 257), intV 3, intV 1]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-quiet-range-precedence"
      run := do
        expectErr "unit/underflow/empty" (runQlshiftdivDirect #[]) .stkUnd
        expectErr "unit/underflow/one-arg" (runQlshiftdivDirect #[intV 1]) .stkUnd
        expectErr "unit/underflow/two-args" (runQlshiftdivDirect #[intV 1, intV 2]) .stkUnd
        expectErr "unit/type/shift-top-null"
          (runQlshiftdivDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "unit/type/shift-top-cell"
          (runQlshiftdivDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "unit/type/y-second-null"
          (runQlshiftdivDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "unit/type/x-third-null"
          (runQlshiftdivDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "unit/error-order/both-non-int-y-before-x"
          (runQlshiftdivDirect #[.cell Cell.empty, .null, intV 2]) .typeChk
        expectErr "unit/error-order/shift-range-does-not-mask-y-type"
          (runQlshiftdivDirect #[intV 1, .null, intV 257]) .typeChk
        expectErr "unit/error-order/shift-range-does-not-mask-x-type"
          (runQlshiftdivDirect #[.null, intV 1, intV 257]) .typeChk
        expectErr "unit/error-order/shift-nan-does-not-mask-y-type"
          (runQlshiftdivDirect #[intV 1, .null, .int .nan]) .typeChk }
    ,
    { name := "unit/direct/pop-order-top-three-consumed-below-preserved"
      run := do
        expectOkStack "unit/pop-order/below-null"
          (runQlshiftdivDirect #[.null, intV 14, intV 3, intV 1]) #[.null, intV 9]
        expectOkStack "unit/pop-order/below-cell-quiet-range"
          (runQlshiftdivDirect #[.cell Cell.empty, intV 14, intV 3, intV 257])
          #[.cell Cell.empty, .int .nan] }
    ,
    { name := "unit/opcode/decode-qlshiftdiv-sequence"
      run := do
        let program : Array Instr := #[qlshiftdivInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "unit/decode/qlshiftdiv" s0 qlshiftdivInstr 24
        let s2 ← expectDecodeStep "unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"unit/decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-qlshiftdiv-falls-through"
      run := do
        expectOkStack "unit/dispatch/fallback"
          (runQlshiftdivDispatchFallback #[]) #[intV 8137] }
  ]
  oracle := #[
    mkCase "ok/floor/sign/pos-pos-shift1" #[intV 7, intV 3, intV 1],
    mkCase "ok/floor/sign/neg-pos-shift1" #[intV (-7), intV 3, intV 1],
    mkCase "ok/floor/sign/pos-neg-shift1" #[intV 7, intV (-3), intV 1],
    mkCase "ok/floor/sign/neg-neg-shift1" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/floor/shift-zero-pos" #[intV 5, intV 2, intV 0],
    mkCase "ok/floor/shift-zero-neg" #[intV (-5), intV 2, intV 0],
    mkCase "ok/floor/zero-numerator-large-shift" #[intV 0, intV 5, intV 200],
    mkCase "ok/exact/divisible" #[intV 9, intV 3, intV 2],
    mkCase "ok/exact/divisible-negative" #[intV (-9), intV 3, intV 2],
    mkCase "ok/boundary/max-shift0-div1" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-shift0-div1" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/max-shift1-div2" #[intV maxInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-shift1-div2" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/boundary/max-minus-one-shift1-div2" #[intV (maxInt257 - 1), intV 2, intV 1],
    mkCase "ok/boundary/min-plus-one-shift1-div2" #[intV (minInt257 + 1), intV 2, intV 1],
    mkCase "ok/boundary/pow255-shift1-div2" #[intV (pow2 255), intV 2, intV 1],
    mkCase "ok/boundary/neg-pow255-shift1-div2" #[intV (-(pow2 255)), intV 2, intV 1],
    mkCase "ok/order/below-null-preserved" #[.null, intV 14, intV 3, intV 1],
    mkCase "ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-14), intV 3, intV 1],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 7, intV 0, intV 1],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 200],
    mkCase "quiet/shift-negative" #[intV 7, intV 3, intV (-1)],
    mkCase "quiet/shift-overmax" #[intV 7, intV 3, intV 257],
    mkCase "quiet/shift-way-overmax" #[intV 7, intV 3, intV 300],
    mkShiftInjectedCase "quiet/shift-nan-via-program" 7 3 .nan,
    mkCaseFromIntVals "quiet/nan-y-via-program" #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "quiet/nan-x-via-program" #[IntVal.nan, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "quiet/nan-both-via-program" #[IntVal.nan, IntVal.nan, IntVal.num 1],
    mkCase "quiet/overflow/max-shift1-div1" #[intV maxInt257, intV 1, intV 1],
    mkCase "quiet/overflow/min-shift1-div1" #[intV minInt257, intV 1, intV 1],
    mkCase "quiet/overflow/min-div-neg1" #[intV minInt257, intV (-1), intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "type/shift-top-null" #[intV 1, intV 2, .null],
    mkCase "type/shift-top-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/y-second-null" #[intV 1, .null, intV 2],
    mkCase "type/x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/both-non-int-y-before-x" #[.cell Cell.empty, .null, intV 2],
    mkCase "error-order/shift-range-does-not-mask-y-type-via-program"
      #[intV 7, .null] #[.pushInt (.num 257), qlshiftdivInstr],
    mkCase "error-order/shift-range-does-not-mask-x-type-via-program"
      #[.null, intV 7] #[.pushInt (.num 257), qlshiftdivInstr],
    mkCase "error-order/shift-nan-does-not-mask-y-type-via-program"
      #[intV 7, .null] #[.pushInt .nan, qlshiftdivInstr],
    mkCaseFromIntVals "error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 7, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-y-low-before-op"
      #[IntVal.num 7, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-high-before-op"
      #[IntVal.num 7, IntVal.num 3, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-low-before-op"
      #[IntVal.num 7, IntVal.num 3, IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-both-before-op"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (maxInt257 + 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftdivSetGasExact), .tonEnvOp .setGasLimit, qlshiftdivInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftdivSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftdivInstr]
  ]
  fuzz := #[
    { seed := 2026020856
      count := 700
      gen := genQlshiftdivFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTDIV
