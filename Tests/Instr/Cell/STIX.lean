import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STIX

/-
STIX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=false rev=false quiet=false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STIX` encode: `0xcf00`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common`).

Branch map used for this suite:
- Lean STIX path: 11 branch sites / 15 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=false pop order; builder capacity;
   fits check including `bits=0`; quiet=false throw path; success push).
- C++ STIX path (args=0): 8 branch sites / 12 aligned outcomes
  (`check_underflow(3)`; bits range [0..257]; pop order; capacity; signed fit).

Key risk areas:
- bits are popped first; bits range/type failures must happen before builder/int type checks;
- `bits=0` is valid only for `x=0` (stores zero bits);
- signed boundary for variable width, including full 257-bit domain;
- `cellOv` must win over value-range errors when builder is already full.
-/

private def stixId : InstrId := { name := "STIX" }

private def stixInstr : Instr :=
  .stIntVar false false false

private def mkStixCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stixInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStixProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStixDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stixInstr stack

private def runStixDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 406)) stack

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then
    0
  else
    -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then
    0
  else
    intPow2 (bits - 1) - 1

private def overflowPosSignedBits (bits : Nat) : Int :=
  if bits = 0 then
    1
  else
    intPow2 (bits - 1)

private def overflowNegSignedBits (bits : Nat) : Int :=
  if bits = 0 then
    -1
  else
    -(intPow2 (bits - 1)) - 1

private def build1023Program : Array Instr :=
  build1023WithVar stixInstr

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, .pushInt (.num 1), stixInstr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, .pushInt (.num 1), stixInstr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1), .xchg0 1, .pushInt (.num 1), stixInstr]

private def stixSetGasExact : Int :=
  computeExactGasBudget stixInstr

private def stixSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stixInstr

private def stixBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257]

private def pickStixBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stixBitsBoundaryPool.size - 1)
  (stixBitsBoundaryPool[idx]!, rng')

private def pickStixBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStixBitsBoundary rng1
  else
    randNat rng1 0 257

private def pickStixInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let lo := minSignedBits bits
  let hi := maxSignedBits bits
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if bits = 0 then
      0
    else if pick = 0 then
      0
    else if pick = 1 then
      1
    else if pick = 2 then
      -1
    else if pick = 3 then
      hi
    else if pick = 4 then
      lo
    else if hi > lo then
      hi - 1
    else
      lo
  (x, rng')

private def genStixFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStixBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStixInRange bits rng2
    (mkStixCase s!"fuzz/ok/top-only/bits-{bits}" #[intV x, .builder Builder.empty, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStixInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 23 else .cell Cell.empty
    (mkStixCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, intV x, .builder Builder.empty, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixCase s!"fuzz/range/overflow-pos/bits-{bitsOv}"
      #[intV (overflowPosSignedBits bitsOv), .builder Builder.empty, intV bitsOv], rng2)
  else if shape = 3 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixCase s!"fuzz/range/overflow-neg/bits-{bitsOv}"
      #[intV (overflowNegSignedBits bitsOv), .builder Builder.empty, intV bitsOv], rng2)
  else if shape = 4 then
    (mkStixCase "fuzz/range/bits-too-large" #[intV 0, .builder Builder.empty, intV 258], rng2)
  else if shape = 5 then
    (mkStixCase "fuzz/range/bits-negative" #[intV 0, .builder Builder.empty, intV (-1)], rng2)
  else if shape = 6 then
    (mkStixCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStixCase s!"fuzz/underflow/two-items/bits-{bits}" #[intV 1, .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStixCase s!"fuzz/type/top-not-builder/bits-{bits}" #[intV 1, .null, intV bits], rng2)
  else if shape = 9 then
    (mkStixCase s!"fuzz/type/second-not-int/bits-{bits}" #[.null, .builder Builder.empty, intV bits], rng2)
  else
    (mkStixProgramCase s!"fuzz/range/nan-program/bits-{bits}"
      #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, .pushInt (.num bits), stixInstr], rng2)

def suite : InstrSuite where
  id := stixId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (0, 0),
            (1, -1),
            (1, 0),
            (8, -128),
            (8, 127),
            (257, minInt257),
            (257, maxInt257)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          let bs : BitString ←
            if bits = 0 then
              pure #[]
            else
              match intToBitsTwos x bits with
              | .ok out => pure out
              | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e} for bits={bits}, x={x}")
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStixDirect #[intV x, .builder Builder.empty, intV bits])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appendedBits ←
          match intToBitsTwos (-3) 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let appended := prefBuilder.storeBits appendedBits
        expectOkStack "ok/append-existing-bits"
          (runStixDirect #[intV (-3), .builder prefBuilder, intV 4])
          #[.builder appended]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStixDirect #[.null, intV 7, .builder Builder.empty, intV 4])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks-for-value-and-bits"
      run := do
        expectErr "range/bits0-x1"
          (runStixDirect #[intV 1, .builder Builder.empty, intV 0]) .rangeChk
        expectErr "range/bits0-xminus1"
          (runStixDirect #[intV (-1), .builder Builder.empty, intV 0]) .rangeChk
        expectErr "range/overflow-pos-bits1"
          (runStixDirect #[intV 1, .builder Builder.empty, intV 1]) .rangeChk
        expectErr "range/overflow-neg-bits1"
          (runStixDirect #[intV (-2), .builder Builder.empty, intV 1]) .rangeChk
        expectErr "range/overflow-pos-bits8"
          (runStixDirect #[intV 128, .builder Builder.empty, intV 8]) .rangeChk
        expectErr "range/overflow-neg-bits8"
          (runStixDirect #[intV (-129), .builder Builder.empty, intV 8]) .rangeChk
        expectErr "range/nan"
          (runStixDirect #[.int .nan, .builder Builder.empty, intV 8]) .rangeChk

        expectErr "range/bits-too-large"
          (runStixDirect #[intV 0, .builder Builder.empty, intV 258]) .rangeChk
        expectErr "range/bits-negative"
          (runStixDirect #[intV 0, .builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/bits-nan"
          (runStixDirect #[intV 0, .builder Builder.empty, .int .nan]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStixDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStixDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStixDirect #[intV 1, .builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStixDirect #[.null]) .stkUnd

        expectErr "type/pop-builder-after-bits"
          (runStixDirect #[intV 1, .null, intV 8]) .typeChk
        expectErr "type/pop-int-after-builder"
          (runStixDirect #[.null, .builder Builder.empty, intV 8]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStixDirect #[.cell Cell.empty, .null, intV 8]) .typeChk

        expectErr "error-order/bits-range-before-builder-type"
          (runStixDirect #[intV 1, .null, intV 258]) .rangeChk
        expectErr "error-order/bits-range-before-int-type"
          (runStixDirect #[.null, .builder Builder.empty, intV (-1)]) .rangeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStixDirect #[intV 0, .builder fullBuilder1023, intV 1]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStixDirect #[.int .nan, .builder fullBuilder1023, intV 1]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStixDirect #[intV 1, .builder fullBuilder1023, intV 1]) .cellOv }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stixInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stix" s0 stixInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStixDispatchFallback #[.null])
          #[.null, intV 406] }
  ]
  oracle := #[
    mkStixCase "ok/bits-0-zero" #[intV 0, .builder Builder.empty, intV 0],
    mkStixCase "ok/bits-1-min" #[intV (-1), .builder Builder.empty, intV 1],
    mkStixCase "ok/bits-1-max" #[intV 0, .builder Builder.empty, intV 1],
    mkStixCase "ok/bits-8-min" #[intV (-128), .builder Builder.empty, intV 8],
    mkStixCase "ok/bits-8-max" #[intV 127, .builder Builder.empty, intV 8],
    mkStixCase "ok/bits-16-min" #[intV (-32768), .builder Builder.empty, intV 16],
    mkStixCase "ok/bits-16-max" #[intV 32767, .builder Builder.empty, intV 16],
    mkStixCase "ok/bits-257-minInt257" #[intV minInt257, .builder Builder.empty, intV 257],
    mkStixCase "ok/bits-257-maxInt257" #[intV maxInt257, .builder Builder.empty, intV 257],
    mkStixCase "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty, intV 4],

    mkStixCase "range/value-bits0-pos" #[intV 1, .builder Builder.empty, intV 0],
    mkStixCase "range/value-bits0-neg" #[intV (-1), .builder Builder.empty, intV 0],
    mkStixCase "range/overflow-pos-bits1" #[intV 1, .builder Builder.empty, intV 1],
    mkStixCase "range/overflow-neg-bits1" #[intV (-2), .builder Builder.empty, intV 1],
    mkStixCase "range/overflow-pos-bits8" #[intV 128, .builder Builder.empty, intV 8],
    mkStixCase "range/overflow-neg-bits8" #[intV (-129), .builder Builder.empty, intV 8],
    mkStixProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, .pushInt (.num 8), stixInstr],
    mkStixCase "range/bits-too-large" #[intV 0, .builder Builder.empty, intV 258],
    mkStixCase "range/bits-negative" #[intV 0, .builder Builder.empty, intV (-1)],

    mkStixCase "underflow/empty" #[],
    mkStixCase "underflow/one-item" #[intV 1],
    mkStixCase "underflow/two-items" #[intV 1, .builder Builder.empty],
    mkStixCase "type/top-not-builder-after-bits" #[intV 1, .null, intV 8],
    mkStixCase "type/second-not-int" #[.null, .builder Builder.empty, intV 8],

    mkStixCase "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stixSetGasExact), .tonEnvOp .setGasLimit, stixInstr],
    mkStixCase "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stixSetGasExactMinusOne), .tonEnvOp .setGasLimit, stixInstr],

    mkStixProgramCase "program/build-1023-success" #[] build1023Program,
    mkStixProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStixProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStixProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020903
      count := 500
      gen := genStixFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STIX
