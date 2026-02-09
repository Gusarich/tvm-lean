import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STIXQ

/-
STIXQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=false rev=false quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STIXQ` encode: `0xcf04`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common` with `quiet=1`).

Branch map used for this suite:
- Lean STIXQ path: 13 branch sites / 19 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=false pop order; capacity guard;
   quiet failure re-push path with `-1`; fits check with `bits=0`; quiet range re-push path with `1`;
   success path with trailing status `0`).
- C++ STIXQ path (args=4): 10 branch sites / 16 aligned outcomes.

Key risk areas:
- quiet mode only affects capacity/fit errors inside common store path;
- bits/type/underflow errors before that path still throw;
- on quiet failure stack order is `[x, builder, code]` (rev=false);
- `cellOv` must map to code `-1`, range failure to code `1`, success to `0`.
-/

private def stixqId : InstrId := { name := "STIXQ" }

private def stixqInstr : Instr :=
  .stIntVar false false true

private def stixInstr : Instr :=
  .stIntVar false false false

private def mkStixqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stixqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStixqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStixqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stixqInstr stack

private def runStixqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 410)) stack

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def overflowPosSignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 (bits - 1)

private def overflowNegSignedBits (bits : Nat) : Int :=
  if bits = 0 then -1 else -(intPow2 (bits - 1)) - 1

private def build1023Program : Array Instr :=
  build1023WithVar stixInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, .xchg0 1, .pushInt (.num bits), stixqInstr]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, .xchg0 1, .pushInt (.num bits), stixqInstr]

private def stixqSetGasExact : Int :=
  computeExactGasBudget stixqInstr

private def stixqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stixqInstr

private def stixqBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257]

private def pickStixqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stixqBitsBoundaryPool.size - 1)
  (stixqBitsBoundaryPool[idx]!, rng')

private def pickStixqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStixqBitsBoundary rng1
  else
    randNat rng1 0 257

private def pickStixqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
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

private def genStixqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStixqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStixqInRange bits rng2
    (mkStixqCase s!"fuzz/ok/top-only/bits-{bits}" #[intV x, .builder Builder.empty, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStixqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 41 else .cell Cell.empty
    (mkStixqCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, intV x, .builder Builder.empty, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixqCase s!"fuzz/quiet-range-pos/bits-{bitsOv}"
      #[intV (overflowPosSignedBits bitsOv), .builder Builder.empty, intV bitsOv], rng2)
  else if shape = 3 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixqCase s!"fuzz/quiet-range-neg/bits-{bitsOv}"
      #[intV (overflowNegSignedBits bitsOv), .builder Builder.empty, intV bitsOv], rng2)
  else if shape = 4 then
    (mkStixqCase "fuzz/range/bits-too-large" #[intV 0, .builder Builder.empty, intV 258], rng2)
  else if shape = 5 then
    (mkStixqCase "fuzz/range/bits-negative" #[intV 0, .builder Builder.empty, intV (-1)], rng2)
  else if shape = 6 then
    (mkStixqCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStixqCase s!"fuzz/type/top-not-builder/bits-{bits}" #[intV 1, .null, intV bits], rng2)
  else if shape = 8 then
    (mkStixqCase s!"fuzz/type/second-not-int/bits-{bits}" #[.null, .builder Builder.empty, intV bits], rng2)
  else if shape = 9 then
    let bitsCellov := if bits = 0 then 1 else bits
    let (x, rng3) := pickStixqInRange bitsCellov rng2
    (mkStixqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-{bitsCellov}" #[]
      (quietCellovProgram (.num x) bitsCellov), rng3)
  else
    (mkStixqProgramCase s!"fuzz/quiet-range-nan/code1/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)

def suite : InstrSuite where
  id := stixqId
  unit := #[
    { name := "unit/direct/success-returns-code0"
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
            (runStixqDirect #[intV x, .builder Builder.empty, intV bits])
            #[.builder expected, intV 0]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStixqDirect #[.null, intV 7, .builder Builder.empty, intV 4])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/bits0-pos"
          (runStixqDirect #[intV 1, .builder Builder.empty, intV 0])
          #[intV 1, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/bits0-neg"
          (runStixqDirect #[intV (-1), .builder Builder.empty, intV 0])
          #[intV (-1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-pos-bits1"
          (runStixqDirect #[intV 1, .builder Builder.empty, intV 1])
          #[intV 1, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits1"
          (runStixqDirect #[intV (-2), .builder Builder.empty, intV 1])
          #[intV (-2), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-pos-bits8"
          (runStixqDirect #[intV 128, .builder Builder.empty, intV 8])
          #[intV 128, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits8"
          (runStixqDirect #[intV (-129), .builder Builder.empty, intV 8])
          #[intV (-129), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/nan"
          (runStixqDirect #[.int .nan, .builder Builder.empty, intV 8])
          #[.int .nan, .builder Builder.empty, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runStixqDirect #[intV 0, .builder fullBuilder1023, intV 1])
          #[intV 0, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runStixqDirect #[.int .nan, .builder fullBuilder1023, intV 1])
          #[.int .nan, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runStixqDirect #[intV 1, .builder fullBuilder1023, intV 1])
          #[intV 1, .builder fullBuilder1023, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runStixqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStixqDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStixqDirect #[intV 1, .builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder-after-bits"
          (runStixqDirect #[intV 1, .null, intV 8]) .typeChk
        expectErr "type/second-not-int"
          (runStixqDirect #[.null, .builder Builder.empty, intV 8]) .typeChk

        expectErr "bits-too-large-still-throws"
          (runStixqDirect #[intV 0, .builder Builder.empty, intV 258]) .rangeChk
        expectErr "bits-negative-still-throws"
          (runStixqDirect #[intV 0, .builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "bits-nan-still-throws"
          (runStixqDirect #[intV 0, .builder Builder.empty, .int .nan]) .rangeChk
        expectErr "error-order/bits-before-builder-type"
          (runStixqDirect #[intV 1, .null, intV 258]) .rangeChk
        expectErr "error-order/bits-before-int-type"
          (runStixqDirect #[.null, .builder Builder.empty, intV (-1)]) .rangeChk }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stixqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stixq" s0 stixqInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStixqDispatchFallback #[.null])
          #[.null, intV 410] }
  ]
  oracle := #[
    mkStixqCase "ok/bits-0-zero" #[intV 0, .builder Builder.empty, intV 0],
    mkStixqCase "ok/bits-1-min" #[intV (-1), .builder Builder.empty, intV 1],
    mkStixqCase "ok/bits-1-max" #[intV 0, .builder Builder.empty, intV 1],
    mkStixqCase "ok/bits-8-min" #[intV (-128), .builder Builder.empty, intV 8],
    mkStixqCase "ok/bits-8-max" #[intV 127, .builder Builder.empty, intV 8],
    mkStixqCase "ok/bits-16-min" #[intV (-32768), .builder Builder.empty, intV 16],
    mkStixqCase "ok/bits-16-max" #[intV 32767, .builder Builder.empty, intV 16],
    mkStixqCase "ok/bits-257-minInt257" #[intV minInt257, .builder Builder.empty, intV 257],
    mkStixqCase "ok/bits-257-maxInt257" #[intV maxInt257, .builder Builder.empty, intV 257],
    mkStixqCase "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty, intV 4],

    mkStixqCase "quiet-range/value-bits0-pos" #[intV 1, .builder Builder.empty, intV 0],
    mkStixqCase "quiet-range/value-bits0-neg" #[intV (-1), .builder Builder.empty, intV 0],
    mkStixqCase "quiet-range/overflow-pos-bits1" #[intV 1, .builder Builder.empty, intV 1],
    mkStixqCase "quiet-range/overflow-neg-bits1" #[intV (-2), .builder Builder.empty, intV 1],
    mkStixqCase "quiet-range/overflow-pos-bits8" #[intV 128, .builder Builder.empty, intV 8],
    mkStixqCase "quiet-range/overflow-neg-bits8" #[intV (-129), .builder Builder.empty, intV 8],
    mkStixqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty]
      (quietRangeNanProgram 8),

    mkStixqCase "underflow/empty" #[],
    mkStixqCase "underflow/one-item" #[intV 1],
    mkStixqCase "underflow/two-items" #[intV 1, .builder Builder.empty],
    mkStixqCase "type/top-not-builder-after-bits" #[intV 1, .null, intV 8],
    mkStixqCase "type/second-not-int" #[.null, .builder Builder.empty, intV 8],
    mkStixqCase "bits-too-large-throws" #[intV 0, .builder Builder.empty, intV 258],
    mkStixqCase "bits-negative-throws" #[intV 0, .builder Builder.empty, intV (-1)],

    mkStixqCase "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stixqSetGasExact), .tonEnvOp .setGasLimit, stixqInstr],
    mkStixqCase "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stixqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stixqInstr],

    mkStixqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkStixqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkStixqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 1) 1),
    mkStixqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program
  ]
  fuzz := #[
    { seed := 2026020907
      count := 300
      gen := genStixqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STIXQ
