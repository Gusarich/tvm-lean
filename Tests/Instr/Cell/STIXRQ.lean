import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STIXRQ

/-
STIXRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=false rev=true quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STIXRQ` encode: `0xcf06`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common` with `rev=1`, `quiet=1`).

Branch map used for this suite:
- Lean STIXRQ path: 13 branch sites / 19 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=true pop order; capacity guard;
   quiet failure re-push path with `-1`; fits check including `bits=0`; quiet range re-push path with `1`;
   success path with trailing status `0`).
- C++ STIXRQ path (args=6): 10 branch sites / 16 aligned outcomes.

Key risk areas:
- quiet mode only affects capacity/fit errors inside common store path;
- bits/type/underflow errors before that path still throw;
- on quiet failure stack order is `[builder, x, code]` (rev=true);
- `cellOv` must map to code `-1`, range failure to code `1`, success to `0`.
-/

private def stixrqId : InstrId := { name := "STIXRQ" }

private def stixrqInstr : Instr :=
  .stIntVar false true true

private def stixrInstr : Instr :=
  .stIntVar false true false

private def mkStixrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stixrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStixrqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStixrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stixrqInstr stack

private def runStixrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 412)) stack

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def overflowPosSignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 (bits - 1)

private def overflowNegSignedBits (bits : Nat) : Int :=
  if bits = 0 then -1 else -(intPow2 (bits - 1)) - 1

private def build1023Program : Array Instr :=
  build1023WithVarRev stixrInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, .pushInt (.num bits), stixrqInstr]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, .pushInt (.num bits), stixrqInstr]

private def stixrqSetGasExact : Int :=
  computeExactGasBudget stixrqInstr

private def stixrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stixrqInstr

private def stixrqBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257]

private def pickStixrqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stixrqBitsBoundaryPool.size - 1)
  (stixrqBitsBoundaryPool[idx]!, rng')

private def pickStixrqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStixrqBitsBoundary rng1
  else
    randNat rng1 0 257

private def pickStixrqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
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

private def genStixrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStixrqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStixrqInRange bits rng2
    (mkStixrqCase s!"fuzz/ok/top-only/bits-{bits}" #[.builder Builder.empty, intV x, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStixrqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 47 else .cell Cell.empty
    (mkStixrqCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, .builder Builder.empty, intV x, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixrqCase s!"fuzz/quiet-range-pos/bits-{bitsOv}"
      #[.builder Builder.empty, intV (overflowPosSignedBits bitsOv), intV bitsOv], rng2)
  else if shape = 3 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixrqCase s!"fuzz/quiet-range-neg/bits-{bitsOv}"
      #[.builder Builder.empty, intV (overflowNegSignedBits bitsOv), intV bitsOv], rng2)
  else if shape = 4 then
    (mkStixrqCase "fuzz/range/bits-too-large" #[.builder Builder.empty, intV 0, intV 258], rng2)
  else if shape = 5 then
    (mkStixrqCase "fuzz/range/bits-negative" #[.builder Builder.empty, intV 0, intV (-1)], rng2)
  else if shape = 6 then
    (mkStixrqCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStixrqCase s!"fuzz/type/x-not-int/bits-{bits}" #[.builder Builder.empty, .null, intV bits], rng2)
  else if shape = 8 then
    (mkStixrqCase s!"fuzz/type/builder-not-builder/bits-{bits}" #[.null, intV 1, intV bits], rng2)
  else if shape = 9 then
    let bitsCellov := if bits = 0 then 1 else bits
    let (x, rng3) := pickStixrqInRange bitsCellov rng2
    (mkStixrqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-{bitsCellov}" #[]
      (quietCellovProgram (.num x) bitsCellov), rng3)
  else
    (mkStixrqProgramCase s!"fuzz/quiet-range-nan/code1/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)

def suite : InstrSuite where
  id := stixrqId
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
            (runStixrqDirect #[.builder Builder.empty, intV x, intV bits])
            #[.builder expected, intV 0]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStixrqDirect #[.null, .builder Builder.empty, intV 7, intV 4])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/bits0-pos"
          (runStixrqDirect #[.builder Builder.empty, intV 1, intV 0])
          #[.builder Builder.empty, intV 1, intV 1]
        expectOkStack "quiet-range/bits0-neg"
          (runStixrqDirect #[.builder Builder.empty, intV (-1), intV 0])
          #[.builder Builder.empty, intV (-1), intV 1]
        expectOkStack "quiet-range/overflow-pos-bits1"
          (runStixrqDirect #[.builder Builder.empty, intV 1, intV 1])
          #[.builder Builder.empty, intV 1, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits1"
          (runStixrqDirect #[.builder Builder.empty, intV (-2), intV 1])
          #[.builder Builder.empty, intV (-2), intV 1]
        expectOkStack "quiet-range/overflow-pos-bits8"
          (runStixrqDirect #[.builder Builder.empty, intV 128, intV 8])
          #[.builder Builder.empty, intV 128, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits8"
          (runStixrqDirect #[.builder Builder.empty, intV (-129), intV 8])
          #[.builder Builder.empty, intV (-129), intV 1]
        expectOkStack "quiet-range/nan"
          (runStixrqDirect #[.builder Builder.empty, .int .nan, intV 8])
          #[.builder Builder.empty, .int .nan, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runStixrqDirect #[.builder fullBuilder1023, intV 0, intV 1])
          #[.builder fullBuilder1023, intV 0, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runStixrqDirect #[.builder fullBuilder1023, .int .nan, intV 1])
          #[.builder fullBuilder1023, .int .nan, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runStixrqDirect #[.builder fullBuilder1023, intV 1, intV 1])
          #[.builder fullBuilder1023, intV 1, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runStixrqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStixrqDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStixrqDirect #[.builder Builder.empty, intV 1]) .stkUnd

        expectErr "type/x-not-int-after-bits"
          (runStixrqDirect #[.builder Builder.empty, .null, intV 8]) .typeChk
        expectErr "type/builder-not-builder"
          (runStixrqDirect #[.null, intV 1, intV 8]) .typeChk

        expectErr "bits-too-large-still-throws"
          (runStixrqDirect #[.builder Builder.empty, intV 0, intV 258]) .rangeChk
        expectErr "bits-negative-still-throws"
          (runStixrqDirect #[.builder Builder.empty, intV 0, intV (-1)]) .rangeChk
        expectErr "bits-nan-still-throws"
          (runStixrqDirect #[.builder Builder.empty, intV 0, .int .nan]) .rangeChk
        expectErr "error-order/bits-before-x-type"
          (runStixrqDirect #[.builder Builder.empty, .null, intV 258]) .rangeChk
        expectErr "error-order/bits-before-builder-type"
          (runStixrqDirect #[.null, intV 0, intV (-1)]) .rangeChk }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stixrqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stixrq" s0 stixrqInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStixrqDispatchFallback #[.null])
          #[.null, intV 412] }
  ]
  oracle := #[
    mkStixrqCase "ok/bits-0-zero" #[.builder Builder.empty, intV 0, intV 0],
    mkStixrqCase "ok/bits-1-min" #[.builder Builder.empty, intV (-1), intV 1],
    mkStixrqCase "ok/bits-1-max" #[.builder Builder.empty, intV 0, intV 1],
    mkStixrqCase "ok/bits-8-min" #[.builder Builder.empty, intV (-128), intV 8],
    mkStixrqCase "ok/bits-8-max" #[.builder Builder.empty, intV 127, intV 8],
    mkStixrqCase "ok/bits-16-min" #[.builder Builder.empty, intV (-32768), intV 16],
    mkStixrqCase "ok/bits-16-max" #[.builder Builder.empty, intV 32767, intV 16],
    mkStixrqCase "ok/bits-257-minInt257" #[.builder Builder.empty, intV minInt257, intV 257],
    mkStixrqCase "ok/bits-257-maxInt257" #[.builder Builder.empty, intV maxInt257, intV 257],
    mkStixrqCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7, intV 4],

    mkStixrqCase "quiet-range/value-bits0-pos" #[.builder Builder.empty, intV 1, intV 0],
    mkStixrqCase "quiet-range/value-bits0-neg" #[.builder Builder.empty, intV (-1), intV 0],
    mkStixrqCase "quiet-range/overflow-pos-bits1" #[.builder Builder.empty, intV 1, intV 1],
    mkStixrqCase "quiet-range/overflow-neg-bits1" #[.builder Builder.empty, intV (-2), intV 1],
    mkStixrqCase "quiet-range/overflow-pos-bits8" #[.builder Builder.empty, intV 128, intV 8],
    mkStixrqCase "quiet-range/overflow-neg-bits8" #[.builder Builder.empty, intV (-129), intV 8],
    mkStixrqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty]
      (quietRangeNanProgram 8),

    mkStixrqCase "underflow/empty" #[],
    mkStixrqCase "underflow/one-item" #[intV 1],
    mkStixrqCase "underflow/two-items" #[.builder Builder.empty, intV 1],
    mkStixrqCase "type/x-not-int-after-bits" #[.builder Builder.empty, .null, intV 8],
    mkStixrqCase "type/builder-not-builder" #[.null, intV 1, intV 8],
    mkStixrqCase "bits-too-large-throws" #[.builder Builder.empty, intV 0, intV 258],
    mkStixrqCase "bits-negative-throws" #[.builder Builder.empty, intV 0, intV (-1)],

    mkStixrqCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stixrqSetGasExact), .tonEnvOp .setGasLimit, stixrqInstr],
    mkStixrqCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stixrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stixrqInstr],

    mkStixrqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkStixrqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkStixrqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 1) 1),
    mkStixrqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program
  ]
  fuzz := #[
    { seed := 2026020909
      count := 300
      gen := genStixrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STIXRQ
