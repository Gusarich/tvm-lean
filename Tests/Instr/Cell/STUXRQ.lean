import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STUXRQ

/-
STUXRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=true rev=true quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STUXRQ` encode: `0xcf07`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common` with `rev=1`, `quiet=1`).

Branch map used for this suite:
- Lean STUXRQ path: 13 branch sites / 19 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=true pop order; capacity guard;
   quiet failure re-push path with `-1`; fits check including `bits=0`; quiet range re-push path with `1`;
   success path with trailing status `0`).
- C++ STUXRQ path (args=7): 10 branch sites / 16 aligned outcomes.

Key risk areas:
- quiet mode only affects capacity/fit errors inside common store path;
- bits/type/underflow errors before that path still throw;
- on quiet failure stack order is `[builder, x, code]` (rev=true);
- `cellOv` must map to code `-1`, range failure to code `1`, success to `0`.
-/

private def stuxrqId : InstrId := { name := "STUXRQ" }

private def stuxrqInstr : Instr :=
  .stIntVar true true true

private def stuxrInstr : Instr :=
  .stIntVar true true false

private def mkStuxrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stuxrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStuxrqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStuxrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stuxrqInstr stack

private def runStuxrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 413)) stack

private def maxUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 bits - 1

private def overflowUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 bits

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithVarRev stuxrInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, .pushInt (.num bits), stuxrqInstr]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, .pushInt (.num bits), stuxrqInstr]

private def stuxrqSetGasExact : Int :=
  computeExactGasBudget stuxrqInstr

private def stuxrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stuxrqInstr

private def stuxrqBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStuxrqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stuxrqBitsBoundaryPool.size - 1)
  (stuxrqBitsBoundaryPool[idx]!, rng')

private def pickStuxrqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStuxrqBitsBoundary rng1
  else
    randNat rng1 0 256

private def pickStuxrqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let hi := maxUnsignedBits bits
  let (pick, rng') := randNat rng 0 4
  let x : Int :=
    if bits = 0 then
      0
    else if pick = 0 then
      0
    else if pick = 1 then
      1
    else if pick = 2 then
      hi
    else if pick = 3 then
      if hi > 0 then hi - 1 else 0
    else
      if hi > 1 then hi / 2 else hi
  (x, rng')

private def genStuxrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStuxrqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStuxrqInRange bits rng2
    (mkStuxrqCase s!"fuzz/ok/top-only/bits-{bits}" #[.builder Builder.empty, intV x, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStuxrqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 53 else .cell Cell.empty
    (mkStuxrqCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, .builder Builder.empty, intV x, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 256 then 255 else bits
    (mkStuxrqCase s!"fuzz/quiet-range-overflow/bits-{bitsOv}"
      #[.builder Builder.empty, intV (overflowUnsignedBits bitsOv), intV bitsOv], rng2)
  else if shape = 3 then
    (mkStuxrqCase s!"fuzz/quiet-range-negative/bits-{bits}" #[.builder Builder.empty, intV (-1), intV bits], rng2)
  else if shape = 4 then
    (mkStuxrqCase "fuzz/range/bits-too-large" #[.builder Builder.empty, intV 0, intV 257], rng2)
  else if shape = 5 then
    (mkStuxrqCase "fuzz/range/bits-negative" #[.builder Builder.empty, intV 0, intV (-1)], rng2)
  else if shape = 6 then
    (mkStuxrqCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStuxrqCase s!"fuzz/type/x-not-int/bits-{bits}" #[.builder Builder.empty, .null, intV bits], rng2)
  else if shape = 8 then
    (mkStuxrqCase s!"fuzz/type/builder-not-builder/bits-{bits}" #[.null, intV 1, intV bits], rng2)
  else if shape = 9 then
    let bitsCellov := if bits = 0 then 1 else bits
    let (x, rng3) := pickStuxrqInRange bitsCellov rng2
    (mkStuxrqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-{bitsCellov}" #[]
      (quietCellovProgram (.num x) bitsCellov), rng3)
  else
    (mkStuxrqProgramCase s!"fuzz/quiet-range-nan/code1/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)

def suite : InstrSuite where
  id := stuxrqId
  unit := #[
    { name := "unit/direct/success-returns-code0"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (0, 0),
            (1, 0),
            (1, 1),
            (8, 0),
            (8, 255),
            (256, 0),
            (256, maxUInt256)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          let bs : BitString :=
            if bits = 0 then #[]
            else natToBits x.toNat bits
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStuxrqDirect #[.builder Builder.empty, intV x, intV bits])
            #[.builder expected, intV 0]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStuxrqDirect #[.null, .builder Builder.empty, intV 7, intV 4])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/bits0-pos"
          (runStuxrqDirect #[.builder Builder.empty, intV 1, intV 0])
          #[.builder Builder.empty, intV 1, intV 1]
        expectOkStack "quiet-range/bits0-neg"
          (runStuxrqDirect #[.builder Builder.empty, intV (-1), intV 0])
          #[.builder Builder.empty, intV (-1), intV 1]
        expectOkStack "quiet-range/overflow-bits1"
          (runStuxrqDirect #[.builder Builder.empty, intV 2, intV 1])
          #[.builder Builder.empty, intV 2, intV 1]
        expectOkStack "quiet-range/negative-bits1"
          (runStuxrqDirect #[.builder Builder.empty, intV (-1), intV 1])
          #[.builder Builder.empty, intV (-1), intV 1]
        expectOkStack "quiet-range/overflow-bits8"
          (runStuxrqDirect #[.builder Builder.empty, intV 256, intV 8])
          #[.builder Builder.empty, intV 256, intV 1]
        expectOkStack "quiet-range/negative-bits8"
          (runStuxrqDirect #[.builder Builder.empty, intV (-1), intV 8])
          #[.builder Builder.empty, intV (-1), intV 1]
        expectOkStack "quiet-range/nan"
          (runStuxrqDirect #[.builder Builder.empty, .int .nan, intV 8])
          #[.builder Builder.empty, .int .nan, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runStuxrqDirect #[.builder fullBuilder1023, intV 0, intV 1])
          #[.builder fullBuilder1023, intV 0, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runStuxrqDirect #[.builder fullBuilder1023, .int .nan, intV 1])
          #[.builder fullBuilder1023, .int .nan, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runStuxrqDirect #[.builder fullBuilder1023, intV 2, intV 1])
          #[.builder fullBuilder1023, intV 2, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runStuxrqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStuxrqDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStuxrqDirect #[.builder Builder.empty, intV 1]) .stkUnd

        expectErr "type/x-not-int-after-bits"
          (runStuxrqDirect #[.builder Builder.empty, .null, intV 8]) .typeChk
        expectErr "type/builder-not-builder"
          (runStuxrqDirect #[.null, intV 1, intV 8]) .typeChk

        expectErr "bits-too-large-still-throws"
          (runStuxrqDirect #[.builder Builder.empty, intV 0, intV 257]) .rangeChk
        expectErr "bits-negative-still-throws"
          (runStuxrqDirect #[.builder Builder.empty, intV 0, intV (-1)]) .rangeChk
        expectErr "bits-nan-still-throws"
          (runStuxrqDirect #[.builder Builder.empty, intV 0, .int .nan]) .rangeChk
        expectErr "error-order/bits-before-x-type"
          (runStuxrqDirect #[.builder Builder.empty, .null, intV 257]) .rangeChk
        expectErr "error-order/bits-before-builder-type"
          (runStuxrqDirect #[.null, intV 0, intV (-1)]) .rangeChk }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stuxrqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stuxrq" s0 stuxrqInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStuxrqDispatchFallback #[.null])
          #[.null, intV 413] }
  ]
  oracle := #[
    mkStuxrqCase "ok/bits-0-zero" #[.builder Builder.empty, intV 0, intV 0],
    mkStuxrqCase "ok/bits-1-zero" #[.builder Builder.empty, intV 0, intV 1],
    mkStuxrqCase "ok/bits-1-one" #[.builder Builder.empty, intV 1, intV 1],
    mkStuxrqCase "ok/bits-8-max" #[.builder Builder.empty, intV 255, intV 8],
    mkStuxrqCase "ok/bits-16-max" #[.builder Builder.empty, intV 65535, intV 16],
    mkStuxrqCase "ok/bits-256-max" #[.builder Builder.empty, intV maxUInt256, intV 256],
    mkStuxrqCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7, intV 4],

    mkStuxrqCase "quiet-range/value-bits0-pos" #[.builder Builder.empty, intV 1, intV 0],
    mkStuxrqCase "quiet-range/value-bits0-neg" #[.builder Builder.empty, intV (-1), intV 0],
    mkStuxrqCase "quiet-range/overflow-bits1" #[.builder Builder.empty, intV 2, intV 1],
    mkStuxrqCase "quiet-range/negative-bits1" #[.builder Builder.empty, intV (-1), intV 1],
    mkStuxrqCase "quiet-range/overflow-bits8" #[.builder Builder.empty, intV 256, intV 8],
    mkStuxrqCase "quiet-range/negative-bits8" #[.builder Builder.empty, intV (-1), intV 8],
    mkStuxrqCase "quiet-range/overflow-bits255" #[.builder Builder.empty, intV (intPow2 255), intV 255],
    mkStuxrqCase "quiet-range/negative-bits256" #[.builder Builder.empty, intV (-1), intV 256],
    mkStuxrqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty]
      (quietRangeNanProgram 8),

    mkStuxrqCase "underflow/empty" #[],
    mkStuxrqCase "underflow/one-item" #[intV 1],
    mkStuxrqCase "underflow/two-items" #[.builder Builder.empty, intV 1],
    mkStuxrqCase "type/x-not-int-after-bits" #[.builder Builder.empty, .null, intV 8],
    mkStuxrqCase "type/builder-not-builder" #[.null, intV 1, intV 8],
    mkStuxrqCase "bits-too-large-throws" #[.builder Builder.empty, intV 0, intV 257],
    mkStuxrqCase "bits-negative-throws" #[.builder Builder.empty, intV 0, intV (-1)],

    mkStuxrqCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stuxrqSetGasExact), .tonEnvOp .setGasLimit, stuxrqInstr],
    mkStuxrqCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stuxrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stuxrqInstr],

    mkStuxrqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkStuxrqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkStuxrqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 2) 1),
    mkStuxrqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program
  ]
  fuzz := #[
    { seed := 2026020910
      count := 500
      gen := genStuxrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STUXRQ
