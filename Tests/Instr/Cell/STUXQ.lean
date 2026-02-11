import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STUXQ

/-
STUXQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=true rev=false quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STUXQ` encode: `0xcf05`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common` with `quiet=1`).

Branch map used for this suite:
- Lean STUXQ path: 13 branch sites / 19 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=false pop order; capacity guard;
   quiet failure re-push path with `-1`; fits check including `bits=0`; quiet range re-push path with `1`;
   success path with trailing status `0`).
- C++ STUXQ path (args=5): 10 branch sites / 16 aligned outcomes.

Key risk areas:
- quiet mode only affects capacity/fit errors inside common store path;
- bits/type/underflow errors before that path still throw;
- on quiet failure stack order is `[x, builder, code]` (rev=false);
- `cellOv` must map to code `-1`, range failure to code `1`, success to `0`.
-/

private def stuxqId : InstrId := { name := "STUXQ" }

private def stuxqInstr : Instr :=
  .stIntVar true false true

private def stuxInstr : Instr :=
  .stIntVar true false false

private def mkStuxqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stuxqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStuxqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStuxqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stuxqInstr stack

private def runStuxqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 411)) stack

private def maxUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 bits - 1

private def overflowUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 bits

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithVar stuxInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, .xchg0 1, .pushInt (.num bits), stuxqInstr]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, .xchg0 1, .pushInt (.num bits), stuxqInstr]

private def stuxqSetGasExact : Int :=
  computeExactGasBudget stuxqInstr

private def stuxqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stuxqInstr

private def stuxqBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStuxqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stuxqBitsBoundaryPool.size - 1)
  (stuxqBitsBoundaryPool[idx]!, rng')

private def pickStuxqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStuxqBitsBoundary rng1
  else
    randNat rng1 0 256

private def pickStuxqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
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

private def genStuxqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStuxqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStuxqInRange bits rng2
    (mkStuxqCase s!"fuzz/ok/top-only/bits-{bits}" #[intV x, .builder Builder.empty, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStuxqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 43 else .cell Cell.empty
    (mkStuxqCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, intV x, .builder Builder.empty, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 256 then 255 else bits
    (mkStuxqCase s!"fuzz/quiet-range-overflow/bits-{bitsOv}"
      #[intV (overflowUnsignedBits bitsOv), .builder Builder.empty, intV bitsOv], rng2)
  else if shape = 3 then
    (mkStuxqCase s!"fuzz/quiet-range-negative/bits-{bits}" #[intV (-1), .builder Builder.empty, intV bits], rng2)
  else if shape = 4 then
    (mkStuxqCase "fuzz/range/bits-too-large" #[intV 0, .builder Builder.empty, intV 257], rng2)
  else if shape = 5 then
    (mkStuxqCase "fuzz/range/bits-negative" #[intV 0, .builder Builder.empty, intV (-1)], rng2)
  else if shape = 6 then
    (mkStuxqCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStuxqCase s!"fuzz/type/top-not-builder/bits-{bits}" #[intV 1, .null, intV bits], rng2)
  else if shape = 8 then
    (mkStuxqCase s!"fuzz/type/second-not-int/bits-{bits}" #[.null, .builder Builder.empty, intV bits], rng2)
  else if shape = 9 then
    let bitsCellov := if bits = 0 then 1 else bits
    let (x, rng3) := pickStuxqInRange bitsCellov rng2
    (mkStuxqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-{bitsCellov}" #[]
      (quietCellovProgram (.num x) bitsCellov), rng3)
  else
    (mkStuxqProgramCase s!"fuzz/quiet-range-nan/code1/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)

def suite : InstrSuite where
  id := stuxqId
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
            (runStuxqDirect #[intV x, .builder Builder.empty, intV bits])
            #[.builder expected, intV 0]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStuxqDirect #[.null, intV 7, .builder Builder.empty, intV 4])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/bits0-pos"
          (runStuxqDirect #[intV 1, .builder Builder.empty, intV 0])
          #[intV 1, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/bits0-neg"
          (runStuxqDirect #[intV (-1), .builder Builder.empty, intV 0])
          #[intV (-1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-bits1"
          (runStuxqDirect #[intV 2, .builder Builder.empty, intV 1])
          #[intV 2, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/negative-bits1"
          (runStuxqDirect #[intV (-1), .builder Builder.empty, intV 1])
          #[intV (-1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-bits8"
          (runStuxqDirect #[intV 256, .builder Builder.empty, intV 8])
          #[intV 256, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/negative-bits8"
          (runStuxqDirect #[intV (-1), .builder Builder.empty, intV 8])
          #[intV (-1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/nan"
          (runStuxqDirect #[.int .nan, .builder Builder.empty, intV 8])
          #[.int .nan, .builder Builder.empty, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runStuxqDirect #[intV 0, .builder fullBuilder1023, intV 1])
          #[intV 0, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runStuxqDirect #[.int .nan, .builder fullBuilder1023, intV 1])
          #[.int .nan, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runStuxqDirect #[intV 2, .builder fullBuilder1023, intV 1])
          #[intV 2, .builder fullBuilder1023, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runStuxqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStuxqDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStuxqDirect #[intV 1, .builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder-after-bits"
          (runStuxqDirect #[intV 1, .null, intV 8]) .typeChk
        expectErr "type/second-not-int"
          (runStuxqDirect #[.null, .builder Builder.empty, intV 8]) .typeChk

        expectErr "bits-too-large-still-throws"
          (runStuxqDirect #[intV 0, .builder Builder.empty, intV 257]) .rangeChk
        expectErr "bits-negative-still-throws"
          (runStuxqDirect #[intV 0, .builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "bits-nan-still-throws"
          (runStuxqDirect #[intV 0, .builder Builder.empty, .int .nan]) .rangeChk
        expectErr "error-order/bits-before-builder-type"
          (runStuxqDirect #[intV 1, .null, intV 257]) .rangeChk
        expectErr "error-order/bits-before-int-type"
          (runStuxqDirect #[.null, .builder Builder.empty, intV (-1)]) .rangeChk }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stuxqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stuxq" s0 stuxqInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStuxqDispatchFallback #[.null])
          #[.null, intV 411] }
  ]
  oracle := #[
    mkStuxqCase "ok/bits-0-zero" #[intV 0, .builder Builder.empty, intV 0],
    mkStuxqCase "ok/bits-1-zero" #[intV 0, .builder Builder.empty, intV 1],
    mkStuxqCase "ok/bits-1-one" #[intV 1, .builder Builder.empty, intV 1],
    mkStuxqCase "ok/bits-8-max" #[intV 255, .builder Builder.empty, intV 8],
    mkStuxqCase "ok/bits-16-max" #[intV 65535, .builder Builder.empty, intV 16],
    mkStuxqCase "ok/bits-256-max" #[intV maxUInt256, .builder Builder.empty, intV 256],
    mkStuxqCase "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty, intV 4],

    mkStuxqCase "quiet-range/value-bits0-pos" #[intV 1, .builder Builder.empty, intV 0],
    mkStuxqCase "quiet-range/value-bits0-neg" #[intV (-1), .builder Builder.empty, intV 0],
    mkStuxqCase "quiet-range/overflow-bits1" #[intV 2, .builder Builder.empty, intV 1],
    mkStuxqCase "quiet-range/negative-bits1" #[intV (-1), .builder Builder.empty, intV 1],
    mkStuxqCase "quiet-range/overflow-bits8" #[intV 256, .builder Builder.empty, intV 8],
    mkStuxqCase "quiet-range/negative-bits8" #[intV (-1), .builder Builder.empty, intV 8],
    mkStuxqCase "quiet-range/overflow-bits255" #[intV (intPow2 255), .builder Builder.empty, intV 255],
    mkStuxqCase "quiet-range/negative-bits256" #[intV (-1), .builder Builder.empty, intV 256],
    mkStuxqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty]
      (quietRangeNanProgram 8),

    mkStuxqCase "underflow/empty" #[],
    mkStuxqCase "underflow/one-item" #[intV 1],
    mkStuxqCase "underflow/two-items" #[intV 1, .builder Builder.empty],
    mkStuxqCase "type/top-not-builder-after-bits" #[intV 1, .null, intV 8],
    mkStuxqCase "type/second-not-int" #[.null, .builder Builder.empty, intV 8],
    mkStuxqCase "bits-too-large-throws" #[intV 0, .builder Builder.empty, intV 257],
    mkStuxqCase "bits-negative-throws" #[intV 0, .builder Builder.empty, intV (-1)],

    mkStuxqCase "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stuxqSetGasExact), .tonEnvOp .setGasLimit, stuxqInstr],
    mkStuxqCase "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stuxqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stuxqInstr],

    mkStuxqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkStuxqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkStuxqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 2) 1),
    mkStuxqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program
  ]
  fuzz := #[
    { seed := 2026020908
      count := 500
      gen := genStuxqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STUXQ
