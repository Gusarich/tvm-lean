import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STIRQ

/-
STIRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean` (`.stIntFixed unsigned=false rev=true quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STIRQ` as `0xcf08`-family with `rev=1`, `quiet=1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf08` fixed-width family decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, args with `rev=1`, `quiet=1`).

Branch map used for this suite:
- Lean STIRQ path: 10 branch sites / 16 terminal outcomes
  (`checkUnderflow 2`; rev pop order; capacity guard; signed fit;
   quiet failure re-push with `-1` / `1`; success append with trailing `0`).
- C++ STIRQ path: 8 branch sites / 14 aligned outcomes.

Key risk areas:
- reversed pop order (`x` first, then `builder`) controls quiet re-push order;
- signed width boundary off-by-one at `[-2^(bits-1), 2^(bits-1)-1]`;
- quiet mode must return status `-1` for capacity and `1` for range failures;
- `cellOv`-class failures must be prioritized before range failures when builder is full.
-/

private def stirqId : InstrId := { name := "STIRQ" }

private def stirqInstr (bits : Nat) : Instr :=
  .stIntFixed false true true bits

private def stirInstr (bits : Nat) : Instr :=
  .stIntFixed false true false bits

private def mkStirqCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stirqInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stirqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStirqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stirqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStirqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (stirqInstr bits) stack

private def runStirqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed .add (VM.push (intV 415)) stack

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def overflowPosSignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 (bits - 1)

private def overflowNegSignedBits (bits : Nat) : Int :=
  if bits = 0 then -1 else -(intPow2 (bits - 1)) - 1

private def build1023Program : Array Instr :=
  build1023WithFixedRev stirInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, stirqInstr bits]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, stirqInstr bits]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num (-3)), stirqInstr 4
  ]

private def stirqGasProbeBits : Nat := 8

private def stirqSetGasExact : Int :=
  computeExactGasBudget (stirqInstr stirqGasProbeBits)

private def stirqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stirqInstr stirqGasProbeBits)

private def stirqBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStirqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stirqBitsBoundaryPool.size - 1)
  (stirqBitsBoundaryPool[idx]!, rng')

private def pickStirqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStirqBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickStirqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let lo := minSignedBits bits
  let hi := maxSignedBits bits
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then hi
    else if pick = 4 then lo
    else if hi > lo then hi - 1 else lo
  (x, rng')

private def genStirqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (bits, rng2) := pickStirqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStirqInRange bits rng2
    (mkStirqCase s!"fuzz/ok/top-only/bits-{bits}" bits #[.builder Builder.empty, intV x], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStirqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 61 else .cell Cell.empty
    (mkStirqCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, .builder Builder.empty, intV x], rng4)
  else if shape = 2 then
    (mkStirqCase s!"fuzz/quiet-range-overflow-pos/bits-{bits}" bits
      #[.builder Builder.empty, intV (overflowPosSignedBits bits)], rng2)
  else if shape = 3 then
    (mkStirqCase s!"fuzz/quiet-range-overflow-neg/bits-{bits}" bits
      #[.builder Builder.empty, intV (overflowNegSignedBits bits)], rng2)
  else if shape = 4 then
    (mkStirqCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStirqCase s!"fuzz/underflow/one-item/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 6 then
    (mkStirqCase s!"fuzz/type/x-not-int/bits-{bits}" bits #[.builder Builder.empty, .null], rng2)
  else if shape = 7 then
    (mkStirqCase s!"fuzz/type/builder-not-builder/bits-{bits}" bits #[.null, intV 1], rng2)
  else if shape = 8 then
    (mkStirqProgramCase s!"fuzz/quiet-range-nan-via-program/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)
  else
    let (x, rng3) := pickStirqInRange 1 rng2
    (mkStirqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-1/x-{x}" #[]
      (quietCellovProgram (.num x) 1), rng3)

def suite : InstrSuite where
  id := stirqId
  unit := #[
    { name := "unit/direct/success-returns-code0"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, -1),
            (1, 0),
            (8, -128),
            (8, 127),
            (256, -(intPow2 255)),
            (256, intPow2 255 - 1)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          let bs ←
            match intToBitsTwos x bits with
            | .ok out => pure out
            | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e} for bits={bits}, x={x}")
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStirqDirect bits #[.builder Builder.empty, intV x])
            #[.builder expected, intV 0]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appendedBits ←
          match intToBitsTwos (-3) 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let appended := prefBuilder.storeBits appendedBits
        expectOkStack "ok/append-existing-bits"
          (runStirqDirect 4 #[.builder prefBuilder, intV (-3)])
          #[.builder appended, intV 0]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStirqDirect 4 #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/overflow-pos-bits1"
          (runStirqDirect 1 #[.builder Builder.empty, intV 1])
          #[.builder Builder.empty, intV 1, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits1"
          (runStirqDirect 1 #[.builder Builder.empty, intV (-2)])
          #[.builder Builder.empty, intV (-2), intV 1]
        expectOkStack "quiet-range/overflow-pos-bits8"
          (runStirqDirect 8 #[.builder Builder.empty, intV 128])
          #[.builder Builder.empty, intV 128, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits8"
          (runStirqDirect 8 #[.builder Builder.empty, intV (-129)])
          #[.builder Builder.empty, intV (-129), intV 1]
        expectOkStack "quiet-range/overflow-pos-bits256"
          (runStirqDirect 256 #[.builder Builder.empty, intV (intPow2 255)])
          #[.builder Builder.empty, intV (intPow2 255), intV 1]
        expectOkStack "quiet-range/overflow-neg-bits256"
          (runStirqDirect 256 #[.builder Builder.empty, intV (-(intPow2 255) - 1)])
          #[.builder Builder.empty, intV (-(intPow2 255) - 1), intV 1]
        expectOkStack "quiet-range/nan"
          (runStirqDirect 8 #[.builder Builder.empty, .int .nan])
          #[.builder Builder.empty, .int .nan, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runStirqDirect 1 #[.builder fullBuilder1023, intV 0])
          #[.builder fullBuilder1023, intV 0, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runStirqDirect 1 #[.builder fullBuilder1023, .int .nan])
          #[.builder fullBuilder1023, .int .nan, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runStirqDirect 1 #[.builder fullBuilder1023, intV 1])
          #[.builder fullBuilder1023, intV 1, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runStirqDirect 8 #[]) .stkUnd
        expectErr "underflow/one-item" (runStirqDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStirqDirect 8 #[.null]) .stkUnd

        expectErr "type/x-not-int-after-pop"
          (runStirqDirect 8 #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/builder-not-builder"
          (runStirqDirect 8 #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-x-first"
          (runStirqDirect 8 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stirqInstr 1, stirqInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stirq-1" s0 (stirqInstr 1) 24
        let s2 ← expectDecodeStep "decode/stirq-256" s1 (stirqInstr 256) 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        match assembleCp0 [stirqInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stirq/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stirq/0: expected assemble rangeChk, got success")
        match assembleCp0 [stirqInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stirq/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stirq/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStirqDispatchFallback #[.null])
          #[.null, intV 415] }
  ]
  oracle := #[
    mkStirqCase "ok/bits1-min" 1 #[.builder Builder.empty, intV (-1)],
    mkStirqCase "ok/bits1-max" 1 #[.builder Builder.empty, intV 0],
    mkStirqCase "ok/bits8-min" 8 #[.builder Builder.empty, intV (-128)],
    mkStirqCase "ok/bits8-max" 8 #[.builder Builder.empty, intV 127],
    mkStirqCase "ok/bits16-min" 16 #[.builder Builder.empty, intV (-32768)],
    mkStirqCase "ok/bits16-max" 16 #[.builder Builder.empty, intV 32767],
    mkStirqCase "ok/bits32-min" 32 #[.builder Builder.empty, intV (-(intPow2 31))],
    mkStirqCase "ok/bits32-max" 32 #[.builder Builder.empty, intV (intPow2 31 - 1)],
    mkStirqCase "ok/bits256-min" 256 #[.builder Builder.empty, intV (-(intPow2 255))],
    mkStirqCase "ok/bits256-max" 256 #[.builder Builder.empty, intV (intPow2 255 - 1)],
    mkStirqCase "ok/deep-stack-below-preserved" 4 #[.null, .builder Builder.empty, intV 7],
    mkStirqProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkStirqCase "quiet-range/overflow-pos-bits1" 1 #[.builder Builder.empty, intV 1],
    mkStirqCase "quiet-range/overflow-neg-bits1" 1 #[.builder Builder.empty, intV (-2)],
    mkStirqCase "quiet-range/overflow-pos-bits8" 8 #[.builder Builder.empty, intV 128],
    mkStirqCase "quiet-range/overflow-neg-bits8" 8 #[.builder Builder.empty, intV (-129)],
    mkStirqCase "quiet-range/overflow-pos-bits256" 256 #[.builder Builder.empty, intV (intPow2 255)],
    mkStirqCase "quiet-range/overflow-neg-bits256" 256 #[.builder Builder.empty, intV (-(intPow2 255) - 1)],
    mkStirqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty] (quietRangeNanProgram 8),

    mkStirqCase "underflow/empty" 8 #[],
    mkStirqCase "underflow/one-item" 8 #[.builder Builder.empty],
    mkStirqCase "type/x-not-int" 8 #[.builder Builder.empty, .null],
    mkStirqCase "type/builder-not-builder" 8 #[.null, intV 1],

    mkStirqCase "gas/exact-cost-succeeds" stirqGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stirqSetGasExact), .tonEnvOp .setGasLimit, stirqInstr stirqGasProbeBits],
    mkStirqCase "gas/exact-minus-one-out-of-gas" stirqGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stirqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stirqInstr stirqGasProbeBits],

    mkStirqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkStirqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkStirqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 1) 1),
    mkStirqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program,
    mkStirqProgramCase "program/build-1023-then-quiet-success" #[] (build1023Program ++ #[.pushInt (.num 0), stirqInstr 1])
  ]
  fuzz := #[
    { seed := 2026020912
      count := 300
      gen := genStirqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STIRQ
