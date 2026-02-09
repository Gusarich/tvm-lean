import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STUQ

/-
STUQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean` (`.stIntFixed unsigned=true rev=false quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STUQ` as `0xcf08`-family with `unsigned=1`, `quiet=1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf08` fixed-width family decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, args with `unsigned=1`, `quiet=1`).

Branch map used for this suite:
- Lean STUQ path: 10 branch sites / 16 terminal outcomes
  (`checkUnderflow 2`; non-rev pop order; capacity guard; unsigned fit;
   quiet failure re-push with `-1` / `1`; success append with trailing `0`).
- C++ STUQ path: 8 branch sites / 14 aligned outcomes.

Key risk areas:
- non-reversed mode uses stack convention `[x, builder]`;
- quiet failures re-push as `[x, builder, code]`;
- unsigned boundaries at `[0, 2^bits - 1]` with negatives mapping to code `1`;
- capacity failure must map to `-1` before any range diagnostics.
-/

private def stuqId : InstrId := { name := "STUQ" }

private def stuqInstr (bits : Nat) : Instr :=
  .stIntFixed true false true bits

private def stuInstr (bits : Nat) : Instr :=
  .stIntFixed true false false bits

private def mkStuqCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stuqInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStuqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStuqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (stuqInstr bits) stack

private def runStuqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed .add (VM.push (intV 419)) stack

private def maxUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 bits - 1

private def overflowUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 bits

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithFixed stuInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, .xchg0 1, stuqInstr bits]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, .xchg0 1, stuqInstr bits]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 17), .xchg0 1, stuqInstr 5
  ]

private def stuqGasProbeBits : Nat := 8

private def stuqSetGasExact : Int :=
  computeExactGasBudget (stuqInstr stuqGasProbeBits)

private def stuqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stuqInstr stuqGasProbeBits)

private def stuqBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStuqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stuqBitsBoundaryPool.size - 1)
  (stuqBitsBoundaryPool[idx]!, rng')

private def pickStuqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStuqBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickStuqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let hi := maxUnsignedBits bits
  let (pick, rng') := randNat rng 0 4
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then hi
    else if pick = 3 then
      if hi > 0 then hi - 1 else 0
    else
      if hi > 1 then hi / 2 else hi
  (x, rng')

private def genStuqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (bits, rng2) := pickStuqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStuqInRange bits rng2
    (mkStuqCase s!"fuzz/ok/top-only/bits-{bits}" bits #[intV x, .builder Builder.empty], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStuqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 79 else .cell Cell.empty
    (mkStuqCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, intV x, .builder Builder.empty], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 256 then 255 else bits
    (mkStuqCase s!"fuzz/quiet-range-overflow/bits-{bitsOv}" bitsOv
      #[intV (overflowUnsignedBits bitsOv), .builder Builder.empty], rng2)
  else if shape = 3 then
    (mkStuqCase s!"fuzz/quiet-range-negative/bits-{bits}" bits #[intV (-1), .builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStuqCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStuqCase s!"fuzz/underflow/one-item/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 6 then
    (mkStuqCase s!"fuzz/type/top-not-builder/bits-{bits}" bits #[intV 1, .null], rng2)
  else if shape = 7 then
    (mkStuqCase s!"fuzz/type/second-not-int/bits-{bits}" bits #[.null, .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStuqProgramCase s!"fuzz/quiet-range-nan-via-program/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)
  else
    let (x, rng3) := pickStuqInRange 1 rng2
    (mkStuqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-1/x-{x}" #[]
      (quietCellovProgram (.num x) 1), rng3)

def suite : InstrSuite where
  id := stuqId
  unit := #[
    { name := "unit/direct/success-returns-code0"
      run := do
        let checks : Array (Nat × Int) :=
          #[
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
          let bs : BitString := natToBits x.toNat bits
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStuqDirect bits #[intV x, .builder Builder.empty])
            #[.builder expected, intV 0]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (natToBits 17 5)
        expectOkStack "ok/append-existing-bits"
          (runStuqDirect 5 #[intV 17, .builder prefBuilder])
          #[.builder appended, intV 0]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStuqDirect 4 #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/overflow-pos-bits1"
          (runStuqDirect 1 #[intV 2, .builder Builder.empty])
          #[intV 2, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/negative-bits1"
          (runStuqDirect 1 #[intV (-1), .builder Builder.empty])
          #[intV (-1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-pos-bits8"
          (runStuqDirect 8 #[intV 256, .builder Builder.empty])
          #[intV 256, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/negative-bits8"
          (runStuqDirect 8 #[intV (-1), .builder Builder.empty])
          #[intV (-1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-pos-bits256"
          (runStuqDirect 256 #[intV overUInt256, .builder Builder.empty])
          #[intV overUInt256, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/negative-bits256"
          (runStuqDirect 256 #[intV (-1), .builder Builder.empty])
          #[intV (-1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/nan"
          (runStuqDirect 8 #[.int .nan, .builder Builder.empty])
          #[.int .nan, .builder Builder.empty, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runStuqDirect 1 #[intV 0, .builder fullBuilder1023])
          #[intV 0, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runStuqDirect 1 #[.int .nan, .builder fullBuilder1023])
          #[.int .nan, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runStuqDirect 1 #[intV 2, .builder fullBuilder1023])
          #[intV 2, .builder fullBuilder1023, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runStuqDirect 8 #[]) .stkUnd
        expectErr "underflow/one-item" (runStuqDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStuqDirect 8 #[.null]) .stkUnd

        expectErr "type/builder-pop-first"
          (runStuqDirect 8 #[intV 1, .null]) .typeChk
        expectErr "type/int-pop-second"
          (runStuqDirect 8 #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStuqDirect 8 #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stuqInstr 1, stuqInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stuq-1" s0 (stuqInstr 1) 24
        let s2 ← expectDecodeStep "decode/stuq-256" s1 (stuqInstr 256) 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        match assembleCp0 [stuqInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stuq/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stuq/0: expected assemble rangeChk, got success")
        match assembleCp0 [stuqInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stuq/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stuq/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStuqDispatchFallback #[.null])
          #[.null, intV 419] }
  ]
  oracle := #[
    mkStuqCase "ok/bits1-zero" 1 #[intV 0, .builder Builder.empty],
    mkStuqCase "ok/bits1-one" 1 #[intV 1, .builder Builder.empty],
    mkStuqCase "ok/bits8-zero" 8 #[intV 0, .builder Builder.empty],
    mkStuqCase "ok/bits8-max" 8 #[intV 255, .builder Builder.empty],
    mkStuqCase "ok/bits16-zero" 16 #[intV 0, .builder Builder.empty],
    mkStuqCase "ok/bits16-max" 16 #[intV 65535, .builder Builder.empty],
    mkStuqCase "ok/bits32-zero" 32 #[intV 0, .builder Builder.empty],
    mkStuqCase "ok/bits32-max" 32 #[intV (intPow2 32 - 1), .builder Builder.empty],
    mkStuqCase "ok/bits256-zero" 256 #[intV 0, .builder Builder.empty],
    mkStuqCase "ok/bits256-max" 256 #[intV maxUInt256, .builder Builder.empty],
    mkStuqCase "ok/deep-stack-below-preserved" 4 #[.null, intV 7, .builder Builder.empty],
    mkStuqProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkStuqCase "quiet-range/overflow-pos-bits1" 1 #[intV 2, .builder Builder.empty],
    mkStuqCase "quiet-range/negative-bits1" 1 #[intV (-1), .builder Builder.empty],
    mkStuqCase "quiet-range/overflow-pos-bits8" 8 #[intV 256, .builder Builder.empty],
    mkStuqCase "quiet-range/negative-bits8" 8 #[intV (-1), .builder Builder.empty],
    mkStuqCase "quiet-range/overflow-pos-bits255" 255 #[intV (intPow2 255), .builder Builder.empty],
    mkStuqCase "quiet-range/negative-bits256" 256 #[intV (-1), .builder Builder.empty],
    mkStuqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty] (quietRangeNanProgram 8),

    mkStuqCase "underflow/empty" 8 #[],
    mkStuqCase "underflow/one-item" 8 #[.builder Builder.empty],
    mkStuqCase "type/builder-pop-first" 8 #[intV 1, .null],
    mkStuqCase "type/int-pop-second" 8 #[.null, .builder Builder.empty],

    mkStuqCase "gas/exact-cost-succeeds" stuqGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stuqSetGasExact), .tonEnvOp .setGasLimit, stuqInstr stuqGasProbeBits],
    mkStuqCase "gas/exact-minus-one-out-of-gas" stuqGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stuqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stuqInstr stuqGasProbeBits],

    mkStuqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkStuqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkStuqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 2) 1),
    mkStuqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program,
    mkStuqProgramCase "program/build-1023-then-quiet-success" #[] (build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stuqInstr 1])
  ]
  fuzz := #[
    { seed := 2026020916
      count := 300
      gen := genStuqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STUQ
