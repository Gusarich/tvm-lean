import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STURQ

/-
STURQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean` (`.stIntFixed unsigned=true rev=true quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STURQ` as `0xcf08`-family with `unsigned=1`, `rev=1`, `quiet=1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf08` fixed-width family decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, args with `unsigned=1`, `rev=1`, `quiet=1`).

Branch map used for this suite:
- Lean STURQ path: 10 branch sites / 16 terminal outcomes
  (`checkUnderflow 2`; rev pop order; capacity guard; unsigned fit;
   quiet failure re-push with `-1` / `1`; success append with trailing `0`).
- C++ STURQ path: 8 branch sites / 14 aligned outcomes.

Key risk areas:
- reversed pop order controls quiet re-push order (`[builder, x, code]`);
- quiet mode maps capacity failure to `-1` and range failure to `1`;
- negative and NaN inputs are value-range failures (`code 1`, not hard throws);
- `cellOv`-class failures must be handled before range in quiet mode.
-/

private def sturqId : InstrId := { name := "STURQ" }

private def sturqInstr (bits : Nat) : Instr :=
  .stIntFixed true true true bits

private def sturInstr (bits : Nat) : Instr :=
  .stIntFixed true true false bits

private def mkSturqCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[sturqInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sturqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSturqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sturqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSturqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (sturqInstr bits) stack

private def runSturqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed .add (VM.push (intV 417)) stack

private def maxUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 bits - 1

private def overflowUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 bits

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithFixedRev sturInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, sturqInstr bits]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, sturqInstr bits]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 17), sturqInstr 5
  ]

private def sturqGasProbeBits : Nat := 8

private def sturqSetGasExact : Int :=
  computeExactGasBudget (sturqInstr sturqGasProbeBits)

private def sturqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (sturqInstr sturqGasProbeBits)

private def sturqBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickSturqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (sturqBitsBoundaryPool.size - 1)
  (sturqBitsBoundaryPool[idx]!, rng')

private def pickSturqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickSturqBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickSturqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
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

private def genSturqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (bits, rng2) := pickSturqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickSturqInRange bits rng2
    (mkSturqCase s!"fuzz/ok/top-only/bits-{bits}" bits #[.builder Builder.empty, intV x], rng3)
  else if shape = 1 then
    let (x, rng3) := pickSturqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 71 else .cell Cell.empty
    (mkSturqCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, .builder Builder.empty, intV x], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 256 then 255 else bits
    (mkSturqCase s!"fuzz/quiet-range-overflow/bits-{bitsOv}" bitsOv
      #[.builder Builder.empty, intV (overflowUnsignedBits bitsOv)], rng2)
  else if shape = 3 then
    (mkSturqCase s!"fuzz/quiet-range-negative/bits-{bits}" bits #[.builder Builder.empty, intV (-1)], rng2)
  else if shape = 4 then
    (mkSturqCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkSturqCase s!"fuzz/underflow/one-item/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 6 then
    (mkSturqCase s!"fuzz/type/x-not-int/bits-{bits}" bits #[.builder Builder.empty, .null], rng2)
  else if shape = 7 then
    (mkSturqCase s!"fuzz/type/builder-not-builder/bits-{bits}" bits #[.null, intV 1], rng2)
  else if shape = 8 then
    (mkSturqProgramCase s!"fuzz/quiet-range-nan-via-program/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)
  else
    let (x, rng3) := pickSturqInRange 1 rng2
    (mkSturqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-1/x-{x}" #[]
      (quietCellovProgram (.num x) 1), rng3)

def suite : InstrSuite where
  id := sturqId
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
            (runSturqDirect bits #[.builder Builder.empty, intV x])
            #[.builder expected, intV 0]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (natToBits 17 5)
        expectOkStack "ok/append-existing-bits"
          (runSturqDirect 5 #[.builder prefBuilder, intV 17])
          #[.builder appended, intV 0]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runSturqDirect 4 #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/overflow-pos-bits1"
          (runSturqDirect 1 #[.builder Builder.empty, intV 2])
          #[.builder Builder.empty, intV 2, intV 1]
        expectOkStack "quiet-range/negative-bits1"
          (runSturqDirect 1 #[.builder Builder.empty, intV (-1)])
          #[.builder Builder.empty, intV (-1), intV 1]
        expectOkStack "quiet-range/overflow-pos-bits8"
          (runSturqDirect 8 #[.builder Builder.empty, intV 256])
          #[.builder Builder.empty, intV 256, intV 1]
        expectOkStack "quiet-range/negative-bits8"
          (runSturqDirect 8 #[.builder Builder.empty, intV (-1)])
          #[.builder Builder.empty, intV (-1), intV 1]
        expectOkStack "quiet-range/overflow-pos-bits256"
          (runSturqDirect 256 #[.builder Builder.empty, intV overUInt256])
          #[.builder Builder.empty, intV overUInt256, intV 1]
        expectOkStack "quiet-range/negative-bits256"
          (runSturqDirect 256 #[.builder Builder.empty, intV (-1)])
          #[.builder Builder.empty, intV (-1), intV 1]
        expectOkStack "quiet-range/nan"
          (runSturqDirect 8 #[.builder Builder.empty, .int .nan])
          #[.builder Builder.empty, .int .nan, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runSturqDirect 1 #[.builder fullBuilder1023, intV 0])
          #[.builder fullBuilder1023, intV 0, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runSturqDirect 1 #[.builder fullBuilder1023, .int .nan])
          #[.builder fullBuilder1023, .int .nan, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runSturqDirect 1 #[.builder fullBuilder1023, intV 2])
          #[.builder fullBuilder1023, intV 2, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runSturqDirect 8 #[]) .stkUnd
        expectErr "underflow/one-item" (runSturqDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runSturqDirect 8 #[.null]) .stkUnd

        expectErr "type/x-not-int-after-pop"
          (runSturqDirect 8 #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/builder-not-builder"
          (runSturqDirect 8 #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-x-first"
          (runSturqDirect 8 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[sturqInstr 1, sturqInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sturq-1" s0 (sturqInstr 1) 24
        let s2 ← expectDecodeStep "decode/sturq-256" s1 (sturqInstr 256) 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        match assembleCp0 [sturqInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"sturq/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "sturq/0: expected assemble rangeChk, got success")
        match assembleCp0 [sturqInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"sturq/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "sturq/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runSturqDispatchFallback #[.null])
          #[.null, intV 417] }
  ]
  oracle := #[
    mkSturqCase "ok/bits1-zero" 1 #[.builder Builder.empty, intV 0],
    mkSturqCase "ok/bits1-one" 1 #[.builder Builder.empty, intV 1],
    mkSturqCase "ok/bits8-zero" 8 #[.builder Builder.empty, intV 0],
    mkSturqCase "ok/bits8-max" 8 #[.builder Builder.empty, intV 255],
    mkSturqCase "ok/bits16-zero" 16 #[.builder Builder.empty, intV 0],
    mkSturqCase "ok/bits16-max" 16 #[.builder Builder.empty, intV 65535],
    mkSturqCase "ok/bits32-zero" 32 #[.builder Builder.empty, intV 0],
    mkSturqCase "ok/bits32-max" 32 #[.builder Builder.empty, intV (intPow2 32 - 1)],
    mkSturqCase "ok/bits256-zero" 256 #[.builder Builder.empty, intV 0],
    mkSturqCase "ok/bits256-max" 256 #[.builder Builder.empty, intV maxUInt256],
    mkSturqCase "ok/deep-stack-below-preserved" 4 #[.null, .builder Builder.empty, intV 7],
    mkSturqProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkSturqCase "quiet-range/overflow-pos-bits1" 1 #[.builder Builder.empty, intV 2],
    mkSturqCase "quiet-range/negative-bits1" 1 #[.builder Builder.empty, intV (-1)],
    mkSturqCase "quiet-range/overflow-pos-bits8" 8 #[.builder Builder.empty, intV 256],
    mkSturqCase "quiet-range/negative-bits8" 8 #[.builder Builder.empty, intV (-1)],
    mkSturqCase "quiet-range/overflow-pos-bits255" 255 #[.builder Builder.empty, intV (intPow2 255)],
    mkSturqCase "quiet-range/negative-bits256" 256 #[.builder Builder.empty, intV (-1)],
    mkSturqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty] (quietRangeNanProgram 8),

    mkSturqCase "underflow/empty" 8 #[],
    mkSturqCase "underflow/one-item" 8 #[.builder Builder.empty],
    mkSturqCase "type/x-not-int" 8 #[.builder Builder.empty, .null],
    mkSturqCase "type/builder-not-builder" 8 #[.null, intV 1],

    mkSturqCase "gas/exact-cost-succeeds" sturqGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num sturqSetGasExact), .tonEnvOp .setGasLimit, sturqInstr sturqGasProbeBits],
    mkSturqCase "gas/exact-minus-one-out-of-gas" sturqGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num sturqSetGasExactMinusOne), .tonEnvOp .setGasLimit, sturqInstr sturqGasProbeBits],

    mkSturqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkSturqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkSturqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 2) 1),
    mkSturqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program,
    mkSturqProgramCase "program/build-1023-then-quiet-success" #[] (build1023Program ++ #[.pushInt (.num 0), sturqInstr 1])
  ]
  fuzz := #[
    { seed := 2026020914
      count := 500
      gen := genSturqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STURQ
