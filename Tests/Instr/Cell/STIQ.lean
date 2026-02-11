import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STIQ

/-
STIQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean` (`.stIntFixed unsigned=false rev=false quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STIQ` as `0xcf08`-family with `quiet=1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf08` fixed-width family decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, args with `quiet=1`).

Branch map used for this suite:
- Lean STIQ path: 10 branch sites / 16 terminal outcomes
  (`checkUnderflow 2`; non-rev pop order; capacity guard; signed fit;
   quiet failure re-push with `-1` / `1`; success append with trailing `0`).
- C++ STIQ path: 8 branch sites / 14 aligned outcomes.

Key risk areas:
- non-reversed mode uses stack convention `[x, builder]`;
- quiet failures must re-push as `[x, builder, code]` in non-rev mode;
- signed boundary off-by-one at `[-2^(bits-1), 2^(bits-1)-1]`;
- capacity failure must map to `-1`, and range failure to `1`.
-/

private def stiqId : InstrId := { name := "STIQ" }

private def stiqInstr (bits : Nat) : Instr :=
  .stIntFixed false false true bits

private def stiInstr (bits : Nat) : Instr :=
  .stIntFixed false false false bits

private def mkStiqCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stiqInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stiqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStiqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stiqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStiqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (stiqInstr bits) stack

private def runStiqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed .add (VM.push (intV 418)) stack

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def overflowPosSignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 (bits - 1)

private def overflowNegSignedBits (bits : Nat) : Int :=
  if bits = 0 then -1 else -(intPow2 (bits - 1)) - 1

private def build1023Program : Array Instr :=
  build1023WithFixed stiInstr

private def quietCellovProgram (x : IntVal) (bits : Nat) : Array Instr :=
  build1023Program ++ #[.pushInt x, .xchg0 1, stiqInstr bits]

private def quietRangeNanProgram (bits : Nat) : Array Instr :=
  #[.pushInt .nan, .xchg0 1, stiqInstr bits]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num (-3)), .xchg0 1, stiqInstr 4
  ]

private def stiqGasProbeBits : Nat := 8

private def stiqSetGasExact : Int :=
  computeExactGasBudget (stiqInstr stiqGasProbeBits)

private def stiqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stiqInstr stiqGasProbeBits)

private def stiqBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStiqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stiqBitsBoundaryPool.size - 1)
  (stiqBitsBoundaryPool[idx]!, rng')

private def pickStiqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStiqBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickStiqInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
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

private def genStiqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (bits, rng2) := pickStiqBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStiqInRange bits rng2
    (mkStiqCase s!"fuzz/ok/top-only/bits-{bits}" bits #[intV x, .builder Builder.empty], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStiqInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 73 else .cell Cell.empty
    (mkStiqCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, intV x, .builder Builder.empty], rng4)
  else if shape = 2 then
    (mkStiqCase s!"fuzz/quiet-range-overflow-pos/bits-{bits}" bits
      #[intV (overflowPosSignedBits bits), .builder Builder.empty], rng2)
  else if shape = 3 then
    (mkStiqCase s!"fuzz/quiet-range-overflow-neg/bits-{bits}" bits
      #[intV (overflowNegSignedBits bits), .builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStiqCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStiqCase s!"fuzz/underflow/one-item/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 6 then
    (mkStiqCase s!"fuzz/type/top-not-builder/bits-{bits}" bits #[intV 1, .null], rng2)
  else if shape = 7 then
    (mkStiqCase s!"fuzz/type/second-not-int/bits-{bits}" bits #[.null, .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStiqProgramCase s!"fuzz/quiet-range-nan-via-program/bits-{bits}" #[.builder Builder.empty]
      (quietRangeNanProgram bits), rng2)
  else
    let (x, rng3) := pickStiqInRange 1 rng2
    (mkStiqProgramCase s!"fuzz/quiet-cellov/code-minus1/bits-1/x-{x}" #[]
      (quietCellovProgram (.num x) 1), rng3)

def suite : InstrSuite where
  id := stiqId
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
            (runStiqDirect bits #[intV x, .builder Builder.empty])
            #[.builder expected, intV 0]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appendedBits ←
          match intToBitsTwos (-3) 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let appended := prefBuilder.storeBits appendedBits
        expectOkStack "ok/append-existing-bits"
          (runStiqDirect 4 #[intV (-3), .builder prefBuilder])
          #[.builder appended, intV 0]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStiqDirect 4 #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-range-returns-code1"
      run := do
        expectOkStack "quiet-range/overflow-pos-bits1"
          (runStiqDirect 1 #[intV 1, .builder Builder.empty])
          #[intV 1, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits1"
          (runStiqDirect 1 #[intV (-2), .builder Builder.empty])
          #[intV (-2), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-pos-bits8"
          (runStiqDirect 8 #[intV 128, .builder Builder.empty])
          #[intV 128, .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits8"
          (runStiqDirect 8 #[intV (-129), .builder Builder.empty])
          #[intV (-129), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-pos-bits256"
          (runStiqDirect 256 #[intV (intPow2 255), .builder Builder.empty])
          #[intV (intPow2 255), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/overflow-neg-bits256"
          (runStiqDirect 256 #[intV (-(intPow2 255) - 1), .builder Builder.empty])
          #[intV (-(intPow2 255) - 1), .builder Builder.empty, intV 1]
        expectOkStack "quiet-range/nan"
          (runStiqDirect 8 #[.int .nan, .builder Builder.empty])
          #[.int .nan, .builder Builder.empty, intV 1] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        expectOkStack "quiet-cellov/full-builder"
          (runStiqDirect 1 #[intV 0, .builder fullBuilder1023])
          #[intV 0, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-nan-range"
          (runStiqDirect 1 #[.int .nan, .builder fullBuilder1023])
          #[.int .nan, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet-cellov/before-overflow-range"
          (runStiqDirect 1 #[intV 1, .builder fullBuilder1023])
          #[intV 1, .builder fullBuilder1023, intV (-1)] }
    ,
    { name := "unit/direct/hard-failures-before-quiet-path"
      run := do
        expectErr "underflow/empty" (runStiqDirect 8 #[]) .stkUnd
        expectErr "underflow/one-item" (runStiqDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStiqDirect 8 #[.null]) .stkUnd

        expectErr "type/builder-pop-first"
          (runStiqDirect 8 #[intV 1, .null]) .typeChk
        expectErr "type/int-pop-second"
          (runStiqDirect 8 #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStiqDirect 8 #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stiqInstr 1, stiqInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stiq-1" s0 (stiqInstr 1) 24
        let s2 ← expectDecodeStep "decode/stiq-256" s1 (stiqInstr 256) 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        match assembleCp0 [stiqInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stiq/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stiq/0: expected assemble rangeChk, got success")
        match assembleCp0 [stiqInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stiq/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stiq/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStiqDispatchFallback #[.null])
          #[.null, intV 418] }
  ]
  oracle := #[
    mkStiqCase "ok/bits1-min" 1 #[intV (-1), .builder Builder.empty],
    mkStiqCase "ok/bits1-max" 1 #[intV 0, .builder Builder.empty],
    mkStiqCase "ok/bits8-min" 8 #[intV (-128), .builder Builder.empty],
    mkStiqCase "ok/bits8-max" 8 #[intV 127, .builder Builder.empty],
    mkStiqCase "ok/bits16-min" 16 #[intV (-32768), .builder Builder.empty],
    mkStiqCase "ok/bits16-max" 16 #[intV 32767, .builder Builder.empty],
    mkStiqCase "ok/bits32-min" 32 #[intV (-(intPow2 31)), .builder Builder.empty],
    mkStiqCase "ok/bits32-max" 32 #[intV (intPow2 31 - 1), .builder Builder.empty],
    mkStiqCase "ok/bits256-min" 256 #[intV (-(intPow2 255)), .builder Builder.empty],
    mkStiqCase "ok/bits256-max" 256 #[intV (intPow2 255 - 1), .builder Builder.empty],
    mkStiqCase "ok/deep-stack-below-preserved" 4 #[.null, intV 7, .builder Builder.empty],
    mkStiqProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkStiqCase "quiet-range/overflow-pos-bits1" 1 #[intV 1, .builder Builder.empty],
    mkStiqCase "quiet-range/overflow-neg-bits1" 1 #[intV (-2), .builder Builder.empty],
    mkStiqCase "quiet-range/overflow-pos-bits8" 8 #[intV 128, .builder Builder.empty],
    mkStiqCase "quiet-range/overflow-neg-bits8" 8 #[intV (-129), .builder Builder.empty],
    mkStiqCase "quiet-range/overflow-pos-bits256" 256 #[intV (intPow2 255), .builder Builder.empty],
    mkStiqCase "quiet-range/overflow-neg-bits256" 256 #[intV (-(intPow2 255) - 1), .builder Builder.empty],
    mkStiqProgramCase "quiet-range/nan-via-program" #[.builder Builder.empty] (quietRangeNanProgram 8),

    mkStiqCase "underflow/empty" 8 #[],
    mkStiqCase "underflow/one-item" 8 #[.builder Builder.empty],
    mkStiqCase "type/builder-pop-first" 8 #[intV 1, .null],
    mkStiqCase "type/int-pop-second" 8 #[.null, .builder Builder.empty],

    mkStiqCase "gas/exact-cost-succeeds" stiqGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stiqSetGasExact), .tonEnvOp .setGasLimit, stiqInstr stiqGasProbeBits],
    mkStiqCase "gas/exact-minus-one-out-of-gas" stiqGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stiqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stiqInstr stiqGasProbeBits],

    mkStiqProgramCase "quiet-cellov/code-minus1" #[] (quietCellovProgram (.num 0) 1),
    mkStiqProgramCase "quiet-cellov-before-nan-range" #[] (quietCellovProgram .nan 1),
    mkStiqProgramCase "quiet-cellov-before-overflow-range" #[] (quietCellovProgram (.num 1) 1),
    mkStiqProgramCase "program/build-1023-success-nonquiet-prefix" #[] build1023Program,
    mkStiqProgramCase "program/build-1023-then-quiet-success" #[] (build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stiqInstr 1])
  ]
  fuzz := #[
    { seed := 2026020915
      count := 500
      gen := genStiqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STIQ
