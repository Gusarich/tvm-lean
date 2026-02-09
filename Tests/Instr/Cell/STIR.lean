import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STIR

/-
STIR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean` (`.stIntFixed unsigned=false rev=true quiet=false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STIR` as `0xcf08`-family with `rev=1`, `quiet=0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf08` fixed-width family decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, args with `rev=1`).

Branch map used for this suite:
- Lean STIR path: 10 branch sites / 13 terminal outcomes
  (`checkUnderflow 2`; rev pop order; capacity guard; signed fit;
   non-quiet throw outcomes; success append).
- C++ STIR path: 8 branch sites / 11 aligned outcomes.

Key risk areas:
- reversed pop order (`x` first, then `builder`) controls type ordering;
- signed width boundary off-by-one at `[-2^(bits-1), 2^(bits-1)-1]`;
- `cellOv` must be raised before range checks when builder is full.
-/

private def stirId : InstrId := { name := "STIR" }

private def stirInstr (bits : Nat) : Instr :=
  .stIntFixed false true false bits

private def mkStirCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stirInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stirId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStirProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stirId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStirDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (stirInstr bits) stack

private def runStirDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed .add (VM.push (intV 414)) stack

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

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), stirInstr 1]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, stirInstr 1]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1), stirInstr 1]

private def stirGasProbeBits : Nat := 8

private def stirSetGasExact : Int :=
  computeExactGasBudget (stirInstr stirGasProbeBits)

private def stirSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stirInstr stirGasProbeBits)

private def stirBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStirBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stirBitsBoundaryPool.size - 1)
  (stirBitsBoundaryPool[idx]!, rng')

private def pickStirBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStirBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickStirInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
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

private def genStirFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (bits, rng2) := pickStirBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStirInRange bits rng2
    (mkStirCase s!"fuzz/ok/top-only/bits-{bits}" bits #[.builder Builder.empty, intV x], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStirInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 59 else .cell Cell.empty
    (mkStirCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, .builder Builder.empty, intV x], rng4)
  else if shape = 2 then
    (mkStirCase s!"fuzz/range/overflow-pos/bits-{bits}" bits #[.builder Builder.empty, intV (overflowPosSignedBits bits)], rng2)
  else if shape = 3 then
    (mkStirCase s!"fuzz/range/overflow-neg/bits-{bits}" bits #[.builder Builder.empty, intV (overflowNegSignedBits bits)], rng2)
  else if shape = 4 then
    (mkStirCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStirCase s!"fuzz/underflow/one-item/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 6 then
    (mkStirCase s!"fuzz/type/x-not-int/bits-{bits}" bits #[.builder Builder.empty, .null], rng2)
  else if shape = 7 then
    (mkStirCase s!"fuzz/type/builder-not-builder/bits-{bits}" bits #[.null, intV 1], rng2)
  else if shape = 8 then
    (mkStirProgramCase s!"fuzz/range/nan-via-program/bits-{bits}" #[.builder Builder.empty]
      #[.pushInt .nan, stirInstr bits], rng2)
  else
    let (x, rng3) := pickStirInRange 1 rng2
    (mkStirProgramCase s!"fuzz/cellov-before-range/bits-1/x-{x}" #[]
      (build1023Program ++ #[.pushInt (.num x), stirInstr 1]), rng3)

def suite : InstrSuite where
  id := stirId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
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
            (runStirDirect bits #[.builder Builder.empty, intV x])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appendedBits ←
          match intToBitsTwos (-3) 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let appended := prefBuilder.storeBits appendedBits
        expectOkStack "ok/append-existing-bits"
          (runStirDirect 4 #[.builder prefBuilder, intV (-3)])
          #[.builder appended]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStirDirect 4 #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/overflow-pos-bits1"
          (runStirDirect 1 #[.builder Builder.empty, intV 1]) .rangeChk
        expectErr "range/overflow-neg-bits1"
          (runStirDirect 1 #[.builder Builder.empty, intV (-2)]) .rangeChk
        expectErr "range/overflow-pos-bits8"
          (runStirDirect 8 #[.builder Builder.empty, intV 128]) .rangeChk
        expectErr "range/overflow-neg-bits8"
          (runStirDirect 8 #[.builder Builder.empty, intV (-129)]) .rangeChk
        expectErr "range/overflow-pos-bits256"
          (runStirDirect 256 #[.builder Builder.empty, intV (intPow2 255)]) .rangeChk
        expectErr "range/overflow-neg-bits256"
          (runStirDirect 256 #[.builder Builder.empty, intV (-(intPow2 255) - 1)]) .rangeChk
        expectErr "range/nan"
          (runStirDirect 8 #[.builder Builder.empty, .int .nan]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStirDirect 8 #[]) .stkUnd
        expectErr "underflow/one-item" (runStirDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStirDirect 8 #[.null]) .stkUnd

        expectErr "type/x-not-int-after-pop"
          (runStirDirect 8 #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/builder-not-builder"
          (runStirDirect 8 #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-x-first"
          (runStirDirect 8 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStirDirect 1 #[.builder fullBuilder1023, intV 0]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStirDirect 1 #[.builder fullBuilder1023, .int .nan]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStirDirect 1 #[.builder fullBuilder1023, intV 1]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stirInstr 1, stirInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stir-1" s0 (stirInstr 1) 24
        let s2 ← expectDecodeStep "decode/stir-256" s1 (stirInstr 256) 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        match assembleCp0 [stirInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stir/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stir/0: expected assemble rangeChk, got success")
        match assembleCp0 [stirInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stir/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stir/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStirDispatchFallback #[.null])
          #[.null, intV 414] }
  ]
  oracle := #[
    mkStirCase "ok/bits1-min" 1 #[.builder Builder.empty, intV (-1)],
    mkStirCase "ok/bits1-max" 1 #[.builder Builder.empty, intV 0],
    mkStirCase "ok/bits8-min" 8 #[.builder Builder.empty, intV (-128)],
    mkStirCase "ok/bits8-max" 8 #[.builder Builder.empty, intV 127],
    mkStirCase "ok/bits16-min" 16 #[.builder Builder.empty, intV (-32768)],
    mkStirCase "ok/bits16-max" 16 #[.builder Builder.empty, intV 32767],
    mkStirCase "ok/bits256-min" 256 #[.builder Builder.empty, intV (-(intPow2 255))],
    mkStirCase "ok/bits256-max" 256 #[.builder Builder.empty, intV (intPow2 255 - 1)],
    mkStirCase "ok/deep-stack-below-preserved" 4 #[.null, .builder Builder.empty, intV 7],

    mkStirCase "range/overflow-pos-bits1" 1 #[.builder Builder.empty, intV 1],
    mkStirCase "range/overflow-neg-bits1" 1 #[.builder Builder.empty, intV (-2)],
    mkStirCase "range/overflow-pos-bits8" 8 #[.builder Builder.empty, intV 128],
    mkStirCase "range/overflow-neg-bits8" 8 #[.builder Builder.empty, intV (-129)],
    mkStirCase "range/overflow-pos-bits256" 256 #[.builder Builder.empty, intV (intPow2 255)],
    mkStirCase "range/overflow-neg-bits256" 256 #[.builder Builder.empty, intV (-(intPow2 255) - 1)],
    mkStirProgramCase "range/nan-via-program" #[.builder Builder.empty] #[.pushInt .nan, stirInstr 8],

    mkStirCase "underflow/empty" 8 #[],
    mkStirCase "underflow/one-item" 8 #[.builder Builder.empty],
    mkStirCase "type/x-not-int" 8 #[.builder Builder.empty, .null],
    mkStirCase "type/builder-not-builder" 8 #[.null, intV 1],

    mkStirCase "gas/exact-cost-succeeds" stirGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stirSetGasExact), .tonEnvOp .setGasLimit, stirInstr stirGasProbeBits],
    mkStirCase "gas/exact-minus-one-out-of-gas" stirGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stirSetGasExactMinusOne), .tonEnvOp .setGasLimit, stirInstr stirGasProbeBits],

    mkStirProgramCase "program/build-1023-success" #[] build1023Program,
    mkStirProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStirProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStirProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020911
      count := 300
      gen := genStirFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STIR
