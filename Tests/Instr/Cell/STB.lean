import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STB

/-
STB branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stb.lean` (`.stb false false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STB` encode: `0xcf13`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf13` decode to `.stb false false`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder`, non-quiet).

Branch map used for this suite:
- Lean STB path: 7 branch sites / 10 terminal outcomes
  (`checkUnderflow 2`; mode guard; top builder pop/type; second builder pop/type;
   capacity check on bits+refs; success append).
- C++ STB path: 6 branch sites / 9 aligned outcomes
  (`check_underflow(2)`; `builder` then `cb2` pops; `can_extend_by`; success or `cell_ov`).

Key risk areas:
- non-rev stack order is `... cb2 builder` (builder on top);
- result builder is `builder ++ cb2` (not the other order);
- capacity checks account for both bits and refs;
- in non-quiet mode overflow throws `cellOv` (no status code push).
-/

private def stbId : InstrId := { name := "STB" }

private def stbInstr : Instr := .stb false false

private def mkStbCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStb stbInstr stack

private def runStbDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStb .add (VM.push (intV 435)) stack

private def stbSetGasExact : Int :=
  computeExactGasBudget stbInstr

private def stbSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stbInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkStbProgramBits
    (cb2Bits : Nat) (bBits : Nat)
    (cb2X : IntVal := .num 0) (bX : IntVal := .num 0) : Array Instr :=
  #[.newc]
    ++ appendBitsToTopBuilder cb2Bits cb2X
    ++ #[.newc]
    ++ appendBitsToTopBuilder bBits bX
    ++ #[stbInstr]

private def mkStbProgramBitsWithNoise
    (cb2Bits : Nat) (bBits : Nat)
    (cb2X : IntVal := .num 0) (bX : IntVal := .num 0) : Array Instr :=
  #[.pushNull]
    ++ mkStbProgramBits cb2Bits bBits cb2X bX

private def appendOneRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder refs

private def mkStbProgramRefs (cb2Refs : Nat) (bRefs : Nat) : Array Instr :=
  mkBuilderWithRefsProgram cb2Refs ++ mkBuilderWithRefsProgram bRefs ++ #[stbInstr]

private def mkCb2Program (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder cb2Bits cb2X

private def mkStbProgramCb2ThenFull
    (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  mkCb2Program cb2Bits cb2X ++ build1023WithFixed .stu ++ #[stbInstr]

private def stbBitsCellOvProgram : Array Instr :=
  mkStbProgramCb2ThenFull 1

private def stbRefsCellOvProgram : Array Instr :=
  mkStbProgramRefs 1 4

private def stbAppendProgram : Array Instr :=
  mkStbProgramBits 5 3 (.num 17) (.num 5)

private def stbAppendProgramWithNoise : Array Instr :=
  mkStbProgramBitsWithNoise 4 2 (.num 9) (.num 3)

private def pickStbBitsSmall (rng : StdGen) : Nat × StdGen :=
  let (pick, rng') := randNat rng 0 6
  let n : Nat :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 2
    else if pick = 3 then 3
    else if pick = 4 then 7
    else if pick = 5 then 8
    else 15
  (n, rng')

private def genStbFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  if shape = 0 then
    (mkStbCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (cb2Bits, rng2) := pickStbBitsSmall rng1
    let (bBits, rng3) := pickStbBitsSmall rng2
    (mkStbProgramCase s!"fuzz/ok/program/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbProgramBits cb2Bits bBits), rng3)
  else if shape = 2 then
    let (cb2Bits, rng2) := pickStbBitsSmall rng1
    let (bBits, rng3) := pickStbBitsSmall rng2
    (mkStbProgramCase s!"fuzz/ok/program-noise/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbProgramBitsWithNoise cb2Bits bBits), rng3)
  else if shape = 3 then
    (mkStbCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 4 then
    (mkStbCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkStbCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 6 then
    (mkStbCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStbProgramCase "fuzz/cellov/bits-overflow-program" #[] stbBitsCellOvProgram, rng1)
  else if shape = 8 then
    (mkStbProgramCase "fuzz/cellov/refs-overflow-program" #[] stbRefsCellOvProgram, rng1)
  else if shape = 9 then
    (mkStbCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else
    let (cb2Bits, rng2) := pickStbBitsSmall rng1
    (mkStbProgramCase s!"fuzz/program/cellov-b-1023-cb2-{cb2Bits}" #[]
      (mkStbProgramCb2ThenFull cb2Bits), rng2)

def suite : InstrSuite where
  id := stbId
  unit := #[
    { name := "unit/direct/success-order-and-append"
      run := do
        expectOkStack "ok/empty-builders"
          (runStbDirect #[.builder Builder.empty, .builder Builder.empty])
          #[.builder Builder.empty]

        let cb2BitsBuilder := Builder.empty.storeBits (natToBits 5 3)
        let bBitsBuilder := Builder.empty.storeBits (natToBits 2 2)
        let expectedBits : Builder :=
          { bits := bBitsBuilder.bits ++ cb2BitsBuilder.bits
            refs := bBitsBuilder.refs ++ cb2BitsBuilder.refs }
        expectOkStack "ok/non-rev-order-builder-top-receives-cb2"
          (runStbDirect #[.builder cb2BitsBuilder, .builder bBitsBuilder])
          #[.builder expectedBits]

        let cb2RefsBuilder : Builder := { cb2BitsBuilder with refs := #[Cell.empty] }
        let bRefsBuilder : Builder := { bBitsBuilder with refs := #[Cell.empty, Cell.empty] }
        let expectedRefs : Builder :=
          { bits := bRefsBuilder.bits ++ cb2RefsBuilder.bits
            refs := bRefsBuilder.refs ++ cb2RefsBuilder.refs }
        expectOkStack "ok/append-refs-and-bits"
          (runStbDirect #[.builder cb2RefsBuilder, .builder bRefsBuilder])
          #[.builder expectedRefs]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStbDirect #[.null, .builder Builder.empty, .builder Builder.empty])
          #[.null, .builder Builder.empty] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStbDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStbDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runStbDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-bits-and-refs"
      run := do
        let cb2Bit1 := Builder.empty.storeBits (natToBits 1 1)
        expectErr "cellov/bits-overflow"
          (runStbDirect #[.builder cb2Bit1, .builder fullBuilder1023]) .cellOv

        let cb2Ref1 : Builder := { Builder.empty with refs := #[Cell.empty] }
        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectErr "cellov/refs-overflow"
          (runStbDirect #[.builder cb2Ref1, .builder bRef4]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stbInstr, .stb true false, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stb" s0 stbInstr 16
        let s2 ← expectDecodeStep "decode/stbr" s1 (.stb true false) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stb-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbDispatchFallback #[.null])
          #[.null, intV 435] }
  ]
  oracle := #[
    mkStbCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbCase "ok/deep-stack-preserve-below" #[.null, .builder Builder.empty, .builder Builder.empty],
    mkStbProgramCase "ok/non-empty-append-via-program" #[] stbAppendProgram,
    mkStbProgramCase "ok/non-empty-append-with-noise-via-program" #[] stbAppendProgramWithNoise,

    mkStbCase "underflow/empty" #[],
    mkStbCase "underflow/one-item" #[.builder Builder.empty],
    mkStbCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbCase "type/both-non-builder" #[.null, intV 1],

    mkStbCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbSetGasExact), .tonEnvOp .setGasLimit, stbInstr],
    mkStbCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbInstr],

    mkStbProgramCase "cellov/bits-overflow-via-program" #[] stbBitsCellOvProgram,
    mkStbProgramCase "cellov/bits-overflow-via-program-alt" #[] (mkStbProgramCb2ThenFull 2),
    mkStbProgramCase "cellov/bits-overflow-via-program-alt2" #[] (mkStbProgramCb2ThenFull 7),
    mkStbProgramCase "cellov/refs-overflow-via-program" #[] stbRefsCellOvProgram,
    mkStbProgramCase "ok/program/cb2-0-b-0" #[] (mkStbProgramBits 0 0),
    mkStbProgramCase "ok/program/cb2-1-b-0" #[] (mkStbProgramBits 1 0),
    mkStbProgramCase "ok/program/cb2-0-b-1" #[] (mkStbProgramBits 0 1),
    mkStbProgramCase "ok/program/cb2-2-b-3" #[] (mkStbProgramBits 2 3),
    mkStbProgramCase "ok/program/cb2-3-b-2" #[] (mkStbProgramBits 3 2),
    mkStbProgramCase "ok/program/cb2-7-b-8" #[] (mkStbProgramBits 7 8),
    mkStbProgramCase "ok/program/cb2-8-b-7" #[] (mkStbProgramBits 8 7),
    mkStbProgramCase "ok/program/cb2-15-b-15" #[] (mkStbProgramBits 15 15)
  ]
  fuzz := #[
    { seed := 2026020936
      count := 320
      gen := genStbFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STB
