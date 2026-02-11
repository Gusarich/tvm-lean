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
- exact-capacity boundaries (`1023` bits, `4` refs) must succeed;
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

private def stbBitsSmallPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15]

private def stbBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 7, 8, 15, 31, 63, 127, 255, 256]

private def stbOverflowBitsPool : Array Nat :=
  #[1, 2, 7, 8, 15]

private def stbRefsSuccessPool : Array (Nat × Nat) :=
  #[(0, 0), (1, 0), (0, 1), (2, 1), (1, 2), (2, 2), (3, 1), (4, 0)]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickStbRefPair (rng : StdGen) : (Nat × Nat) × StdGen :=
  let (idx, rng') := randNat rng 0 (stbRefsSuccessPool.size - 1)
  (stbRefsSuccessPool[idx]!, rng')

private def genStbFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    (mkStbCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    (mkStbCase "fuzz/ok/deep-stack-preserve-below"
      #[.null, .builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 2 then
    let (cb2Bits, rng2) := pickNatFromPool stbBitsSmallPool rng1
    let (bBits, rng3) := pickNatFromPool stbBitsSmallPool rng2
    (mkStbProgramCase s!"fuzz/ok/program/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbProgramBits cb2Bits bBits), rng3)
  else if shape = 3 then
    let (cb2Bits, rng2) := pickNatFromPool stbBitsBoundaryPool rng1
    let (bBits, rng3) := pickNatFromPool stbBitsBoundaryPool rng2
    (mkStbProgramCase s!"fuzz/ok/program-boundary/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbProgramBits cb2Bits bBits), rng3)
  else if shape = 4 then
    let (cb2Bits, rng2) := pickNatFromPool stbBitsSmallPool rng1
    let (bBits, rng3) := pickNatFromPool stbBitsSmallPool rng2
    (mkStbProgramCase s!"fuzz/ok/program-noise/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbProgramBitsWithNoise cb2Bits bBits), rng3)
  else if shape = 5 then
    let ((cb2Refs, bRefs), rng2) := pickStbRefPair rng1
    (mkStbProgramCase s!"fuzz/ok/refs/cb2-{cb2Refs}-b-{bRefs}" #[]
      (mkStbProgramRefs cb2Refs bRefs), rng2)
  else if shape = 6 then
    (mkStbCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkStbCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 8 then
    (mkStbCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 9 then
    (mkStbCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 10 then
    (mkStbCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else if shape = 11 then
    let (ovBits, rng2) := pickNatFromPool stbOverflowBitsPool rng1
    (mkStbProgramCase s!"fuzz/cellov/bits-overflow/cb2-{ovBits}" #[]
      (mkStbProgramCb2ThenFull ovBits), rng2)
  else if shape = 12 then
    (mkStbProgramCase "fuzz/cellov/refs-overflow" #[] stbRefsCellOvProgram, rng1)
  else if shape = 13 then
    (mkStbCase "fuzz/gas/exact-cost-succeeds"
      #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbSetGasExact), .tonEnvOp .setGasLimit, stbInstr], rng1)
  else
    (mkStbCase "fuzz/gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbInstr], rng1)

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

        let cb2Bit1 := Builder.empty.storeBits (natToBits 1 1)
        let bBits1022 := Builder.empty.storeBits (Array.replicate 1022 false)
        let expected1023 : Builder :=
          { bits := bBits1022.bits ++ cb2Bit1.bits
            refs := bBits1022.refs ++ cb2Bit1.refs }
        expectOkStack "ok/capacity-boundary-bits-1022-plus-1"
          (runStbDirect #[.builder cb2Bit1, .builder bBits1022])
          #[.builder expected1023]

        let cb2Ref1 : Builder := { Builder.empty with refs := #[Cell.empty] }
        let bRef3 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty] }
        let expectedRef4 : Builder :=
          { bits := bRef3.bits ++ cb2Ref1.bits
            refs := bRef3.refs ++ cb2Ref1.refs }
        expectOkStack "ok/capacity-boundary-refs-3-plus-1"
          (runStbDirect #[.builder cb2Ref1, .builder bRef3])
          #[.builder expectedRef4]

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
        let program : Array Instr := #[stbInstr, .stb true false, .stb false true, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stb" s0 stbInstr 16
        let s2 ← expectDecodeStep "decode/stbr" s1 (.stb true false) 16
        let s3 ← expectDecodeStep "decode/stbq" s2 (.stb false true) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
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
    mkStbProgramCase "ok/program/cb2-15-b-15" #[] (mkStbProgramBits 15 15),
    mkStbProgramCase "ok/program/cb2-255-b-1" #[] (mkStbProgramBits 255 1),
    mkStbProgramCase "ok/program/full-builder-plus-empty-cb2" #[] (mkStbProgramCb2ThenFull 0),
    mkStbProgramCase "ok/program/refs-cb2-3-b-1" #[] (mkStbProgramRefs 3 1),
    mkStbProgramCase "ok/program/refs-cb2-4-b-0" #[] (mkStbProgramRefs 4 0),
    mkStbProgramCase "ok/program/refs-cb2-2-b-2" #[] (mkStbProgramRefs 2 2)
  ]
  fuzz := #[
    { seed := 2026020936
      count := 320
      gen := genStbFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STB
