import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSLICEQ

/-
STSLICEQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StSlice.lean` (`.stSlice false true`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf1a` decode to `.stSlice false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.stSlice false true` encode as `0xcf1a`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_slice(..., quiet=true)` and opcode table entry `0xcf1a`).

Branch map used for this suite (non-rev, quiet store-slice):
- dispatch match (`.stSlice` vs fallback `next`);
- `checkUnderflow 2` before any pop/type path;
- non-rev pop order is top `builder`, then second `slice`;
- capacity guard `canExtendBy(bitsRemaining, refsRemaining)` on slice remainder;
- quiet success pushes `[builder', 0]`;
- quiet overflow restores `[slice, builder]` and pushes `-1` (no `cellOv` throw).

Key risk areas:
- non-rev stack contract is `... slice builder` (builder on top);
- partial slices must append only remaining bits/refs (`toCellRemaining`);
- quiet overflow must preserve operand order and slice positions;
- underflow/type errors happen before quiet status handling.
-/

private def stsliceqId : InstrId := { name := "STSLICEQ" }

private def stsliceqInstr : Instr := .stSlice false true

private def mkStsliceqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stsliceqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsliceqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStsliceqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsliceqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStsliceqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStSlice stsliceqInstr stack

private def runStsliceqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStSlice .add (VM.push (intV 642)) stack

private def stsliceqSetGasExact : Int :=
  computeExactGasBudget stsliceqInstr

private def stsliceqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stsliceqInstr

private def appendBitsToTopBuilder (bits : Nat) (value : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt value, .xchg0 1, .stu bits]

private def mkBuilderProgram
    (bits refs : Nat)
    (value : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits value ++ appendRefsToTopBuilder refs

private def mkSliceProgram
    (bits refs : Nat)
    (value : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs value ++ #[.endc, .ctos]

private def mkStsliceqProgramBuilderSlice
    (builderBits builderRefs sliceBits sliceRefs : Nat)
    (builderValue : IntVal := .num 0)
    (sliceValue : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram builderBits builderRefs builderValue
    ++ mkSliceProgram sliceBits sliceRefs sliceValue
    ++ #[.xchg0 1, stsliceqInstr]

private def mkStsliceqProgramBuilderSliceWithNoise
    (builderBits builderRefs sliceBits sliceRefs : Nat)
    (builderValue : IntVal := .num 0)
    (sliceValue : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStsliceqProgramBuilderSlice
    builderBits builderRefs sliceBits sliceRefs builderValue sliceValue

private def mkStsliceqProgramFullBuilderSliceBits
    (sliceBits : Nat)
    (sliceValue : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu ++ mkSliceProgram sliceBits 0 sliceValue ++ #[.xchg0 1, stsliceqInstr]

private def mkStsliceqProgramFullBuilderSliceBitsWithNoise
    (sliceBits : Nat)
    (sliceValue : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStsliceqProgramFullBuilderSliceBits sliceBits sliceValue

private def mkStsliceqProgramBuilderRefs4SliceRefs
    (sliceRefs : Nat) : Array Instr :=
  mkBuilderProgram 0 4 ++ mkSliceProgram 0 sliceRefs ++ #[.xchg0 1, stsliceqInstr]

private def mkStsliceqProgramBuilderRefs4SliceRefsWithNoise
    (sliceRefs : Nat) : Array Instr :=
  #[.pushNull] ++ mkStsliceqProgramBuilderRefs4SliceRefs sliceRefs

private def mkStsliceqProgramFullBitsRefs4Slice
    (sliceBits sliceRefs : Nat)
    (sliceValue : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu
    ++ appendRefsToTopBuilder 4
    ++ mkSliceProgram sliceBits sliceRefs sliceValue
    ++ #[.xchg0 1, stsliceqInstr]

private def mkCellFromBitsValue (bits : Nat) (value : Nat) : Cell :=
  if bits = 0 then
    Cell.empty
  else
    (Builder.empty.storeBits (natToBits value bits)).finalize

private def cellBits1 : Cell :=
  mkCellFromBitsValue 1 1

private def cellBits3 : Cell :=
  mkCellFromBitsValue 3 5

private def cellBits8 : Cell :=
  mkCellFromBitsValue 8 173

private def cellBits16 : Cell :=
  mkCellFromBitsValue 16 65535

private def cellWithOneRef : Cell :=
  ({ Builder.empty with refs := #[Cell.empty] }).finalize

private def cellWithTwoRefs : Cell :=
  ({ Builder.empty with refs := #[cellBits1, cellBits3] }).finalize

private def partialSliceSource : Cell :=
  Cell.mkOrdinary (natToBits 45 6) #[cellBits1, cellBits3]

private def partialSlice : Slice :=
  { cell := partialSliceSource, bitPos := 2, refPos := 1 }

private def appendRemainingSliceExpected (builder : Builder) (sliceValue : Slice) : Builder :=
  let remCell := sliceValue.toCellRemaining
  { bits := builder.bits ++ remCell.bits
    refs := builder.refs ++ remCell.refs }

private def stsliceqProgramOkBits0Refs0Slice0Refs0 : Array Instr :=
  mkStsliceqProgramBuilderSlice 0 0 0 0

private def stsliceqProgramOkBits3Refs0Slice1Refs0 : Array Instr :=
  mkStsliceqProgramBuilderSlice 3 0 1 0 (.num 5) (.num 1)

private def stsliceqProgramOkBits0Refs2Slice0Refs1 : Array Instr :=
  mkStsliceqProgramBuilderSlice 0 2 0 1

private def stsliceqProgramOkBits7Refs1Slice8Refs1 : Array Instr :=
  mkStsliceqProgramBuilderSlice 7 1 8 1 (.num 65) (.num 173)

private def stsliceqProgramOkBits15Refs0Slice0Refs3 : Array Instr :=
  mkStsliceqProgramBuilderSlice 15 0 0 3 (.num 21845) (.num 0)

private def stsliceqProgramOkBits0Refs3Slice16Refs1 : Array Instr :=
  mkStsliceqProgramBuilderSlice 0 3 16 1 (.num 0) (.num 65535)

private def stsliceqProgramOkNearBits1023SliceEmpty : Array Instr :=
  mkStsliceqProgramFullBuilderSliceBits 0

private def stsliceqProgramOkNearRefs4SliceEmpty : Array Instr :=
  mkStsliceqProgramBuilderRefs4SliceRefs 0

private def stsliceqProgramOkWithNoise : Array Instr :=
  mkStsliceqProgramBuilderSliceWithNoise 3 2 4 1 (.num 7) (.num 11)

private def stsliceqProgramCellovBits : Array Instr :=
  mkStsliceqProgramFullBuilderSliceBits 1 (.num 1)

private def stsliceqProgramCellovBitsWithNoise : Array Instr :=
  mkStsliceqProgramFullBuilderSliceBitsWithNoise 2 (.num 2)

private def stsliceqProgramCellovRefs : Array Instr :=
  mkStsliceqProgramBuilderRefs4SliceRefs 1

private def stsliceqProgramCellovRefsWithNoise : Array Instr :=
  mkStsliceqProgramBuilderRefs4SliceRefsWithNoise 2

private def stsliceqProgramCellovFullBitsRefs4 : Array Instr :=
  mkStsliceqProgramFullBitsRefs4Slice 1 1 (.num 1)

private def stsliceqBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 12, 16]

private def pickStsliceqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (index, rng') := randNat rng 0 (stsliceqBitsBoundaryPool.size - 1)
  (stsliceqBitsBoundaryPool[index]!, rng')

private def pickStsliceqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickStsliceqBitsBoundary rng1
  else
    randNat rng1 0 16

private def maxUnsignedNatByBits (bits : Nat) : Nat :=
  if bits = 0 then 0 else (1 <<< bits) - 1

private def pickUnsignedForBits (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    let hi := maxUnsignedNatByBits bits
    let (pick, rng1) := randNat rng0 0 4
    let value : Nat :=
      if pick = 0 then 0
      else if pick = 1 then 1
      else if pick = 2 then hi
      else if pick = 3 then
        if hi > 0 then hi - 1 else 0
      else
        if hi > 1 then hi / 2 else hi
    (value, rng1)

private def stsliceqDirectSliceCellPool : Array Cell :=
  #[Cell.empty, cellBits1, cellBits3, cellBits8, cellBits16, cellWithOneRef, cellWithTwoRefs]

private def pickDirectSliceCell (rng : StdGen) : Cell × StdGen :=
  let (index, rng') := randNat rng 0 (stsliceqDirectSliceCellPool.size - 1)
  (stsliceqDirectSliceCellPool[index]!, rng')

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 29
    else if pick = 2 then .cell cellBits3
    else if pick = 3 then .slice (Slice.ofCell cellBits1)
    else .cell cellWithOneRef
  (noise, rng1)

private def genStsliceqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    let (sliceCell, rng2) := pickDirectSliceCell rng1
    (mkStsliceqCase "fuzz/ok/direct/top-only"
      #[.slice (Slice.ofCell sliceCell), .builder Builder.empty], rng2)
  else if shape = 1 then
    let (sliceCell, rng2) := pickDirectSliceCell rng1
    let (noise, rng3) := pickNoiseValue rng2
    (mkStsliceqCase "fuzz/ok/direct/deep-stack"
      #[noise, .slice (Slice.ofCell sliceCell), .builder Builder.empty], rng3)
  else if shape = 2 then
    (mkStsliceqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkStsliceqCase "fuzz/underflow/one-item-builder" #[.builder Builder.empty], rng1)
  else if shape = 4 then
    let (sliceCell, rng2) := pickDirectSliceCell rng1
    (mkStsliceqCase "fuzz/underflow/one-item-slice" #[.slice (Slice.ofCell sliceCell)], rng2)
  else if shape = 5 then
    let (sliceCell, rng2) := pickDirectSliceCell rng1
    (mkStsliceqCase "fuzz/type/top-not-builder" #[.slice (Slice.ofCell sliceCell), .null], rng2)
  else if shape = 6 then
    (mkStsliceqCase "fuzz/type/second-not-slice" #[.null, .builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStsliceqCase "fuzz/type/both-invalid-top-first" #[.null, intV 5], rng1)
  else if shape = 8 then
    let (builderBits, rng2) := pickStsliceqBitsMixed rng1
    let (builderRefs, rng3) := randNat rng2 0 4
    let (sliceRefs, rng4) := randNat rng3 0 (4 - builderRefs)
    let (sliceBits, rng5) := pickStsliceqBitsMixed rng4
    let (builderValueNat, rng6) := pickUnsignedForBits (if builderBits = 0 then 1 else builderBits) rng5
    let (sliceValueNat, rng7) := pickUnsignedForBits (if sliceBits = 0 then 1 else sliceBits) rng6
    (mkStsliceqProgramCase
      s!"fuzz/ok/program/b-{builderBits}r{builderRefs}-s-{sliceBits}r{sliceRefs}" #[]
      (mkStsliceqProgramBuilderSlice builderBits builderRefs sliceBits sliceRefs
        (.num (Int.ofNat builderValueNat)) (.num (Int.ofNat sliceValueNat))), rng7)
  else if shape = 9 then
    let (builderBits, rng2) := pickStsliceqBitsMixed rng1
    let (builderRefs, rng3) := randNat rng2 0 4
    let (sliceRefs, rng4) := randNat rng3 0 (4 - builderRefs)
    let (sliceBits, rng5) := pickStsliceqBitsMixed rng4
    let (builderValueNat, rng6) := pickUnsignedForBits (if builderBits = 0 then 1 else builderBits) rng5
    let (sliceValueNat, rng7) := pickUnsignedForBits (if sliceBits = 0 then 1 else sliceBits) rng6
    (mkStsliceqProgramCase
      s!"fuzz/ok/program-noise/b-{builderBits}r{builderRefs}-s-{sliceBits}r{sliceRefs}" #[]
      (mkStsliceqProgramBuilderSliceWithNoise builderBits builderRefs sliceBits sliceRefs
        (.num (Int.ofNat builderValueNat)) (.num (Int.ofNat sliceValueNat))), rng7)
  else if shape = 10 then
    let (sliceBitsRaw, rng2) := pickStsliceqBitsMixed rng1
    let sliceBits := if sliceBitsRaw = 0 then 1 else sliceBitsRaw
    let (sliceValueNat, rng3) := pickUnsignedForBits sliceBits rng2
    (mkStsliceqProgramCase
      s!"fuzz/quiet-cellov/bits/full-builder-slice-{sliceBits}" #[]
      (mkStsliceqProgramFullBuilderSliceBits sliceBits (.num (Int.ofNat sliceValueNat))), rng3)
  else if shape = 11 then
    let (sliceRefs, rng2) := randNat rng1 1 3
    (mkStsliceqProgramCase
      s!"fuzz/quiet-cellov/refs/builder-4-slice-{sliceRefs}" #[]
      (mkStsliceqProgramBuilderRefs4SliceRefs sliceRefs), rng2)
  else if shape = 12 then
    (mkStsliceqProgramCase "fuzz/near-capacity/success/bits1023-plus-empty-slice" #[]
      stsliceqProgramOkNearBits1023SliceEmpty, rng1)
  else if shape = 13 then
    let (sliceCell, rng2) := pickDirectSliceCell rng1
    (mkStsliceqCase "fuzz/gas/exact"
      #[.slice (Slice.ofCell sliceCell), .builder Builder.empty]
      #[.pushInt (.num stsliceqSetGasExact), .tonEnvOp .setGasLimit, stsliceqInstr], rng2)
  else if shape = 14 then
    let (sliceCell, rng2) := pickDirectSliceCell rng1
    (mkStsliceqCase "fuzz/gas/exact-minus-one"
      #[.slice (Slice.ofCell sliceCell), .builder Builder.empty]
      #[.pushInt (.num stsliceqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stsliceqInstr], rng2)
  else
    let (sliceBitsRaw, rng2) := pickStsliceqBitsMixed rng1
    let sliceBits := if sliceBitsRaw = 0 then 1 else sliceBitsRaw
    let (sliceValueNat, rng3) := pickUnsignedForBits sliceBits rng2
    (mkStsliceqProgramCase
      s!"fuzz/quiet-cellov/full-bits-refs4/slice-{sliceBits}r1" #[]
      (mkStsliceqProgramFullBitsRefs4Slice sliceBits 1 (.num (Int.ofNat sliceValueNat))), rng3)

def suite : InstrSuite where
  id := stsliceqId
  unit := #[
    { name := "unit/direct/success-status0-and-append-order"
      run := do
        let fullSlice := Slice.ofCell cellBits8
        expectOkStack "ok/store-full-slice-into-empty-builder"
          (runStsliceqDirect #[.slice fullSlice, .builder Builder.empty])
          #[.builder (appendRemainingSliceExpected Builder.empty fullSlice), intV 0]

        let baseBuilder : Builder :=
          { (Builder.empty.storeBits (natToBits 2 2)) with refs := #[cellBits16] }
        expectOkStack "ok/store-partial-slice-remainder"
          (runStsliceqDirect #[.slice partialSlice, .builder baseBuilder])
          #[.builder (appendRemainingSliceExpected baseBuilder partialSlice), intV 0]

        let emptySlice := Slice.ofCell Cell.empty
        expectOkStack "ok/near-capacity-bits1023-plus-empty-slice"
          (runStsliceqDirect #[.slice emptySlice, .builder fullBuilder1023])
          #[.builder fullBuilder1023, intV 0]

        let refSlice := Slice.ofCell cellWithOneRef
        expectOkStack "ok/deep-stack-preserve-below"
          (runStsliceqDirect #[.null, .slice refSlice, .builder Builder.empty])
          #[.null, .builder (appendRemainingSliceExpected Builder.empty refSlice), intV 0] }
    ,
    { name := "unit/direct/quiet-overflow-status-minus1"
      run := do
        let bitSlice := Slice.ofCell cellBits1
        expectOkStack "quiet-cellov/bits-overflow"
          (runStsliceqDirect #[.slice bitSlice, .builder fullBuilder1023])
          #[.slice bitSlice, .builder fullBuilder1023, intV (-1)]

        let refs4Builder : Builder :=
          { Builder.empty with refs := #[Cell.empty, cellBits1, cellBits3, cellBits8] }
        let refsSlice := Slice.ofCell cellWithOneRef
        expectOkStack "quiet-cellov/refs-overflow"
          (runStsliceqDirect #[.slice refsSlice, .builder refs4Builder])
          #[.slice refsSlice, .builder refs4Builder, intV (-1)]

        expectOkStack "quiet-cellov/preserve-partial-slice-and-below"
          (runStsliceqDirect #[.null, .slice partialSlice, .builder fullBuilder1023])
          #[.null, .slice partialSlice, .builder fullBuilder1023, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStsliceqDirect #[]) .stkUnd
        expectErr "underflow/one-item-builder" (runStsliceqDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runStsliceqDirect #[.slice (Slice.ofCell cellBits1)]) .stkUnd
        expectErr "underflow/one-item-null" (runStsliceqDirect #[.null]) .stkUnd

        expectErr "type/top-not-builder"
          (runStsliceqDirect #[.slice (Slice.ofCell cellBits3), .null]) .typeChk
        expectErr "type/second-not-slice"
          (runStsliceqDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/top-builder-second-int"
          (runStsliceqDirect #[intV 9, .builder Builder.empty]) .typeChk
        expectErr "type/both-invalid-top-first"
          (runStsliceqDirect #[.null, intV 5]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [stsliceqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits 0xcf1a 16 then
          pure ()
        else
          throw (IO.userError s!"stsliceq canonical encode mismatch: got bits {canonicalOnly.bits}")

        let program : Array Instr :=
          #[stsliceqInstr, .stSlice false false, .stSlice true false, .stSlice true true, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stsliceq" s0 stsliceqInstr 16
        let s2 ← expectDecodeStep "decode/stslice-8bit-alias" s1 (.stSlice false false) 8
        let s3 ← expectDecodeStep "decode/stslicer" s2 (.stSlice true false) 16
        let s4 ← expectDecodeStep "decode/stslicerq" s3 (.stSlice true true) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits
          (natToBits 0xcf1a 16 ++ natToBits 0xcf12 16 ++ natToBits 0xcf1e 16 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-cf1a" raw stsliceqInstr 16
        let raw2 ← expectDecodeStep "decode/raw-cf12" raw1 (.stSlice false false) 16
        let raw3 ← expectDecodeStep "decode/raw-cf1e" raw2 (.stSlice true true) 16
        let raw4 ← expectDecodeStep "decode/raw-tail-add" raw3 .add 8
        if raw4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {raw4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stslice-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStsliceqDispatchFallback #[.null])
          #[.null, intV 642] }
  ]
  oracle := #[
    mkStsliceqCase "ok/direct/empty-slice-empty-builder" #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty],
    mkStsliceqCase "ok/direct/slice-bits1" #[.slice (Slice.ofCell cellBits1), .builder Builder.empty],
    mkStsliceqCase "ok/direct/slice-bits8" #[.slice (Slice.ofCell cellBits8), .builder Builder.empty],
    mkStsliceqCase "ok/direct/slice-with-ref" #[.slice (Slice.ofCell cellWithOneRef), .builder Builder.empty],
    mkStsliceqCase "ok/direct/slice-with-two-refs" #[.slice (Slice.ofCell cellWithTwoRefs), .builder Builder.empty],
    mkStsliceqCase "ok/direct/deep-stack-null" #[.null, .slice (Slice.ofCell cellBits3), .builder Builder.empty],
    mkStsliceqCase "ok/direct/deep-stack-int" #[intV 77, .slice (Slice.ofCell cellBits16), .builder Builder.empty],

    mkStsliceqProgramCase "ok/program/b0r0-s0r0" #[] stsliceqProgramOkBits0Refs0Slice0Refs0,
    mkStsliceqProgramCase "ok/program/b3r0-s1r0" #[] stsliceqProgramOkBits3Refs0Slice1Refs0,
    mkStsliceqProgramCase "ok/program/b0r2-s0r1" #[] stsliceqProgramOkBits0Refs2Slice0Refs1,
    mkStsliceqProgramCase "ok/program/b7r1-s8r1" #[] stsliceqProgramOkBits7Refs1Slice8Refs1,
    mkStsliceqProgramCase "ok/program/b15r0-s0r3" #[] stsliceqProgramOkBits15Refs0Slice0Refs3,
    mkStsliceqProgramCase "ok/program/b0r3-s16r1" #[] stsliceqProgramOkBits0Refs3Slice16Refs1,
    mkStsliceqProgramCase "ok/program/near-capacity-bits1023-empty-slice" #[] stsliceqProgramOkNearBits1023SliceEmpty,
    mkStsliceqProgramCase "ok/program/near-capacity-refs4-empty-slice" #[] stsliceqProgramOkNearRefs4SliceEmpty,
    mkStsliceqProgramCase "ok/program/with-noise" #[] stsliceqProgramOkWithNoise,

    mkStsliceqCase "underflow/empty" #[],
    mkStsliceqCase "underflow/one-item-builder" #[.builder Builder.empty],
    mkStsliceqCase "underflow/one-item-slice" #[.slice (Slice.ofCell cellBits1)],
    mkStsliceqCase "underflow/one-item-null" #[.null],

    mkStsliceqCase "type/top-not-builder" #[.slice (Slice.ofCell cellBits3), .null],
    mkStsliceqCase "type/second-not-slice" #[.null, .builder Builder.empty],
    mkStsliceqCase "type/top-builder-second-int" #[intV 9, .builder Builder.empty],
    mkStsliceqCase "type/both-invalid-top-first" #[.null, intV 5],

    mkStsliceqCase "gas/exact-cost-succeeds" #[.slice (Slice.ofCell cellBits8), .builder Builder.empty]
      #[.pushInt (.num stsliceqSetGasExact), .tonEnvOp .setGasLimit, stsliceqInstr],
    mkStsliceqCase "gas/exact-minus-one-out-of-gas" #[.slice (Slice.ofCell cellBits8), .builder Builder.empty]
      #[.pushInt (.num stsliceqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stsliceqInstr],

    mkStsliceqProgramCase "quiet-cellov/program/full-bits-plus-slice1" #[] stsliceqProgramCellovBits,
    mkStsliceqProgramCase "quiet-cellov/program/full-bits-plus-slice2-with-noise" #[] stsliceqProgramCellovBitsWithNoise,
    mkStsliceqProgramCase "quiet-cellov/program/refs4-plus-slice-ref1" #[] stsliceqProgramCellovRefs,
    mkStsliceqProgramCase "quiet-cellov/program/refs4-plus-slice-ref2-with-noise" #[] stsliceqProgramCellovRefsWithNoise,
    mkStsliceqProgramCase "quiet-cellov/program/full-bits-refs4-plus-slice1r1" #[] stsliceqProgramCellovFullBitsRefs4
  ]
  fuzz := #[
    { seed := 2026021026
      count := 500
      gen := genStsliceqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSLICEQ
