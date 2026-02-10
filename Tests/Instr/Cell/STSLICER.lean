import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSLICER

/-
STSLICER branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StSlice.lean` (`.stSlice rev=true quiet=false`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf16` decode to `.stSlice true false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.stSlice true false` encode as `0xcf16`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_slice_rev`, non-quiet).

Branch map used for this suite (`rev=true`, `quiet=false`, i.e. STSLICER):
- Lean STSLICER path: 5 branch sites / 6 terminal outcomes
  (`checkUnderflow 2`; pop top as slice; pop second as builder;
   capacity guard over remaining slice bits/refs; success append or `cellOv` throw).
- C++ STSLICER path: 4 branch sites / 5 aligned outcomes
  (`check_underflow(2)`; `pop_cellslice`; `pop_builder`; `can_extend_by`).

Key risk areas:
- reverse stack order is `... builder slice` (slice on top);
- type-check ordering (`slice` pop fails before builder pop);
- append uses slice remainder (`toCellRemaining`) not whole source cell;
- non-quiet overflow throws `cellOv` and does not restore operands.
-/

private def stslicerId : InstrId := { name := "STSLICER" }

private def stslicerInstr : Instr := .stSlice true false

private def mkStslicerCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stslicerInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stslicerId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStslicerProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stslicerId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStslicerDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStSlice stslicerInstr stack

private def runStslicerDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStSlice .add (VM.push (intV 516)) stack

private def appendSliceRemaining (b : Builder) (s : Slice) : Builder :=
  let c := s.toCellRemaining
  { bits := b.bits ++ c.bits
    refs := b.refs ++ c.refs }

private def sliceCellBit1 : Cell :=
  Cell.ofUInt 1 1

private def sliceCellByteA5 : Cell :=
  Cell.ofUInt 8 0xA5

private def sliceCellWithRef : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[Cell.empty]

private def sliceCellBitsAndRefs : Cell :=
  Cell.mkOrdinary (natToBits 21 5) #[sliceCellBit1, Cell.empty]

private def sliceCellPool : Array Cell :=
  #[
    Cell.empty,
    sliceCellBit1,
    sliceCellByteA5,
    sliceCellWithRef,
    sliceCellBitsAndRefs,
    Cell.ofUInt 12 0xABC,
    Cell.mkOrdinary (natToBits 2 2) #[sliceCellBit1, sliceCellByteA5]
  ]

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  Id.run do
    let mut out : Array Instr := #[]
    let mut rem := bits
    while rem > 0 do
      let chunk : Nat := Nat.min 256 rem
      out := out ++ #[.pushInt x, .xchg0 1, .stu chunk]
      rem := rem - chunk
    return out

private def appendOneRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

private def mkBuilderProgram (bits refs : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkSliceProgram (bits refs : Nat) (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[.endc, .ctos]

private def mkStslicerProgram
    (bBits bRefs sBits sRefs : Nat)
    (bX : IntVal := .num 0)
    (sX : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bBits bRefs bX
    ++ mkSliceProgram sBits sRefs sX
    ++ #[stslicerInstr]

private def mkStslicerProgramFullBits
    (sBits sRefs : Nat)
    (sX : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu ++ mkSliceProgram sBits sRefs sX ++ #[stslicerInstr]

private def stslicerProgramBitsOv1 : Array Instr :=
  mkStslicerProgramFullBits 1 0 (.num 1)

private def stslicerProgramBitsOv8Ref1 : Array Instr :=
  mkStslicerProgramFullBits 8 1 (.num 0)

private def stslicerProgramRefsOv1 : Array Instr :=
  mkStslicerProgram 0 4 0 1

private def stslicerProgramRefsOv2Bits7 : Array Instr :=
  mkStslicerProgram 19 4 7 2 (.num 1) (.num 5)

private def stslicerSetGasExact : Int :=
  computeExactGasBudget stslicerInstr

private def stslicerSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stslicerInstr

private def stslicerBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 63, 127, 255, 256, 511, 512, 768, 1023]

private def stslicerOverflowBitsPool : Array Nat :=
  #[1, 2, 7, 8, 15]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickStslicerCell (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (sliceCellPool.size - 1)
  (sliceCellPool[idx]!, rng')

private def pickStslicerBitsBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool stslicerBitsBoundaryPool rng

private def pickStslicerBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStslicerBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickStslicerNoise (rng0 : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng0 0 3
  if k = 0 then
    (.null, rng1)
  else if k = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), rng2)
  else if k = 2 then
    let (c, rng2) := pickStslicerCell rng1
    (.cell c, rng2)
  else
    let (c, rng2) := pickStslicerCell rng1
    (.slice (Slice.ofCell c), rng2)

private def genStslicerFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (c, rng2) := pickStslicerCell rng1
  if shape = 0 then
    (mkStslicerCase s!"fuzz/ok/top-only/bits-{c.bits.size}-refs-{c.refs.size}"
      #[.builder Builder.empty, .slice (Slice.ofCell c)], rng2)
  else if shape = 1 then
    let (noise, rng3) := pickStslicerNoise rng2
    (mkStslicerCase s!"fuzz/ok/deep-stack/bits-{c.bits.size}-refs-{c.refs.size}"
      #[noise, .builder Builder.empty, .slice (Slice.ofCell c)], rng3)
  else if shape = 2 then
    (mkStslicerCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 3 then
    (mkStslicerCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStslicerCase s!"fuzz/underflow/one-slice/bits-{c.bits.size}" #[.slice (Slice.ofCell c)], rng2)
  else if shape = 5 then
    (mkStslicerCase "fuzz/type/top-not-slice" #[.builder Builder.empty, .null], rng2)
  else if shape = 6 then
    (mkStslicerCase s!"fuzz/type/second-not-builder/bits-{c.bits.size}"
      #[.null, .slice (Slice.ofCell c)], rng2)
  else if shape = 7 then
    (mkStslicerCase s!"fuzz/type/reverse-order-misuse/bits-{c.bits.size}"
      #[.slice (Slice.ofCell c), .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStslicerCase "fuzz/type/both-wrong-top-first" #[.null, intV 9], rng2)
  else if shape = 9 then
    let (bBits, rng3) := pickStslicerBitsMixed rng2
    let (bRefs, rng4) := randNat rng3 0 3
    let (sBitsRaw, rng5) := pickStslicerBitsMixed rng4
    let sBits := Nat.min sBitsRaw (1023 - bBits)
    let (sRefs, rng6) := randNat rng5 0 (4 - bRefs)
    (mkStslicerProgramCase
      s!"fuzz/program/ok/bb-{bBits}-br-{bRefs}-sb-{sBits}-sr-{sRefs}"
      #[]
      (mkStslicerProgram bBits bRefs sBits sRefs),
      rng6)
  else if shape = 10 then
    let (bBitsRaw, rng3) := pickStslicerBitsBoundary rng2
    let bBits := Nat.min bBitsRaw 1023
    let (sBitsRaw, rng4) := pickStslicerBitsBoundary rng3
    let sBits := Nat.min sBitsRaw (1023 - bBits)
    (mkStslicerProgramCase
      s!"fuzz/program/ok/boundary/bb-{bBits}-sb-{sBits}"
      #[]
      (mkStslicerProgram bBits 0 sBits 0),
      rng4)
  else if shape = 11 then
    let (ovBits, rng3) := pickNatFromPool stslicerOverflowBitsPool rng2
    (mkStslicerProgramCase
      s!"fuzz/program/cellov/bits/full-plus-{ovBits}"
      #[]
      (mkStslicerProgramFullBits ovBits 0),
      rng3)
  else if shape = 12 then
    let (sliceRefs, rng3) := randNat rng2 1 2
    let (sliceBits, rng4) := pickNatFromPool stslicerOverflowBitsPool rng3
    (mkStslicerProgramCase
      s!"fuzz/program/cellov/refs/full-plus-r{sliceRefs}-b{sliceBits}"
      #[]
      (mkStslicerProgram 0 4 sliceBits sliceRefs),
      rng4)
  else if shape = 13 then
    (mkStslicerCase "fuzz/gas/exact"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerSetGasExact), .tonEnvOp .setGasLimit, stslicerInstr], rng2)
  else if shape = 14 then
    (mkStslicerCase "fuzz/gas/minus-one"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerSetGasExactMinusOne), .tonEnvOp .setGasLimit, stslicerInstr], rng2)
  else
    (mkStslicerProgramCase "fuzz/program/ok/full-bits-empty-slice" #[]
      (mkStslicerProgram 1023 0 0 0), rng2)

def suite : InstrSuite where
  id := stslicerId
  unit := #[
    { name := "unit/direct/success-reverse-order-and-append"
      run := do
        let sEmpty := Slice.ofCell Cell.empty
        expectOkStack "ok/empty-builder-empty-slice"
          (runStslicerDirect #[.builder Builder.empty, .slice sEmpty])
          #[.builder Builder.empty]

        let sBit1 := Slice.ofCell sliceCellBit1
        let expectedBit1 := appendSliceRemaining Builder.empty sBit1
        expectOkStack "ok/empty-builder-bit1-slice"
          (runStslicerDirect #[.builder Builder.empty, .slice sBit1])
          #[.builder expectedBit1]

        let prefBuilder : Builder :=
          { bits := natToBits 5 3
            refs := #[sliceCellByteA5] }
        let sWithRefs := Slice.ofCell sliceCellBitsAndRefs
        let expectedAppend := appendSliceRemaining prefBuilder sWithRefs
        expectOkStack "ok/append-bits-and-refs"
          (runStslicerDirect #[.builder prefBuilder, .slice sWithRefs])
          #[.builder expectedAppend]

        let sourceCell : Cell :=
          Cell.mkOrdinary (natToBits 0x2D 6) #[sliceCellBit1, sliceCellByteA5, Cell.empty]
        let s0 := Slice.ofCell sourceCell
        let sPartial : Slice := { (s0.advanceBits 2) with refPos := s0.refPos + 1 }
        let expectedPartial := appendSliceRemaining prefBuilder sPartial
        expectOkStack "ok/append-partial-slice-remainder"
          (runStslicerDirect #[.builder prefBuilder, .slice sPartial])
          #[.builder expectedPartial]

        let expectedDeep := appendSliceRemaining Builder.empty sBit1
        expectOkStack "ok/deep-stack-preserve-below"
          (runStslicerDirect #[.null, .builder Builder.empty, .slice sBit1])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        let sBit1 := Slice.ofCell sliceCellBit1
        expectErr "underflow/empty" (runStslicerDirect #[]) .stkUnd
        expectErr "underflow/one-builder" (runStslicerDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-slice" (runStslicerDirect #[.slice sBit1]) .stkUnd
        expectErr "underflow/one-null" (runStslicerDirect #[.null]) .stkUnd

        expectErr "type/top-not-slice-null"
          (runStslicerDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/top-not-slice-int"
          (runStslicerDirect #[.builder Builder.empty, intV 3]) .typeChk
        expectErr "type/second-not-builder-null"
          (runStslicerDirect #[.null, .slice sBit1]) .typeChk
        expectErr "type/second-not-builder-int"
          (runStslicerDirect #[intV 8, .slice sBit1]) .typeChk
        expectErr "type/reverse-order-misuse"
          (runStslicerDirect #[.slice sBit1, .builder Builder.empty]) .typeChk
        expectErr "type/both-wrong-top-first"
          (runStslicerDirect #[.null, intV 5]) .typeChk }
    ,
    { name := "unit/direct/cellov-bits-and-refs"
      run := do
        let sBit1 := Slice.ofCell sliceCellBit1
        expectErr "cellov/bits-full-plus-1"
          (runStslicerDirect #[.builder fullBuilder1023, .slice sBit1]) .cellOv

        let bRef4 : Builder :=
          { bits := #[]
            refs := #[Cell.empty, sliceCellBit1, sliceCellByteA5, sliceCellWithRef] }
        let sRef1 : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 3 2) #[Cell.empty])
        expectErr "cellov/refs-full-plus-1"
          (runStslicerDirect #[.builder bRef4, .slice sRef1]) .cellOv

        let sBitsAndRef := Slice.ofCell (Cell.mkOrdinary (natToBits 0x7F 7) #[Cell.empty])
        expectErr "cellov/bits-full-plus-bits-and-ref"
          (runStslicerDirect #[.builder fullBuilder1023, .slice sBitsAndRef]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr :=
          #[stslicerInstr, .stSlice true true, .stSlice false false, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stslicer" s0 stslicerInstr 16
        let s2 ← expectDecodeStep "decode/stslicerq-neighbor" s1 (.stSlice true true) 16
        let s3 ← expectDecodeStep "decode/stslice-8bit-neighbor" s2 (.stSlice false false) 8
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stslice-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStslicerDispatchFallback #[.null])
          #[.null, intV 516] }
  ]
  oracle := #[
    mkStslicerCase "ok/empty-builder-empty-slice"
      #[.builder Builder.empty, .slice (Slice.ofCell Cell.empty)],
    mkStslicerCase "ok/empty-builder-bit1-slice"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)],
    mkStslicerCase "ok/empty-builder-byte-slice"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellByteA5)],
    mkStslicerCase "ok/empty-builder-slice-with-ref"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellWithRef)],
    mkStslicerCase "ok/empty-builder-slice-bits-and-refs"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBitsAndRefs)],
    mkStslicerCase "ok/deep-stack-preserve-null"
      #[.null, .builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)],
    mkStslicerCase "ok/deep-stack-preserve-int"
      #[intV 99, .builder Builder.empty, .slice (Slice.ofCell sliceCellByteA5)],

    mkStslicerProgramCase "ok/program/b0r0-s0r0" #[]
      (mkStslicerProgram 0 0 0 0),
    mkStslicerProgramCase "ok/program/b3r0-s5r0" #[]
      (mkStslicerProgram 3 0 5 0 (.num 5) (.num 17)),
    mkStslicerProgramCase "ok/program/b0r1-s2r0" #[]
      (mkStslicerProgram 0 1 2 0 (.num 0) (.num 3)),
    mkStslicerProgramCase "ok/program/b5r1-s7r1" #[]
      (mkStslicerProgram 5 1 7 1 (.num 1) (.num 9)),
    mkStslicerProgramCase "ok/program/b31r2-s15r1" #[]
      (mkStslicerProgram 31 2 15 1 (.num 0) (.num 7)),
    mkStslicerProgramCase "ok/program/b255r0-s1r0" #[]
      (mkStslicerProgram 255 0 1 0 (.num 0) (.num 1)),
    mkStslicerProgramCase "ok/program/b512r1-s256r0" #[]
      (mkStslicerProgram 512 1 256 0),
    mkStslicerProgramCase "ok/program/b1023r0-s0r0" #[]
      (mkStslicerProgram 1023 0 0 0),
    mkStslicerProgramCase "ok/program/b0r4-s0r0" #[]
      (mkStslicerProgram 0 4 0 0),
    mkStslicerProgramCase "ok/program/noise-preserved" #[.null]
      (mkStslicerProgram 7 1 3 1 (.num 1) (.num 5)),
    mkStslicerProgramCase "ok/program/slice-refs-3" #[]
      (mkStslicerProgram 1 0 0 3 (.num 1) (.num 0)),

    mkStslicerCase "underflow/empty" #[],
    mkStslicerCase "underflow/one-builder" #[.builder Builder.empty],
    mkStslicerCase "underflow/one-slice" #[.slice (Slice.ofCell sliceCellBit1)],

    mkStslicerCase "type/top-not-slice-null"
      #[.builder Builder.empty, .null],
    mkStslicerCase "type/top-not-slice-int"
      #[.builder Builder.empty, intV 3],
    mkStslicerCase "type/second-not-builder-null"
      #[.null, .slice (Slice.ofCell sliceCellBit1)],
    mkStslicerCase "type/reverse-order-misuse"
      #[.slice (Slice.ofCell sliceCellBit1), .builder Builder.empty],
    mkStslicerCase "type/both-wrong-top-first"
      #[.null, intV 5],

    mkStslicerCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerSetGasExact), .tonEnvOp .setGasLimit, stslicerInstr],
    mkStslicerCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerSetGasExactMinusOne), .tonEnvOp .setGasLimit, stslicerInstr],

    mkStslicerProgramCase "cellov/program/bits-overflow-full-plus-1" #[]
      stslicerProgramBitsOv1,
    mkStslicerProgramCase "cellov/program/refs-overflow-b4-plus-ref1" #[]
      stslicerProgramRefsOv1,
    mkStslicerProgramCase "cellov/program/bits-overflow-full-plus8-ref1" #[]
      stslicerProgramBitsOv8Ref1,
    mkStslicerProgramCase "cellov/program/refs-overflow-b4-plus-ref2-bits7" #[]
      stslicerProgramRefsOv2Bits7
  ]
  fuzz := #[
    { seed := 2026021016
      count := 320
      gen := genStslicerFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSLICER
