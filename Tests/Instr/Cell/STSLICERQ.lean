import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSLICERQ

/-
STSLICERQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StSlice.lean` (`.stSlice true true`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf1e` decode to `.stSlice true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.stSlice true true` encode as `0xcf1e`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_slice_rev(..., quiet=true)` and opcode table entry `0xcf1e`).

Branch map used for this suite (reverse + quiet store-slice):
- dispatch match (`.stSlice` vs fallback `next`);
- `checkUnderflow 2` before any pops;
- reverse pop order is top `slice`, then second `builder`;
- capacity guard `canExtendBy(bitsRemaining, refsRemaining)` on slice remainder;
- quiet success pushes `[builder', 0]`;
- quiet overflow restores `[builder, slice]` and pushes `-1` (no `cellOv` throw).

Key risk areas:
- reverse stack contract is `... builder slice` (slice on top);
- type-check ordering (`slice` pop fails before builder pop);
- append uses slice remainder (`toCellRemaining`) for both bits and refs;
- quiet overflow restores operands in reverse-mode order and preserves deep stack.
-/

private def stslicerqId : InstrId := { name := "STSLICERQ" }

private def stslicerqInstr : Instr := .stSlice true true

private def mkStslicerqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stslicerqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stslicerqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStslicerqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stslicerqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStslicerqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStSlice stslicerqInstr stack

private def runStslicerqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStSlice .add (VM.push (intV 733)) stack

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

private def mkStslicerqProgram
    (bBits bRefs sBits sRefs : Nat)
    (bX : IntVal := .num 0)
    (sX : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bBits bRefs bX
    ++ mkSliceProgram sBits sRefs sX
    ++ #[stslicerqInstr]

private def mkStslicerqProgramFullBits
    (sBits sRefs : Nat)
    (sX : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu ++ mkSliceProgram sBits sRefs sX ++ #[stslicerqInstr]

private def stslicerqProgramBitsOv1 : Array Instr :=
  mkStslicerqProgramFullBits 1 0 (.num 1)

private def stslicerqProgramBitsOv8Ref1 : Array Instr :=
  mkStslicerqProgramFullBits 8 1 (.num 0)

private def stslicerqProgramRefsOv1 : Array Instr :=
  mkStslicerqProgram 0 4 0 1

private def stslicerqProgramRefsOv2Bits7 : Array Instr :=
  mkStslicerqProgram 19 4 7 2 (.num 1) (.num 5)

private def stslicerqSetGasExact : Int :=
  computeExactGasBudget stslicerqInstr

private def stslicerqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stslicerqInstr

private def stslicerqBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 63, 127, 255, 256, 511, 512, 768, 1023]

private def stslicerqOverflowBitsPool : Array Nat :=
  #[1, 2, 7, 8, 15]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickStslicerqCell (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (sliceCellPool.size - 1)
  (sliceCellPool[idx]!, rng')

private def pickStslicerqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool stslicerqBitsBoundaryPool rng

private def pickStslicerqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStslicerqBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickStslicerqNoise (rng0 : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng0 0 3
  if k = 0 then
    (.null, rng1)
  else if k = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), rng2)
  else if k = 2 then
    let (c, rng2) := pickStslicerqCell rng1
    (.cell c, rng2)
  else
    let (c, rng2) := pickStslicerqCell rng1
    (.slice (Slice.ofCell c), rng2)

private def genStslicerqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (c, rng2) := pickStslicerqCell rng1
  if shape = 0 then
    (mkStslicerqCase s!"fuzz/ok/top-only/bits-{c.bits.size}-refs-{c.refs.size}"
      #[.builder Builder.empty, .slice (Slice.ofCell c)], rng2)
  else if shape = 1 then
    let (noise, rng3) := pickStslicerqNoise rng2
    (mkStslicerqCase s!"fuzz/ok/deep-stack/bits-{c.bits.size}-refs-{c.refs.size}"
      #[noise, .builder Builder.empty, .slice (Slice.ofCell c)], rng3)
  else if shape = 2 then
    (mkStslicerqCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 3 then
    (mkStslicerqCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStslicerqCase s!"fuzz/underflow/one-slice/bits-{c.bits.size}" #[.slice (Slice.ofCell c)], rng2)
  else if shape = 5 then
    (mkStslicerqCase "fuzz/type/top-not-slice" #[.builder Builder.empty, .null], rng2)
  else if shape = 6 then
    (mkStslicerqCase s!"fuzz/type/second-not-builder/bits-{c.bits.size}"
      #[.null, .slice (Slice.ofCell c)], rng2)
  else if shape = 7 then
    (mkStslicerqCase s!"fuzz/type/reverse-order-misuse/bits-{c.bits.size}"
      #[.slice (Slice.ofCell c), .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStslicerqCase "fuzz/type/both-wrong-top-first" #[.null, intV 9], rng2)
  else if shape = 9 then
    let (bBits, rng3) := pickStslicerqBitsMixed rng2
    let (bRefs, rng4) := randNat rng3 0 3
    let (sBitsRaw, rng5) := pickStslicerqBitsMixed rng4
    let sBits := Nat.min sBitsRaw (1023 - bBits)
    let (sRefs, rng6) := randNat rng5 0 (4 - bRefs)
    (mkStslicerqProgramCase
      s!"fuzz/program/ok/bb-{bBits}-br-{bRefs}-sb-{sBits}-sr-{sRefs}"
      #[]
      (mkStslicerqProgram bBits bRefs sBits sRefs),
      rng6)
  else if shape = 10 then
    let (bBitsRaw, rng3) := pickStslicerqBitsBoundary rng2
    let bBits := Nat.min bBitsRaw 1023
    let (sBitsRaw, rng4) := pickStslicerqBitsBoundary rng3
    let sBits := Nat.min sBitsRaw (1023 - bBits)
    (mkStslicerqProgramCase
      s!"fuzz/program/ok/boundary/bb-{bBits}-sb-{sBits}"
      #[]
      (mkStslicerqProgram bBits 0 sBits 0),
      rng4)
  else if shape = 11 then
    let (ovBits, rng3) := pickNatFromPool stslicerqOverflowBitsPool rng2
    (mkStslicerqProgramCase
      s!"fuzz/program/quiet-cellov/bits/full-plus-{ovBits}"
      #[]
      (mkStslicerqProgramFullBits ovBits 0),
      rng3)
  else if shape = 12 then
    let (sliceRefs, rng3) := randNat rng2 1 2
    let (sliceBits, rng4) := pickNatFromPool stslicerqOverflowBitsPool rng3
    (mkStslicerqProgramCase
      s!"fuzz/program/quiet-cellov/refs/full-plus-r{sliceRefs}-b{sliceBits}"
      #[]
      (mkStslicerqProgram 0 4 sliceBits sliceRefs),
      rng4)
  else if shape = 13 then
    (mkStslicerqCase "fuzz/gas/exact"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerqSetGasExact), .tonEnvOp .setGasLimit, stslicerqInstr], rng2)
  else if shape = 14 then
    (mkStslicerqCase "fuzz/gas/minus-one"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stslicerqInstr], rng2)
  else if shape = 15 then
    (mkStslicerqProgramCase "fuzz/program/quiet-cellov/bits/full-plus-1-alt"
      #[]
      (mkStslicerqProgramFullBits 1 0),
      rng2)
  else
    (mkStslicerqProgramCase "fuzz/program/ok/full-bits-empty-slice" #[]
      (mkStslicerqProgram 1023 0 0 0), rng2)

def suite : InstrSuite where
  id := stslicerqId
  unit := #[
    { name := "unit/direct/success-status0-rev-order-and-append"
      run := do
        let sEmpty := Slice.ofCell Cell.empty
        expectOkStack "ok/empty-builder-empty-slice"
          (runStslicerqDirect #[.builder Builder.empty, .slice sEmpty])
          #[.builder Builder.empty, intV 0]

        let sBit1 := Slice.ofCell sliceCellBit1
        let expectedBit1 := appendSliceRemaining Builder.empty sBit1
        expectOkStack "ok/empty-builder-bit1-slice"
          (runStslicerqDirect #[.builder Builder.empty, .slice sBit1])
          #[.builder expectedBit1, intV 0]

        let prefBuilder : Builder :=
          { bits := natToBits 5 3
            refs := #[sliceCellByteA5] }
        let sWithRefs := Slice.ofCell sliceCellBitsAndRefs
        let expectedAppend := appendSliceRemaining prefBuilder sWithRefs
        expectOkStack "ok/append-bits-and-refs"
          (runStslicerqDirect #[.builder prefBuilder, .slice sWithRefs])
          #[.builder expectedAppend, intV 0]

        let sourceCell : Cell :=
          Cell.mkOrdinary (natToBits 0x2D 6) #[sliceCellBit1, sliceCellByteA5, Cell.empty]
        let s0 := Slice.ofCell sourceCell
        let sPartial : Slice := { (s0.advanceBits 2) with refPos := s0.refPos + 1 }
        let expectedPartial := appendSliceRemaining prefBuilder sPartial
        expectOkStack "ok/append-partial-slice-remainder"
          (runStslicerqDirect #[.builder prefBuilder, .slice sPartial])
          #[.builder expectedPartial, intV 0]

        let expectedDeep := appendSliceRemaining Builder.empty sBit1
        expectOkStack "ok/deep-stack-preserve-below"
          (runStslicerqDirect #[.null, .builder Builder.empty, .slice sBit1])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        let sBit1 := Slice.ofCell sliceCellBit1
        expectErr "underflow/empty" (runStslicerqDirect #[]) .stkUnd
        expectErr "underflow/one-builder" (runStslicerqDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-slice" (runStslicerqDirect #[.slice sBit1]) .stkUnd
        expectErr "underflow/one-null" (runStslicerqDirect #[.null]) .stkUnd

        expectErr "type/top-not-slice-null"
          (runStslicerqDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/top-not-slice-int"
          (runStslicerqDirect #[.builder Builder.empty, intV 3]) .typeChk
        expectErr "type/second-not-builder-null"
          (runStslicerqDirect #[.null, .slice sBit1]) .typeChk
        expectErr "type/second-not-builder-int"
          (runStslicerqDirect #[intV 8, .slice sBit1]) .typeChk
        expectErr "type/reverse-order-misuse"
          (runStslicerqDirect #[.slice sBit1, .builder Builder.empty]) .typeChk
        expectErr "type/both-wrong-top-first"
          (runStslicerqDirect #[.null, intV 5]) .typeChk }
    ,
    { name := "unit/direct/quiet-cellov-status-and-stack-restore"
      run := do
        let sBit1 := Slice.ofCell sliceCellBit1
        expectOkStack "quiet-cellov/bits-full-plus-1"
          (runStslicerqDirect #[.builder fullBuilder1023, .slice sBit1])
          #[.builder fullBuilder1023, .slice sBit1, intV (-1)]

        let bRef4 : Builder :=
          { bits := #[]
            refs := #[Cell.empty, sliceCellBit1, sliceCellByteA5, sliceCellWithRef] }
        let sRef1 : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 3 2) #[Cell.empty])
        expectOkStack "quiet-cellov/refs-full-plus-1"
          (runStslicerqDirect #[.builder bRef4, .slice sRef1])
          #[.builder bRef4, .slice sRef1, intV (-1)]

        let sourceCell : Cell :=
          Cell.mkOrdinary (natToBits 0x35 6) #[sliceCellBit1, sliceCellByteA5]
        let s0 := Slice.ofCell sourceCell
        let sPartial : Slice := { (s0.advanceBits 1) with refPos := s0.refPos + 1 }
        expectOkStack "quiet-cellov/preserve-partial-slice-and-below"
          (runStslicerqDirect #[.null, .builder fullBuilder1023, .slice sPartial])
          #[.null, .builder fullBuilder1023, .slice sPartial, intV (-1)] }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [stslicerqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits 0xcf1e 16 then
          pure ()
        else
          throw (IO.userError s!"stslicerq canonical encode mismatch: got bits {canonicalOnly.bits}")

        let program : Array Instr :=
          #[stslicerqInstr, .stSlice true false, .stSlice false true, .stSlice false false, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stslicerq" s0 stslicerqInstr 16
        let s2 ← expectDecodeStep "decode/stslicer" s1 (.stSlice true false) 16
        let s3 ← expectDecodeStep "decode/stsliceq" s2 (.stSlice false true) 16
        let s4 ← expectDecodeStep "decode/stslice-8bit-alias" s3 (.stSlice false false) 8
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits
          (natToBits 0xcf1e 16 ++ natToBits 0xcf16 16 ++ natToBits 0xcf1a 16 ++ natToBits 0xcf12 16 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-cf1e" raw stslicerqInstr 16
        let raw2 ← expectDecodeStep "decode/raw-cf16" raw1 (.stSlice true false) 16
        let raw3 ← expectDecodeStep "decode/raw-cf1a" raw2 (.stSlice false true) 16
        let raw4 ← expectDecodeStep "decode/raw-cf12" raw3 (.stSlice false false) 16
        let raw5 ← expectDecodeStep "decode/raw-tail-add" raw4 .add 8
        if raw5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {raw5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stslice-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStslicerqDispatchFallback #[.null])
          #[.null, intV 733] }
  ]
  oracle := #[
    mkStslicerqCase "ok/empty-builder-empty-slice"
      #[.builder Builder.empty, .slice (Slice.ofCell Cell.empty)],
    mkStslicerqCase "ok/empty-builder-bit1-slice"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)],
    mkStslicerqCase "ok/empty-builder-byte-slice"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellByteA5)],
    mkStslicerqCase "ok/empty-builder-slice-with-ref"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellWithRef)],
    mkStslicerqCase "ok/empty-builder-slice-bits-and-refs"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBitsAndRefs)],
    mkStslicerqCase "ok/deep-stack-preserve-null"
      #[.null, .builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)],
    mkStslicerqCase "ok/deep-stack-preserve-int"
      #[intV 99, .builder Builder.empty, .slice (Slice.ofCell sliceCellByteA5)],

    mkStslicerqProgramCase "ok/program/b0r0-s0r0" #[]
      (mkStslicerqProgram 0 0 0 0),
    mkStslicerqProgramCase "ok/program/b3r0-s5r0" #[]
      (mkStslicerqProgram 3 0 5 0 (.num 5) (.num 17)),
    mkStslicerqProgramCase "ok/program/b0r1-s2r0" #[]
      (mkStslicerqProgram 0 1 2 0 (.num 0) (.num 3)),
    mkStslicerqProgramCase "ok/program/b5r1-s7r1" #[]
      (mkStslicerqProgram 5 1 7 1 (.num 1) (.num 9)),
    mkStslicerqProgramCase "ok/program/b31r2-s15r1" #[]
      (mkStslicerqProgram 31 2 15 1 (.num 0) (.num 7)),
    mkStslicerqProgramCase "ok/program/b255r0-s1r0" #[]
      (mkStslicerqProgram 255 0 1 0 (.num 0) (.num 1)),
    mkStslicerqProgramCase "ok/program/b512r1-s256r0" #[]
      (mkStslicerqProgram 512 1 256 0),
    mkStslicerqProgramCase "ok/program/b1023r0-s0r0" #[]
      (mkStslicerqProgram 1023 0 0 0),
    mkStslicerqProgramCase "ok/program/b0r4-s0r0" #[]
      (mkStslicerqProgram 0 4 0 0),
    mkStslicerqProgramCase "ok/program/noise-preserved" #[.null]
      (mkStslicerqProgram 7 1 3 1 (.num 1) (.num 5)),
    mkStslicerqProgramCase "ok/program/slice-refs-3" #[]
      (mkStslicerqProgram 1 0 0 3 (.num 1) (.num 0)),

    mkStslicerqCase "underflow/empty" #[],
    mkStslicerqCase "underflow/one-builder" #[.builder Builder.empty],
    mkStslicerqCase "underflow/one-slice" #[.slice (Slice.ofCell sliceCellBit1)],

    mkStslicerqCase "type/top-not-slice-null"
      #[.builder Builder.empty, .null],
    mkStslicerqCase "type/top-not-slice-int"
      #[.builder Builder.empty, intV 3],
    mkStslicerqCase "type/second-not-builder-null"
      #[.null, .slice (Slice.ofCell sliceCellBit1)],
    mkStslicerqCase "type/reverse-order-misuse"
      #[.slice (Slice.ofCell sliceCellBit1), .builder Builder.empty],
    mkStslicerqCase "type/both-wrong-top-first"
      #[.null, intV 5],

    mkStslicerqCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerqSetGasExact), .tonEnvOp .setGasLimit, stslicerqInstr],
    mkStslicerqCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, .slice (Slice.ofCell sliceCellBit1)]
      #[.pushInt (.num stslicerqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stslicerqInstr],

    mkStslicerqProgramCase "quiet-cellov/program/bits-overflow-full-plus-1" #[]
      stslicerqProgramBitsOv1,
    mkStslicerqProgramCase "quiet-cellov/program/refs-overflow-b4-plus-ref1" #[]
      stslicerqProgramRefsOv1,
    mkStslicerqProgramCase "quiet-cellov/program/bits-overflow-full-plus8-ref1" #[]
      stslicerqProgramBitsOv8Ref1,
    mkStslicerqProgramCase "quiet-cellov/program/refs-overflow-b4-plus-ref2-bits7" #[]
      stslicerqProgramRefsOv2Bits7
  ]
  fuzz := #[
    { seed := 2026021018
      count := 320
      gen := genStslicerqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSLICERQ
