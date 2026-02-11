import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSLICE

/-
STSLICE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stslice.lean` (`.stSlice rev quiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xce` canonical + `0xcf12` alias decode to `.stSlice false false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.stSlice false false` assembles canonically as `0xce`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_slice(..., quiet=false)` for `0xce` and `0xcf12`).

Branch map used for this suite (STSLICE only: `rev=false`, `quiet=false`):
- dispatch fallthrough for non-`.stSlice`;
- `checkUnderflow 2`;
- top pop/type (`popBuilder`);
- second pop/type (`popSlice`);
- capacity guard `canExtendBy(bits,refs)` on slice remainder;
- success append (`builder.bits ++ rem.bits`, `builder.refs ++ rem.refs`) or `cellOv`.

Key risk areas:
- stack order is `... slice builder` (builder on top);
- append uses `Slice.toCellRemaining` (current cursor matters for direct handler calls);
- overflow can be triggered by bit capacity, ref capacity, or both;
- canonical asm is `0xce`, but decoder must also accept alias `0xcf12`;
- exact gas edge for `PUSHINT n; SETGASLIMIT; STSLICE`.
-/

private def stsliceId : InstrId := { name := "STSLICE" }

private def stsliceInstr : Instr := .stSlice false false

private def stsliceAliasOpcode : Nat := 0xcf12

private def stsliceCanonicalOpcode : Nat := 0xce

private def mkStsliceCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stsliceInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsliceId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStsliceProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsliceId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStsliceDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStSlice stsliceInstr stack

private def runStsliceDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStSlice .add (VM.push (intV 436)) stack

private def stsliceSetGasExact : Int :=
  computeExactGasBudget stsliceInstr

private def stsliceSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stsliceInstr

private def expectedStoredBuilder (b : Builder) (s : Slice) : Builder :=
  let c := s.toCellRemaining
  { bits := b.bits ++ c.bits
    refs := b.refs ++ c.refs }

private def mkBuilderProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkCellProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[.endc]

private def mkSliceProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkCellProgram bits refs x ++ #[.ctos]

private def mkStsliceProgram
    (sliceBits : Nat)
    (sliceRefs : Nat)
    (builderBits : Nat)
    (builderRefs : Nat)
    (sliceX : IntVal := .num 0)
    (builderX : IntVal := .num 0) : Array Instr :=
  mkSliceProgram sliceBits sliceRefs sliceX
    ++ mkBuilderProgram builderBits builderRefs builderX
    ++ #[stsliceInstr]

private def mkStsliceProgramWithNoise
    (sliceBits : Nat)
    (sliceRefs : Nat)
    (builderBits : Nat)
    (builderRefs : Nat)
    (sliceX : IntVal := .num 0)
    (builderX : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStsliceProgram sliceBits sliceRefs builderBits builderRefs sliceX builderX

private def mkStsliceBitsOvProgram
    (sliceBits : Nat)
    (sliceX : IntVal := .num 1) : Array Instr :=
  mkSliceProgram sliceBits 0 sliceX ++ mkBuilderProgram 1023 0 ++ #[stsliceInstr]

private def mkStsliceRefsOvProgram (sliceRefs : Nat) : Array Instr :=
  mkSliceProgram 0 sliceRefs ++ mkBuilderProgram 0 4 ++ #[stsliceInstr]

private def mkStsliceBothOvProgram
    (sliceBits : Nat)
    (sliceRefs : Nat)
    (sliceX : IntVal := .num 1) : Array Instr :=
  mkSliceProgram sliceBits sliceRefs sliceX ++ mkBuilderProgram 1023 4 ++ #[stsliceInstr]

private def stsliceAppendProgram : Array Instr :=
  mkStsliceProgram 5 1 3 1 (.num 17) (.num 6)

private def stsliceAppendBitsOnlyProgram : Array Instr :=
  mkStsliceProgram 8 0 7 0 (.num 170) (.num 5)

private def stsliceAppendRefsOnlyProgram : Array Instr :=
  mkStsliceProgram 0 2 0 1

private def stsliceAppendMixedProgram : Array Instr :=
  mkStsliceProgram 3 1 9 2 (.num 5) (.num 3)

private def stsliceAppendMixedAltProgram : Array Instr :=
  mkStsliceProgram 4 2 6 1 (.num 9) (.num 7)

private def stsliceBoundaryFullBitsProgram : Array Instr :=
  mkStsliceProgram 0 0 1023 0

private def stsliceBoundaryFullRefsProgram : Array Instr :=
  mkStsliceProgram 0 0 0 4

private def stsliceBoundaryFullBitsRefs3ThenRefProgram : Array Instr :=
  mkStsliceProgram 0 1 1023 3

private def stsliceBoundaryRefs4Bits1022ThenBitProgram : Array Instr :=
  mkStsliceProgram 1 0 1022 4 (.num 1) (.num 0)

private def stsliceAppendProgramWithNoise : Array Instr :=
  mkStsliceProgramWithNoise 4 1 3 1 (.num 7) (.num 3)

private def stsliceCellOvBitsProgram : Array Instr :=
  mkStsliceBitsOvProgram 1 (.num 1)

private def stsliceCellOvRefsProgram : Array Instr :=
  mkStsliceRefsOvProgram 1

private def stsliceCellOvBothProgram : Array Instr :=
  mkStsliceBothOvProgram 1 1 (.num 1)

private def stsliceBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31]

private def pickStsliceBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stsliceBitsBoundaryPool.size - 1)
  (stsliceBitsBoundaryPool[idx]!, rng')

private def pickStsliceBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickStsliceBitsBoundary rng1
  else
    randNat rng1 0 31

private def pickPayloadForBits (bits : Nat) (rng : StdGen) : IntVal × StdGen :=
  if bits = 0 then
    (.num 0, rng)
  else
    let hi : Int := intPow2 bits - 1
    let (pick, rng') := randNat rng 0 4
    let x : Int :=
      if pick = 0 then 0
      else if pick = 1 then 1
      else if pick = 2 then hi
      else if pick = 3 then
        if hi > 0 then hi - 1 else 0
      else
        hi / 2
    (.num x, rng')

private def genStsliceFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    (mkStsliceCase "fuzz/ok/direct/minimal"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noisePick, rng2) := randNat rng1 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 91 else .cell Cell.empty
    (mkStsliceCase "fuzz/ok/direct/deep-stack"
      #[noise, .slice (Slice.ofCell Cell.empty), .builder Builder.empty], rng2)
  else if shape = 2 then
    (mkStsliceCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkStsliceCase "fuzz/underflow/one-slice" #[.slice (Slice.ofCell Cell.empty)], rng1)
  else if shape = 4 then
    (mkStsliceCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkStsliceCase "fuzz/type/top-not-builder"
      #[.slice (Slice.ofCell Cell.empty), .null], rng1)
  else if shape = 6 then
    (mkStsliceCase "fuzz/type/second-not-slice" #[.null, .builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStsliceCase "fuzz/type/reversed-order"
      #[.builder Builder.empty, .slice (Slice.ofCell Cell.empty)], rng1)
  else if shape = 8 then
    let (sliceBits, rng2) := pickStsliceBitsMixed rng1
    let (sliceRefs, rng3) := randNat rng2 0 2
    let (builderBits, rng4) := randNat rng3 0 (Nat.min 31 (1023 - sliceBits))
    let (builderRefs, rng5) := randNat rng4 0 (4 - sliceRefs)
    let (sliceX, rng6) := pickPayloadForBits sliceBits rng5
    let (builderX, rng7) := pickPayloadForBits builderBits rng6
    (mkStsliceProgramCase
      s!"fuzz/ok/program/sb-{sliceBits}-sr-{sliceRefs}-bb-{builderBits}-br-{builderRefs}"
      #[]
      (mkStsliceProgram sliceBits sliceRefs builderBits builderRefs sliceX builderX), rng7)
  else if shape = 9 then
    let (mode, rng2) := randNat rng1 0 2
    if mode = 0 then
      (mkStsliceProgramCase "fuzz/ok/program/boundary/full-bits-refs3-plus-ref1"
        #[] stsliceBoundaryFullBitsRefs3ThenRefProgram, rng2)
    else if mode = 1 then
      (mkStsliceProgramCase "fuzz/ok/program/boundary/refs4-bits1022-plus-bit1"
        #[] stsliceBoundaryRefs4Bits1022ThenBitProgram, rng2)
    else
      (mkStsliceProgramCase "fuzz/ok/program/boundary/full-bits-empty-slice"
        #[] stsliceBoundaryFullBitsProgram, rng2)
  else if shape = 10 then
    let (sliceBits, rng2) := randNat rng1 1 8
    let (sliceX, rng3) := pickPayloadForBits sliceBits rng2
    (mkStsliceProgramCase s!"fuzz/cellov/program/bits-{sliceBits}"
      #[]
      (mkStsliceBitsOvProgram sliceBits sliceX), rng3)
  else if shape = 11 then
    let (sliceRefs, rng2) := randNat rng1 1 3
    (mkStsliceProgramCase s!"fuzz/cellov/program/refs-{sliceRefs}"
      #[]
      (mkStsliceRefsOvProgram sliceRefs), rng2)
  else if shape = 12 then
    let (sliceBits, rng2) := randNat rng1 1 4
    let (sliceRefs, rng3) := randNat rng2 1 2
    let (sliceX, rng4) := pickPayloadForBits sliceBits rng3
    (mkStsliceProgramCase s!"fuzz/cellov/program/both-b{sliceBits}-r{sliceRefs}"
      #[]
      (mkStsliceBothOvProgram sliceBits sliceRefs sliceX), rng4)
  else if shape = 13 then
    (mkStsliceProgramCase "fuzz/ok/program/noise-below"
      #[]
      stsliceAppendProgramWithNoise, rng1)
  else if shape = 14 then
    let (exact, rng2) := randBool rng1
    if exact then
      (mkStsliceCase "fuzz/gas/exact"
        #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
        #[.pushInt (.num stsliceSetGasExact), .tonEnvOp .setGasLimit, stsliceInstr], rng2)
    else
      (mkStsliceCase "fuzz/gas/exact-minus-one"
        #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
        #[.pushInt (.num stsliceSetGasExactMinusOne), .tonEnvOp .setGasLimit, stsliceInstr], rng2)
  else
    (mkStsliceCase "fuzz/type/both-wrong" #[intV 1, .null], rng1)

def suite : InstrSuite where
  id := stsliceId
  unit := #[
    { name := "unit/direct/success-order-and-slice-remaining"
      run := do
        expectOkStack "ok/empty-slice-empty-builder"
          (runStsliceDirect #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty])
          #[.builder Builder.empty]

        let srcCell : Cell := Cell.mkOrdinary (natToBits 17 5) #[Cell.ofUInt 2 2]
        let srcSlice : Slice := Slice.ofCell srcCell
        let dstBuilder : Builder := { bits := natToBits 6 3, refs := #[Cell.ofUInt 1 1] }
        expectOkStack "ok/non-empty-append-tail-order"
          (runStsliceDirect #[.slice srcSlice, .builder dstBuilder])
          #[.builder (expectedStoredBuilder dstBuilder srcSlice)]

        let partialCell : Cell := Cell.mkOrdinary (natToBits 45 6) #[Cell.ofUInt 1 1, Cell.ofUInt 2 2]
        let partialSlice : Slice := { cell := partialCell, bitPos := 2, refPos := 1 }
        let partialBuilder : Builder := { bits := natToBits 3 2, refs := #[Cell.empty] }
        expectOkStack "ok/uses-slice-remainder-only"
          (runStsliceDirect #[.slice partialSlice, .builder partialBuilder])
          #[.builder (expectedStoredBuilder partialBuilder partialSlice)]

        let boundaryBuilder : Builder :=
          { bits := fullBuilder1023.bits
            refs := #[Cell.empty, Cell.ofUInt 1 1, Cell.ofUInt 2 2] }
        let boundarySlice : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[Cell.ofUInt 2 3])
        expectOkStack "ok/full-bits-refs3-plus-ref1"
          (runStsliceDirect #[.slice boundarySlice, .builder boundaryBuilder])
          #[.builder (expectedStoredBuilder boundaryBuilder boundarySlice)]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStsliceDirect #[.null, .slice (Slice.ofCell Cell.empty), .builder Builder.empty])
          #[.null, .builder Builder.empty] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStsliceDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runStsliceDirect #[.slice (Slice.ofCell Cell.empty)]) .stkUnd
        expectErr "underflow/one-builder"
          (runStsliceDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStsliceDirect #[.slice (Slice.ofCell Cell.empty), .null]) .typeChk
        expectErr "type/second-not-slice"
          (runStsliceDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/reversed-order-builder-below-slice-top"
          (runStsliceDirect #[.builder Builder.empty, .slice (Slice.ofCell Cell.empty)]) .typeChk
        expectErr "type/both-wrong"
          (runStsliceDirect #[intV 1, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-bits-and-refs"
      run := do
        let sliceBit1 : Slice := Slice.ofCell (Cell.ofUInt 1 1)
        expectErr "cellov/bits-full-builder-plus-one-bit"
          (runStsliceDirect #[.slice sliceBit1, .builder fullBuilder1023]) .cellOv

        let refs4 : Array Cell := #[Cell.empty, Cell.ofUInt 1 1, Cell.ofUInt 2 2, Cell.ofUInt 2 3]
        let bRef4 : Builder := { bits := #[], refs := refs4 }
        let sliceRef1 : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[Cell.empty])
        expectErr "cellov/refs-full-builder-plus-one-ref"
          (runStsliceDirect #[.slice sliceRef1, .builder bRef4]) .cellOv

        let bFullRef4 : Builder := { bits := fullBuilder1023.bits, refs := refs4 }
        let sliceBoth : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[Cell.empty])
        expectErr "cellov/full-builder-plus-bits-and-refs"
          (runStsliceDirect #[.slice sliceBoth, .builder bFullRef4]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-with-alias"
      run := do
        let canonicalOnly ←
          match assembleCp0 [stsliceInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits stsliceCanonicalOpcode 8 then
          pure ()
        else
          throw (IO.userError s!"stslice canonical encode mismatch: got bits {canonicalOnly.bits}")

        let canonicalCode ←
          match assembleCp0 [stsliceInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical sequence failed: {e}")
        let s0 := Slice.ofCell canonicalCode
        let s1 ← expectDecodeStep "decode/canonical-ce" s0 stsliceInstr 8
        let s2 ← expectDecodeStep "decode/canonical-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/canonical-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let aliasCode : Cell := Cell.mkOrdinary (natToBits stsliceAliasOpcode 16 ++ addCell.bits) #[]
        let a0 := Slice.ofCell aliasCode
        let a1 ← expectDecodeStep "decode/alias-cf12" a0 stsliceInstr 16
        let a2 ← expectDecodeStep "decode/alias-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/alias-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stslice-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStsliceDispatchFallback #[.null])
          #[.null, intV 436] }
  ]
  oracle := #[
    mkStsliceCase "ok/direct/empty-slice-empty-builder"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty],
    mkStsliceCase "ok/direct/deep-stack-preserve-below"
      #[.null, .slice (Slice.ofCell Cell.empty), .builder Builder.empty],

    mkStsliceProgramCase "ok/program/slice1-builder0" #[] (mkStsliceProgram 1 0 0 0 (.num 1)),
    mkStsliceProgramCase "ok/program/slice5-builder3-refs1" #[] stsliceAppendProgram,
    mkStsliceProgramCase "ok/program/slice8-builder7" #[] stsliceAppendBitsOnlyProgram,
    mkStsliceProgramCase "ok/program/slice-refs2-builder-refs1" #[] stsliceAppendRefsOnlyProgram,
    mkStsliceProgramCase "ok/program/mixed-bits-refs" #[] stsliceAppendMixedProgram,
    mkStsliceProgramCase "ok/program/mixed-bits-refs-alt" #[] stsliceAppendMixedAltProgram,
    mkStsliceProgramCase "ok/program/full-bits-empty-slice" #[] stsliceBoundaryFullBitsProgram,
    mkStsliceProgramCase "ok/program/full-refs-empty-slice" #[] stsliceBoundaryFullRefsProgram,
    mkStsliceProgramCase "ok/program/full-bits-refs3-plus-ref1" #[] stsliceBoundaryFullBitsRefs3ThenRefProgram,
    mkStsliceProgramCase "ok/program/refs4-bits1022-plus-bit1" #[] stsliceBoundaryRefs4Bits1022ThenBitProgram,
    mkStsliceProgramCase "ok/program/noise-below-preserved" #[] stsliceAppendProgramWithNoise,

    mkStsliceCase "underflow/empty" #[],
    mkStsliceCase "underflow/one-slice" #[.slice (Slice.ofCell Cell.empty)],
    mkStsliceCase "underflow/one-builder" #[.builder Builder.empty],
    mkStsliceCase "type/top-not-builder" #[.slice (Slice.ofCell Cell.empty), .null],
    mkStsliceCase "type/second-not-slice" #[.null, .builder Builder.empty],
    mkStsliceCase "type/reversed-order" #[.builder Builder.empty, .slice (Slice.ofCell Cell.empty)],
    mkStsliceCase "type/both-wrong" #[intV 1, .null],

    mkStsliceCase "gas/exact-cost-succeeds"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
      #[.pushInt (.num stsliceSetGasExact), .tonEnvOp .setGasLimit, stsliceInstr],
    mkStsliceCase "gas/exact-minus-one-out-of-gas"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
      #[.pushInt (.num stsliceSetGasExactMinusOne), .tonEnvOp .setGasLimit, stsliceInstr],

    mkStsliceProgramCase "cellov/program/bits-full-builder-slice1" #[] stsliceCellOvBitsProgram,
    mkStsliceProgramCase "cellov/program/bits-full-builder-slice7" #[] (mkStsliceBitsOvProgram 7 (.num 127)),
    mkStsliceProgramCase "cellov/program/refs-builder4-slice1" #[] stsliceCellOvRefsProgram,
    mkStsliceProgramCase "cellov/program/refs-builder4-slice2" #[] (mkStsliceRefsOvProgram 2),
    mkStsliceProgramCase "cellov/program/both-full-builder-slice1-ref1" #[] stsliceCellOvBothProgram,
    mkStsliceProgramCase "cellov/program/both-full-builder-slice4-ref2" #[] (mkStsliceBothOvProgram 4 2 (.num 15)),
    mkStsliceProgramCase "cellov/program/noise-below-full-builder"
      #[]
      (#[.pushNull] ++ stsliceCellOvBitsProgram)
  ]
  fuzz := #[
    { seed := 2026021011
      count := 500
      gen := genStsliceFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSLICE
