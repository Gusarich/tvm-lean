import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDFIRST

/-
SDFIRST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdFirst`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc703` decode to `.cellOp .sdFirst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.cellOp .sdFirst` encode as `0xc703`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`SDFIRST`, `prefetch_long(1) == -1` at opcode `0xc703`).

Branch map used for this suite:
- dispatch guard in instruction-local handler (`.cellOp .sdFirst` vs fallback);
- `checkUnderflow 1` then `popSlice` (type-check on top value);
- boolean result split: first remaining bit is `1` -> push `-1`, otherwise push `0`;
- decode/assemble boundary at exact opcode `0xc703` with nearby `0xc702`/`0xc704`.
-/

private def sdFirstId : InstrId := { name := "SDFIRST" }

private def sdFirstInstr : Instr :=
  .cellOp .sdFirst

private def sdSfxInstr : Instr :=
  .cellOp .sdSfx

private def dispatchSentinel : Int := 53003

private def sdFirstOpcode : Nat := 0xc703

private def execInstrCellOpSdFirstOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdFirst => execCellOpExt .sdFirst next
  | _ => next

private def mkSdFirstCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdFirstInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdFirstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdFirstDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSdFirstOnly sdFirstInstr stack

private def runSdFirstDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSdFirstOnly instr (VM.push (intV dispatchSentinel)) stack

private def expectedSdFirstInt (s : Slice) : Int :=
  if s.haveBits 1 && s.cell.bits[s.bitPos]! then -1 else 0

private def runSdFirstModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.isEmpty then
    throw .stkUnd
  let top := stack.back!
  let below := stack.extract 0 (stack.size - 1)
  match top with
  | .slice s =>
      pure (below.push (intV (expectedSdFirstInt s)))
  | _ =>
      throw .typeChk

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[]

private def bitsLeadTrue256 : BitString :=
  #[true] ++ stripeBits 255 0

private def bitsLeadFalse256 : BitString :=
  #[false] ++ stripeBits 255 1

private def bitsLeadTrue1023 : BitString :=
  #[true] ++ stripeBits 1022 0

private def bitsLeadFalse1023 : BitString :=
  #[false] ++ stripeBits 1022 1

private def sliceEmpty : Slice := mkSliceWithBitsRefs #[]
private def sliceSingleFalse : Slice := mkSliceWithBitsRefs #[false]
private def sliceSingleTrue : Slice := mkSliceWithBitsRefs #[true]
private def sliceLeadTrue5 : Slice := mkSliceWithBitsRefs #[true, false, true, false, true]
private def sliceLeadFalse5 : Slice := mkSliceWithBitsRefs #[false, true, false, true, false]
private def sliceLeadTrue8 : Slice := mkSliceWithBitsRefs #[true, false, true, false, true, false, true, false]
private def sliceLeadFalse8 : Slice := mkSliceWithBitsRefs #[false, true, false, true, false, true, false, true]
private def sliceLeadTrue256 : Slice := mkSliceWithBitsRefs bitsLeadTrue256
private def sliceLeadFalse256 : Slice := mkSliceWithBitsRefs bitsLeadFalse256
private def sliceLeadTrue1023 : Slice := mkSliceWithBitsRefs bitsLeadTrue1023
private def sliceLeadFalse1023 : Slice := mkSliceWithBitsRefs bitsLeadFalse1023
private def sliceRefsOnly : Slice := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
private def sliceBitsRefsLeadTrue : Slice := mkSliceWithBitsRefs #[true, false, false, true] #[refLeafA, refLeafB]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary #[false, true, false, true, true, false] #[refLeafA, refLeafB, refLeafC]

private def partialSliceBitPos1 : Slice :=
  { cell := partialCursorCell, bitPos := 1, refPos := 0 }

private def partialSliceBitPos2 : Slice :=
  { cell := partialCursorCell, bitPos := 2, refPos := 1 }

private def partialSliceAtEnd : Slice :=
  { cell := partialCursorCell, bitPos := partialCursorCell.bits.size, refPos := 2 }

private def sdFirstSetGasExact : Int :=
  computeExactGasBudget sdFirstInstr

private def sdFirstSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdFirstInstr

private def sdFirstLenPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023]

private def pickSdFirstBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (sdFirstLenPool.size - 1)
    (sdFirstLenPool[idx]!, rng2)
  else if mode ≤ 6 then
    randNat rng1 0 96
  else
    randNat rng1 97 1023

private def pickSdFirstRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (4, rng1)
  else
    randNat rng1 0 4

private def mkRefsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, Cell.empty]

private def mkFuzzSlice (bits refs : Nat) (phase : Nat := 0) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase) (mkRefsByCount refs)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    (intV (-3), rng1)
  else
    (.cell refLeafB, rng1)

private def pickBadTopValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    (intV 11, "int", rng1)
  else if pick = 2 then
    (.cell refLeafA, "cell", rng1)
  else if pick = 3 then
    (.builder Builder.empty, "builder", rng1)
  else
    (.tuple #[], "tuple", rng1)

private def sskipfirstInstr : Instr := .cellOp .sskipfirst

private def genSdFirstFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  if shape = 0 then
    (mkSdFirstCase "fuzz/ok/empty" #[.slice (mkFuzzSlice 0 0)], rng1)
  else if shape = 1 then
    let (bits, rng2) := pickSdFirstBitsMixed rng1
    let (refs, rng3) := pickSdFirstRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    (mkSdFirstCase s!"fuzz/ok/full/bits-{bits}/refs-{refs}/phase-{phase}"
      #[.slice (mkFuzzSlice bits refs phase)], rng4)
  else if shape = 2 then
    let (bits, rng2) := pickSdFirstBitsMixed rng1
    let (refs, rng3) := pickSdFirstRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    let (noise, rng5) := pickNoiseValue rng4
    (mkSdFirstCase s!"fuzz/ok/deep/bits-{bits}/refs-{refs}"
      #[noise, .slice (mkFuzzSlice bits refs phase)], rng5)
  else if shape = 3 then
    let (bits, rng2) := pickSdFirstBitsMixed rng1
    let (refs, rng3) := pickSdFirstRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    let (skipBits, rng5) := randNat rng4 0 bits
    let (skipRefs, rng6) := randNat rng5 0 refs
    (mkSdFirstCase s!"fuzz/ok/cursor/skipb-{skipBits}/skipr-{skipRefs}/bits-{bits}/refs-{refs}"
      #[.slice (mkFuzzSlice bits refs phase), intV (Int.ofNat skipBits), intV (Int.ofNat skipRefs)]
      #[sskipfirstInstr, sdFirstInstr], rng6)
  else if shape = 4 then
    (mkSdFirstCase "fuzz/underflow/empty" #[], rng1)
  else
    let (bad, tag, rng2) := pickBadTopValue rng1
    if shape = 5 then
      (mkSdFirstCase s!"fuzz/type/top-{tag}" #[bad], rng2)
    else
      let (bits, rng3) := pickSdFirstBitsMixed rng2
      let (refs, rng4) := pickSdFirstRefsMixed rng3
      let (phase, rng5) := randNat rng4 0 1
      (mkSdFirstCase s!"fuzz/type/deep-top-{tag}"
        #[.slice (mkFuzzSlice bits refs phase), bad], rng5)

def suite : InstrSuite where
  id := { name := "SDFIRST" }
  unit := #[
    { name := "unit/direct/first-bit-semantic-and-stack-shape"
      run := do
        let checks : Array (String × Slice × Int) :=
          #[
            ("empty-slice", sliceEmpty, 0),
            ("single-false", sliceSingleFalse, 0),
            ("single-true", sliceSingleTrue, -1),
            ("lead-true-5", sliceLeadTrue5, -1),
            ("lead-false-5", sliceLeadFalse5, 0),
            ("refs-only-empty-bits", sliceRefsOnly, 0),
            ("bits-and-refs-lead-true", sliceBitsRefsLeadTrue, -1)
          ]
        for (name, s, expected) in checks do
          expectOkStack s!"{name}"
            (runSdFirstDirect #[.slice s])
            #[intV expected]

        expectOkStack "deep-stack/preserve-below-values"
          (runSdFirstDirect #[.null, intV 77, .slice sliceLeadTrue8])
          #[.null, intV 77, intV (-1)]

        expectOkStack "deep-stack/preserve-below-cell"
          (runSdFirstDirect #[.cell refLeafA, .slice sliceLeadFalse8])
          #[.cell refLeafA, intV 0] }
    ,
    { name := "unit/direct/partial-cursor-selects-current-bit"
      run := do
        expectOkStack "partial/bitpos1-first-bit-true"
          (runSdFirstDirect #[.slice partialSliceBitPos1])
          #[intV (-1)]

        expectOkStack "partial/bitpos2-first-bit-false"
          (runSdFirstDirect #[.slice partialSliceBitPos2])
          #[intV 0]

        expectOkStack "partial/at-end-no-bits-left"
          (runSdFirstDirect #[.slice partialSliceAtEnd])
          #[intV 0]

        expectOkStack "partial/refpos-does-not-affect-bit-result"
          (runSdFirstDirect #[.slice { partialSliceBitPos1 with refPos := 2 }])
          #[intV (-1)] }
    ,
    { name := "unit/direct/underflow-type-and-order"
      run := do
        expectErr "underflow/empty"
          (runSdFirstDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runSdFirstDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runSdFirstDirect #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runSdFirstDirect #[.cell refLeafA]) .typeChk
        expectErr "type/top-builder"
          (runSdFirstDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-empty-tuple"
          (runSdFirstDirect #[.tuple #[]]) .typeChk

        expectErr "type/order-top-null-over-valid-slice"
          (runSdFirstDirect #[.slice sliceSingleTrue, .null]) .typeChk
        expectErr "type/order-top-cell-over-valid-slice"
          (runSdFirstDirect #[.slice sliceSingleTrue, .cell refLeafB]) .typeChk }
    ,
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-slice", #[.slice sliceEmpty]),
            ("ok/single-true", #[.slice sliceSingleTrue]),
            ("ok/single-false", #[.slice sliceSingleFalse]),
            ("ok/partial-bitpos1", #[.slice partialSliceBitPos1]),
            ("ok/partial-at-end", #[.slice partialSliceAtEnd]),
            ("ok/deep", #[.null, intV 9, .slice sliceLeadFalse8]),
            ("err/underflow", #[]),
            ("err/type-null", #[.null]),
            ("err/type-order", #[.slice sliceSingleTrue, .null])
          ]
        for (name, stack) in samples do
          expectSameOutcome s!"model/{name}"
            (runSdFirstDirect stack)
            (runSdFirstModel stack) }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let canonical ←
          match assembleCp0 [sdFirstInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/canonical failed: {e}")
        if canonical.bits = natToBits sdFirstOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/canonical: expected opcode 0xc703, got bits {canonical.bits}")

        let program : Array Instr :=
          #[.sdempty, .srempty, sdFirstInstr, .sdLexCmp, sdSfxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdempty-neighbor" s0 .sdempty 16
        let s2 ← expectDecodeStep "decode/srempty-neighbor" s1 .srempty 16
        let s3 ← expectDecodeStep "decode/sdfirst" s2 sdFirstInstr 16
        let s4 ← expectDecodeStep "decode/sdlexcmp-neighbor" s3 .sdLexCmp 16
        let s5 ← expectDecodeStep "decode/sdsfx-neighbor" s4 sdSfxInstr 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/sequence-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xc702 16
            ++ natToBits sdFirstOpcode 16
            ++ natToBits 0xc704 16
            ++ natToBits 0xc70c 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-srempty" r0 .srempty 16
        let r2 ← expectDecodeStep "decode/raw-sdfirst" r1 sdFirstInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdlexcmp" r2 .sdLexCmp 16
        let r4 ← expectDecodeStep "decode/raw-sdsfx" r3 sdSfxInstr 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdfirst-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runSdFirstDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-sdempty"
          (runSdFirstDispatchFallback .sdempty #[intV 7])
          #[intV 7, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-sdsfx"
          (runSdFirstDispatchFallback sdSfxInstr #[.slice sliceSingleTrue])
          #[.slice sliceSingleTrue, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdFirstCase "ok/empty-slice" #[.slice sliceEmpty],
    mkSdFirstCase "ok/single-false" #[.slice sliceSingleFalse],
    mkSdFirstCase "ok/single-true" #[.slice sliceSingleTrue],
    mkSdFirstCase "ok/lead-true-5" #[.slice sliceLeadTrue5],
    mkSdFirstCase "ok/lead-false-5" #[.slice sliceLeadFalse5],
    mkSdFirstCase "ok/lead-true-8" #[.slice sliceLeadTrue8],
    mkSdFirstCase "ok/lead-false-8" #[.slice sliceLeadFalse8],
    mkSdFirstCase "ok/lead-true-256" #[.slice sliceLeadTrue256],
    mkSdFirstCase "ok/lead-false-256" #[.slice sliceLeadFalse256],
    mkSdFirstCase "ok/lead-true-1023" #[.slice sliceLeadTrue1023],
    mkSdFirstCase "ok/lead-false-1023" #[.slice sliceLeadFalse1023],
    mkSdFirstCase "ok/refs-only-empty-bits" #[.slice sliceRefsOnly],
    mkSdFirstCase "ok/bits-and-refs-lead-true" #[.slice sliceBitsRefsLeadTrue],
    mkSdFirstCase "ok/deep-stack-preserve-below"
      #[.null, intV 42, .slice sliceLeadFalse8],

    mkSdFirstCase "underflow/empty" #[],
    mkSdFirstCase "type/top-null" #[.null],
    mkSdFirstCase "type/top-int" #[intV 11],
    mkSdFirstCase "type/top-cell" #[.cell refLeafA],
    mkSdFirstCase "type/top-builder" #[.builder Builder.empty],
    mkSdFirstCase "type/top-empty-tuple" #[.tuple #[]],
    mkSdFirstCase "type/order-top-null-over-slice" #[.slice sliceSingleTrue, .null],
    mkSdFirstCase "type/order-top-cell-over-slice" #[.slice sliceSingleTrue, .cell refLeafB],

    mkSdFirstCase "gas/exact-cost-succeeds"
      #[.slice sliceSingleTrue]
      #[.pushInt (.num sdFirstSetGasExact), .tonEnvOp .setGasLimit, sdFirstInstr],
    mkSdFirstCase "gas/exact-minus-one-out-of-gas"
      #[.slice sliceSingleTrue]
      #[.pushInt (.num sdFirstSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdFirstInstr]
  ]
  fuzz := #[
    { seed := 2026021114
      count := 500
      gen := genSdFirstFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDFIRST
