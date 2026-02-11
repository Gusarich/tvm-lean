import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDEQ

/-
SDEQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdEq.lean` (`.sdEq`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SDEQ` encode: `0xc705`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc705` decode to `.sdEq`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`register_cell_cmp_ops`, `exec_bin_cs_cmp`, `SDEQ`)
  - `/Users/daniil/Coding/ton/crypto/vm/cells/CellSlice.cpp`
    (`CellSlice::lex_cmp`)

Branch map used for this suite:
- execute dispatch: `.sdEq` vs fallback to `next`;
- stack path: first `popSlice` (top = `s2`), then second `popSlice` (`s1`);
- success path: push `-1` iff slices are equal by handler criterion, else `0`;
- error ordering: underflow/type behavior is inherited from pop order;
- opcode path: `SDEQ` exact opcode (`0xc705`), with neighbor decode boundaries.

Compatibility note:
- Lean currently compares `s1.toCellRemaining == s2.toCellRemaining` (bits + refs).
- C++ `SDEQ` uses `!lex_cmp`, where `lex_cmp` compares bits only.
- Oracle cases focus on shared outcomes; ref-only inequality is covered in direct unit checks.
-/

private def sdeqId : InstrId := { name := "SDEQ" }

private def sdeqInstr : Instr := .sdEq
private def sdlexcmpInstr : Instr := .sdLexCmp
private def sdpfxInstr : Instr := .sdPfx

private def sdeqOpcode : Nat := 0xc705
private def dispatchSentinel : Int := 705

private def mkSdeqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdeqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdeqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSdeqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkSdeqCase name stack program gasLimits fuel

private def runSdeqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdEq sdeqInstr stack

private def runSdeqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdEq instr (VM.push (intV dispatchSentinel)) stack

private def mkSdeqStack (s1 s2 : Slice) : Array Value :=
  #[.slice s1, .slice s2]

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 11 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 6 3) #[refLeafA]

private def sliceEmpty : Slice := mkSliceWithBitsRefs #[]
private def sliceBit0 : Slice := mkSliceWithBitsRefs #[false]
private def sliceBit1 : Slice := mkSliceWithBitsRefs #[true]

private def sliceBits8A : Slice := mkSliceWithBitsRefs (natToBits 0xa5 8)
private def sliceBits8FirstDiff : Slice := mkSliceWithBitsRefs (natToBits 0x25 8)
private def sliceBits8MidDiff : Slice := mkSliceWithBitsRefs (natToBits 0xad 8)
private def sliceBits8LastDiff : Slice := mkSliceWithBitsRefs (natToBits 0xa4 8)

private def sliceBits7Len : Slice := mkSliceWithBitsRefs (natToBits 0x52 7)
private def sliceBits8Len : Slice := mkSliceWithBitsRefs (natToBits 0x52 8)

private def sliceBits255A : Slice := mkSliceWithBitsRefs (stripeBits 255 0)
private def sliceBits255B : Slice := mkSliceWithBitsRefs (stripeBits 255 1)
private def sliceBits1023A : Slice := mkSliceWithBitsRefs (stripeBits 1023 0)
private def sliceBits1023B : Slice := mkSliceWithBitsRefs (stripeBits 1023 1)

private def sliceRef1EqA : Slice := mkSliceWithBitsRefs (natToBits 0x15 5) #[refLeafA]
private def sliceRef1EqB : Slice := mkSliceWithBitsRefs (natToBits 0x15 5) #[refLeafA]
private def sliceRef2EqA : Slice := mkSliceWithBitsRefs (natToBits 0x15 5) #[refLeafA, refLeafB]
private def sliceRef2EqB : Slice := mkSliceWithBitsRefs (natToBits 0x15 5) #[refLeafA, refLeafB]
private def sliceRef2BitDiff : Slice := mkSliceWithBitsRefs (natToBits 0x1d 5) #[refLeafA, refLeafB]
private def sliceRef2RefDiff : Slice := mkSliceWithBitsRefs (natToBits 0x15 5) #[refLeafA, refLeafC]

private def partialBase : Cell :=
  Cell.mkOrdinary (natToBits 717 10) #[refLeafA, refLeafB, refLeafC]

private def partialLeft : Slice :=
  { cell := partialBase, bitPos := 3, refPos := 1 }

private def partialEquivalent : Slice :=
  Slice.ofCell partialLeft.toCellRemaining

private def partialBitMismatch : Slice :=
  mkSliceWithBitsRefs (natToBits 85 partialLeft.bitsRemaining) #[refLeafB, refLeafC]

private def partialRefMismatch : Slice :=
  mkSliceWithBitsRefs (partialLeft.readBits partialLeft.bitsRemaining) #[refLeafB]

private def sdeqSetGasExact : Int :=
  computeExactGasBudget sdeqInstr

private def sdeqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdeqInstr

private structure EqCheck where
  label : String
  left : Slice
  right : Slice
  expected : Int

private def sdeqLenPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023]

private def pickSdeqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (sdeqLenPool.size - 1)
    (sdeqLenPool[idx]!, rng2)
  else if mode ≤ 6 then
    randNat rng1 0 96
  else
    randNat rng1 97 1023

private def pickSdeqRefsMixed (rng0 : StdGen) : Nat × StdGen :=
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
    (intV 41, rng1)
  else
    (.cell refLeafB, rng1)

private def pickBadNonSliceValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    (intV 7, "int", rng1)
  else if pick = 2 then
    (.cell refLeafC, "cell", rng1)
  else if pick = 3 then
    (.builder Builder.empty, "builder", rng1)
  else if pick = 4 then
    (.tuple #[], "tuple", rng1)
  else
    (.cont (.quit 0), "cont", rng1)

private def genSdeqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (bits, rng2) := pickSdeqBitsMixed rng1
    let (refs, rng3) := pickSdeqRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    let s := mkFuzzSlice bits refs phase
    (mkSdeqCase s!"fuzz/ok/equal/bits-{bits}/refs-{refs}" (mkSdeqStack s s), rng4)
  else if shape = 1 then
    let (bits, rng2) := pickSdeqBitsMixed rng1
    let (refsA, rng3) := pickSdeqRefsMixed rng2
    let (refsB, rng4) := pickSdeqRefsMixed rng3
    let (phase, rng5) := randNat rng4 0 3
    let sBits := stripeBits bits phase
    let s1 := mkSliceWithBitsRefs sBits (mkRefsByCount refsA)
    let s2 := mkSliceWithBitsRefs sBits (mkRefsByCount refsB)
    (mkSdeqCase s!"fuzz/ok/equal-bits-diff-refs/bits-{bits}/ra-{refsA}/rb-{refsB}" (mkSdeqStack s1 s2), rng5)
  else if shape = 2 then
    let (bits, rng2) := pickSdeqBitsMixed rng1
    let (refs, rng3) := pickSdeqRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    let s1 := mkFuzzSlice bits refs phase
    let s2 := mkFuzzSlice bits refs (phase + 1)
    (mkSdeqCase s!"fuzz/ok/not-equal/bits-{bits}/refs-{refs}" (mkSdeqStack s1 s2), rng4)
  else if shape = 3 then
    let (bits, rng2) := pickSdeqBitsMixed rng1
    let bits' := if bits = 1023 then 1022 else bits
    let (refs, rng3) := pickSdeqRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    let s1 := mkFuzzSlice bits' refs phase
    let s2 := mkFuzzSlice (bits' + 1) refs phase
    (mkSdeqCase s!"fuzz/ok/len-mismatch/b1-{bits'}/b2-{bits' + 1}/refs-{refs}" (mkSdeqStack s1 s2), rng4)
  else if shape = 4 then
    let (bits, rng2) := pickSdeqBitsMixed rng1
    let (refs, rng3) := pickSdeqRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    let (noise, rng5) := pickNoiseValue rng4
    let s1 := mkFuzzSlice bits refs phase
    let s2 := mkFuzzSlice bits refs phase
    (mkSdeqCase s!"fuzz/ok/deep/bits-{bits}/refs-{refs}" #[noise, .slice s1, .slice s2], rng5)
  else if shape = 5 then
    (mkSdeqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    let (bits, rng2) := pickSdeqBitsMixed rng1
    let s := mkFuzzSlice bits 0 0
    (mkSdeqCase s!"fuzz/underflow/one-slice/bits-{bits}" #[.slice s], rng2)
  else if shape = 7 then
    let (bad, tag, rng2) := pickBadNonSliceValue rng1
    (mkSdeqCase s!"fuzz/type/top-{tag}" #[.slice sliceEmpty, bad], rng2)
  else if shape = 8 then
    let (bad, tag, rng2) := pickBadNonSliceValue rng1
    (mkSdeqCase s!"fuzz/type/second-{tag}" #[bad, .slice sliceBit1], rng2)
  else if shape = 9 then
    let (bad, tag, rng2) := pickBadNonSliceValue rng1
    (mkSdeqCase s!"fuzz/type/one-{tag}" #[bad], rng2)
  else if shape = 10 then
    let (bad, tag, rng2) := pickBadNonSliceValue rng1
    let s1 := mkFuzzSlice 8 1 0
    let s2 := mkFuzzSlice 8 1 1
    (mkSdeqCase s!"fuzz/type/deep-top-{tag}" #[.slice s1, .slice s2, bad], rng2)
  else
    let bits : Nat := 64
    let sBits := stripeBits bits 1
    let s1 := mkSliceWithBitsRefs sBits #[refLeafA]
    let s2 := mkSliceWithBitsRefs sBits #[refLeafB, refLeafC]
    (mkSdeqCase "fuzz/ok/equal-bits-heavy-refs" (mkSdeqStack s1 s2), rng1)

def suite : InstrSuite where
  id := sdeqId
  unit := #[
    { name := "unit/direct/equality-matrix-bits-and-refs"
      run := do
        let checks : Array EqCheck :=
          #[
            { label := "eq/empty", left := sliceEmpty, right := sliceEmpty, expected := -1 },
            { label := "eq/bit0", left := sliceBit0, right := sliceBit0, expected := -1 },
            { label := "eq/bit1", left := sliceBit1, right := sliceBit1, expected := -1 },
            { label := "eq/bits8", left := sliceBits8A, right := sliceBits8A, expected := -1 },
            { label := "eq/bits255", left := sliceBits255A, right := sliceBits255A, expected := -1 },
            { label := "eq/bits1023", left := sliceBits1023A, right := sliceBits1023A, expected := -1 },
            { label := "eq/with-ref", left := sliceRef1EqA, right := sliceRef1EqB, expected := -1 },
            { label := "eq/with-two-refs", left := sliceRef2EqA, right := sliceRef2EqB, expected := -1 },

            { label := "neq/first-bit", left := sliceBits8A, right := sliceBits8FirstDiff, expected := 0 },
            { label := "neq/mid-bit", left := sliceBits8A, right := sliceBits8MidDiff, expected := 0 },
            { label := "neq/last-bit", left := sliceBits8A, right := sliceBits8LastDiff, expected := 0 },
            { label := "neq/len-7-vs-8", left := sliceBits7Len, right := sliceBits8Len, expected := 0 },
            { label := "neq/bits255", left := sliceBits255A, right := sliceBits255B, expected := 0 },
            { label := "neq/bits1023", left := sliceBits1023A, right := sliceBits1023B, expected := 0 },
            { label := "neq/ref-count", left := sliceRef2EqA, right := sliceRef1EqA, expected := 0 },
            { label := "neq/ref-content", left := sliceRef2EqA, right := sliceRef2RefDiff, expected := 0 }
          ]
        for c in checks do
          expectOkStack c.label
            (runSdeqDirect (mkSdeqStack c.left c.right))
            #[intV c.expected] }
    ,
    { name := "unit/direct/partial-slice-remainder-and-stack-order"
      run := do
        expectOkStack "eq/partial-vs-equivalent-full-remainder"
          (runSdeqDirect (mkSdeqStack partialLeft partialEquivalent))
          #[intV (-1)]
        expectOkStack "neq/partial-vs-bit-mismatch"
          (runSdeqDirect (mkSdeqStack partialLeft partialBitMismatch))
          #[intV 0]
        expectOkStack "neq/partial-vs-ref-mismatch"
          (runSdeqDirect (mkSdeqStack partialLeft partialRefMismatch))
          #[intV 0]
        expectOkStack "ok/deep-stack-preserve-below"
          (runSdeqDirect #[.null, intV 44, .slice partialLeft, .slice partialEquivalent])
          #[.null, intV 44, intV (-1)] }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runSdeqDirect #[]) .stkUnd
        expectErr "underflow/one-slice" (runSdeqDirect #[.slice sliceBit1]) .stkUnd

        expectErr "type/one-int" (runSdeqDirect #[intV 7]) .typeChk
        expectErr "type/top-null" (runSdeqDirect #[.slice sliceBit0, .null]) .typeChk
        expectErr "type/top-int" (runSdeqDirect #[.slice sliceBit0, intV 1]) .typeChk
        expectErr "type/top-cell" (runSdeqDirect #[.slice sliceBit0, .cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runSdeqDirect #[.slice sliceBit0, .builder Builder.empty]) .typeChk

        expectErr "type/second-null-after-valid-top"
          (runSdeqDirect #[.null, .slice sliceBit1]) .typeChk
        expectErr "type/second-cell-after-valid-top"
          (runSdeqDirect #[.cell Cell.empty, .slice sliceBit1]) .typeChk
        expectErr "error-order/top-type-before-second-pop"
          (runSdeqDirect #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/opcode/decode-assemble-and-invalid-neighbor"
      run := do
        let program : Array Instr := #[sdeqInstr, sdlexcmpInstr, sdpfxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble failed: {e}")

        if code.bits.extract 0 16 = natToBits sdeqOpcode 16 then
          pure ()
        else
          throw (IO.userError "encode/sdeq: expected first instruction word 0xc705")

        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdeq" s0 sdeqInstr 16
        let s2 ← expectDecodeStep "decode/sdlexcmp-neighbor" s1 sdlexcmpInstr 16
        let s3 ← expectDecodeStep "decode/sdpfx-neighbor" s2 sdpfxInstr 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        let invalid := mkSliceFromBits (natToBits 0xc706 16)
        match decodeCp0WithBits invalid with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"decode/invalid-0xc706: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError
              s!"decode/invalid-0xc706: expected failure, got {reprStr instr} ({bits} bits)") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-sdeq-add"
          (runSdeqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-sdeq-sdlexcmp"
          (runSdeqDispatchFallback .sdLexCmp #[intV 7])
          #[intV 7, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdeqCase "ok/equal/empty" (mkSdeqStack sliceEmpty sliceEmpty),
    mkSdeqCase "ok/equal/bit1" (mkSdeqStack sliceBit1 sliceBit1),
    mkSdeqCase "ok/equal/bits8" (mkSdeqStack sliceBits8A sliceBits8A),
    mkSdeqCase "ok/equal/bits255-pattern" (mkSdeqStack sliceBits255A sliceBits255A),
    mkSdeqCase "ok/equal/bits1023-pattern" (mkSdeqStack sliceBits1023A sliceBits1023A),
    mkSdeqCase "ok/equal/with-one-ref" (mkSdeqStack sliceRef1EqA sliceRef1EqB),
    mkSdeqCase "ok/equal/with-two-refs" (mkSdeqStack sliceRef2EqA sliceRef2EqB),

    mkSdeqCase "ok/not-equal/first-bit-diff" (mkSdeqStack sliceBits8A sliceBits8FirstDiff),
    mkSdeqCase "ok/not-equal/mid-bit-diff" (mkSdeqStack sliceBits8A sliceBits8MidDiff),
    mkSdeqCase "ok/not-equal/last-bit-diff" (mkSdeqStack sliceBits8A sliceBits8LastDiff),
    mkSdeqCase "ok/not-equal/len-7-vs-8" (mkSdeqStack sliceBits7Len sliceBits8Len),
    mkSdeqCase "ok/not-equal/empty-vs-nonempty" (mkSdeqStack sliceEmpty sliceBit0),
    mkSdeqCase "ok/not-equal/bits255-pattern" (mkSdeqStack sliceBits255A sliceBits255B),
    mkSdeqCase "ok/not-equal/bits1023-pattern" (mkSdeqStack sliceBits1023A sliceBits1023B),
    mkSdeqCase "ok/not-equal/with-refs-and-bit-diff" (mkSdeqStack sliceRef2EqA sliceRef2BitDiff),

    mkSdeqCase "ok/deep-stack/null-below"
      #[.null, .slice sliceBits8A, .slice sliceBits8A],
    mkSdeqCase "ok/deep-stack/int-cell-below"
      #[intV (-9), .cell refLeafC, .slice sliceBits8A, .slice sliceBits8LastDiff],

    mkSdeqCase "underflow/empty" #[],
    mkSdeqCase "underflow/one-slice" #[.slice sliceBit0],

    mkSdeqCase "type/top-null" #[.slice sliceBit1, .null],
    mkSdeqCase "type/top-int" #[.slice sliceBit1, intV 1],
    mkSdeqCase "type/top-cell" #[.slice sliceBit1, .cell Cell.empty],
    mkSdeqCase "type/top-builder" #[.slice sliceBit1, .builder Builder.empty],
    mkSdeqCase "type/second-null-after-valid-top" #[.null, .slice sliceBit1],
    mkSdeqCase "type/second-cell-after-valid-top" #[.cell Cell.empty, .slice sliceBit1],

    mkSdeqProgramCase "gas/exact-cost-succeeds"
      (mkSdeqStack sliceBits8A sliceBits8LastDiff)
      #[.pushInt (.num sdeqSetGasExact), .tonEnvOp .setGasLimit, sdeqInstr],
    mkSdeqProgramCase "gas/exact-minus-one-out-of-gas"
      (mkSdeqStack sliceBits8A sliceBits8LastDiff)
      #[.pushInt (.num sdeqSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdeqInstr]
  ]
  fuzz := #[
    { seed := 2026021115
      count := 500
      gen := genSdeqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDEQ
