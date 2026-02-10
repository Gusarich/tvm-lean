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

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSdeqStack (s1 s2 : Slice) : Array Value :=
  #[.slice s1, .slice s2]

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
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
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDEQ
