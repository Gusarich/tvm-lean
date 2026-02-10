import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PUSHSLICE_LONG

/-
PUSHSLICE_LONG branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PushSliceConst.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (18-bit `0x8d` arm)
  - `TvmLean/Model/Basics/Bytes.lean` (`bitsStripTrailingMarker`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_push_slice_r2`)

Branch map covered by this suite:
- execution branch (`.pushSliceConst s` => push `s`, otherwise fallback);
- decode guard chain for `PUSHSLICE_LONG`:
  `haveBits 18` -> prefix `0x8d` -> refs range (`0..4`) ->
  inline bits availability (`len7 * 8 + 6`) -> inline refs availability;
- decode boundaries with neighboring families:
  `PUSHSLICE` (`0x8b`, 12-bit), `PUSHSLICE_REFS` (`0x8c`, 15-bit),
  `PUSHSLICE_LONG` (`0x8d`, 18-bit).

Key risks covered:
- payload marker stripping behavior (including non-canonical all-zero raw payload);
- refs boundary (`0` and `4`) and reserved refs (`5..7`);
- truncated prefix/data and missing-inline-refs decode rejections;
- cursor-relative decode correctness (`bitPos`/`refPos` offsets).
-/

private def dispatchSentinel : Int := 8413

private def pushsliceLongPrefix : Nat := 0x8d

private def runPushSliceDirect (s : Slice) (stack : Array Value := #[]) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushSliceConst (.pushSliceConst s) stack

private def runPushSliceDispatch (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushSliceConst instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0b0111 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0b11001 5) #[Cell.empty]

private def refLeafD : Cell :=
  Cell.mkOrdinary (natToBits 0b111000 6) #[]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 32 1) #[refLeafA, refLeafB, refLeafC]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 7, refPos := 1 }

private def longDataBits (len7 : Nat) : Nat :=
  len7 * 8 + 6

private def longWord (refs len7 : Nat) : Nat :=
  (pushsliceLongPrefix <<< 10) + ((refs &&& 0x7) <<< 7) + (len7 &&& 0x7f)

private def mkMarkedRawForWidth (payload : BitString) (width : Nat) : IO BitString := do
  if payload.size + 1 > width then
    throw (IO.userError
      s!"mkMarkedRawForWidth: payload={payload.size} exceeds width={width} (needs marker bit)")
  pure (payload ++ #[true] ++ Array.replicate (width - payload.size - 1) false)

private def mkLongRawMarked (payload : BitString) (len7 : Nat) : IO BitString :=
  mkMarkedRawForWidth payload (longDataBits len7)

private def mkLongBits (refs len7 : Nat) (raw : BitString) : IO BitString := do
  let want := longDataBits len7
  if raw.size != want then
    throw (IO.userError s!"mkLongBits: raw size={raw.size}, expected={want} for len7={len7}")
  pure (natToBits (longWord refs len7) 18 ++ raw)

private def mkLongSlice
    (refs len7 : Nat)
    (raw : BitString)
    (codeRefs : Array Cell := #[])
    (tailBits : BitString := #[]) : IO Slice := do
  let bits ← mkLongBits refs len7 raw
  pure (Slice.ofCell (Cell.mkOrdinary (bits ++ tailBits) codeRefs))

private def expectedLongInstr (raw : BitString) (refs : Array Cell := #[]) : Instr :=
  .pushSliceConst (Slice.ofCell (Cell.mkOrdinary (bitsStripTrailingMarker raw) refs))

private def expectDecodeErr (label : String) (s : Slice) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")

private def expectCursor (label : String) (s : Slice) (bits refs : Nat) : IO Unit := do
  if s.bitsRemaining != bits then
    throw (IO.userError s!"{label}: expected bitsRemaining={bits}, got {s.bitsRemaining}")
  if s.refsRemaining != refs then
    throw (IO.userError s!"{label}: expected refsRemaining={refs}, got {s.refsRemaining}")

private def mkPushsliceShortBits (args4 : Nat) (raw : BitString) : IO BitString := do
  let a : Nat := args4 &&& 0xf
  let want : Nat := a * 8 + 4
  if raw.size != want then
    throw (IO.userError s!"mkPushsliceShortBits: raw size={raw.size}, expected={want}")
  pure (natToBits 0x8b 8 ++ natToBits a 4 ++ raw)

private def mkPushsliceRefsBits (r bits5 : Nat) (raw : BitString) : IO BitString := do
  let r2 : Nat := r &&& 0x3
  let b5 : Nat := bits5 &&& 0x1f
  let want : Nat := b5 * 8 + 1
  if raw.size != want then
    throw (IO.userError s!"mkPushsliceRefsBits: raw size={raw.size}, expected={want}")
  let w15 : Nat := (0x8c <<< 7) + (r2 <<< 5) + b5
  pure (natToBits w15 15 ++ raw)

private def addOpcodeBits : BitString :=
  natToBits 0xa0 8

def suite : InstrSuite where
  id := { name := "PUSHSLICE_LONG" }
  unit := #[
    { name := "unit/exec/push-empty-slice-on-empty-stack"
      run := do
        let s := mkSliceWithBitsRefs #[] #[]
        expectOkStack "exec/empty"
          (runPushSliceDirect s)
          #[.slice s] }
    ,
    { name := "unit/exec/push-bits-only"
      run := do
        let s := mkSliceWithBitsRefs (stripeBits 11 0) #[]
        expectOkStack "exec/bits-only"
          (runPushSliceDirect s)
          #[.slice s] }
    ,
    { name := "unit/exec/push-refs-only"
      run := do
        let s := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB, refLeafC]
        expectOkStack "exec/refs-only"
          (runPushSliceDirect s)
          #[.slice s] }
    ,
    { name := "unit/exec/push-bits-and-refs"
      run := do
        let s := mkSliceWithBitsRefs (stripeBits 19 1) #[refLeafA, refLeafD]
        expectOkStack "exec/bits-and-refs"
          (runPushSliceDirect s)
          #[.slice s] }
    ,
    { name := "unit/exec/push-partial-cursor-slice"
      run := do
        expectOkStack "exec/partial-cursor"
          (runPushSliceDirect partialCursorSlice)
          #[.slice partialCursorSlice] }
    ,
    { name := "unit/exec/preserve-deep-stack"
      run := do
        let s := mkSliceWithBitsRefs (stripeBits 9 1) #[refLeafA]
        expectOkStack "exec/deep-stack"
          (runPushSliceDirect s #[.null, intV 7, .cell refLeafC])
          #[.null, intV 7, .cell refLeafC, .slice s] }
    ,
    { name := "unit/exec/preserve-mixed-values-below"
      run := do
        let s := mkSliceWithBitsRefs (stripeBits 6 0) #[]
        expectOkStack "exec/mixed-below"
          (runPushSliceDirect s #[.builder Builder.empty, .tuple #[], .cont (.quit 0)])
          #[.builder Builder.empty, .tuple #[], .cont (.quit 0), .slice s] }
    ,
    { name := "unit/dispatch/fallback-on-non-flow-instr"
      run := do
        expectOkStack "dispatch/add-fallback"
          (runPushSliceDispatch .add #[intV 1])
          #[intV 1, intV dispatchSentinel] }
    ,
    { name := "unit/dispatch/fallback-on-other-flow-instr"
      run := do
        expectOkStack "dispatch/pushref-fallback"
          (runPushSliceDispatch (.pushRef refLeafA) #[.null])
          #[.null, intV dispatchSentinel] }
    ,
    { name := "unit/dispatch/handles-pushsliceconst-no-fallback"
      run := do
        let s := mkSliceWithBitsRefs (stripeBits 5 1) #[refLeafB]
        expectOkStack "dispatch/pushslice-handled"
          (runPushSliceDispatch (.pushSliceConst s) #[.null])
          #[.null, .slice s] }
    ,
    { name := "unit/decode/len0-marker-only-decodes-empty"
      run := do
        let raw ← mkLongRawMarked #[] 0
        let s0 ← mkLongSlice 0 0 raw
        let s1 ← expectDecodeStep "decode/len0/marker-only" s0 (expectedLongInstr raw #[]) 18
        expectCursor "decode/len0/marker-only/rest" s1 0 0 }
    ,
    { name := "unit/decode/len0-max-payload5"
      run := do
        let payload := stripeBits 5 1
        let raw ← mkLongRawMarked payload 0
        let s0 ← mkLongSlice 0 0 raw
        let s1 ← expectDecodeStep "decode/len0/payload5" s0 (expectedLongInstr raw #[]) 18
        expectCursor "decode/len0/payload5/rest" s1 0 0 }
    ,
    { name := "unit/decode/len0-trailing-zeroes-in-payload-preserved"
      run := do
        let payload : BitString := #[true, false, false, false]
        let raw ← mkLongRawMarked payload 0
        let s0 ← mkLongSlice 0 0 raw
        let _ ← expectDecodeStep "decode/len0/trailing-zeroes" s0 (expectedLongInstr raw #[]) 18
        pure () }
    ,
    { name := "unit/decode/refs4-len0"
      run := do
        let payload := stripeBits 2 0
        let raw ← mkLongRawMarked payload 0
        let refs := #[refLeafA, refLeafB, refLeafC, refLeafD]
        let s0 ← mkLongSlice 4 0 raw refs
        let s1 ← expectDecodeStep "decode/refs4/len0" s0 (expectedLongInstr raw refs) 18
        expectCursor "decode/refs4/len0/rest" s1 0 0 }
    ,
    { name := "unit/decode/len1-payload13"
      run := do
        let payload := stripeBits 13 0
        let raw ← mkLongRawMarked payload 1
        let s0 ← mkLongSlice 0 1 raw
        let _ ← expectDecodeStep "decode/len1/payload13" s0 (expectedLongInstr raw #[]) 18
        pure () }
    ,
    { name := "unit/decode/len7-payload57"
      run := do
        let payload := stripeBits 57 1
        let raw ← mkLongRawMarked payload 7
        let s0 ← mkLongSlice 0 7 raw
        let _ ← expectDecodeStep "decode/len7/payload57" s0 (expectedLongInstr raw #[]) 18
        pure () }
    ,
    { name := "unit/decode/len31-payload250"
      run := do
        let payload := stripeBits 250 0
        let raw ← mkLongRawMarked payload 31
        let s0 ← mkLongSlice 0 31 raw
        let _ ← expectDecodeStep "decode/len31/payload250" s0 (expectedLongInstr raw #[]) 18
        pure () }
    ,
    { name := "unit/decode/len127-empty"
      run := do
        let raw ← mkLongRawMarked #[] 127
        let s0 ← mkLongSlice 0 127 raw
        let _ ← expectDecodeStep "decode/len127/empty" s0 (expectedLongInstr raw #[]) 18
        pure () }
    ,
    { name := "unit/decode/len127-max-payload1021"
      run := do
        let payload := stripeBits 1021 1
        let raw ← mkLongRawMarked payload 127
        let s0 ← mkLongSlice 0 127 raw
        let _ ← expectDecodeStep "decode/len127/payload1021" s0 (expectedLongInstr raw #[]) 18
        pure () }
    ,
    { name := "unit/decode/noncanonical-all-zero-raw-decodes-empty"
      run := do
        let raw : BitString := Array.replicate (longDataBits 9) false
        let s0 ← mkLongSlice 0 9 raw
        let _ ← expectDecodeStep "decode/noncanonical/all-zero-raw" s0 (expectedLongInstr raw #[]) 18
        pure () }
    ,
    { name := "unit/decode/consumes-inline-refs-leaves-tail-refs"
      run := do
        let payload := stripeBits 8 1
        let raw ← mkLongRawMarked payload 1
        let inlineRefs := #[refLeafA, refLeafB]
        let tailRefs := #[refLeafC, refLeafD]
        let s0 ← mkLongSlice 2 1 raw (inlineRefs ++ tailRefs)
        let s1 ← expectDecodeStep "decode/refs/consume-inline" s0 (expectedLongInstr raw inlineRefs) 18
        expectCursor "decode/refs/consume-inline/rest" s1 0 2 }
    ,
    { name := "unit/decode/consumes-inline-bits-leaves-tail-bits"
      run := do
        let payload := stripeBits 9 0
        let raw ← mkLongRawMarked payload 1
        let s0 ← mkLongSlice 0 1 raw #[] addOpcodeBits
        let s1 ← expectDecodeStep "decode/bits/consume-inline" s0 (expectedLongInstr raw #[]) 18
        let s2 ← expectDecodeStep "decode/bits/tail-add" s1 .add 8
        expectCursor "decode/bits/tail-add/rest" s2 0 0 }
    ,
    { name := "unit/decode/long-sequence-with-tail-add-and-mul"
      run := do
        let payload := stripeBits 3 1
        let raw ← mkLongRawMarked payload 0
        let tailCode ←
          match assembleCp0 [.add, .mul] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble tail failed: {e}")
        let s0 ← mkLongSlice 0 0 raw #[] tailCode.bits
        let s1 ← expectDecodeStep "decode/seq/long" s0 (expectedLongInstr raw #[]) 18
        let s2 ← expectDecodeStep "decode/seq/add" s1 .add 8
        let s3 ← expectDecodeStep "decode/seq/mul" s2 .mul 8
        expectCursor "decode/seq/end" s3 0 0 }
    ,
    { name := "unit/decode/family-boundary-8b-8c-8d"
      run := do
        let shortPayload := stripeBits 2 0
        let shortRaw ← mkMarkedRawForWidth shortPayload 4
        let shortBits ← mkPushsliceShortBits 0 shortRaw

        let refsRaw ← mkMarkedRawForWidth #[] 1
        let refsBits ← mkPushsliceRefsBits 0 0 refsRaw
        let refsInline := #[refLeafA]

        let longPayload := stripeBits 3 1
        let longRaw ← mkLongRawMarked longPayload 0
        let longBits ← mkLongBits 2 0 longRaw
        let longInline := #[refLeafB, refLeafC]

        let codeBits := shortBits ++ refsBits ++ longBits
        let codeRefs := refsInline ++ longInline
        let s0 := Slice.ofCell (Cell.mkOrdinary codeBits codeRefs)
        let s1 ← expectDecodeStep "decode/family/8b" s0 (expectedLongInstr shortRaw #[]) 12
        let s2 ← expectDecodeStep "decode/family/8c" s1 (expectedLongInstr refsRaw refsInline) 15
        let s3 ← expectDecodeStep "decode/family/8d" s2 (expectedLongInstr longRaw longInline) 18
        expectCursor "decode/family/end" s3 0 0 }
    ,
    { name := "unit/decode/from-shifted-cursor-bitpos-refpos"
      run := do
        let prefixBits : BitString := natToBits 0b101 3
        let prefixRefs := #[refLeafD]
        let longPayload := stripeBits 4 0
        let longRaw ← mkLongRawMarked longPayload 0
        let longBits ← mkLongBits 2 0 longRaw
        let inlineRefs := #[refLeafA, refLeafB]
        let tailCode ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let cell : Cell :=
          Cell.mkOrdinary (prefixBits ++ longBits ++ tailCode.bits) (prefixRefs ++ inlineRefs)
        let s0 : Slice := { cell := cell, bitPos := prefixBits.size, refPos := prefixRefs.size }
        let s1 ← expectDecodeStep "decode/shifted/long" s0 (expectedLongInstr longRaw inlineRefs) 18
        let s2 ← expectDecodeStep "decode/shifted/add" s1 .add 8
        expectCursor "decode/shifted/end" s2 0 0 }
    ,
    { name := "unit/decode/error-header-only-missing-inline-data"
      run := do
        let bits := natToBits (longWord 0 0) 18
        expectDecodeErr "decode/error/header-only" (Slice.ofCell (Cell.mkOrdinary bits #[])) .invOpcode }
    ,
    { name := "unit/decode/error-truncated-inline-data-len127"
      run := do
        let want := longDataBits 127
        let rawShort : BitString := Array.replicate (want - 1) false
        let bits := natToBits (longWord 0 127) 18 ++ rawShort
        expectDecodeErr "decode/error/truncated-data-len127"
          (Slice.ofCell (Cell.mkOrdinary bits #[])) .invOpcode }
    ,
    { name := "unit/decode/error-missing-inline-refs"
      run := do
        let raw ← mkLongRawMarked (stripeBits 2 1) 0
        let s0 ← mkLongSlice 2 0 raw #[refLeafA]
        expectDecodeErr "decode/error/missing-refs" s0 .invOpcode }
    ,
    { name := "unit/decode/error-reserved-refs5"
      run := do
        let raw ← mkLongRawMarked #[] 0
        let s0 ← mkLongSlice 5 0 raw
        expectDecodeErr "decode/error/refs5" s0 .invOpcode }
    ,
    { name := "unit/decode/error-reserved-refs7"
      run := do
        let raw ← mkLongRawMarked #[] 0
        let s0 ← mkLongSlice 7 0 raw
        expectDecodeErr "decode/error/refs7" s0 .invOpcode }
    ,
    { name := "unit/decode/error-empty-slice"
      run := do
        expectDecodeErr "decode/error/empty" (mkSliceFromBits #[]) .invOpcode }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHSLICE_LONG
