import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PUSHREFSLICE

/-
PUSHREFSLICE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PushRefSlice.lean` (`.pushRefSlice c`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0x89` decode + `haveRefs 1` guard)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.pushRefSlice _` rejected by assembler)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_push_ref(..., mode=1)`)

Branch map covered by this suite:
- dispatch guard: `.pushRefSlice` executes, other opcodes fall through to `next`;
- success path: push full `Slice.ofCell c` and preserve lower stack entries;
- registerCellLoad accounting split: fresh load vs cached reload;
- decode split around `0x89`: success with exactly one ref, `invOpcode` on missing refs/bits;
- opcode/decode boundaries in `0x88/0x89/0x8a` neighborhood;
- assembler boundary: ref-immediate ops (`PUSHREF*`) are decode-only (`assembleCp0` rejects).

Harness note:
- `.pushRefSlice` is currently non-assemblable in `assembleCp0`, so oracle/fuzz
  sections are intentionally empty and coverage is concentrated in unit tests.
-/

private def pushRefSliceId : InstrId := { name := "PUSHREFSLICE" }

private def pushRefOpcode : Nat := 0x88
private def pushRefSliceOpcode : Nat := 0x89
private def pushRefContOpcode : Nat := 0x8a

private def dispatchSentinel : Int := 889

private def runPushRefSliceDirect
    (c : Cell)
    (stack : Array Value := #[]) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushRefSlice (.pushRefSlice c) stack

private def runPushRefSliceDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushRefSlice instr (VM.push (intV dispatchSentinel)) stack

private def runPushRefSliceRaw
    (c : Cell)
    (stack : Array Value := #[])
    (loadedCells : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      loadedCells := loadedCells }
  (execInstrFlowPushRefSlice (.pushRefSlice c) (pure ())).run st0

private def expectedPushRefSliceStack (below : Array Value) (c : Cell) : Array Value :=
  below ++ #[.slice (Slice.ofCell c)]

private def mkDecodeSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def expectDecodeInvOpcode (label : String) (s : Slice) : IO Unit := do
  match decodeCp0WithBits s with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, consumed, _) =>
      throw (IO.userError
        s!"{label}: expected decode failure, got instr={reprStr instr} consumed={consumed}")

private def expectRawSuccess
    (label : String)
    (out : Except Excno Unit × VmState)
    (expectedStack : Array Value)
    (expectedLoaded : Array (Array UInt8))
    (expectedGasConsumed : Int) : IO Unit := do
  let (res, st) := out
  match res with
  | .ok _ =>
      if st.stack == expectedStack then
        pure ()
      else
        throw (IO.userError
          s!"{label}/stack: expected {reprStr expectedStack}, got {reprStr st.stack}")
      if st.loadedCells == expectedLoaded then
        pure ()
      else
        throw (IO.userError
          s!"{label}/loaded: expected {reprStr expectedLoaded}, got {reprStr st.loadedCells}")
      if st.gas.gasConsumed = expectedGasConsumed then
        pure ()
      else
        throw (IO.userError
          s!"{label}/gas: expected {expectedGasConsumed}, got {st.gas.gasConsumed}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectAssembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok code =>
      throw (IO.userError s!"{label}: expected assembler rejection, got code bits {code.bits}")

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2A 6) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (stripeBits 9 1) #[refLeafA, Cell.empty]

private def refLeafD : Cell :=
  Cell.mkOrdinary (natToBits 0x9 4) #[refLeafB]

private def cOrdEmpty : Cell :=
  Cell.empty

private def cOrdBits1 : Cell :=
  Cell.ofUInt 1 1

private def cOrdBits7 : Cell :=
  Cell.ofUInt 7 0x55

private def cOrdBits255 : Cell :=
  Cell.mkOrdinary (stripeBits 255 1) #[]

private def cOrdBits1023 : Cell :=
  Cell.mkOrdinary (stripeBits 1023 2) #[]

private def cOrdRefs1 : Cell :=
  Cell.mkOrdinary (stripeBits 5 0) #[refLeafA]

private def cOrdRefs4 : Cell :=
  Cell.mkOrdinary (stripeBits 17 3) #[refLeafA, refLeafB, refLeafC, refLeafD]

private def cOrdNested : Cell :=
  Cell.mkOrdinary (stripeBits 33 2) #[refLeafB, refLeafC]

private def specialLibraryCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def specialUnknownCell : Cell :=
  { bits := natToBits 7 8 ++ natToBits 0 24
    refs := #[]
    special := true
    levelMask := 0 }

private def specialWithRefCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 true
    refs := #[refLeafA]
    special := true
    levelMask := 0 }

private def mkDirectCase
    (name : String)
    (c : Cell)
    (below : Array Value := #[]) : UnitCase :=
  { name := name
    run := do
      expectOkStack name
        (runPushRefSliceDirect c below)
        (expectedPushRefSliceStack below c) }

private def mkFallbackCase
    (name : String)
    (instr : Instr)
    (stack : Array Value) : UnitCase :=
  { name := name
    run := do
      expectOkStack name
        (runPushRefSliceDispatchFallback instr stack)
        (stack ++ #[intV dispatchSentinel]) }

def suite : InstrSuite where
  id := pushRefSliceId
  unit := #[
    mkDirectCase "unit/direct/ok/ordinary-empty" cOrdEmpty,
    mkDirectCase "unit/direct/ok/ordinary-bits1" cOrdBits1,
    mkDirectCase "unit/direct/ok/ordinary-bits7" cOrdBits7,
    mkDirectCase "unit/direct/ok/ordinary-bits255" cOrdBits255,
    mkDirectCase "unit/direct/ok/ordinary-bits1023" cOrdBits1023,
    mkDirectCase "unit/direct/ok/ordinary-refs1" cOrdRefs1,
    mkDirectCase "unit/direct/ok/ordinary-refs4" cOrdRefs4,
    mkDirectCase "unit/direct/ok/ordinary-nested" cOrdNested,
    mkDirectCase "unit/direct/ok/special-library" specialLibraryCell,
    mkDirectCase "unit/direct/ok/special-unknown" specialUnknownCell,
    mkDirectCase "unit/direct/ok/special-with-ref" specialWithRefCell,
    mkDirectCase "unit/direct/ok/deep-preserve-null" cOrdBits7 #[.null],
    mkDirectCase "unit/direct/ok/deep-preserve-int-and-builder"
      cOrdRefs1 #[intV (-17), .builder Builder.empty],
    mkDirectCase "unit/direct/ok/deep-preserve-three-values"
      cOrdNested #[.tuple #[], .null, intV 5],

    { name := "unit/dispatch/match-does-not-call-next"
      run := do
        expectOkStack "dispatch/match"
          (runPushRefSliceDispatchFallback (.pushRefSlice cOrdRefs1) #[intV 9])
          (expectedPushRefSliceStack #[intV 9] cOrdRefs1) }
    ,
    mkFallbackCase "unit/dispatch/fallback-add" .add #[.null],
    mkFallbackCase "unit/dispatch/fallback-pushref" (.pushRef refLeafA) #[intV 3],
    mkFallbackCase "unit/dispatch/fallback-pushrefcont" (.pushRefCont refLeafB) #[.tuple #[]],
    mkFallbackCase "unit/dispatch/fallback-pushcont" (.pushCont (Slice.ofCell cOrdBits7)) #[.builder Builder.empty],

    { name := "unit/raw/gas/fresh-load-ordinary"
      run := do
        let c := cOrdRefs4
        let h : Array UInt8 := Cell.hashBytes c
        expectRawSuccess "raw/fresh-ordinary"
          (runPushRefSliceRaw c)
          (expectedPushRefSliceStack #[] c)
          #[h]
          cellLoadGasPrice }
    ,
    { name := "unit/raw/gas/reload-ordinary"
      run := do
        let c := cOrdRefs4
        let h : Array UInt8 := Cell.hashBytes c
        expectRawSuccess "raw/reload-ordinary"
          (runPushRefSliceRaw c #[] #[h])
          (expectedPushRefSliceStack #[] c)
          #[h]
          cellReloadGasPrice }
    ,
    { name := "unit/raw/gas/cache-hit-in-middle"
      run := do
        let c := cOrdRefs1
        let h : Array UInt8 := Cell.hashBytes c
        let h0 : Array UInt8 := Cell.hashBytes cOrdBits7
        let h1 : Array UInt8 := Cell.hashBytes cOrdNested
        let preloaded : Array (Array UInt8) := #[h0, h, h1]
        expectRawSuccess "raw/reload-middle"
          (runPushRefSliceRaw c #[] preloaded)
          (expectedPushRefSliceStack #[] c)
          preloaded
          cellReloadGasPrice }
    ,
    { name := "unit/raw/gas/fresh-appends-after-other"
      run := do
        let c := cOrdNested
        let h : Array UInt8 := Cell.hashBytes c
        let h0 : Array UInt8 := Cell.hashBytes cOrdBits255
        expectRawSuccess "raw/fresh-append"
          (runPushRefSliceRaw c #[] #[h0])
          (expectedPushRefSliceStack #[] c)
          #[h0, h]
          cellLoadGasPrice }
    ,
    { name := "unit/raw/gas/special-fresh"
      run := do
        let c := specialLibraryCell
        let h : Array UInt8 := Cell.hashBytes c
        expectRawSuccess "raw/special-fresh"
          (runPushRefSliceRaw c)
          (expectedPushRefSliceStack #[] c)
          #[h]
          cellLoadGasPrice }
    ,
    { name := "unit/raw/gas/special-reload"
      run := do
        let c := specialLibraryCell
        let h : Array UInt8 := Cell.hashBytes c
        expectRawSuccess "raw/special-reload"
          (runPushRefSliceRaw c #[] #[h])
          (expectedPushRefSliceStack #[] c)
          #[h]
          cellReloadGasPrice }
    ,

    { name := "unit/decode/single-0x89-success"
      run := do
        let s0 := mkDecodeSlice (natToBits pushRefSliceOpcode 8) #[refLeafB]
        let s1 ← expectDecodeStep "decode/single-pushrefslice" s0 (.pushRefSlice refLeafB) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/single-end: expected exhausted slice, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    { name := "unit/decode/boundary-sequence-88-89-8a"
      run := do
        let addCode ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits pushRefOpcode 8 ++
          natToBits pushRefSliceOpcode 8 ++
          natToBits pushRefContOpcode 8 ++
          addCode.bits
        let s0 := mkDecodeSlice rawBits #[refLeafA, refLeafB, refLeafC]
        let s1 ← expectDecodeStep "decode/pushref-0x88" s0 (.pushRef refLeafA) 8
        let s2 ← expectDecodeStep "decode/pushrefslice-0x89" s1 (.pushRefSlice refLeafB) 8
        let s3 ← expectDecodeStep "decode/pushrefcont-0x8a" s2 (.pushRefCont refLeafC) 8
        let s4 ← expectDecodeStep "decode/add-tail" s3 .add 8
        if s4.bitsRemaining = 0 ∧ s4.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/sequence-end: expected exhausted slice, got bits={s4.bitsRemaining} refs={s4.refsRemaining}") }
    ,
    { name := "unit/decode/pushrefslice-consumes-exactly-one-ref"
      run := do
        let addCode ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits pushRefSliceOpcode 8 ++ addCode.bits
        let s0 := mkDecodeSlice rawBits #[refLeafC, refLeafD]
        let s1 ← expectDecodeStep "decode/first-pushrefslice" s0 (.pushRefSlice refLeafC) 8
        if s1.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError
            s!"decode/first-pushrefslice: expected one remaining ref, got {s1.refsRemaining}")
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError
            s!"decode/tail-add: expected bits=0 refs=1, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    { name := "unit/decode/error-no-ref"
      run := do
        let s := mkSliceFromBits (natToBits pushRefSliceOpcode 8)
        expectDecodeInvOpcode "decode/no-ref" s }
    ,
    { name := "unit/decode/error-insufficient-bits"
      run := do
        let s := mkSliceFromBits (natToBits 0x45 7)
        expectDecodeInvOpcode "decode/insufficient-bits" s }
    ,
    { name := "unit/decode/error-second-pushrefslice-missing-ref"
      run := do
        let rawBits : BitString :=
          natToBits pushRefSliceOpcode 8 ++
          natToBits pushRefSliceOpcode 8
        let s0 := mkDecodeSlice rawBits #[refLeafA]
        let s1 ← expectDecodeStep "decode/first-0x89" s0 (.pushRefSlice refLeafA) 8
        expectDecodeInvOpcode "decode/second-0x89-missing-ref" s1 }
    ,

    { name := "unit/assembler/ref-immediate-opcodes-are-rejected"
      run := do
        expectAssembleInvOpcode "assemble/pushref" (.pushRef refLeafA)
        expectAssembleInvOpcode "assemble/pushrefslice" (.pushRefSlice refLeafB)
        expectAssembleInvOpcode "assemble/pushrefcont" (.pushRefCont refLeafC) }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHREFSLICE
