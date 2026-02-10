import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PUSHCONT_SHORT

/-
PUSHCONT_SHORT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PushCont.lean` (`execInstrFlowPushCont`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`p4 = 0x9` tiny PUSHCONT decode: 4-bit prefix + 4-bit byte-length)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.pushCont _` rejected by standalone assembler)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_push_cont_simple`, opcode table `mkext(9, 4, 4, ...)`)

Branch map used for this suite:
- exec path: 1 branch site / 2 outcomes
  (`.pushCont code` pushes ordinary continuation; non-`.pushCont` falls through).
- short decode path (`p4 = 0x9`): success when payload bits exist, `.invOpcode` when truncated.
- boundary split: short `PUSHCONT_SHORT` (`0x9*`, 8-bit header) vs general PUSHCONT
  (`0x8e/0x8f` region, 16-bit header with ref-capable args).
- assembler boundary: `.pushCont _` is decode-only in current `assembleCp0`.

Harness note:
- `OracleCase`/`FuzzSpec` require `assembleCp0` support, but `.pushCont _` is currently
  non-assemblable, so oracle/fuzz are intentionally empty and coverage is concentrated in unit tests.
-/

private def dispatchSentinel : Int := 9017

private def refLeafA : Cell :=
  Cell.ofUInt 5 0x13

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x55 7) #[refLeafA]

private def bytesToBits (bytes : Array Nat) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits (b % 256) 8) #[]

private def stripedBytes (count : Nat) (phase : Nat := 0) : Array Nat :=
  Array.ofFn (n := count) fun i => ((i.1 * 73 + phase * 29 + 11) % 256)

private def codeSliceFromBytes (bytes : Array Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (bytesToBits bytes) #[])

private def shortHeaderByte (lenBytes : Nat) : Nat :=
  0x90 + (lenBytes &&& 0xf)

private def shortBits (lenBytes : Nat) (payloadBytes : Array Nat) : BitString :=
  natToBits (shortHeaderByte lenBytes) 8 ++ bytesToBits payloadBytes

private def mkDecodeSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def pushContValue (code : Slice) : Value :=
  .cont (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)

private def expectedPushContStack (below : Array Value) (code : Slice) : Array Value :=
  below ++ #[pushContValue code]

private def runPushContDirect (code : Slice) (stack : Array Value := #[]) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushCont (.pushCont code) stack

private def runPushContDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushCont instr (VM.push (intV dispatchSentinel)) stack

private def runPushContState (instr : Instr) (stack : Array Value := #[]) :
    Except Excno VmState := do
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrFlowPushCont instr (pure ())).run st0
  match res with
  | .ok _ => pure st1
  | .error e => throw e

private def expectDecodeInvOpcode (label : String) (s : Slice) : IO Unit := do
  match decodeCp0WithBits s with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, consumed, _) =>
      throw (IO.userError
        s!"{label}: expected decode failure, got instr={reprStr instr} consumed={consumed}")

private def expectInvOpcode (label : String) (res : Except Excno α) : IO Unit := do
  match res with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode, got success")

private def codeEmpty : Slice :=
  codeSliceFromBytes #[]

private def codeOneByte : Slice :=
  codeSliceFromBytes #[0xa0]

private def codeTwoBytes : Slice :=
  codeSliceFromBytes #[0x70, 0xa0]

private def codeEightBytes : Slice :=
  codeSliceFromBytes (stripedBytes 8 1)

private def codeFifteenBytes : Slice :=
  codeSliceFromBytes (stripedBytes 15 2)

def suite : InstrSuite where
  id := { name := "PUSHCONT_SHORT" }
  unit := #[
    -- Branch map: exec success arm (`.pushCont code`) with empty short-style payload.
    { name := "unit/direct/push-empty-cont-on-empty-stack"
      run := do
        expectOkStack "direct/empty"
          (runPushContDirect codeEmpty)
          #[pushContValue codeEmpty] }
    ,
    -- Branch map: exec success arm with one-byte inline code payload.
    { name := "unit/direct/push-one-byte-cont"
      run := do
        expectOkStack "direct/one-byte"
          (runPushContDirect codeOneByte)
          #[pushContValue codeOneByte] }
    ,
    -- Branch map: exec success arm at short max payload boundary (15 bytes).
    { name := "unit/direct/push-fifteen-byte-cont"
      run := do
        expectOkStack "direct/fifteen-bytes"
          (runPushContDirect codeFifteenBytes)
          #[pushContValue codeFifteenBytes] }
    ,
    -- Branch map: no-pop contract preserves below-stack entries.
    { name := "unit/direct/preserve-null-below"
      run := do
        expectOkStack "direct/preserve-null"
          (runPushContDirect codeOneByte #[.null])
          #[.null, pushContValue codeOneByte] }
    ,
    -- Branch map: no-pop contract preserves deep mixed stack order.
    { name := "unit/direct/preserve-mixed-below"
      run := do
        let below : Array Value := #[intV (-9), .builder Builder.empty, .tuple #[]]
        expectOkStack "direct/preserve-mixed"
          (runPushContDirect codeTwoBytes below)
          (expectedPushContStack below codeTwoBytes) }
    ,
    -- Branch map: no-pop contract preserves an existing continuation below top.
    { name := "unit/direct/preserve-continuation-below"
      run := do
        let below : Array Value := #[.cont (.quit 7)]
        expectOkStack "direct/preserve-cont"
          (runPushContDirect codeOneByte below)
          (expectedPushContStack below codeOneByte) }
    ,
    -- Branch map: repeated success path appends one continuation per execution.
    { name := "unit/direct/repeated-appends-continuations"
      run := do
        let s1 ←
          match runPushContDirect codeOneByte #[intV 3] with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"repeat/first: expected success, got {e}")
        expectOkStack "repeat/second"
          (runPushContDirect codeFifteenBytes s1)
          #[intV 3, pushContValue codeOneByte, pushContValue codeFifteenBytes] }
    ,
    -- Branch map: matched `.pushCont` path must not invoke fallback `next`.
    { name := "unit/dispatch/match-does-not-call-next"
      run := do
        expectOkStack "dispatch/match"
          (runPushContDispatchFallback (.pushCont codeOneByte) #[intV 9])
          #[intV 9, pushContValue codeOneByte] }
    ,
    -- Branch map: non-`.pushCont` dispatch falls through to `next`.
    { name := "unit/dispatch/fallback-add"
      run := do
        expectOkStack "dispatch/add"
          (runPushContDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel] }
    ,
    -- Branch map: PUSHCONT must not mutate cell-load cache side effects.
    { name := "unit/direct/no-cell-load-side-effect"
      run := do
        match runPushContState (.pushCont codeEightBytes) #[intV 1] with
        | .error e =>
            throw (IO.userError s!"state/no-cell-load: expected success, got {e}")
        | .ok st =>
            if st.stack != #[intV 1, pushContValue codeEightBytes] then
              throw (IO.userError s!"state/no-cell-load: unexpected stack {reprStr st.stack}")
            else if st.loadedCells.isEmpty then
              pure ()
            else
              throw (IO.userError
                s!"state/no-cell-load: expected empty loadedCells, got {st.loadedCells.size}") }
    ,

    -- Branch map: short decode success (`0x90`, len=0 bytes).
    { name := "unit/decode/short-0x90-empty"
      run := do
        let s0 := mkDecodeSlice (shortBits 0 #[])
        let s1 ← expectDecodeStep "decode/short-0x90" s0 (.pushCont codeEmpty) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-0x90-end: expected bits=0 refs=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    -- Branch map: short decode success (`0x91`, len=1 byte).
    { name := "unit/decode/short-0x91-one-byte"
      run := do
        let payload := #[0xa0]
        let s0 := mkDecodeSlice (shortBits 1 payload)
        let s1 ← expectDecodeStep "decode/short-0x91" s0 (.pushCont (codeSliceFromBytes payload)) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-0x91-end: expected bits=0 refs=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    -- Branch map: short decode success (`0x92`, len=2 bytes).
    { name := "unit/decode/short-0x92-two-bytes"
      run := do
        let payload := #[0x70, 0xa0]
        let s0 := mkDecodeSlice (shortBits 2 payload)
        let s1 ← expectDecodeStep "decode/short-0x92" s0 (.pushCont (codeSliceFromBytes payload)) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-0x92-end: expected bits=0 refs=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    -- Branch map: short decode success over mid-size payload (len=8 bytes).
    { name := "unit/decode/short-0x98-eight-bytes"
      run := do
        let payload := stripedBytes 8 4
        let s0 := mkDecodeSlice (shortBits 8 payload)
        let s1 ← expectDecodeStep "decode/short-0x98" s0 (.pushCont (codeSliceFromBytes payload)) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-0x98-end: expected bits=0 refs=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    -- Branch map: short decode success at max nibble payload (len=15 bytes).
    { name := "unit/decode/short-0x9f-fifteen-bytes"
      run := do
        let payload := stripedBytes 15 5
        let s0 := mkDecodeSlice (shortBits 15 payload)
        let s1 ← expectDecodeStep "decode/short-0x9f" s0 (.pushCont (codeSliceFromBytes payload)) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-0x9f-end: expected bits=0 refs=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    -- Branch map: short decode leaves correct tail bits for the next opcode.
    { name := "unit/decode/short-followed-by-add"
      run := do
        let payload := #[0x7f]
        let s0 := mkDecodeSlice (shortBits 1 payload ++ natToBits 0xa0 8)
        let s1 ← expectDecodeStep "decode/short-first" s0 (.pushCont (codeSliceFromBytes payload)) 8
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-followed-end: expected bits=0 refs=0, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    -- Branch map: consecutive short opcodes decode in-order.
    { name := "unit/decode/short-sequence-0x90-then-0x91"
      run := do
        let payload := #[0x55]
        let bits : BitString := shortBits 0 #[] ++ shortBits 1 payload
        let s0 := mkDecodeSlice bits
        let s1 ← expectDecodeStep "decode/seq-first-0x90" s0 (.pushCont codeEmpty) 8
        let s2 ← expectDecodeStep "decode/seq-second-0x91" s1 (.pushCont (codeSliceFromBytes payload)) 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-seq-end: expected bits=0 refs=0, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    -- Branch map: short decode must not consume attached refs from the hosting code cell.
    { name := "unit/decode/short-len0-leaves-all-refs"
      run := do
        let s0 := mkDecodeSlice (shortBits 0 #[]) #[refLeafA, refLeafB]
        let s1 ← expectDecodeStep "decode/short-len0-refs" s0 (.pushCont codeEmpty) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 2 ∧ s1.refPos = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-len0-refs: expected bits=0 refs=2 refPos=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining} refPos={s1.refPos}") }
    ,
    -- Branch map: short decode preserves both tail bits and untouched refs.
    { name := "unit/decode/short-len2-leaves-refs-and-tail"
      run := do
        let payload := #[0x11, 0x22]
        let s0 := mkDecodeSlice (shortBits 2 payload ++ natToBits 0xa0 8) #[refLeafB]
        let s1 ← expectDecodeStep "decode/short-len2" s0 (.pushCont (codeSliceFromBytes payload)) 8
        if s1.bitsRemaining = 8 ∧ s1.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-len2-mid: expected bits=8 refs=1, got bits={s1.bitsRemaining} refs={s1.refsRemaining}")
        let s2 ← expectDecodeStep "decode/short-len2-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-len2-end: expected bits=0 refs=1, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    -- Branch map: short decode honors current bit offset (`bitPos`) correctly.
    { name := "unit/decode/short-nonzero-bitpos"
      run := do
        let payload := #[0x2c]
        let bits : BitString := #[false] ++ shortBits 1 payload ++ natToBits 0xa0 8
        let shifted : Slice := { mkDecodeSlice bits with bitPos := 1 }
        let s1 ← expectDecodeStep "decode/short-nonzero-bitpos-first"
          shifted (.pushCont (codeSliceFromBytes payload)) 8
        let s2 ← expectDecodeStep "decode/short-nonzero-bitpos-tail" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short-nonzero-bitpos-end: expected bits=0, got bits={s2.bitsRemaining}") }
    ,
    -- Branch map: boundary with general PUSHCONT prefix (`0x8e00`) stays on 16-bit path.
    { name := "unit/decode/boundary-general-pushcont-empty-0x8e00"
      run := do
        let s0 := mkDecodeSlice (natToBits 0x8e00 16)
        let s1 ← expectDecodeStep "decode/general-0x8e00" s0 (.pushCont codeEmpty) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general-0x8e00-end: expected bits=0 refs=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    -- Branch map: boundary with general PUSHCONT args (refs=1,len=0) consumes one ref on 16-bit path.
    { name := "unit/decode/boundary-general-pushcont-ref-0x8e80"
      run := do
        let expectedCode := Slice.ofCell (Cell.mkOrdinary #[] #[refLeafA])
        let s0 := mkDecodeSlice (natToBits 0x8e80 16) #[refLeafA]
        let s1 ← expectDecodeStep "decode/general-0x8e80" s0 (.pushCont expectedCode) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general-0x8e80-end: expected bits=0 refs=0, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,

    -- Branch map: decode error on empty slice.
    { name := "unit/decode/error-empty-slice"
      run := do
        expectDecodeInvOpcode "decode/error-empty" (Slice.ofCell Cell.empty) }
    ,
    -- Branch map: decode error on truncated short prefix (<8 bits).
    { name := "unit/decode/error-truncated-prefix-7bits"
      run := do
        expectDecodeInvOpcode "decode/error-truncated-7"
          (mkDecodeSlice (natToBits 0x48 7)) }
    ,
    -- Branch map: short decode failure when len=1 but payload byte is missing.
    { name := "unit/decode/error-0x91-missing-byte"
      run := do
        expectDecodeInvOpcode "decode/error-0x91-missing-byte"
          (mkDecodeSlice (shortBits 1 #[])) }
    ,
    -- Branch map: short decode failure when len=2 but only one payload byte exists.
    { name := "unit/decode/error-0x92-only-one-byte"
      run := do
        expectDecodeInvOpcode "decode/error-0x92-only-one-byte"
          (mkDecodeSlice (shortBits 2 #[0xaa])) }
    ,
    -- Branch map: short decode failure at max len nibble when payload is short by one byte.
    { name := "unit/decode/error-0x9f-fourteen-of-fifteen"
      run := do
        expectDecodeInvOpcode "decode/error-0x9f-fourteen-of-fifteen"
          (mkDecodeSlice (shortBits 15 (stripedBytes 14 7))) }
    ,
    -- Branch map: short decode checks payload bits only; refs cannot satisfy missing data.
    { name := "unit/decode/error-0x9f-no-bytes-even-with-refs"
      run := do
        expectDecodeInvOpcode "decode/error-0x9f-no-bytes-with-refs"
          (mkDecodeSlice (shortBits 15 #[]) #[refLeafA, refLeafB]) }
    ,
    -- Branch map: general PUSHCONT boundary error for missing required ref (0x8e80).
    { name := "unit/decode/error-general-0x8e80-missing-ref"
      run := do
        expectDecodeInvOpcode "decode/error-general-0x8e80-no-ref"
          (mkDecodeSlice (natToBits 0x8e80 16)) }
    ,

    -- Branch map: assembler-side single-instr encoder rejects `.pushCont _`.
    { name := "unit/assembler/encodecp0-rejects-pushcont"
      run := do
        expectInvOpcode "assembler/encodecp0-pushcont"
          (encodeCp0 (.pushCont codeOneByte)) }
    ,
    -- Branch map: program assembly rejects standalone PUSHCONT immediate.
    { name := "unit/assembler/assemblecp0-single-pushcont-rejected"
      run := do
        expectInvOpcode "assembler/assemble-single-pushcont"
          (assembleCp0 [(.pushCont codeOneByte)]) }
    ,
    -- Branch map: assembly fails even when PUSHCONT is surrounded by encodable neighbors.
    { name := "unit/assembler/assemblecp0-sequence-with-pushcont-rejected"
      run := do
        expectInvOpcode "assembler/assemble-sequence-with-pushcont"
          (assembleCp0 [.add, (.pushCont codeOneByte), .newc]) }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHCONT_SHORT
