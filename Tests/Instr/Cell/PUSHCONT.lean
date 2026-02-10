import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PUSHCONT

/-
PUSHCONT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PushCont.lean` (`.pushCont code` pushes ordinary continuation)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (two decode forms: short `0x9*` and general `p7=0x47`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.pushCont _` rejected by assembler)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_push_cont`)

Branch map covered by this suite:
- dispatch branch: `.pushCont _` executes, all other opcodes fall through to `next`;
- execution contract: pushes `.cont (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)`,
  preserving below-stack values and slice offsets exactly;
- decode coverage: short (`0x9`) and general (`0x47`) encodings, including max payload/ref boundaries;
- decode failures: truncated header, missing payload bits, missing refs, and empty input;
- assembler boundary: `encodeCp0` / `assembleCp0` reject `.pushCont _` (decode-only path).
-/

private def pushContId : InstrId := { name := "PUSHCONT" }

private def dispatchSentinel : Int := 901

private def pushContGeneralPrefix : Nat := 0x47
private def pushContShortPrefix : Nat := 0x9

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

private def mkDecodeSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkGeneralHeader (refs : Nat) (lenBytes : Nat) : Nat :=
  (pushContGeneralPrefix <<< 9) + ((refs &&& 0x3) <<< 7) + (lenBytes &&& 0x7f)

private def mkGeneralBits (refs : Nat) (lenBytes : Nat) (payload : BitString) : BitString :=
  natToBits (mkGeneralHeader refs lenBytes) 16 ++ payload

private def mkShortBits (lenBytes : Nat) (payload : BitString) : BitString :=
  natToBits ((pushContShortPrefix <<< 4) + (lenBytes &&& 0xf)) 8 ++ payload

private def decodedPushContInstr (payload : BitString) (refs : Array Cell := #[]) : Instr :=
  .pushCont (Slice.ofCell (Cell.mkOrdinary payload refs))

private def pushedContValue (code : Slice) : Value :=
  .cont (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)

private def runPushContDirect
    (code : Slice)
    (stack : Array Value := #[]) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushCont (.pushCont code) stack

private def runPushContDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushCont instr (VM.push (intV dispatchSentinel)) stack

private def runPushContRaw
    (code : Slice)
    (stack : Array Value := #[])
    (regs : Regs := Regs.initial)
    (loadedCells : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      loadedCells := loadedCells }
  (execInstrFlowPushCont (.pushCont code) (pure ())).run st0

private def expectDecodeInvOpcode (label : String) (s : Slice) : IO Unit := do
  match decodeCp0WithBits s with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, consumed, _) =>
      throw (IO.userError
        s!"{label}: expected decode failure, got instr={reprStr instr} consumed={consumed}")

private def expectInvOpcode (label : String) (res : Except Excno α) : IO Unit := do
  match res with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode, got success")

private def cregsEmpty (cregs : OrdCregs) : Bool :=
  cregs.c0.isNone &&
  cregs.c1.isNone &&
  cregs.c2.isNone &&
  cregs.c3.isNone &&
  cregs.c4.isNone &&
  cregs.c5.isNone &&
  cregs.c7.isNone

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

private def expectTopIsFreshOrdinaryCont
    (label : String)
    (st : VmState)
    (expectedCode : Slice) : IO Unit := do
  if h : 0 < st.stack.size then
    let top := st.stack.back (h := h)
    match top with
    | .cont (.ordinary code saved cregs cdata) =>
        if code != expectedCode then
          throw (IO.userError s!"{label}: unexpected code slice {reprStr code}")
        else if saved != .quit 0 then
          throw (IO.userError s!"{label}: expected saved c0 = quit(0), got {reprStr saved}")
        else if !(cregsEmpty cregs) then
          throw (IO.userError s!"{label}: expected empty cregs")
        else if !(cdataEmpty cdata) then
          throw (IO.userError s!"{label}: expected empty cdata")
        else
          pure ()
    | _ =>
        throw (IO.userError s!"{label}: expected continuation on top, got {reprStr top}")
  else
    throw (IO.userError s!"{label}: empty stack")

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (stripeBits 9 1) #[refLeafA, Cell.empty]

private def refLeafD : Cell :=
  Cell.mkOrdinary (natToBits 0x9 4) #[refLeafB]

private def codeEmpty : Slice :=
  Slice.ofCell Cell.empty

private def codeBits32 : Slice :=
  mkDecodeSlice (natToBits 0xc0de 16 ++ natToBits 0x55aa 16)

private def codeWithRefs1 : Slice :=
  mkDecodeSlice (stripeBits 24 0) #[refLeafA]

private def codeWithRefs3 : Slice :=
  mkDecodeSlice (stripeBits 40 2) #[refLeafA, refLeafB, refLeafC]

private def codeShifted : Slice :=
  let base := mkDecodeSlice (#[true] ++ stripeBits 17 1) #[refLeafA, refLeafB]
  { base with bitPos := 1, refPos := 1 }

private def code1016 : BitString :=
  stripeBits (127 * 8) 3

def suite : InstrSuite where
  id := pushContId
  unit := #[
    -- Branch: execution success on direct `.pushCont` dispatch.
    { name := "unit/direct/ok/empty-code-empty-stack"
      run := do
        expectOkStack "direct/empty"
          (runPushContDirect codeEmpty)
          #[pushedContValue codeEmpty] }
    ,
    { name := "unit/direct/ok/bits32"
      run := do
        expectOkStack "direct/bits32"
          (runPushContDirect codeBits32)
          #[pushedContValue codeBits32] }
    ,
    { name := "unit/direct/ok/code-with-one-ref"
      run := do
        expectOkStack "direct/refs1"
          (runPushContDirect codeWithRefs1)
          #[pushedContValue codeWithRefs1] }
    ,
    { name := "unit/direct/ok/code-with-three-refs"
      run := do
        expectOkStack "direct/refs3"
          (runPushContDirect codeWithRefs3)
          #[pushedContValue codeWithRefs3] }
    ,
    { name := "unit/direct/ok/preserves-nonzero-slice-offsets"
      run := do
        expectOkStack "direct/shifted"
          (runPushContDirect codeShifted)
          #[pushedContValue codeShifted] }
    ,
    { name := "unit/direct/ok/preserve-mixed-below-stack"
      run := do
        let below : Array Value := #[.null, intV (-17), .builder Builder.empty, .tuple #[]]
        expectOkStack "direct/preserve-below"
          (runPushContDirect codeWithRefs1 below)
          (below ++ #[pushedContValue codeWithRefs1]) }
    ,
    { name := "unit/direct/ok/repeated-appends-two-continuations"
      run := do
        let st1 ←
          match runPushContDirect codeBits32 #[intV 9] with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"direct/repeat-first: expected success, got {e}")
        expectOkStack "direct/repeat-second"
          (runPushContDirect codeWithRefs3 st1)
          #[intV 9, pushedContValue codeBits32, pushedContValue codeWithRefs3] }
    ,

    -- Branch: non-matching opcodes must fall through to `next`.
    { name := "unit/dispatch/match-does-not-call-next"
      run := do
        expectOkStack "dispatch/match"
          (runPushContDispatchFallback (.pushCont codeWithRefs1) #[intV 1])
          #[intV 1, pushedContValue codeWithRefs1] }
    ,
    { name := "unit/dispatch/fallback-add"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runPushContDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel] }
    ,
    { name := "unit/dispatch/fallback-neighbor-pushrefcont"
      run := do
        expectOkStack "dispatch/fallback-pushrefcont"
          (runPushContDispatchFallback (.pushRefCont refLeafB) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel] }
    ,

    -- Branch: PUSHCONT has no cell-load side effects and pushes fresh ordinary continuation shape.
    { name := "unit/raw/state/no-load-side-effect-and-zero-gas"
      run := do
        let preloaded : Array (Array UInt8) := #[Cell.hashBytes refLeafA, Cell.hashBytes refLeafB]
        let (res, st) := runPushContRaw codeWithRefs3 #[intV 3] Regs.initial preloaded
        match res with
        | .error e =>
            throw (IO.userError s!"raw/no-load: expected success, got {e}")
        | .ok _ =>
            if st.loadedCells != preloaded then
              throw (IO.userError s!"raw/no-load: expected loadedCells unchanged")
            else if st.gas.gasConsumed != 0 then
              throw (IO.userError s!"raw/no-load: expected gasConsumed=0, got {st.gas.gasConsumed}")
            else if st.stack != #[intV 3, pushedContValue codeWithRefs3] then
              throw (IO.userError s!"raw/no-load: unexpected stack {reprStr st.stack}")
            else
              pure () }
    ,
    { name := "unit/raw/state/top-cont-uses-quit0-and-empty-cregs-cdata"
      run := do
        let regs : Regs := { Regs.initial with c0 := .quit 77 }
        let (res, st) := runPushContRaw codeShifted #[.null] regs
        match res with
        | .error e =>
            throw (IO.userError s!"raw/shape: expected success, got {e}")
        | .ok _ =>
            if st.stack.size != 2 then
              throw (IO.userError s!"raw/shape: expected stack size 2, got {st.stack.size}")
            else
              expectTopIsFreshOrdinaryCont "raw/shape/top" st codeShifted }
    ,

    -- Branch: cp0 general decode (`p7 = 0x47`) success paths and boundaries.
    { name := "unit/decode/general/len0-refs0"
      run := do
        let s0 := mkDecodeSlice (mkGeneralBits 0 0 #[])
        let s1 ← expectDecodeStep "decode/general/0r0l" s0 (decodedPushContInstr #[]) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/0r0l/end: expected exhausted slice, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    { name := "unit/decode/general/len1-refs0"
      run := do
        let payload := natToBits 0xa5 8
        let s0 := mkDecodeSlice (mkGeneralBits 0 1 payload)
        let s1 ← expectDecodeStep "decode/general/0r1l" s0 (decodedPushContInstr payload) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/0r1l/end: expected exhausted slice, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    { name := "unit/decode/general/len0-refs3"
      run := do
        let refs : Array Cell := #[refLeafA, refLeafB, refLeafC]
        let s0 := mkDecodeSlice (mkGeneralBits 3 0 #[]) refs
        let s1 ← expectDecodeStep "decode/general/3r0l" s0 (decodedPushContInstr #[] refs) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/3r0l/end: expected exhausted slice, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    { name := "unit/decode/general/len2-refs2-plus-tail-add"
      run := do
        let payload := natToBits 0xc0de 16
        let refs : Array Cell := #[refLeafB, refLeafC, refLeafD]
        let bits := mkGeneralBits 2 2 payload ++ natToBits 0xa0 8
        let s0 := mkDecodeSlice bits refs
        let s1 ← expectDecodeStep "decode/general/2r2l" s0 (decodedPushContInstr payload #[refLeafB, refLeafC]) 16
        let s2 ← expectDecodeStep "decode/general/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/2r2l/end: expected bits=0 refs=1, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    { name := "unit/decode/general/max-len127-refs0"
      run := do
        let s0 := mkDecodeSlice (mkGeneralBits 0 127 code1016)
        let s1 ← expectDecodeStep "decode/general/maxlen/0refs" s0 (decodedPushContInstr code1016) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/maxlen/0refs/end: expected exhausted slice, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    { name := "unit/decode/general/max-len127-refs3"
      run := do
        let refs : Array Cell := #[refLeafA, refLeafC, refLeafD]
        let s0 := mkDecodeSlice (mkGeneralBits 3 127 code1016) refs
        let s1 ← expectDecodeStep "decode/general/maxlen/3refs" s0 (decodedPushContInstr code1016 refs) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/maxlen/3refs/end: expected exhausted slice, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    { name := "unit/decode/general/nonzero-bitpos"
      run := do
        let payload := natToBits 0x4b 8
        let baseBits : BitString := #[false, true] ++ mkGeneralBits 0 1 payload ++ natToBits 0xa0 8
        let base := mkDecodeSlice baseBits
        let shifted : Slice := { base with bitPos := 2 }
        let s1 ← expectDecodeStep "decode/general/nonzero-bitpos" shifted (decodedPushContInstr payload) 16
        let s2 ← expectDecodeStep "decode/general/nonzero-bitpos-tail" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/general/nonzero-bitpos/end: expected exhausted bits, got {s2.bitsRemaining}") }
    ,
    { name := "unit/decode/general/nonzero-refpos"
      run := do
        let refs : Array Cell := #[refLeafA, refLeafB, refLeafC]
        let bits := mkGeneralBits 1 0 #[] ++ natToBits 0xa0 8
        let base := mkDecodeSlice bits refs
        let shifted : Slice := { base with refPos := 1 }
        let s1 ← expectDecodeStep "decode/general/nonzero-refpos" shifted (decodedPushContInstr #[] #[refLeafB]) 16
        let s2 ← expectDecodeStep "decode/general/nonzero-refpos-tail" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/nonzero-refpos/end: expected bits=0 refs=1, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    { name := "unit/decode/general/two-opcodes-consume-refs-in-order"
      run := do
        let bits := mkGeneralBits 1 0 #[] ++ mkGeneralBits 1 0 #[]
        let s0 := mkDecodeSlice bits #[refLeafA, refLeafC]
        let s1 ← expectDecodeStep "decode/general/first" s0 (decodedPushContInstr #[] #[refLeafA]) 16
        let s2 ← expectDecodeStep "decode/general/second" s1 (decodedPushContInstr #[] #[refLeafC]) 16
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/two/end: expected exhausted slice, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    { name := "unit/decode/general/leaves-extra-tail-refs"
      run := do
        let s0 := mkDecodeSlice (mkGeneralBits 1 0 #[]) #[refLeafA, refLeafB, refLeafC]
        let s1 ← expectDecodeStep "decode/general/extra-refs" s0 (decodedPushContInstr #[] #[refLeafA]) 16
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 2 ∧ s1.refPos = 1 then
          pure ()
        else
          throw (IO.userError
            s!"decode/general/extra-refs/end: expected bits=0 refs=2 refPos=1, got bits={s1.bitsRemaining} refs={s1.refsRemaining} refPos={s1.refPos}") }
    ,

    -- Branch: short-vs-general and neighboring opcode boundaries.
    { name := "unit/decode/boundary/short-single-consumed8"
      run := do
        let payload := natToBits 0x3c 8
        let s0 := mkDecodeSlice (mkShortBits 1 payload)
        let s1 ← expectDecodeStep "decode/short/single" s0 (decodedPushContInstr payload) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/short/single/end: expected exhausted slice, got bits={s1.bitsRemaining} refs={s1.refsRemaining}") }
    ,
    { name := "unit/decode/boundary/short-then-general-sequence"
      run := do
        let shortPayload : BitString := #[]
        let generalPayload := natToBits 0xb7 8
        let bits : BitString :=
          mkShortBits 0 shortPayload ++
          mkGeneralBits 1 1 generalPayload ++
          natToBits 0xa0 8
        let s0 := mkDecodeSlice bits #[refLeafD]
        let s1 ← expectDecodeStep "decode/boundary/short" s0 (decodedPushContInstr #[]) 8
        let s2 ← expectDecodeStep "decode/boundary/general" s1 (decodedPushContInstr generalPayload #[refLeafD]) 16
        let s3 ← expectDecodeStep "decode/boundary/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 ∧ s3.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/boundary/short-general/end: expected exhausted slice, got bits={s3.bitsRemaining} refs={s3.refsRemaining}") }
    ,
    { name := "unit/decode/boundary/neighbor-0x8b-is-pushsliceconst"
      run := do
        let bits : BitString :=
          natToBits 0x8b 8 ++ natToBits 0 4 ++ natToBits 0x8 4 ++ natToBits 0xa0 8
        let s0 := mkDecodeSlice bits
        let s1 ← expectDecodeStep "decode/boundary/0x8b" s0 (.pushSliceConst (Slice.ofCell Cell.empty)) 12
        let s2 ← expectDecodeStep "decode/boundary/0x8b-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/boundary/0x8b/end: expected exhausted bits, got {s2.bitsRemaining}") }
    ,

    -- Branch: decode error paths for general/short PUSHCONT forms.
    { name := "unit/decode/error/general-truncated-15bits"
      run := do
        let truncated := (mkGeneralBits 0 0 #[]).pop
        expectDecodeInvOpcode "decode/error/general-truncated" (mkSliceFromBits truncated) }
    ,
    { name := "unit/decode/error/general-missing-inline-bits"
      run := do
        let bits := mkGeneralBits 0 3 (natToBits 0x1234 16)
        expectDecodeInvOpcode "decode/error/general-missing-bits" (mkSliceFromBits bits) }
    ,
    { name := "unit/decode/error/general-missing-refs"
      run := do
        let bits := mkGeneralBits 2 1 (natToBits 0xff 8)
        expectDecodeInvOpcode "decode/error/general-missing-refs" (mkDecodeSlice bits #[refLeafA]) }
    ,
    { name := "unit/decode/error/second-general-missing-ref-after-first"
      run := do
        let bits := mkGeneralBits 1 0 #[] ++ mkGeneralBits 1 0 #[]
        let s0 := mkDecodeSlice bits #[refLeafA]
        let s1 ← expectDecodeStep "decode/error/first-general" s0 (decodedPushContInstr #[] #[refLeafA]) 16
        expectDecodeInvOpcode "decode/error/second-general" s1 }
    ,
    { name := "unit/decode/error/empty-slice"
      run := do
        expectDecodeInvOpcode "decode/error/empty" (Slice.ofCell Cell.empty) }
    ,

    -- Branch: assembler rejects `.pushCont _` (decode-only in current `assembleCp0`).
    { name := "unit/assembler/encodecp0-rejects-pushcont"
      run := do
        expectInvOpcode "assemble/encode-pushcont"
          (encodeCp0 (.pushCont codeBits32)) }
    ,
    { name := "unit/assembler/assemblecp0-single-pushcont-rejected"
      run := do
        expectInvOpcode "assemble/single-pushcont"
          (assembleCp0 [(.pushCont codeWithRefs1)]) }
    ,
    { name := "unit/assembler/assemblecp0-sequence-containing-pushcont-rejected"
      run := do
        expectInvOpcode "assemble/sequence-pushcont"
          (assembleCp0 [.add, (.pushCont codeWithRefs3), .newc]) }
  ]
  -- `.pushCont` is not encodable by `assembleCp0`; oracle/fuzz harness requires assembly.
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHCONT
