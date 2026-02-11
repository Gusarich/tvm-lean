import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PUSHSLICE_REFS

/-!
PUSHSLICE_REFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PushSliceConst.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`PUSHSLICE_REFS` decode path)
  - `TvmLean/Spec/Index.lean` (`PUSHSLICE_REFS` prefix row)
- C++ authority (referenced by Lean decoder comments):
  - `crypto/vm/cellops.cpp` (`exec_push_slice_r`).

Covered branches:
- flow dispatch guard: `.pushSliceConst` handled vs fallthrough to `next`;
- push semantics contract: push exact slice value, preserve deeper stack order;
- decoder success across `r=0..3` and `bits5=0..31` boundaries;
- decoder failure branches for truncated data and insufficient inline refs;
- opcode/decode boundary checks vs neighboring 0x8b (`PUSHSLICE`),
  18-bit 0x8d (`PUSHSLICE_LONG`), and 16-bit 0x8e (`PUSHCONT`).
-/

private def pushsliceRefsId : InstrId := { name := "PUSHSLICE_REFS" }

private def dispatchSentinel : Int := 920317

private def execInstrFlowPushsliceRefsOnly (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrFlowPushSliceConst i next

private def runPushsliceRefsDirect
    (s : Slice)
    (stack : Array Value := #[]) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushsliceRefsOnly (.pushSliceConst s) stack

private def runPushsliceRefsDispatchWithNext
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushsliceRefsOnly instr (VM.push (intV dispatchSentinel)) stack

private def patternBits (n : Nat) (phase : Nat := 0) : BitString := Id.run do
  let mut out : BitString := #[]
  for i in [0:n] do
    let bit := ((i + phase) % 2 = 0) || ((i + phase) % 5 = 3)
    out := out.push bit
  return out

private def refCellA : Cell :=
  Cell.empty

private def refCellB : Cell :=
  Cell.mkOrdinary (patternBits 5 1) #[]

private def refCellC : Cell :=
  Cell.mkOrdinary (patternBits 11 2) #[refCellA]

private def refCellD : Cell :=
  Cell.mkOrdinary (patternBits 17 3) #[refCellB, refCellA]

private def refs1 : Array Cell :=
  #[refCellA]

private def refs2 : Array Cell :=
  #[refCellA, refCellB]

private def refs3 : Array Cell :=
  #[refCellA, refCellB, refCellC]

private def refs4 : Array Cell :=
  #[refCellA, refCellB, refCellC, refCellD]

private def execSliceBase : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternBits 23 1) refs4)

private def execSliceEmpty : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] refs1)

private def execSliceShifted : Slice :=
  { execSliceBase.advanceBits 9 with refPos := 2 }

private def execSlicePastEnd : Slice :=
  { execSliceBase with
      bitPos := execSliceBase.cell.bits.size + 5
      refPos := execSliceBase.cell.refs.size + 1 }

private def expectedPushsliceRefsOut (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[.slice s]

private def mkPushsliceRefsHeaderBits (r bits5 : Nat) : Except String BitString := do
  if r > 3 then
    throw s!"invalid r={r}, expected 0..3"
  if bits5 > 31 then
    throw s!"invalid bits5={bits5}, expected 0..31"
  let w15 : Nat := ((0x8c : Nat) <<< 7) + (r <<< 5) + bits5
  pure (natToBits w15 15)

private def mkRawWithMarker (payloadBits : BitString) (bits5 : Nat) : Except String BitString := do
  let cap : Nat := bits5 * 8
  if payloadBits.size > cap then
    throw s!"payload size {payloadBits.size} exceeds bits5 capacity {cap}"
  let pad : Nat := cap - payloadBits.size
  pure (payloadBits ++ #[true] ++ Array.replicate pad false)

private def mkPushsliceRefsCodeBits
    (r bits5 : Nat)
    (payloadBits : BitString)
    (tailBits : BitString := #[]) : Except String BitString := do
  let hdr ← mkPushsliceRefsHeaderBits r bits5
  let raw ← mkRawWithMarker payloadBits bits5
  pure (hdr ++ raw ++ tailBits)

private def mkPushsliceRefsCodeBitsRaw
    (r bits5 : Nat)
    (raw : BitString)
    (tailBits : BitString := #[]) : Except String BitString := do
  let hdr ← mkPushsliceRefsHeaderBits r bits5
  let needRaw : Nat := bits5 * 8 + 1
  if raw.size != needRaw then
    throw s!"raw size mismatch: expected {needRaw}, got {raw.size}"
  pure (hdr ++ raw ++ tailBits)

private def mkPushsliceShortBits (args4 : Nat) (raw : BitString) : Except String BitString := do
  if args4 > 15 then
    throw s!"invalid args4={args4}, expected <= 15"
  let needRaw : Nat := args4 * 8 + 4
  if raw.size != needRaw then
    throw s!"short raw size mismatch: expected {needRaw}, got {raw.size}"
  pure (natToBits 0x8b 8 ++ natToBits args4 4 ++ raw)

private def mkPushsliceLongBits (refs len7 : Nat) (raw : BitString) : Except String BitString := do
  if refs > 4 then
    throw s!"invalid refs={refs}, expected <= 4"
  if len7 > 127 then
    throw s!"invalid len7={len7}, expected <= 127"
  let needRaw : Nat := len7 * 8 + 6
  if raw.size != needRaw then
    throw s!"long raw size mismatch: expected {needRaw}, got {raw.size}"
  let w18 : Nat := ((0x8d : Nat) <<< 10) + (refs <<< 7) + len7
  pure (natToBits w18 18 ++ raw)

private def unwrapBits (label : String) (x : Except String BitString) : IO BitString := do
  match x with
  | .ok bits => pure bits
  | .error e => throw (IO.userError s!"{label}: {e}")

private def expectedDecodedPushsliceRefsInstr
    (payloadBits : BitString)
    (allRefs : Array Cell)
    (r : Nat) : Instr :=
  .pushSliceConst (Slice.ofCell (Cell.mkOrdinary payloadBits (allRefs.extract 0 (r + 1))))

private def expectDecodePushsliceRefsOk
    (label : String)
    (r bits5 : Nat)
    (payloadBits : BitString)
    (refs : Array Cell)
    (tailBits : BitString := #[]) : IO Slice := do
  let codeBits ← unwrapBits label (mkPushsliceRefsCodeBits r bits5 payloadBits tailBits)
  let s0 := Slice.ofCell (Cell.mkOrdinary codeBits refs)
  expectDecodeStep label s0 (expectedDecodedPushsliceRefsInstr payloadBits refs r) 15

private def expectDecodePushsliceRefsOkRaw
    (label : String)
    (r bits5 : Nat)
    (raw : BitString)
    (expectedPayload : BitString)
    (refs : Array Cell)
    (tailBits : BitString := #[]) : IO Slice := do
  let codeBits ← unwrapBits label (mkPushsliceRefsCodeBitsRaw r bits5 raw tailBits)
  let s0 := Slice.ofCell (Cell.mkOrdinary codeBits refs)
  expectDecodeStep label s0 (expectedDecodedPushsliceRefsInstr expectedPayload refs r) 15

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectRemaining
    (label : String)
    (s : Slice)
    (expectedBits expectedRefs : Nat) : IO Unit := do
  if s.bitsRemaining = expectedBits then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected bitsRemaining={expectedBits}, got {s.bitsRemaining}")
  if s.refsRemaining = expectedRefs then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected refsRemaining={expectedRefs}, got {s.refsRemaining}")

private def expectRemainingTailBits
    (label : String)
    (s : Slice)
    (expected : BitString) : IO Unit := do
  let got := s.readBits s.bitsRemaining
  if got = expected then
    pure ()
  else
    throw (IO.userError s!"{label}: tail bits mismatch; expected {expected}, got {got}")

private def remainingRefs (s : Slice) : Array Cell :=
  s.cell.refs.extract s.refPos s.cell.refs.size

private def expectRemainingRefs
    (label : String)
    (s : Slice)
    (expected : Array Cell) : IO Unit := do
  let got := remainingRefs s
  if got == expected then
    pure ()
  else
    throw (IO.userError s!"{label}: remaining refs mismatch; expected {reprStr expected}, got {reprStr got}")

private def decodeOnce
    (label : String)
    (s : Slice) : IO (Instr × Nat × Slice) := do
  match decodeCp0WithBits s with
  | .ok out => pure out
  | .error e => throw (IO.userError s!"{label}: decode failed with {e}")

def suite : InstrSuite where
  id := pushsliceRefsId
  unit := #[
    { name := "unit/exec/direct/push-empty-slice"
      run := do
        expectOkStack "exec/empty"
          (runPushsliceRefsDirect execSliceEmpty)
          #[.slice execSliceEmpty] }
    ,
    { name := "unit/exec/direct/preserve-below-stack"
      run := do
        expectOkStack "exec/deep"
          (runPushsliceRefsDirect execSliceBase #[.null, intV (-17)])
          (expectedPushsliceRefsOut #[.null, intV (-17)] execSliceBase) }
    ,
    { name := "unit/exec/direct/push-shifted-slice-verbatim"
      run := do
        expectOkStack "exec/shifted"
          (runPushsliceRefsDirect execSliceShifted)
          #[.slice execSliceShifted] }
    ,
    { name := "unit/exec/direct/push-past-end-slice-verbatim"
      run := do
        expectOkStack "exec/past-end"
          (runPushsliceRefsDirect execSlicePastEnd)
          #[.slice execSlicePastEnd] }
    ,
    { name := "unit/exec/dispatch/fallback-on-non-pushsliceconst"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runPushsliceRefsDispatchWithNext .add #[.cell refCellA])
          #[.cell refCellA, intV dispatchSentinel]
        expectOkStack "dispatch/fallback-pushref"
          (runPushsliceRefsDispatchWithNext (.pushRef refCellB) #[intV 3])
          #[intV 3, intV dispatchSentinel] }
    ,
    { name := "unit/exec/dispatch/handled-pushsliceconst-skips-next"
      run := do
        expectOkStack "dispatch/handled"
          (runPushsliceRefsDispatchWithNext (.pushSliceConst execSliceBase) #[.null])
          #[.null, .slice execSliceBase] }
    ,
    { name := "unit/decode/ok/r0-bits0-minimal"
      run := do
        let rest ← expectDecodePushsliceRefsOk "decode/r0-b0" 0 0 #[] refs1
        expectRemaining "decode/r0-b0/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r0-bits1"
      run := do
        let payload := patternBits 1 0
        let rest ← expectDecodePushsliceRefsOk "decode/r0-b1" 0 1 payload refs1
        expectRemaining "decode/r0-b1/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r0-bits7"
      run := do
        let payload := patternBits 7 1
        let rest ← expectDecodePushsliceRefsOk "decode/r0-b7" 0 1 payload refs1
        expectRemaining "decode/r0-b7/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r0-bits8"
      run := do
        let payload := patternBits 8 2
        let rest ← expectDecodePushsliceRefsOk "decode/r0-b8" 0 1 payload refs1
        expectRemaining "decode/r0-b8/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r1-bits0"
      run := do
        let rest ← expectDecodePushsliceRefsOk "decode/r1-b0" 1 0 #[] refs2
        expectRemaining "decode/r1-b0/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r1-bits9"
      run := do
        let payload := patternBits 9 3
        let rest ← expectDecodePushsliceRefsOk "decode/r1-b9" 1 2 payload refs2
        expectRemaining "decode/r1-b9/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r2-bits16"
      run := do
        let payload := patternBits 16 1
        let rest ← expectDecodePushsliceRefsOk "decode/r2-b16" 2 2 payload refs3
        expectRemaining "decode/r2-b16/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r2-bits23"
      run := do
        let payload := patternBits 23 4
        let rest ← expectDecodePushsliceRefsOk "decode/r2-b23" 2 3 payload refs3
        expectRemaining "decode/r2-b23/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r3-bits0"
      run := do
        let rest ← expectDecodePushsliceRefsOk "decode/r3-b0" 3 0 #[] refs4
        expectRemaining "decode/r3-b0/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r3-bits31"
      run := do
        let payload := patternBits 31 2
        let rest ← expectDecodePushsliceRefsOk "decode/r3-b31" 3 4 payload refs4
        expectRemaining "decode/r3-b31/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/r3-bits248-maximum"
      run := do
        let payload := patternBits 248 5
        let rest ← expectDecodePushsliceRefsOk "decode/r3-b248" 3 31 payload refs4
        expectRemaining "decode/r3-b248/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/markerless-all-zero-raw-decodes-empty"
      run := do
        let raw : BitString := Array.replicate 17 false
        let rest ←
          expectDecodePushsliceRefsOkRaw
            "decode/markerless-zero"
            0
            2
            raw
            #[]
            refs1
        expectRemaining "decode/markerless-zero/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/rest-tail-bits-preserved"
      run := do
        let payload := patternBits 5 1
        let tailBits := patternBits 13 2
        let rest ← expectDecodePushsliceRefsOk "decode/rest-tail" 0 1 payload refs1 tailBits
        expectRemaining "decode/rest-tail/size" rest tailBits.size 0
        expectRemainingTailBits "decode/rest-tail/bits" rest tailBits }
    ,
    { name := "unit/decode/ok/rest-extra-refs-preserved"
      run := do
        let payload := patternBits 4 0
        let rest ← expectDecodePushsliceRefsOk "decode/rest-refs" 1 1 payload refs4
        expectRemaining "decode/rest-refs/size" rest 0 2
        expectRemainingRefs "decode/rest-refs/order" rest #[refCellC, refCellD] }
    ,
    { name := "unit/decode/ok/ref-order-preserved-r3"
      run := do
        let payload := patternBits 6 3
        let codeBits ← unwrapBits "decode/ref-order" (mkPushsliceRefsCodeBits 3 1 payload)
        let s0 := Slice.ofCell (Cell.mkOrdinary codeBits refs4)
        let (instr, bits, rest) ← decodeOnce "decode/ref-order" s0
        if bits = 15 then
          pure ()
        else
          throw (IO.userError s!"decode/ref-order: expected bits=15, got {bits}")
        let expected := expectedDecodedPushsliceRefsInstr payload refs4 3
        if instr == expected then
          pure ()
        else
          throw (IO.userError s!"decode/ref-order: instr mismatch; expected {reprStr expected}, got {reprStr instr}")
        expectRemaining "decode/ref-order/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/data-padding-after-marker"
      run := do
        let payload := patternBits 10 2
        let rest ← expectDecodePushsliceRefsOk "decode/padded" 0 4 payload refs1
        expectRemaining "decode/padded/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/consumed-width-is-15"
      run := do
        let payload := patternBits 12 4
        let codeBits ← unwrapBits "decode/consumed-width" (mkPushsliceRefsCodeBits 2 2 payload)
        let s0 := Slice.ofCell (Cell.mkOrdinary codeBits refs3)
        let (_, bits, rest) ← decodeOnce "decode/consumed-width" s0
        if bits = 15 then
          pure ()
        else
          throw (IO.userError s!"decode/consumed-width: expected 15 bits consumed, got {bits}")
        expectRemaining "decode/consumed-width/rest" rest 0 0 }
    ,
    { name := "unit/decode/ok/multi-step-sequence-8b-8c-8d-add"
      run := do
        let shortBits ← unwrapBits "decode/seq/short" (mkPushsliceShortBits 0 #[true, false, false, false])
        let refsBits ← unwrapBits "decode/seq/refs" (mkPushsliceRefsCodeBits 0 0 #[])
        let longBits ←
          unwrapBits
            "decode/seq/long"
            (mkPushsliceLongBits 1 0 #[true, false, false, false, false, false])
        let addCode ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"decode/seq/add-assemble failed: {e}")
        let codeBits : BitString := shortBits ++ refsBits ++ longBits ++ addCode.bits
        let s0 := Slice.ofCell (Cell.mkOrdinary codeBits #[refCellA, refCellB])
        let s1 ← expectDecodeStep "decode/seq/8b-short" s0 (.pushSliceConst (Slice.ofCell (Cell.mkOrdinary #[] #[]))) 12
        let s2 ← expectDecodeStep "decode/seq/8c-refs" s1 (.pushSliceConst (Slice.ofCell (Cell.mkOrdinary #[] #[refCellA]))) 15
        let s3 ← expectDecodeStep "decode/seq/8d-long" s2 (.pushSliceConst (Slice.ofCell (Cell.mkOrdinary #[] #[refCellB]))) 18
        let s4 ← expectDecodeStep "decode/seq/tail-add" s3 .add 8
        expectRemaining "decode/seq/end" s4 0 0 }
    ,
    { name := "unit/decode/err/header-only-no-data"
      run := do
        let hdr ← unwrapBits "decode/err/header-only" (mkPushsliceRefsHeaderBits 0 0)
        expectDecodeErr "decode/err/header-only" (Slice.ofCell (Cell.mkOrdinary hdr refs1)) .invOpcode }
    ,
    { name := "unit/decode/err/header-plus-partial-data"
      run := do
        let hdr ← unwrapBits "decode/err/partial" (mkPushsliceRefsHeaderBits 1 3)
        let partialData : BitString := patternBits 9 1
        let bits := hdr ++ partialData
        expectDecodeErr "decode/err/partial" (Slice.ofCell (Cell.mkOrdinary bits refs2)) .invOpcode }
    ,
    { name := "unit/decode/err/full-data-missing-refs-r0"
      run := do
        let bits ← unwrapBits "decode/err/missing-refs-r0" (mkPushsliceRefsCodeBits 0 1 (patternBits 7 2))
        expectDecodeErr "decode/err/missing-refs-r0" (Slice.ofCell (Cell.mkOrdinary bits #[])) .invOpcode }
    ,
    { name := "unit/decode/err/full-data-missing-refs-r3"
      run := do
        let bits ← unwrapBits "decode/err/missing-refs-r3" (mkPushsliceRefsCodeBits 3 1 (patternBits 2 3))
        expectDecodeErr "decode/err/missing-refs-r3" (Slice.ofCell (Cell.mkOrdinary bits refs3)) .invOpcode }
    ,
    { name := "unit/decode/err/only-14-bits-with-8c-prefix"
      run := do
        let bits : BitString := natToBits 0x8c 8 ++ natToBits 0 6
        expectDecodeErr "decode/err/14bit-8c" (Slice.ofCell (Cell.mkOrdinary bits refs1)) .invOpcode }
    ,
    { name := "unit/decode/boundary/neighbors-not-8c-path"
      run := do
        let shortBits ← unwrapBits "decode/boundary/8b" (mkPushsliceShortBits 0 #[true, false, false, false])
        let shortSlice := Slice.ofCell (Cell.mkOrdinary shortBits #[])
        let _ ←
          expectDecodeStep
            "decode/boundary/8b"
            shortSlice
            (.pushSliceConst (Slice.ofCell (Cell.mkOrdinary #[] #[])))
            12

        let longBits ←
          unwrapBits
            "decode/boundary/8d"
            (mkPushsliceLongBits 1 0 #[true, false, false, false, false, false])
        let longSlice := Slice.ofCell (Cell.mkOrdinary longBits refs1)
        let _ ←
          expectDecodeStep
            "decode/boundary/8d"
            longSlice
            (.pushSliceConst (Slice.ofCell (Cell.mkOrdinary #[] #[refCellA])))
            18

        let pushcontWord : Nat := ((0x47 : Nat) <<< 9)
        let pushcontBits : BitString := natToBits pushcontWord 16
        let pushcontSlice := Slice.ofCell (Cell.mkOrdinary pushcontBits #[])
        let _ ←
          expectDecodeStep
            "decode/boundary/8e"
            pushcontSlice
            (.pushCont (Slice.ofCell (Cell.mkOrdinary #[] #[])))
            16
        pure () }
  ]
  oracle :=
    let unwrapBitsP (label : String) (x : Except String BitString) : BitString :=
      match x with
      | .ok bits => bits
      | .error e => panic! s!"PUSHSLICE_REFS oracle: {label}: {e}"

    let mkOk
        (name : String)
        (r bits5 : Nat)
        (payloadBits : BitString)
        (refs : Array Cell)
        (initStack : Array Value := #[]) : OracleCase :=
      let codeBits := unwrapBitsP name (mkPushsliceRefsCodeBits r bits5 payloadBits)
      { name := name
        instr := pushsliceRefsId
        codeCell? := some (Cell.mkOrdinary codeBits refs)
        initStack := initStack }

    let mkTruncatedRaw
        (name : String)
        (r bits5 : Nat)
        (payloadBits : BitString)
        (refs : Array Cell)
        (initStack : Array Value := #[]) : OracleCase :=
      let hdr := unwrapBitsP s!"{name}/hdr" (mkPushsliceRefsHeaderBits r bits5)
      let raw := unwrapBitsP s!"{name}/raw" (mkRawWithMarker payloadBits bits5)
      { name := name
        instr := pushsliceRefsId
        codeCell? := some (Cell.mkOrdinary (hdr ++ raw.take (raw.size - 1)) refs)
        initStack := initStack }

    #[
      mkOk "oracle/ok/r0-bits0-ref1-empty" 0 0 #[] refs1,
      mkOk "oracle/ok/r0-bits1-ref1" 0 1 (patternBits 7 0) refs1,
      mkOk "oracle/ok/r1-bits5-ref2" 1 5 (patternBits 39 1) refs2 #[.null, intV (-17)],
      mkOk "oracle/ok/r2-bits9-ref3" 2 9 (patternBits 56 2) refs3,
      mkOk "oracle/ok/r3-bits31-ref4-max" 3 31 (patternBits 248 1) refs4,

      -- Decode error: missing inline bits after header.
      { name := "oracle/err/decode/header-only-missing-inline-data"
        instr := pushsliceRefsId
        codeCell? := some (Cell.mkOrdinary (unwrapBitsP "oracle/err/decode/header-only" (mkPushsliceRefsHeaderBits 0 31)) refs1)
        initStack := #[] },

      -- Decode error: missing inline refs for r>0.
      mkOk "oracle/err/decode/missing-inline-refs" 3 3 (patternBits 20 0) refs3,

      -- Decode error: truncated inline data (raw missing final bit).
      mkTruncatedRaw "oracle/err/decode/truncated-inline-data" 0 1 (patternBits 4 1) refs1
    ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHSLICE_REFS
