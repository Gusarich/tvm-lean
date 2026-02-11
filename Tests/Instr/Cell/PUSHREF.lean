import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PUSHREF

/-
PUSHREF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PushRef.lean` (`execInstrFlowPushRef`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0x88` decode with one attached ref)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.pushRef _` rejected by standalone encoder)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_push_ref`, mode 0 path; table entry at opcode `0x88`)

Branch map used for this suite:
- exec path: 1 branch site / 2 outcomes
  (`.pushRef c` pushes `.cell c`; non-`.pushRef` falls through to `next`).
- decode path for `0x88`: success (has one ref) vs `.invOpcode` (missing attached ref).
- assembler path: `encodeCp0`/`assembleCp0` reject `.pushRef _` (`.invOpcode`).

Key risk areas:
- PUSHREF must not pop/type-check any existing stack entries;
- pushed value must preserve full referenced cell payload/graph exactly;
- PUSHREF must not perform a cell-load side effect (contrast with PUSHREFSLICE);
- opcode boundaries around `0x88` (`0x89`, `0x8a`, `0x8b`) and truncated/missing-ref decode errors.
-/

private def pushRefId : InstrId := { name := "PUSHREF" }

private def dispatchSentinel : Int := 8801

private def mkCell (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary bits refs

private def refLeaf0 : Cell :=
  Cell.empty

private def refLeaf1 : Cell :=
  mkCell (natToBits 0b10101 5)

private def refLeaf2 : Cell :=
  mkCell (natToBits 0xA5 8) #[refLeaf0]

private def refLeaf3 : Cell :=
  mkCell (natToBits 0x15 5) #[refLeaf1, Cell.empty]

private def pushCellEmpty : Cell :=
  Cell.empty

private def pushCellBitsOnly : Cell :=
  mkCell (natToBits 0x5AA 11)

private def pushCellOneRef : Cell :=
  mkCell (natToBits 0x7F 7) #[refLeaf1]

private def pushCellFourRefsMaxBits : Cell :=
  mkCell (Array.replicate 1023 false) #[refLeaf0, refLeaf1, refLeaf2, refLeaf3]

private def pushCellNested : Cell :=
  mkCell (natToBits 0x12F 9) #[refLeaf2, refLeaf3]

private def noiseSlice : Slice :=
  Slice.ofCell (mkCell (natToBits 0x3A 6) #[refLeaf0, refLeaf2])

private def runPushRefDirect (c : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushRef (.pushRef c) stack

private def runPushRefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushRef instr (VM.push (intV dispatchSentinel)) stack

private def runPushRefState
    (instr : Instr)
    (stack : Array Value) : Except Excno VmState := do
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrFlowPushRef instr (pure ())).run st0
  match res with
  | .ok _ => pure st1
  | .error e => throw e

private def mkCodeSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

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
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectInvOpcode
    (label : String)
    (res : Except Excno α) : IO Unit := do
  match res with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode, got success")

private def pushRefOpcode : Nat := 0x88

private def mkOracleCase
    (name : String)
    (refCell : Cell)
    (initStack : Array Value := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pushRefId
    codeCell? := some (Cell.mkOrdinary (natToBits pushRefOpcode 8) #[refCell])
    initStack := initStack
    fuel := fuel }

private def mkOracleMissingRefCase
    (name : String)
    (initStack : Array Value := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pushRefId
    codeCell? := some (Cell.mkOrdinary (natToBits pushRefOpcode 8) #[])
    initStack := initStack
    fuel := fuel }

def suite : InstrSuite where
  id := pushRefId
  unit := #[
    -- Branch map: exec success arm (`.pushRef c`) on empty stack.
    { name := "unit/direct/push-empty-cell-on-empty-stack"
      run := do
        expectOkStack "direct/empty-cell"
          (runPushRefDirect pushCellEmpty #[])
          #[.cell pushCellEmpty] }
    ,
    -- Branch map: exec success arm with bits-only payload.
    { name := "unit/direct/push-bits-only-cell"
      run := do
        expectOkStack "direct/bits-only"
          (runPushRefDirect pushCellBitsOnly #[])
          #[.cell pushCellBitsOnly] }
    ,
    -- Branch map: exec success arm with one nested ref.
    { name := "unit/direct/push-cell-with-one-ref"
      run := do
        expectOkStack "direct/one-ref"
          (runPushRefDirect pushCellOneRef #[])
          #[.cell pushCellOneRef] }
    ,
    -- Branch map: exec success arm with max refs(4) and max bits(1023) boundary payload.
    { name := "unit/direct/push-cell-with-four-refs-and-1023-bits"
      run := do
        expectOkStack "direct/four-refs-1023-bits"
          (runPushRefDirect pushCellFourRefsMaxBits #[])
          #[.cell pushCellFourRefsMaxBits] }
    ,
    -- Branch map: no-pop contract preserves below-stack `null`.
    { name := "unit/direct/preserve-null-below"
      run := do
        expectOkStack "direct/preserve-null"
          (runPushRefDirect pushCellNested #[.null])
          #[.null, .cell pushCellNested] }
    ,
    -- Branch map: no-pop contract preserves below-stack int.
    { name := "unit/direct/preserve-int-below"
      run := do
        expectOkStack "direct/preserve-int"
          (runPushRefDirect pushCellNested #[intV (-19)])
          #[intV (-19), .cell pushCellNested] }
    ,
    -- Branch map: no-pop contract preserves below-stack cell.
    { name := "unit/direct/preserve-cell-below"
      run := do
        expectOkStack "direct/preserve-cell"
          (runPushRefDirect pushCellNested #[.cell refLeaf2])
          #[.cell refLeaf2, .cell pushCellNested] }
    ,
    -- Branch map: no-pop contract preserves below-stack slice.
    { name := "unit/direct/preserve-slice-below"
      run := do
        expectOkStack "direct/preserve-slice"
          (runPushRefDirect pushCellNested #[.slice noiseSlice])
          #[.slice noiseSlice, .cell pushCellNested] }
    ,
    -- Branch map: no-pop contract preserves below-stack builder.
    { name := "unit/direct/preserve-builder-below"
      run := do
        expectOkStack "direct/preserve-builder"
          (runPushRefDirect pushCellNested #[.builder Builder.empty])
          #[.builder Builder.empty, .cell pushCellNested] }
    ,
    -- Branch map: no-pop contract preserves below-stack tuple.
    { name := "unit/direct/preserve-tuple-below"
      run := do
        expectOkStack "direct/preserve-tuple"
          (runPushRefDirect pushCellNested #[.tuple #[]])
          #[.tuple #[], .cell pushCellNested] }
    ,
    -- Branch map: no-pop contract preserves below-stack continuation.
    { name := "unit/direct/preserve-quit-continuation-below"
      run := do
        expectOkStack "direct/preserve-cont"
          (runPushRefDirect pushCellNested #[.cont (.quit 3)])
          #[.cont (.quit 3), .cell pushCellNested] }
    ,
    -- Branch map: no-pop contract preserves deep mixed stack order exactly.
    { name := "unit/direct/deep-mixed-stack-preservation"
      run := do
        let inStack : Array Value :=
          #[.null, intV 7, .slice noiseSlice, .builder Builder.empty, .tuple #[]]
        expectOkStack "direct/deep-preserve"
          (runPushRefDirect pushCellOneRef inStack)
          (inStack ++ #[.cell pushCellOneRef]) }
    ,
    -- Branch map: repeated success path appends one cell per execution.
    { name := "unit/direct/repeated-pushref-appends-cells"
      run := do
        let s1 ←
          match runPushRefDirect pushCellBitsOnly #[intV 9] with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"repeat/first: expected success, got {e}")
        expectOkStack "repeat/second"
          (runPushRefDirect pushCellOneRef s1)
          #[intV 9, .cell pushCellBitsOnly, .cell pushCellOneRef] }
    ,
    -- Branch map: success path must not register cell-load side effects.
    { name := "unit/direct/no-cell-load-side-effect"
      run := do
        match runPushRefState (.pushRef pushCellNested) #[intV 1] with
        | .error e =>
            throw (IO.userError s!"state/no-cell-load: expected success, got {e}")
        | .ok st =>
            if st.stack != #[intV 1, .cell pushCellNested] then
              throw (IO.userError s!"state/no-cell-load: unexpected stack {reprStr st.stack}")
            else if st.loadedCells.isEmpty then
              pure ()
            else
              throw (IO.userError s!"state/no-cell-load: expected no loaded cells, got {st.loadedCells.size}") }
    ,
    -- Branch map: non-`.pushRef` dispatch falls through to `next`.
    { name := "unit/dispatch/non-pushref-add-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runPushRefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel] }
    ,
    -- Branch map: non-`.pushRef` neighbor opcode (`PUSHREFSLICE`) still falls through in this handler.
    { name := "unit/dispatch/non-pushref-neighbor-falls-through"
      run := do
        expectOkStack "dispatch/pushrefslice-neighbor"
          (runPushRefDispatchFallback (.pushRefSlice pushCellOneRef) #[intV 4])
          #[intV 4, intV dispatchSentinel] }
    ,
    -- Branch map: cp0 decode success for exact `0x88` with one attached ref.
    { name := "unit/decode/0x88-single-ref"
      run := do
        let s0 := mkCodeSlice (natToBits 0x88 8) #[pushCellOneRef]
        let s1 ← expectDecodeStep "decode/0x88" s0 (.pushRef pushCellOneRef) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/0x88: expected exhausted slice, got bits={s1.bitsRemaining}, refs={s1.refsRemaining}") }
    ,
    -- Branch map: cp0 `0x88` decode then tail opcode decode continuity.
    { name := "unit/decode/0x88-followed-by-add"
      run := do
        let s0 := mkCodeSlice (natToBits 0x88 8 ++ natToBits 0xa0 8) #[pushCellNested]
        let s1 ← expectDecodeStep "decode/0x88-first" s0 (.pushRef pushCellNested) 8
        let s2 ← expectDecodeStep "decode/0xa0-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/0x88+add-end: expected exhausted slice, got bits={s2.bitsRemaining}, refs={s2.refsRemaining}") }
    ,
    -- Branch map: opcode neighborhood around `0x88` decodes to PUSHREF/PUSHREFSLICE/PUSHREFCONT in order.
    { name := "unit/decode/sequence-0x88-0x89-0x8a"
      run := do
        let bits : BitString :=
          natToBits 0x88 8 ++ natToBits 0x89 8 ++ natToBits 0x8a 8
        let refs : Array Cell := #[pushCellEmpty, pushCellOneRef, pushCellNested]
        let s0 := mkCodeSlice bits refs
        let s1 ← expectDecodeStep "decode/seq-0x88" s0 (.pushRef pushCellEmpty) 8
        let s2 ← expectDecodeStep "decode/seq-0x89" s1 (.pushRefSlice pushCellOneRef) 8
        let s3 ← expectDecodeStep "decode/seq-0x8a" s2 (.pushRefCont pushCellNested) 8
        if s3.bitsRemaining = 0 ∧ s3.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/seq-end: expected exhausted slice, got bits={s3.bitsRemaining}, refs={s3.refsRemaining}") }
    ,
    -- Branch map: right-neighbor `0x89` must decode as PUSHREFSLICE, not PUSHREF.
    { name := "unit/decode/neighbor-0x89-pushrefslice"
      run := do
        let s0 := mkCodeSlice (natToBits 0x89 8) #[pushCellOneRef]
        let s1 ← expectDecodeStep "decode/0x89" s0 (.pushRefSlice pushCellOneRef) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/0x89-end: expected exhausted slice, got bits={s1.bitsRemaining}, refs={s1.refsRemaining}") }
    ,
    -- Branch map: right-neighbor `0x8a` must decode as PUSHREFCONT, not PUSHREF.
    { name := "unit/decode/neighbor-0x8a-pushrefcont"
      run := do
        let s0 := mkCodeSlice (natToBits 0x8a 8) #[pushCellNested]
        let s1 ← expectDecodeStep "decode/0x8a" s0 (.pushRefCont pushCellNested) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/0x8a-end: expected exhausted slice, got bits={s1.bitsRemaining}, refs={s1.refsRemaining}") }
    ,
    -- Branch map: next opcode `0x8b` (PUSHSLICE const) is decoded distinctly from PUSHREF family.
    { name := "unit/decode/neighbor-0x8b-pushsliceconst"
      run := do
        let bits : BitString :=
          natToBits 0x8b 8 ++ natToBits 0 4 ++ natToBits 0x8 4 ++ natToBits 0xa0 8
        let s0 := mkCodeSlice bits
        let s1 ← expectDecodeStep "decode/0x8b-pushsliceconst" s0 (.pushSliceConst (Slice.ofCell Cell.empty)) 12
        let s2 ← expectDecodeStep "decode/0x8b-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/0x8b-end: expected exhausted bits, got {s2.bitsRemaining}") }
    ,
    -- Branch map: consecutive PUSHREF opcodes consume refs in-order.
    { name := "unit/decode/ref-consumption-order-two-pushrefs"
      run := do
        let s0 := mkCodeSlice (natToBits 0x88 8 ++ natToBits 0x88 8) #[pushCellBitsOnly, pushCellOneRef]
        let s1 ← expectDecodeStep "decode/first-0x88" s0 (.pushRef pushCellBitsOnly) 8
        let s2 ← expectDecodeStep "decode/second-0x88" s1 (.pushRef pushCellOneRef) 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/two-0x88-end: expected exhausted slice, got bits={s2.bitsRemaining}, refs={s2.refsRemaining}") }
    ,
    -- Branch map: single `0x88` consumes exactly one ref and leaves any extras untouched.
    { name := "unit/decode/0x88-leaves-extra-refs"
      run := do
        let s0 := mkCodeSlice (natToBits 0x88 8) #[pushCellEmpty, pushCellBitsOnly, pushCellNested]
        let s1 ← expectDecodeStep "decode/0x88-extra-refs" s0 (.pushRef pushCellEmpty) 8
        if s1.bitsRemaining = 0 ∧ s1.refsRemaining = 2 ∧ s1.refPos = 1 then
          pure ()
        else
          throw (IO.userError s!"decode/0x88-extra-refs: expected bits=0 refs=2 refPos=1, got bits={s1.bitsRemaining} refs={s1.refsRemaining} refPos={s1.refPos}") }
    ,
    -- Branch map: rest slice after decoding `0x88` preserves both tail bits and tail refs.
    { name := "unit/decode/0x88-rest-preserves-tail-bits-and-refs"
      run := do
        let s0 := mkCodeSlice (natToBits 0x88 8 ++ natToBits 0xa0 8) #[pushCellOneRef, pushCellNested]
        let s1 ← expectDecodeStep "decode/0x88-rest" s0 (.pushRef pushCellOneRef) 8
        if s1.bitsRemaining = 8 ∧ s1.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError s!"decode/0x88-rest: expected bits=8 refs=1, got bits={s1.bitsRemaining} refs={s1.refsRemaining}")
        let s2 ← expectDecodeStep "decode/rest-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError s!"decode/rest-end: expected bits=0 refs=1, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    -- Branch map: `0x88` decode error branch when no attached ref exists.
    { name := "unit/decode/error-0x88-missing-ref"
      run := do
        expectDecodeErr "decode/error-no-ref"
          (mkCodeSlice (natToBits 0x88 8) #[])
          .invOpcode }
    ,
    -- Branch map: second `0x88` in sequence hits missing-ref error after first succeeds.
    { name := "unit/decode/error-second-0x88-missing-ref"
      run := do
        let s0 := mkCodeSlice (natToBits 0x88 8 ++ natToBits 0x88 8) #[pushCellBitsOnly]
        let tail ← expectDecodeStep "decode/error-seq-first" s0 (.pushRef pushCellBitsOnly) 8
        expectDecodeErr "decode/error-seq-second"
          tail
          .invOpcode }
    ,
    -- Branch map: truncated prefix (<8 bits) must fail as invalid opcode.
    { name := "unit/decode/error-truncated-prefix-7bits"
      run := do
        expectDecodeErr "decode/error-truncated-7bits"
          (mkCodeSlice (natToBits 0x44 7))
          .invOpcode }
    ,
    -- Branch map: empty code slice decode failure.
    { name := "unit/decode/error-empty-slice"
      run := do
        expectDecodeErr "decode/error-empty"
          (Slice.ofCell Cell.empty)
          .invOpcode }
    ,
    -- Branch map: missing-ref check for `0x88` fires before/independent of tail bits.
    { name := "unit/decode/error-0x88-missing-ref-even-with-tail"
      run := do
        expectDecodeErr "decode/error-no-ref-with-tail"
          (mkCodeSlice (natToBits 0x88 8 ++ natToBits 0xa0 8) #[])
          .invOpcode }
    ,
    -- Branch map: decode honors current `refPos`; already-consumed refs trigger missing-ref branch.
    { name := "unit/decode/error-nonzero-refpos-no-remaining-ref"
      run := do
        let base := mkCodeSlice (natToBits 0x88 8) #[pushCellOneRef]
        let shifted : Slice := { base with refPos := 1 }
        expectDecodeErr "decode/error-refpos-shifted"
          shifted
          .invOpcode }
    ,
    -- Branch map: decode honors current `bitPos`; 0x88 at non-zero bit offset still decodes.
    { name := "unit/decode/nonzero-bitpos-still-decodes-0x88"
      run := do
        let baseBits : BitString := #[false] ++ natToBits 0x88 8 ++ natToBits 0xa0 8
        let base := mkCodeSlice baseBits #[pushCellNested]
        let shifted : Slice := { base with bitPos := 1 }
        let s1 ← expectDecodeStep "decode/nonzero-bitpos-0x88" shifted (.pushRef pushCellNested) 8
        let s2 ← expectDecodeStep "decode/nonzero-bitpos-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/nonzero-bitpos-end: expected exhausted slice, got bits={s2.bitsRemaining}") }
    ,
    -- Branch map: assembler-side standalone encoder rejects `.pushRef _`.
    { name := "unit/assembler/encodecp0-rejects-pushref"
      run := do
        expectInvOpcode "assembler/encodecp0-pushref"
          (encodeCp0 (.pushRef pushCellEmpty)) }
    ,
    -- Branch map: assembler-side program assembly rejects PUSHREF (ref-embedded opcode gap).
    { name := "unit/assembler/assemblecp0-single-pushref-rejected"
      run := do
        expectInvOpcode "assembler/assemble-single-pushref"
          (assembleCp0 [(.pushRef pushCellOneRef)]) }
    ,
    -- Branch map: assembly fails even when PUSHREF appears after encodable neighbors.
    { name := "unit/assembler/assemblecp0-sequence-containing-pushref-rejected"
      run := do
        expectInvOpcode "assembler/assemble-seq-with-pushref"
          (assembleCp0 [.add, (.pushRef pushCellNested), .newc]) }
  ]
  oracle := #[
    -- Branch: successful decode+exec pushes referenced cell value.
    mkOracleCase "ok/ref-empty-cell" pushCellEmpty,
    mkOracleCase "ok/ref-bits-only" pushCellBitsOnly,
    mkOracleCase "ok/ref-one-ref" pushCellOneRef,
    mkOracleCase "ok/ref-nested" pushCellNested,
    mkOracleCase "ok/ref-four-refs-1023-bits" pushCellFourRefsMaxBits,
    mkOracleCase "ok/deep-stack-preservation" pushCellOneRef
      #[.null, intV 7, .slice noiseSlice, .builder Builder.empty, .tuple #[]],

    -- Branch: decode-time `haveRefs 1` guard (`invOpcode`) when ref is missing.
    mkOracleMissingRefCase "decode/err/missing-ref",
    mkOracleMissingRefCase "decode/err/missing-ref-with-deep-stack"
      #[.null, intV (-9)]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHREF
