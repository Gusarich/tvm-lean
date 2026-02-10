import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.XLOAD

/-
XLOAD branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.xload quiet)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd73a/0xd73b` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`XLOAD/XLOADQ` currently not encodable via `assembleCp0`; decode-only boundary)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_special_cell`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::load_library`, `lookup_library_in`)

Branch map covered by this suite:
- dispatch guard (`.xload` vs fallback `next`);
- pop path (`checkUnderflow`/`popCell`: `stkUnd` and `typeChk`);
- mandatory `registerCellLoad` (fresh vs reload gas/cache) before resolve;
- resolve split:
  ordinary passthrough, special-short, non-library special, malformed library shape,
  library lookup hit/miss/hash-mismatch/no-ref-value;
- quiet wrapping:
  success appends `-1`, resolve-failure pushes `0`, but underflow/type still throw;
- opcode/decode boundaries around `0xd739/0xd73a/0xd73b` (`XCTOS/XLOAD/XLOADQ`).
-/

private def xloadId : InstrId := { name := "XLOAD" }

private def xloadInstr : Instr := .cellExt (.xload false)

private def xloadqInstr : Instr := .cellExt (.xload true)

private def xctosInstr : Instr := .xctos

private def xloadOpcode : Nat := 0xd73a

private def xloadqOpcode : Nat := 0xd73b

private def xctosOpcode : Nat := 0xd739

private def dispatchSentinel : Int := 731

private def runXloadDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt xloadInstr stack

private def runXloadQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt xloadqInstr stack

private def runXloadDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt instr (VM.push (intV dispatchSentinel)) stack

private def runXloadRaw
    (instr : Instr)
    (stack : Array Value)
    (libraries : Array Cell := #[])
    (loadedCells : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      libraries := libraries
      loadedCells := loadedCells }
  let (res, st1) := (execInstrCellExt instr (pure ())).run st0
  (res, st1)

private def expectOkExcept {α : Type} (label : String) (res : Except Excno α) : IO α := do
  match res with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawOkStack
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Array Value) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ =>
      if st.stack == expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st.stack}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErrStack
    (label : String)
    (out : Except Excno Unit × VmState)
    (expectedErr : Excno)
    (expected : Array Value) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expectedErr}, got stack {reprStr st.stack}")
  | .error e =>
      if e != expectedErr then
        throw (IO.userError s!"{label}: expected error {expectedErr}, got {e}")
      if st.stack == expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st.stack}")

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2A 6) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (stripeBits 9 1) #[refLeafA, Cell.empty]

private def refLeafD : Cell :=
  Cell.mkOrdinary (stripeBits 4 2) #[refLeafB]

private def cOrdEmpty : Cell := Cell.empty

private def cOrdBits8 : Cell := Cell.ofUInt 8 0xA5

private def cOrdBits255Refs1 : Cell :=
  Cell.mkOrdinary (stripeBits 255 1) #[refLeafA]

private def cOrdBits511Refs2 : Cell :=
  Cell.mkOrdinary (stripeBits 511 0) #[refLeafB, refLeafC]

private def cOrdNested : Cell :=
  Cell.mkOrdinary (stripeBits 33 1) #[refLeafB, refLeafC]

private def cOrdRefs4 : Cell :=
  Cell.mkOrdinary (stripeBits 17 2) #[refLeafA, refLeafB, refLeafC, refLeafD]

private def libTargetA : Cell :=
  Cell.mkOrdinary (natToBits 0x55AA 16) #[refLeafA, refLeafB]

private def libTargetB : Cell :=
  Cell.mkOrdinary (stripeBits 40 1) #[refLeafC]

private def hashBitsOf (c : Cell) : BitString :=
  natToBits (bytesToNatBE (Cell.hashBytes c)) 256

private def mkLibraryRefCellFromHashBits (hashBits : BitString) : Cell :=
  { bits := natToBits 2 8 ++ hashBits
    refs := #[]
    special := true
    levelMask := 0 }

private def mkLibraryRefCell (target : Cell) : Cell :=
  mkLibraryRefCellFromHashBits (hashBitsOf target)

private def specialShort7 : Cell :=
  { bits := natToBits 0b1010101 7
    refs := #[]
    special := true
    levelMask := 0 }

private def specialTag1Only : Cell :=
  { bits := natToBits 1 8
    refs := #[]
    special := true
    levelMask := 0 }

private def specialTag255Only : Cell :=
  { bits := natToBits 255 8
    refs := #[]
    special := true
    levelMask := 0 }

private def specialLibraryBits263 : Cell :=
  { bits := natToBits 2 8 ++ natToBits 0 255
    refs := #[]
    special := true
    levelMask := 0 }

private def specialLibraryBits272 : Cell :=
  { bits := natToBits 2 8 ++ natToBits 0 264
    refs := #[]
    special := true
    levelMask := 0 }

private def specialLibraryWithRef : Cell :=
  { bits := natToBits 2 8 ++ hashBitsOf libTargetA
    refs := #[Cell.empty]
    special := true
    levelMask := 0 }

private def specialLibraryRefA : Cell := mkLibraryRefCell libTargetA

private def mkLibraryCollectionRef (keyBits : BitString) (valRef : Cell) : Except Excno Cell := do
  let (root?, ok, _, _) ← dictSetRefWithCells none keyBits valRef .set
  if !ok then
    throw .dictErr
  match root? with
  | some root => return root
  | none => throw .dictErr

private def mkLibraryCollectionSlice (keyBits : BitString) (val : Slice) : Except Excno Cell := do
  let (root?, ok, _, _) ← dictSetSliceWithCells none keyBits val .set
  if !ok then
    throw .dictErr
  match root? with
  | some root => return root
  | none => throw .dictErr

private def mkLibraryCollectionFor (target : Cell) : Except Excno Cell :=
  mkLibraryCollectionRef (hashBitsOf target) target

private def mkLibraryCollectionKeyToValue (keyCell : Cell) (valRef : Cell) : Except Excno Cell :=
  mkLibraryCollectionRef (hashBitsOf keyCell) valRef

private def mkLibraryCollectionNoRefValue (keyCell : Cell) : Except Excno Cell :=
  mkLibraryCollectionSlice (hashBitsOf keyCell) (Slice.ofCell Cell.empty)

private def expectedXloadOut (below : Array Value) (c : Cell) : Array Value :=
  below ++ #[.cell c]

private def expectedXloadQOut (below : Array Value) (c : Cell) : Array Value :=
  below ++ #[.cell c, intV (-1)]

def suite : InstrSuite where
  id := xloadId
  unit := #[
    { name := "unit/direct/success-ordinary-and-quiet-flag"
      run := do
        -- Branch: ordinary cell bypasses library resolution.
        expectOkStack "ok/nonquiet/ordinary-empty"
          (runXloadDirect #[.cell cOrdEmpty])
          (expectedXloadOut #[] cOrdEmpty)
        expectOkStack "ok/nonquiet/ordinary-bits255-refs1"
          (runXloadDirect #[.cell cOrdBits255Refs1])
          (expectedXloadOut #[] cOrdBits255Refs1)
        expectOkStack "ok/nonquiet/deep-stack-preserve"
          (runXloadDirect #[.null, intV 5, .cell cOrdNested])
          (expectedXloadOut #[.null, intV 5] cOrdNested)

        -- Branch: quiet success appends `-1`.
        expectOkStack "ok/quiet/ordinary-top"
          (runXloadQDirect #[.cell cOrdBits8])
          (expectedXloadQOut #[] cOrdBits8)
        expectOkStack "ok/quiet/ordinary-deep"
          (runXloadQDirect #[intV (-3), .cell cOrdBits511Refs2])
          (expectedXloadQOut #[intV (-3)] cOrdBits511Refs2) }
    ,
    { name := "unit/direct/underflow-type-cellund-order"
      run := do
        -- Branch: underflow gate runs before pop/type checks.
        expectErr "underflow/nonquiet-empty" (runXloadDirect #[]) .stkUnd
        expectErr "underflow/quiet-empty" (runXloadQDirect #[]) .stkUnd

        -- Branch: popCell type check (quiet does not suppress this stage).
        expectErr "type/nonquiet-null" (runXloadDirect #[.null]) .typeChk
        expectErr "type/nonquiet-int" (runXloadDirect #[intV 7]) .typeChk
        expectErr "type/nonquiet-slice" (runXloadDirect #[.slice (Slice.ofCell Cell.empty)]) .typeChk
        expectErr "type/quiet-null" (runXloadQDirect #[.null]) .typeChk
        expectErr "type/deep-top-not-cell"
          (runXloadDirect #[.cell cOrdBits8, .builder Builder.empty]) .typeChk

        -- Branch: special-cell rejection branches.
        expectErr "cellund/special-short7" (runXloadDirect #[.cell specialShort7]) .cellUnd
        expectErr "cellund/special-tag1" (runXloadDirect #[.cell specialTag1Only]) .cellUnd
        expectErr "cellund/special-tag255" (runXloadDirect #[.cell specialTag255Only]) .cellUnd
        expectErr "cellund/library-len263" (runXloadDirect #[.cell specialLibraryBits263]) .cellUnd
        expectErr "cellund/library-len272" (runXloadDirect #[.cell specialLibraryBits272]) .cellUnd
        expectErr "cellund/library-with-ref" (runXloadDirect #[.cell specialLibraryWithRef]) .cellUnd

        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok", runXloadDirect #[.cell cOrdEmpty]),
            ("underflow", runXloadDirect #[]),
            ("type", runXloadDirect #[.null]),
            ("cellund", runXloadDirect #[.cell specialShort7])
          ]
        for (label, res) in probes do
          match res with
          | .error .rangeChk =>
              throw (IO.userError s!"{label}: unexpected rangeChk for XLOAD")
          | _ => pure () }
    ,
    { name := "unit/direct/library-resolution-success-paths"
      run := do
        let collA ← expectOkExcept "dict/collA" (mkLibraryCollectionFor libTargetA)
        let collB ← expectOkExcept "dict/collB" (mkLibraryCollectionFor libTargetB)

        -- Branch: library lookup hit.
        let _ ← expectRawOkStack "lib/hit/nonquiet-single"
          (runXloadRaw xloadInstr #[.cell specialLibraryRefA] #[collA])
          (expectedXloadOut #[] libTargetA)

        -- Branch: quiet lookup hit appends `-1`.
        let _ ← expectRawOkStack "lib/hit/quiet-single"
          (runXloadRaw xloadqInstr #[.cell specialLibraryRefA] #[collA])
          (expectedXloadQOut #[] libTargetA)

        -- Branch: stack below top remains untouched on success.
        let _ ← expectRawOkStack "lib/hit/deep-preserve"
          (runXloadRaw xloadInstr #[.null, intV 11, .cell specialLibraryRefA] #[collA])
          (expectedXloadOut #[.null, intV 11] libTargetA)

        -- Branch: iterate over multiple library collections until found.
        let _ ← expectRawOkStack "lib/hit/after-miss-first"
          (runXloadRaw xloadInstr #[.cell specialLibraryRefA] #[collB, collA])
          (expectedXloadOut #[] libTargetA)

        -- Branch: malformed first collection behaves as miss; second still resolves.
        let _ ← expectRawOkStack "lib/hit/after-malformed-first"
          (runXloadRaw xloadInstr #[.cell specialLibraryRefA] #[specialTag1Only, collA])
          (expectedXloadOut #[] libTargetA)
        pure () }
    ,
    { name := "unit/direct/library-resolution-miss-and-quiet-fallback"
      run := do
        let collB ← expectOkExcept "dict/collB" (mkLibraryCollectionFor libTargetB)
        let collNoRef ← expectOkExcept "dict/coll-no-ref" (mkLibraryCollectionNoRefValue libTargetA)
        let collMismatch ← expectOkExcept "dict/coll-hash-mismatch"
          (mkLibraryCollectionKeyToValue libTargetA libTargetB)

        -- Branch: all miss forms map to `cellUnd` in non-quiet mode.
        let _ ← expectRawErrStack "lib/miss/no-libraries"
          (runXloadRaw xloadInstr #[intV 9, .cell specialLibraryRefA])
          .cellUnd
          #[intV 9]
        let _ ← expectRawErrStack "lib/miss/wrong-key"
          (runXloadRaw xloadInstr #[intV 10, .cell specialLibraryRefA] #[collB])
          .cellUnd
          #[intV 10]
        let _ ← expectRawErrStack "lib/miss/value-no-ref"
          (runXloadRaw xloadInstr #[intV 11, .cell specialLibraryRefA] #[collNoRef])
          .cellUnd
          #[intV 11]
        let _ ← expectRawErrStack "lib/miss/hash-mismatch"
          (runXloadRaw xloadInstr #[intV 12, .cell specialLibraryRefA] #[collMismatch])
          .cellUnd
          #[intV 12]

        -- Branch: quiet wraps resolve errors as `0`.
        let _ ← expectRawOkStack "lib/miss/quiet-push0-no-libraries"
          (runXloadRaw xloadqInstr #[intV 21, .cell specialLibraryRefA] #[])
          #[intV 21, intV 0]
        let _ ← expectRawOkStack "lib/miss/quiet-push0-wrong-key"
          (runXloadRaw xloadqInstr #[intV 22, .cell specialLibraryRefA] #[collB])
          #[intV 22, intV 0]
        pure () }
    ,
    { name := "unit/direct/gas-and-load-cache-branches"
      run := do
        -- Branch: first load vs reload gas for ordinary success.
        let hOrd : Array UInt8 := Cell.hashBytes cOrdRefs4
        let stFresh ← expectRawOkStack "gas/ordinary/fresh"
          (runXloadRaw xloadInstr #[.cell cOrdRefs4])
          (expectedXloadOut #[] cOrdRefs4)
        if stFresh.loadedCells == #[hOrd] then
          pure ()
        else
          throw (IO.userError s!"gas/ordinary/fresh: expected loaded cache [hash], got {reprStr stFresh.loadedCells}")
        if stFresh.gas.gasConsumed = cellLoadGasPrice then
          pure ()
        else
          throw (IO.userError s!"gas/ordinary/fresh: expected gas {cellLoadGasPrice}, got {stFresh.gas.gasConsumed}")

        let stReload ← expectRawOkStack "gas/ordinary/reload"
          (runXloadRaw xloadInstr #[.cell cOrdRefs4] #[] #[hOrd])
          (expectedXloadOut #[] cOrdRefs4)
        if stReload.loadedCells == #[hOrd] then
          pure ()
        else
          throw (IO.userError s!"gas/ordinary/reload: expected loaded cache unchanged, got {reprStr stReload.loadedCells}")
        if stReload.gas.gasConsumed = cellReloadGasPrice then
          pure ()
        else
          throw (IO.userError s!"gas/ordinary/reload: expected gas {cellReloadGasPrice}, got {stReload.gas.gasConsumed}")

        -- Branch: gas/cache still applied when resolve fails.
        let hBad : Array UInt8 := Cell.hashBytes specialShort7
        let stErrFresh ← expectRawErrStack "gas/error/fresh"
          (runXloadRaw xloadInstr #[intV 31, .cell specialShort7])
          .cellUnd
          #[intV 31]
        if stErrFresh.loadedCells == #[hBad] then
          pure ()
        else
          throw (IO.userError s!"gas/error/fresh: expected loaded cache [hash], got {reprStr stErrFresh.loadedCells}")
        if stErrFresh.gas.gasConsumed = cellLoadGasPrice then
          pure ()
        else
          throw (IO.userError s!"gas/error/fresh: expected gas {cellLoadGasPrice}, got {stErrFresh.gas.gasConsumed}")

        let stErrReload ← expectRawErrStack "gas/error/reload"
          (runXloadRaw xloadInstr #[intV 32, .cell specialShort7] #[] #[hBad])
          .cellUnd
          #[intV 32]
        if stErrReload.loadedCells == #[hBad] then
          pure ()
        else
          throw (IO.userError s!"gas/error/reload: expected loaded cache unchanged, got {reprStr stErrReload.loadedCells}")
        if stErrReload.gas.gasConsumed = cellReloadGasPrice then
          pure ()
        else
          throw (IO.userError s!"gas/error/reload: expected gas {cellReloadGasPrice}, got {stErrReload.gas.gasConsumed}")

        let stQuietErr ← expectRawOkStack "gas/error/quiet-still-charged"
          (runXloadRaw xloadqInstr #[intV 33, .cell specialShort7])
          #[intV 33, intV 0]
        if stQuietErr.gas.gasConsumed = cellLoadGasPrice then
          pure ()
        else
          throw (IO.userError s!"gas/error/quiet-still-charged: expected gas {cellLoadGasPrice}, got {stQuietErr.gas.gasConsumed}") }
    ,
    { name := "unit/opcode-decode-boundaries"
      run := do
        let xctosOnly ←
          match assembleCp0 [xctosInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/xctos failed: {e}")
        if xctosOnly.bits == natToBits xctosOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/xctos: expected 0xd739, got bits {xctosOnly.bits}")

        -- Current assembler boundary: XLOAD/XLOADQ are decode-only in `encodeCellExtInstr`.
        match assembleCp0 [xloadInstr] with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"assemble/xload: expected invOpcode, got {e}")
        | .ok cell =>
            throw (IO.userError s!"assemble/xload: unexpectedly encodable with bits {cell.bits}")
        match assembleCp0 [xloadqInstr] with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"assemble/xloadq: expected invOpcode, got {e}")
        | .ok cell =>
            throw (IO.userError s!"assemble/xloadq: unexpectedly encodable with bits {cell.bits}")

        -- Decode boundary around contiguous opcodes XCTOS/XLOAD/XLOADQ.
        let codeBits : BitString :=
          natToBits xctosOpcode 16
            ++ natToBits xloadOpcode 16
            ++ natToBits xloadqOpcode 16
        let s0 := Slice.ofCell (Cell.mkOrdinary codeBits #[])
        let s1 ← expectDecodeStep "decode/xctos-d739" s0 xctosInstr 16
        let s2 ← expectDecodeStep "decode/xload-d73a" s1 xloadInstr 16
        let s3 ← expectDecodeStep "decode/xloadq-d73b" s2 xloadqInstr 16
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-xload-falls-through"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runXloadDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/fallback-xctos"
          (runXloadDispatchFallback .xctos #[.null])
          #[.null, intV dispatchSentinel] }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.XLOAD
