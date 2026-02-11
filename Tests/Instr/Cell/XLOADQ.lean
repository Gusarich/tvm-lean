import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.XLOADQ

/-
XLOADQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.xload quiet)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd73a/0xd73b` decode to `XLOAD/XLOADQ`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`encodeCellExtInstr` currently rejects `.xload _`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_special_cell`)

Branch map covered by this suite:
- dispatch (`.cellExt` / `.xload`) vs fallback `next`;
- `checkUnderflow 1` + top `popCell` type/underflow guards;
- unconditional `registerCellLoad` charging load/reload gas before special resolution;
- resolution split:
  - ordinary cell: success;
  - special short/unknown/malformed: fail;
  - special library: dictionary lookup + hash-match check across `VmState.libraries`;
- quiet split:
  - success => push resolved cell + `-1`;
  - failure => push `0` (no exception);
  - non-quiet failures throw `cellUnd`.

Note: because `assembleCp0` currently rejects `.cellExt (.xload _)`, oracle/fuzz harness
entries cannot encode direct XLOADQ programs yet; this suite is unit-heavy by design.
-/

private def xloadqId : InstrId := { name := "XLOADQ" }

private def xloadInstr : Instr := .cellExt (.xload false)

private def xloadqInstr : Instr := .cellExt (.xload true)

private def xctosInstr : Instr := .xctos

private def dispatchSentinel : Int := 997

private def liftExc {α} (label : String) (x : Except Excno α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{label}: {reprStr e}")

private def runXloadRawInstr
    (instr : Instr)
    (stack : Array Value)
    (libraries : Array Cell := #[])
    (loadedCells : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      libraries := libraries
      loadedCells := loadedCells }
  (execInstrCellExt instr (pure ())).run st0

private def runXloadInstrWithLibraries
    (instr : Instr)
    (stack : Array Value)
    (libraries : Array Cell := #[]) : Except Excno (Array Value) :=
  let (res, st1) := runXloadRawInstr instr stack libraries
  match res with
  | .ok _ => .ok st1.stack
  | .error e => .error e

private def runXloadDirect (stack : Array Value) : Except Excno (Array Value) :=
  runXloadInstrWithLibraries xloadInstr stack

private def runXloadqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runXloadInstrWithLibraries xloadqInstr stack

private def runXloadWithLibraries (stack : Array Value) (libraries : Array Cell) :
    Except Excno (Array Value) :=
  runXloadInstrWithLibraries xloadInstr stack libraries

private def runXloadqWithLibraries (stack : Array Value) (libraries : Array Cell) :
    Except Excno (Array Value) :=
  runXloadInstrWithLibraries xloadqInstr stack libraries

private def runXloadqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt instr (VM.push (intV dispatchSentinel)) stack

private def quietSuccessExpected (below : Array Value) (c : Cell) : Array Value :=
  below ++ #[.cell c, intV (-1)]

private def quietFailExpected (below : Array Value := #[]) : Array Value :=
  below ++ #[intV 0]

private def hashBitsOfCell (c : Cell) : BitString :=
  natToBits (bytesToNatBE (Cell.hashBytes c)) 256

private def mkLibraryCellByHashBits (hashBits : BitString) : Cell :=
  { bits := natToBits 2 8 ++ hashBits
    refs := #[]
    special := true
    levelMask := 0 }

private def mkLibraryCellForTarget (target : Cell) : Cell :=
  mkLibraryCellByHashBits (hashBitsOfCell target)

private def mkLibraryCollectionRef (keyBits : BitString) (target : Cell) : Except Excno Cell := do
  let (root?, ok, _, _) ← dictSetRefWithCells none keyBits target .set
  if !ok then
    throw .dictErr
  match root? with
  | some root => pure root
  | none => throw .dictErr

private def mkLibraryCollectionSlice (keyBits : BitString) (value : Slice) : Except Excno Cell := do
  let (root?, ok, _, _) ← dictSetSliceWithCells none keyBits value .set
  if !ok then
    throw .dictErr
  match root? with
  | some root => pure root
  | none => throw .dictErr

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[Cell.empty]

private def ordinaryEmpty : Cell := Cell.empty

private def ordinaryBits31 : Cell := Cell.mkOrdinary (natToBits 0x5a5a5a5 31) #[]

private def ordinaryRefs2 : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA, refLeafB]

private def ordinaryBits1023 : Cell := Cell.mkOrdinary (Array.replicate 1023 false) #[]

private def ordinaryNested : Cell := Cell.mkOrdinary (natToBits 0x155 9) #[ordinaryBits31, ordinaryRefs2]

private def ordinaryAlt : Cell := Cell.mkOrdinary (natToBits 0x1234 16) #[refLeafA]

private def specialShortBits : Cell :=
  { bits := #[true, false, true, false, true, false, true]
    refs := #[]
    special := true
    levelMask := 0 }

private def specialUnknownType : Cell :=
  { bits := natToBits 7 8 ++ natToBits 0 16
    refs := #[]
    special := true
    levelMask := 0 }

private def specialMerkleLike : Cell :=
  { bits := natToBits 3 8 ++ natToBits 0 32
    refs := #[]
    special := true
    levelMask := 0 }

private def specialLibraryBadLen : Cell :=
  { bits := natToBits 2 8 ++ natToBits 0 255
    refs := #[]
    special := true
    levelMask := 0 }

private def specialLibraryWithRef : Cell :=
  { bits := natToBits 2 8 ++ natToBits 0 256
    refs := #[ordinaryEmpty]
    special := true
    levelMask := 0 }

private def randBitString (bitCount : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:bitCount] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def genRandomOrdinaryCell (rng0 : StdGen) : Cell × StdGen :=
  let (bitCount, rng1) := randNat rng0 0 96
  let (bits, rng2) := randBitString bitCount rng1
  let (refCount, rng3) := randNat rng2 0 2
  let refs : Array Cell :=
    if refCount = 0 then
      #[]
    else if refCount = 1 then
      #[refLeafA]
    else
      #[refLeafA, refLeafB]
  (Cell.mkOrdinary bits refs, rng3)

def suite : InstrSuite where
  id := xloadqId
  unit := #[
    { name := "unit/direct/success/ordinary-empty"
      run := do
        expectOkStack "ok/ordinary-empty"
          (runXloadqDirect #[.cell ordinaryEmpty])
          (quietSuccessExpected #[] ordinaryEmpty) }
    ,
    { name := "unit/direct/success/ordinary-bits31"
      run := do
        expectOkStack "ok/ordinary-bits31"
          (runXloadqDirect #[.cell ordinaryBits31])
          (quietSuccessExpected #[] ordinaryBits31) }
    ,
    { name := "unit/direct/success/ordinary-refs2"
      run := do
        expectOkStack "ok/ordinary-refs2"
          (runXloadqDirect #[.cell ordinaryRefs2])
          (quietSuccessExpected #[] ordinaryRefs2) }
    ,
    { name := "unit/direct/success/ordinary-bits1023"
      run := do
        expectOkStack "ok/ordinary-bits1023"
          (runXloadqDirect #[.cell ordinaryBits1023])
          (quietSuccessExpected #[] ordinaryBits1023) }
    ,
    { name := "unit/direct/success/deep-stack-preserve-below"
      run := do
        expectOkStack "ok/deep-stack-preserve-below"
          (runXloadqDirect #[.null, intV 42, .cell ordinaryRefs2])
          (quietSuccessExpected #[.null, intV 42] ordinaryRefs2) }
    ,
    { name := "unit/direct/success/nonquiet-ordinary-no-status"
      run := do
        expectOkStack "ok/nonquiet-no-status"
          (runXloadDirect #[.cell ordinaryBits31])
          #[.cell ordinaryBits31] }
    ,
    { name := "unit/library/success/quiet-single-collection-hit"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let libCell := mkLibraryCellByHashBits key
        let collection ← liftExc "lib/single-hit" (mkLibraryCollectionRef key ordinaryNested)
        expectOkStack "ok/lib-single-hit"
          (runXloadqWithLibraries #[.cell libCell] #[collection])
          (quietSuccessExpected #[] ordinaryNested) }
    ,
    { name := "unit/library/success/quiet-second-collection-hit"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let libCell := mkLibraryCellByHashBits key
        let miss ← liftExc "lib/first-miss" (mkLibraryCollectionRef key ordinaryAlt)
        let hit ← liftExc "lib/second-hit" (mkLibraryCollectionRef key ordinaryNested)
        expectOkStack "ok/lib-second-hit"
          (runXloadqWithLibraries #[.cell libCell] #[miss, hit])
          (quietSuccessExpected #[] ordinaryNested) }
    ,
    { name := "unit/library/success/nonquiet-hit-no-status"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let libCell := mkLibraryCellByHashBits key
        let collection ← liftExc "lib/nonquiet-hit" (mkLibraryCollectionRef key ordinaryNested)
        expectOkStack "ok/lib-nonquiet-hit"
          (runXloadWithLibraries #[.cell libCell] #[collection])
          #[.cell ordinaryNested] }
    ,
    { name := "unit/library/success/deep-stack-preserve-below"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let libCell := mkLibraryCellByHashBits key
        let collection ← liftExc "lib/deep-hit" (mkLibraryCollectionRef key ordinaryNested)
        expectOkStack "ok/lib-deep-stack"
          (runXloadqWithLibraries #[intV (-7), .null, .cell libCell] #[collection])
          (quietSuccessExpected #[intV (-7), .null] ordinaryNested) }
    ,
    { name := "unit/library/fail/quiet-missing-key-status0"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let missKey := hashBitsOfCell ordinaryAlt
        let libCell := mkLibraryCellByHashBits key
        let collection ← liftExc "lib/missing-key" (mkLibraryCollectionRef missKey ordinaryAlt)
        expectOkStack "fail/quiet-missing-key"
          (runXloadqWithLibraries #[.cell libCell] #[collection])
          (quietFailExpected #[]) }
    ,
    { name := "unit/library/fail/quiet-hash-mismatch-status0"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let libCell := mkLibraryCellByHashBits key
        -- Key exists, but value's referenced cell hash does not match key.
        let mismatch ← liftExc "lib/hash-mismatch" (mkLibraryCollectionRef key ordinaryAlt)
        expectOkStack "fail/quiet-hash-mismatch"
          (runXloadqWithLibraries #[.cell libCell] #[mismatch])
          (quietFailExpected #[]) }
    ,
    { name := "unit/library/fail/quiet-value-without-ref-status0"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let libCell := mkLibraryCellByHashBits key
        let valueNoRef := mkSliceFromBits (natToBits 0 3)
        let noRefCollection ←
          liftExc "lib/value-no-ref" (mkLibraryCollectionSlice key valueNoRef)
        expectOkStack "fail/quiet-value-no-ref"
          (runXloadqWithLibraries #[.cell libCell] #[noRefCollection])
          (quietFailExpected #[]) }
    ,
    { name := "unit/library/fail/quiet-malformed-dict-status0"
      run := do
        let libCell := mkLibraryCellForTarget ordinaryNested
        expectOkStack "fail/quiet-malformed-dict-root"
          (runXloadqWithLibraries #[.cell libCell] #[ordinaryEmpty])
          (quietFailExpected #[]) }
    ,
    { name := "unit/special/fail/quiet-short-bits-status0"
      run := do
        expectOkStack "fail/quiet-short-bits"
          (runXloadqDirect #[.cell specialShortBits])
          (quietFailExpected #[]) }
    ,
    { name := "unit/special/fail/quiet-unknown-type-status0"
      run := do
        expectOkStack "fail/quiet-unknown-type"
          (runXloadqDirect #[.cell specialUnknownType])
          (quietFailExpected #[]) }
    ,
    { name := "unit/special/fail/quiet-library-bad-length-status0"
      run := do
        expectOkStack "fail/quiet-library-bad-length"
          (runXloadqDirect #[.cell specialLibraryBadLen])
          (quietFailExpected #[]) }
    ,
    { name := "unit/special/fail/quiet-library-with-ref-status0"
      run := do
        expectOkStack "fail/quiet-library-with-ref"
          (runXloadqDirect #[.cell specialLibraryWithRef])
          (quietFailExpected #[]) }
    ,
    { name := "unit/library/fail/nonquiet-missing-key-cellund"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let missKey := hashBitsOfCell ordinaryAlt
        let libCell := mkLibraryCellByHashBits key
        let collection ← liftExc "lib/nonquiet-missing-key" (mkLibraryCollectionRef missKey ordinaryAlt)
        expectErr "fail/nonquiet-missing-key"
          (runXloadWithLibraries #[.cell libCell] #[collection]) .cellUnd }
    ,
    { name := "unit/special/fail/nonquiet-merkle-type-cellund"
      run := do
        expectErr "fail/nonquiet-merkle-type"
          (runXloadDirect #[.cell specialMerkleLike]) .cellUnd }
    ,
    { name := "unit/special/fail/nonquiet-short-bits-cellund"
      run := do
        expectErr "fail/nonquiet-short-bits"
          (runXloadDirect #[.cell specialShortBits]) .cellUnd }
    ,
    { name := "unit/special/fail/nonquiet-library-bad-length-cellund"
      run := do
        expectErr "fail/nonquiet-library-bad-length"
          (runXloadDirect #[.cell specialLibraryBadLen]) .cellUnd }
    ,
    { name := "unit/errors/underflow-empty"
      run := do
        expectErr "err/underflow-empty"
          (runXloadqDirect #[]) .stkUnd }
    ,
    { name := "unit/errors/type-top-null"
      run := do
        expectErr "err/type-top-null"
          (runXloadqDirect #[.null]) .typeChk }
    ,
    { name := "unit/errors/type-top-int"
      run := do
        expectErr "err/type-top-int"
          (runXloadqDirect #[intV 5]) .typeChk }
    ,
    { name := "unit/errors/type-order-top-before-below"
      run := do
        expectErr "err/type-order-top-before-below"
          (runXloadqDirect #[.cell ordinaryNested, .null]) .typeChk }
    ,
    { name := "unit/errors/quiet-does-not-mask-type"
      run := do
        let key := hashBitsOfCell ordinaryNested
        let libCell := mkLibraryCellByHashBits key
        let collection ← liftExc "err/type-mask/lib-build" (mkLibraryCollectionRef key ordinaryNested)
        expectErr "err/type-not-masked-by-quiet"
          (runXloadqWithLibraries #[.cell libCell, intV 3] #[collection]) .typeChk }
    ,
    { name := "unit/gas/cell-load-vs-reload-and-cache"
      run := do
        let c := ordinaryRefs2
        let h : Array UInt8 := Cell.hashBytes c

        let (resFresh, stFresh) := runXloadRawInstr xloadqInstr #[.cell c]
        match resFresh with
        | .ok _ =>
            if stFresh.stack == quietSuccessExpected #[] c then
              pure ()
            else
              throw (IO.userError
                s!"gas/fresh-stack: expected {reprStr (quietSuccessExpected #[] c)}, got {reprStr stFresh.stack}")
            if stFresh.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"gas/fresh-loaded: expected [hash], got {reprStr stFresh.loadedCells}")
            if stFresh.gas.gasConsumed = cellLoadGasPrice then
              pure ()
            else
              throw (IO.userError
                s!"gas/fresh: expected {cellLoadGasPrice}, got {stFresh.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"gas/fresh: expected success, got {e}")

        let (resReload, stReload) := runXloadRawInstr xloadqInstr #[.cell c] #[] #[h]
        match resReload with
        | .ok _ =>
            if stReload.stack == quietSuccessExpected #[] c then
              pure ()
            else
              throw (IO.userError
                s!"gas/reload-stack: expected {reprStr (quietSuccessExpected #[] c)}, got {reprStr stReload.stack}")
            if stReload.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"gas/reload-loaded: expected unchanged [hash], got {reprStr stReload.loadedCells}")
            if stReload.gas.gasConsumed = cellReloadGasPrice then
              pure ()
            else
              throw (IO.userError
                s!"gas/reload: expected {cellReloadGasPrice}, got {stReload.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"gas/reload: expected success, got {e}") }
    ,
    { name := "unit/gas/load-charged-on-quiet-failure"
      run := do
        let c := specialUnknownType
        let h : Array UInt8 := Cell.hashBytes c
        let (res, st) := runXloadRawInstr xloadqInstr #[.cell c]
        match res with
        | .ok _ =>
            if st.stack == quietFailExpected #[] then
              pure ()
            else
              throw (IO.userError s!"gas/quiet-fail-stack: expected [0], got {reprStr st.stack}")
            if st.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"gas/quiet-fail-loaded: expected [hash], got {reprStr st.loadedCells}")
            if st.gas.gasConsumed = cellLoadGasPrice then
              pure ()
            else
              throw (IO.userError
                s!"gas/quiet-fail: expected {cellLoadGasPrice}, got {st.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"gas/quiet-fail: expected success, got {e}") }
    ,
    { name := "unit/opcode/decode-assembler-boundary-and-dispatch"
      run := do
        let raw := mkSliceFromBits
          (natToBits 0xd739 16 ++
           natToBits 0xd73a 16 ++
           natToBits 0xd73b 16 ++
           natToBits 0xa0 8)
        let s1 ← expectDecodeStep "decode/xctos-neighbor" raw xctosInstr 16
        let s2 ← expectDecodeStep "decode/xload" s1 xloadInstr 16
        let s3 ← expectDecodeStep "decode/xloadq" s2 xloadqInstr 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits")

        let invalid := mkSliceFromBits (natToBits 0xd73c 16)
        match decodeCp0WithBits invalid with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"decode/invalid-0xd73c: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError
              s!"decode/invalid-0xd73c: expected failure, got instr={reprStr instr} bits={bits}")

        match assembleCp0 [xloadInstr] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/xload: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/xload: expected invOpcode, got success")

        match assembleCp0 [xloadqInstr] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/xloadq: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/xloadq: expected invOpcode, got success")

        expectOkStack "dispatch/non-cellext-add"
          (runXloadqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellext-xctos"
          (runXloadqDispatchFallback .xctos #[intV 7])
          #[intV 7, intV dispatchSentinel] }
    ,
    { name := "unit/fuzz/structured-seeded-320"
      run := do
        let mut rng := mkStdGen 2026021098
        for i in [0:320] do
          let (shape, rng1) := randNat rng 0 8
          if shape = 0 then
            let (c, rng2) := genRandomOrdinaryCell rng1
            expectOkStack s!"fuzz/{i}/ok/ordinary"
              (runXloadqDirect #[.cell c])
              (quietSuccessExpected #[] c)
            rng := rng2
          else if shape = 1 then
            expectOkStack s!"fuzz/{i}/fail/quiet-unknown"
              (runXloadqDirect #[.cell specialUnknownType])
              (quietFailExpected #[])
            rng := rng1
          else if shape = 2 then
            let (target, rng2) := genRandomOrdinaryCell rng1
            let keyHit := hashBitsOfCell target
            let keyMiss :=
              if keyHit == hashBitsOfCell ordinaryAlt then hashBitsOfCell ordinaryBits31 else hashBitsOfCell ordinaryAlt
            let libCell := mkLibraryCellByHashBits keyHit
            let collection ←
              liftExc s!"fuzz/{i}/lib-miss-build" (mkLibraryCollectionRef keyMiss ordinaryAlt)
            expectOkStack s!"fuzz/{i}/fail/quiet-lib-miss"
              (runXloadqWithLibraries #[.cell libCell] #[collection])
              (quietFailExpected #[])
            rng := rng2
          else if shape = 3 then
            expectErr s!"fuzz/{i}/err/underflow" (runXloadqDirect #[]) .stkUnd
            rng := rng1
          else if shape = 4 then
            expectErr s!"fuzz/{i}/err/type-null" (runXloadqDirect #[.null]) .typeChk
            rng := rng1
          else if shape = 5 then
            expectErr s!"fuzz/{i}/err/nonquiet-unknown"
              (runXloadDirect #[.cell specialUnknownType]) .cellUnd
            rng := rng1
          else if shape = 6 then
            let (c, rng2) := genRandomOrdinaryCell rng1
            expectOkStack s!"fuzz/{i}/ok/deep-stack"
              (runXloadqDirect #[.null, intV (-1), .cell c])
              (quietSuccessExpected #[.null, intV (-1)] c)
            rng := rng2
          else if shape = 7 then
            let (target, rng2) := genRandomOrdinaryCell rng1
            let key := hashBitsOfCell target
            let libCell := mkLibraryCellByHashBits key
            let collection ←
              liftExc s!"fuzz/{i}/lib-hit-build" (mkLibraryCollectionRef key target)
            expectOkStack s!"fuzz/{i}/ok/quiet-lib-hit"
              (runXloadqWithLibraries #[.cell libCell] #[collection])
              (quietSuccessExpected #[] target)
            rng := rng2
          else
            expectOkStack s!"fuzz/{i}/fail/quiet-short"
              (runXloadqDirect #[.cell specialShortBits])
              (quietFailExpected #[])
            rng := rng1 }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.XLOADQ
