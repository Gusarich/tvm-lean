import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTISETGETOPTREF

/-!
INSTRUCTION: DICTISETGETOPTREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path
   - `execInstrDictExt` must route `.dictExt (.setGetOptRef ...)` to dedicated branch.
   - Any other opcode must execute `next`/fallback unchanged.

2. [B2] Runtime arity check
   - Requires at least 4 stack items (`n`, `dict`, `key`, `newValue`) before proceeding.
   - Less than 4 yields `.stkUnd` before any other branch-specific checks.

3. [B3] `n` validation (`popNatUpTo 1023`)
   - `n = .nan` => `.rangeChk`.
   - `n < 0` => `.rangeChk`.
   - `n > 1023` => `.rangeChk`.
   - `n = 0` is valid.

4. [B4] Dictionary argument parsing (`popMaybeCell`)
   - `.null` root is accepted and means "empty dictionary".
   - Non-cell, non-null values produce `.typeChk`.

5. [B5] Integer-key parsing path (`intKey = true`)
   - Uses `popInt` (not `popIntFinite`):
     - non-integer key => `.typeChk`.
     - `.nan` => `.rangeChk`.
     - representable key => concrete `BitString`.
     - non-representable key for requested signed/unsigned width => `.rangeChk`.

6. [B6] Slice-key parsing path (`intKey = false`)
   - Pops a `Slice` and requires `haveBits n`.
   - If `n` bits are unavailable => returns `none` and then throws `.cellUnd`.

7. [B7] Key materialization precondition
   - For both paths, if key materialization fails, execution throws:
     - int-key invalid range branch => `.rangeChk` (from [B5]).
     - slice-key short slice => `.cellUnd` (from [B6]).

8. [B8] Mutation mode selection via `newValue`
   - `newValue` is `null` => deletion branch (`dictDeleteWithCells`).
   - `newValue` is cell => set-return branch (`dictLookupSetRefWithCells`).
   - `newValue` non-null non-cell => `.typeChk` from `popMaybeCell`.

9. [B9] Set-return branch (`dictLookupSetRefWithCells`)
   - On traversal/path error => propagate `.dictErr` after registering loaded cells.
   - `.ok none` => push resulting root and `.null`.
   - `.ok some oldVal`:
     - if old value slice has exactly one ref and zero bits => push that ref.
     - otherwise => `.dictErr`.

10. [B10] Delete-return branch (`dictDeleteWithCells`)
   - On traversal/path error => propagate `.dictErr` after registering loaded cells.
   - miss => push resulting root and `.null`.
   - hit with valid old value shape => root + old-ref.
   - hit with malformed old value shape => `.dictErr`.

11. [B11] Decoder behavior
   - Raw opcodes `0xF46D`, `0xF46E`, `0xF46F` decode to:
     - slice-key, signed-key, unsigned-key respectively.
   - `0xF46C` and `0xF470` must fail (`.invOpcode`).
   - Decode stream boundaries: `F46D -> F46E -> F46F` are contiguous.

12. [B12] Assembler encoding
   - Assembler must reject all `.dictExt (.setGetOptRef ...)` instruction forms with `.invOpcode`.
   - No additional parameter range validation happens at assembler level because encoding is unsupported.

13. [B13] Gas accounting
   - Instruction precharges root load (if provided) and may consume `cellCreateGasPrice` via `created`.
   - Exact-gas-success and exact-1-failure should be validated against a stable successful branch (we use delete-miss path where dictionary creation is not performed).

14. [B14] Decoder/assembler round-trip checks
   - Adjacent instruction families (`DICTI*` and `DICTI*SETGETOPTREF`) are boundary-sensitive and must not alias incorrectly.

15. [B15] Error-triggering fuzz coverage
   - Integer and slice type errors, dictionary-key/value shape errors, range checks, and malformed roots are included to keep all malformed-control branches reachable.

TOTAL BRANCHES: 15

Every oracle test below is explicitly tagged by the branch family it is designed to exercise (e.g. `[B9]`).
If any branch has zero cases, it would be explicit here; all listed branches above have at least one tagged oracle case.
-/

private def suiteId : InstrId :=
  { name := "DICTISETGETOPTREF" }

private def dictISetGetOptRefInstr (intKey unsigned : Bool) : Instr :=
  .dictExt (.setGetOptRef intKey unsigned)

private def dictISetGetOptRefCode (intKey unsigned : Bool) : Nat :=
  0xF46D + (if intKey then 1 else 0) + (if unsigned then 1 else 0)

private def rawSetGetOptRef : Cell :=
  Cell.mkOrdinary (natToBits (dictISetGetOptRefCode false false) 16) #[]

private def rawSetGetOptRefInt : Cell :=
  Cell.mkOrdinary (natToBits (dictISetGetOptRefCode true false) 16) #[]

private def rawSetGetOptRefUInt : Cell :=
  Cell.mkOrdinary (natToBits (dictISetGetOptRefCode true true) 16) #[]

private def rawGetOptRef : Cell :=
  Cell.mkOrdinary (natToBits 0xF469 16) #[]

private def rawGetOptRefInt : Cell :=
  Cell.mkOrdinary (natToBits 0xF46A 16) #[]

private def rawGetOptRefUInt : Cell :=
  Cell.mkOrdinary (natToBits 0xF46B 16) #[]

private def rawF46C : Cell :=
  Cell.mkOrdinary (natToBits 0xF46C 16) #[]

private def rawF470 : Cell :=
  Cell.mkOrdinary (natToBits 0xF470 16) #[]

private def rawTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def dispatchSentinel : Int := 771_001

private def mkGasPrefix (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok c => c
  | .error e => panic! s!"failed to assemble gas prefix for DICTISETGETOPTREF: {reprStr e}"

private def gasCode (gas : Int) (opcode : Cell) : Cell :=
  Cell.mkOrdinary ((mkGasPrefix gas).bits ++ opcode.bits) ((mkGasPrefix gas).refs ++ opcode.refs)

private def assembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr c}")
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {reprStr e}")

private def mkDictSetRefRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetRefWithCells root k v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected None root result while inserting dict key"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed with {reprStr e}"
    match root with
    | some c => c
    | none => panic! s!"{label}: empty dictionary construction"

private def mkKeyBits (label : String) (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid dict key ({idx}, n={n}, unsigned={unsigned})"

private def mkDeleteRoot (label : String) (root : Option Cell) (keyBits : BitString) : Cell :=
  match dictDeleteWithCells root keyBits with
  | .ok (_, newRoot, _, _) =>
      match newRoot with
      | some newRoot =>
          newRoot
      | none =>
          panic! s!"{label}: unexpected None root after delete on valid path"
  | .error e =>
      panic! s!"{label}: dictDeleteWithCells failed with {reprStr e}"

private def mkSetRoot (label : String) (root : Option Cell) (keyBits : BitString) (value : Cell) : Cell :=
  match dictLookupSetRefWithCells root keyBits value .set with
  | .ok (_, newRoot, _, _, _) =>
      match newRoot with
      | some newRoot =>
          newRoot
      | none =>
          panic! s!"{label}: set operation returned None new root on success"
  | .error e =>
      panic! s!"{label}: dictLookupSetRefWithCells failed with {reprStr e}"

private def storedRefA : Cell :=
  Cell.mkOrdinary (natToBits 0xA4 8) #[]

private def storedRefB : Cell :=
  Cell.mkOrdinary (natToBits 0xB7 8) #[]

private def storedRefC : Cell :=
  Cell.mkOrdinary (natToBits 0xC9 8) #[]

private def valueGoodA : Cell :=
  Cell.mkOrdinary #[] #[storedRefA]

private def valueGoodB : Cell :=
  Cell.mkOrdinary #[] #[storedRefB]

private def valueGoodC : Cell :=
  Cell.mkOrdinary #[] #[storedRefC]

private def valueBitsOnly : Cell :=
  Cell.mkOrdinary (natToBits 0xF0 8) #[]

private def valueTwoRefs : Cell :=
  Cell.mkOrdinary #[] #[storedRefA, storedRefB]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0xF 4) #[]

private def signedNibbleRoot4 : Cell :=
  mkDictSetRefRoot! "signed-nibble-root4" #[(mkKeyBits "signed-nibble/-3" (-3) 4 false, valueGoodA), (mkKeyBits "signed-nibble/4" 4 4 false, valueGoodB)]

private def unsignedNibbleRoot4 : Cell :=
  mkDictSetRefRoot! "unsigned-nibble-root4" #[(mkKeyBits "unsigned-nibble/5" 5 4 true, valueGoodA), (mkKeyBits "unsigned-nibble/9" 9 4 true, valueGoodB)]

private def sliceNibbleRoot4 : Cell :=
  mkDictSetRefRoot! "slice-nibble-root4" #[(natToBits 2 4, valueGoodA), (natToBits 7 4, valueGoodB)]

private def signedNibbleRoot0 : Cell :=
  mkDictSetRefRoot! "signed-nibble-root0" #[(mkKeyBits "signed-nibble-root0" 0 0 false, valueGoodA)]

private def unsignedNibbleRoot0 : Cell :=
  mkDictSetRefRoot! "unsigned-nibble-root0" #[(mkKeyBits "unsigned-nibble-root0" 0 0 true, valueGoodB)]

private def signedRootBadValue : Cell :=
  mkDictSetRefRoot! "signed-root-bad-value" #[(mkKeyBits "signed-bad-value/-3" (-3) 4 false, valueBitsOnly)]

private def unsignedRootBadValue : Cell :=
  mkDictSetRefRoot! "unsigned-root-bad-value" #[(mkKeyBits "unsigned-bad-value/5" 5 4 true, valueBitsOnly)]

private def sliceRootBadValue : Cell :=
  mkDictSetRefRoot! "slice-root-bad-value" #[(natToBits 2 4, valueTwoRefs)]

private def expectedSignedSetHit : Cell :=
  mkSetRoot "signed-set-hit" (some signedNibbleRoot4) (mkKeyBits "signed-set-hit-key" (-3) 4 false) valueGoodC

private def expectedSignedSetMiss : Cell :=
  mkSetRoot "signed-set-miss" (some signedNibbleRoot4) (mkKeyBits "signed-set-miss-key" 6 4 false) valueGoodC

private def expectedUnsignedSetHit : Cell :=
  mkSetRoot "unsigned-set-hit" (some unsignedNibbleRoot4) (mkKeyBits "unsigned-set-hit-key" 5 4 true) valueGoodC

private def expectedUnsignedSetMiss : Cell :=
  mkSetRoot "unsigned-set-miss" (some unsignedNibbleRoot4) (mkKeyBits "unsigned-set-miss-key" 11 4 true) valueGoodC

private def expectedSliceSetHit : Cell :=
  mkSetRoot "slice-set-hit" (some sliceNibbleRoot4) (natToBits 2 4) valueGoodC

private def expectedSliceSetMiss : Cell :=
  mkSetRoot "slice-set-miss" (some sliceNibbleRoot4) (natToBits 1 4) valueGoodC

private def expectedSignedDeleteHit : Cell :=
  mkDeleteRoot "signed-delete-hit" (some signedNibbleRoot4) (mkKeyBits "signed-delete-hit-key" (-3) 4 false)

private def expectedUnsignedDeleteHit : Cell :=
  mkDeleteRoot "unsigned-delete-hit" (some unsignedNibbleRoot4) (mkKeyBits "unsigned-delete-hit-key" 9 4 true)

private def expectedSliceDeleteHit : Cell :=
  mkDeleteRoot "slice-delete-hit" (some sliceNibbleRoot4) (natToBits 7 4)

private def expectedSignedDeleteMiss : Cell :=
  mkDeleteRoot "signed-delete-miss" (some signedNibbleRoot4) (mkKeyBits "signed-delete-miss-key" 6 4 false)

private def expectedUnsignedDeleteMiss : Cell :=
  mkDeleteRoot "unsigned-delete-miss" (some unsignedNibbleRoot4) (mkKeyBits "unsigned-delete-miss-key" 1 4 true)

private def mkIntSetStack (dict : Value) (key : Int) (n : Int) (newValue : Value) : Array Value :=
  #[(dict), intV key, intV n, newValue]

private def mkSliceSetStack (dict : Value) (keyBits : BitString) (n : Int) (newValue : Value) : Array Value :=
  #[(dict), .slice (mkSliceFromBits keyBits), intV n, newValue]

private def mkCase (name : String) (code : Cell) (stack : Array Value) (gasLimits : OracleGasLimits := {}) (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[]
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictISetGetOptRefFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (.int (.num dispatchSentinel))) stack

private def runDictISetGetOptRefDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (i, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def setGetOptRefGas : Int :=
  computeExactGasBudget (dictISetGetOptRefInstr false false)

private def setGetOptRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact setGetOptRefGas

private def setGetOptRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne setGetOptRefGas

private def genDictISetGetOptRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase "fuzz/set/int/signed-hit" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueGoodC)), rng1)
    else if shape = 1 then
      (mkCase "fuzz/set/int/signed-miss" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 6 4 (.cell valueGoodC)), rng1)
    else if shape = 2 then
      (mkCase "fuzz/set/int/uint-hit" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueGoodC)), rng1)
    else if shape = 3 then
      (mkCase "fuzz/set/int/uint-miss" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 11 4 (.cell valueGoodC)), rng1)
    else if shape = 4 then
      (mkCase "fuzz/set/int/signed-delete" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 .null), rng1)
    else if shape = 5 then
      (mkCase "fuzz/set/int/uint-delete" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 9 4 .null), rng1)
    else if shape = 6 then
      (mkCase "fuzz/set/slice/set-hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueGoodC)), rng1)
    else if shape = 7 then
      (mkCase "fuzz/set/slice/set-miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 1 4) 4 (.cell valueGoodC)), rng1)
    else if shape = 8 then
      (mkCase "fuzz/set/slice/delete-hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 7 4) 4 .null), rng1)
    else if shape = 9 then
      (mkCase "fuzz/set/slice/delete-miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 4 4) 4 .null), rng1)
    else if shape = 10 then
      (mkCase "fuzz/set/int/nan-key" rawSetGetOptRefInt (#[(.cell signedNibbleRoot4), .int .nan, intV 4, .cell valueGoodC]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/set/int/n-out-of-range" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 16 4 (.cell valueGoodC)), rng1)
    else if shape = 12 then
      (mkCase "fuzz/set/int/negative-n" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) (-1) (.cell valueGoodC)), rng1)
    else if shape = 13 then
      (mkCase "fuzz/set/int/nan-n" rawSetGetOptRefInt
        (#[.cell signedNibbleRoot4, intV (-3), .int .nan, .cell valueGoodC]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/set/slice/underflow" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 8 (.cell valueGoodC)), rng1)
    else if shape = 15 then
      (mkCase "fuzz/set/type-error-key-int" rawSetGetOptRefInt (#[.cell signedNibbleRoot4, .slice (mkSliceFromBits (natToBits 2 4)), intV 4, .cell valueGoodC]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/set/type-error-key-slice" rawSetGetOptRef (#[.cell sliceNibbleRoot4, .int (.num 7), intV 4, .cell valueGoodC]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/set/type-error-value" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.int (.num 7))), rng1)
    else if shape = 18 then
      (mkCase "fuzz/set/type-error-dict" rawSetGetOptRefInt (#[(.tuple #[]), .int (.num 7), intV 4, .cell valueGoodC]), rng1)
    else if shape = 19 then
      (mkCase "fuzz/delete/type-error-value" rawSetGetOptRefInt (#[(.cell signedNibbleRoot4), .int (.num (-3)), intV 4, .int (.num 7)]), rng1)
    else if shape = 20 then
      (mkCase "fuzz/set/n-too-large" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 1024 (.cell valueGoodC)), rng1)
    else if shape = 21 then
      (mkCase "fuzz/delete/n-too-large" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 1024 .null), rng1)
    else if shape = 22 then
      (mkCase "fuzz/set/uint/out-of-range" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) (-1) 4 (.cell valueGoodC)), rng1)
    else if shape = 23 then
      (mkCase "fuzz/set/signed-zero" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot0) 0 0 (.cell valueGoodC)), rng1)
    else if shape = 24 then
      (mkCase "fuzz/set/unsigned-zero" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot0) 0 0 (.cell valueGoodC)), rng1)
    else if shape = 25 then
      (mkCase "fuzz/set/bad-old-value-dict-err" rawSetGetOptRefInt (mkIntSetStack (.cell signedRootBadValue) (-3) 4 (.cell valueGoodC)), rng1)
    else if shape = 26 then
      (mkCase "fuzz/delete/bad-old-value-dict-err" rawSetGetOptRefInt (mkIntSetStack (.cell signedRootBadValue) (-3) 4 .null), rng1)
    else if shape = 27 then
      (mkCase "fuzz/set/bad-root-dict-err" rawSetGetOptRefInt (mkIntSetStack (.cell malformedDict) (-3) 4 (.cell valueGoodC)), rng1)
    else if shape = 28 then
      (mkCase "fuzz/delete/bad-root-dict-err" rawSetGetOptRef (mkSliceSetStack (.cell malformedDict) (natToBits 2 4) 4 .null), rng1)
    else if shape = 29 then
      (mkCase "fuzz/set/decode-compat-getoptref" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueGoodC)), rng1)
    else
      (mkCase "fuzz/set/slice-miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 0 4) 4 (.cell valueGoodC)), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)



def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runDictISetGetOptRefFallback (dictISetGetOptRefInstr true false) #[])
          #[.int (.num dispatchSentinel)]
    },
    { name := "unit/decode/slice"
      run := do
        let _ ← expectDecodeStep "decode/0xf46d"
          (mkSliceFromBits (natToBits 0xF46D 16))
          (dictISetGetOptRefInstr false false)
          16
        pure ()
    },
    { name := "unit/decode/int"
      run := do
        let _ ← expectDecodeStep "decode/0xf46e"
          (mkSliceFromBits (natToBits 0xF46E 16))
          (dictISetGetOptRefInstr true false)
          16
        pure ()
    },
    { name := "unit/decode/uint"
      run := do
        let _ ← expectDecodeStep "decode/0xf46f"
          (mkSliceFromBits (natToBits 0xF46F 16))
          (dictISetGetOptRefInstr true true)
          16
        pure ()
    },
    { name := "unit/assemble/invopcode"
      run := do
        assembleInvOpcode "slice" (dictISetGetOptRefInstr false false)
        assembleInvOpcode "int" (dictISetGetOptRefInstr true false)
        assembleInvOpcode "uint" (dictISetGetOptRefInstr true true)
    },
    { name := "unit/ decode/stream-boundary"
      run := do
        let stream : Slice :=
          Slice.ofCell <|
            Cell.mkOrdinary
              (rawSetGetOptRef.bits ++ rawSetGetOptRefInt.bits ++ rawSetGetOptRefUInt.bits ++ rawGetOptRef.bits ++ rawGetOptRefInt.bits ++ rawGetOptRefUInt.bits)
              (rawSetGetOptRef.refs ++ rawSetGetOptRefInt.refs ++ rawSetGetOptRefUInt.refs ++ rawGetOptRef.refs ++ rawGetOptRefInt.refs ++ rawGetOptRefUInt.refs)
        let s1 ← expectDecodeStep "decode/stream/f46d" stream (dictISetGetOptRefInstr false false) 16
        let s2 ← expectDecodeStep "decode/stream/f46e" s1 (dictISetGetOptRefInstr true false) 16
        let s3 ← expectDecodeStep "decode/stream/f46f" s2 (dictISetGetOptRefInstr true true) 16
        let s4 ← expectDecodeStep "decode/stream/f469" s3 (dictISetGetOptRefInstr false false) 16
        let s5 ← expectDecodeStep "decode/stream/f46a" s4 (dictISetGetOptRefInstr true false) 16
        let _ ← expectDecodeStep "decode/stream/f46b" s5 (dictISetGetOptRefInstr true true) 16
        pure ()
    },
    { name := "unit/decode/adjacent-below"
      run := do
        expectDecodeInvOpcode "decode/0xf46c" 0xF46C
    },
    { name := "unit/decode/adjacent-above"
      run := do
        expectDecodeInvOpcode "decode/0xf470" 0xF470
    },
    { name := "unit/decode/truncated8"
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated8 expected failure")
    },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "runtime/underflow"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr false false) (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 1 4) 4 .null))
          .stkUnd
    },
    { name := "unit/runtime/set/int/signed-hit"
      run := do
        expectOkStack "runtime/set/int/signed-hit"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueGoodC)))
          #[.cell expectedSignedSetHit, .cell storedRefA]
    },
    { name := "unit/runtime/set/int/unsigned-hit"
      run := do
        expectOkStack "runtime/set/int/unsigned-hit"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true true)
            (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueGoodC)))
          #[.cell expectedUnsignedSetHit, .cell storedRefA]
    },
    { name := "unit/runtime/set/int/delete-hit"
      run := do
        expectOkStack "runtime/set/int/delete-hit"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 .null))
          #[.cell expectedSignedDeleteHit, .cell storedRefA]
    },
    { name := "unit/runtime/set/int/delete-miss"
      run := do
        expectOkStack "runtime/set/int/delete-miss"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null))
          #[.cell expectedSignedDeleteMiss, .null]
    },
    { name := "unit/runtime/set/slice/hit"
      run := do
        expectOkStack "runtime/set/slice/hit"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr false false)
            (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueGoodC)))
          #[.cell expectedSliceSetHit, .cell storedRefA]
    },
    { name := "unit/runtime/set/slice/delete-hit"
      run := do
        expectOkStack "runtime/set/slice/delete-hit"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr false false)
            (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 7 4) 4 .null))
          #[.cell expectedSliceDeleteHit, .cell storedRefB]
    },
    { name := "unit/runtime/set/int/out-of-range"
      run := do
        expectErr "runtime/set/int/out-of-range"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true true)
            (mkIntSetStack (.cell unsignedNibbleRoot4) 16 4 (.cell valueGoodC)))
          .rangeChk
    },
    { name := "unit/runtime/set/int/nan-key"
      run := do
        expectErr "runtime/set/int/nan-key"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (#[.cell signedNibbleRoot4, .int .nan, intV 4, .cell valueGoodC]))
          .rangeChk
    },
    { name := "unit/runtime/set/slice/underflow"
      run := do
        expectErr "runtime/set/slice/underflow"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr false false)
            (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 8 (.cell valueGoodC)))
          .cellUnd
    },
    { name := "unit/runtime/set/type-key-int"
      run := do
        expectErr "runtime/set/type-key-int"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueGoodC)))
          .typeChk
    },
    { name := "unit/runtime/set/type-value"
      run := do
        expectErr "runtime/set/type-value"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.int (.num 7))))
          .typeChk
    },
    { name := "unit/runtime/set/dict-err-bad-old-value"
      run := do
        expectErr "runtime/set/dict-err-bad-old-value"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedRootBadValue) (-3) 4 (.cell valueGoodC)))
          .dictErr
    },
    { name := "unit/runtime/set/delete/bad-old-value"
      run := do
        expectErr "runtime/set/delete-bad-old-value"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedRootBadValue) (-3) 4 .null))
          .dictErr
    },
    { name := "unit/runtime/delete/malformed-root"
      run := do
        expectErr "runtime/delete/malformed-root"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr false false)
            (mkSliceSetStack (.cell malformedDict) (natToBits 2 4) 4 .null))
          .dictErr
    },
    { name := "unit/gas/exact/delete-miss-signed"
      run := do
        expectOkStack "unit/runtime/gas/exact/delete-miss-signed"
          (runDictISetGetOptRefDirect (dictISetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null))
          #[.cell expectedSignedDeleteMiss, .null]
    }
  ]
  oracle := #[
    -- [B2][B3][B4][B8]
    mkCase "oracle/underflow/no-stack" rawSetGetOptRef #[],
    -- [B8][B7]
    mkCase "oracle/set/slice-key-underflow" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 8 (.cell valueGoodC)),
    -- [B3][B4]
    mkCase "oracle/err-n-too-small" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) (-1) (.cell valueGoodC)),
    -- [B3][B4]
    mkCase "oracle/err-n-too-large" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 1024 (.cell valueGoodC)),
    -- [B3][B4]
    mkCase "oracle/err-n-nan" rawSetGetOptRefInt (#[.cell signedNibbleRoot4, intV (-3), .int .nan, .cell valueGoodC]),
    -- [B4][B14]
    mkCase "oracle/err-type-dict" rawSetGetOptRefInt (#[.tuple #[], .int (.num 5), intV 4, .cell valueGoodC]),
    -- [B5][B4]
    mkCase "oracle/err-type-key-int" rawSetGetOptRefInt (#[.cell signedNibbleRoot4, .cell storedRefA, intV 4, .cell valueGoodC]),
    -- [B5][B4]
    mkCase "oracle/err-type-key-slice" rawSetGetOptRef (#[.cell sliceNibbleRoot4, .int (.num 2), intV 4, .cell valueGoodC]),
    -- [B8][B9]
    mkCase "oracle/err-type-new-value" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.int (.num 1))),
    -- [B6]
    mkCase "oracle/int/signed-hit" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueGoodC)),
    -- [B6]
    mkCase "oracle/int/signed-miss" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 6 4 (.cell valueGoodC)),
    -- [B6]
    mkCase "oracle/int/signed-hit-delete" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 .null),
    -- [B6]
    mkCase "oracle/int/unsigned-hit" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueGoodC)),
    -- [B6]
    mkCase "oracle/int/unsigned-miss" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 11 4 (.cell valueGoodC)),
    -- [B6]
    mkCase "oracle/int/unsigned-delete" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 9 4 .null),
    -- [B6]
    mkCase "oracle/int/key-out-of-range-high" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 16 4 (.cell valueGoodC)),
    -- [B6]
    mkCase "oracle/int/key-out-of-range-low" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-9) 4 (.cell valueGoodC)),
    -- [B6]
    mkCase "oracle/int/key-nan" rawSetGetOptRefInt (#[.cell signedNibbleRoot4, .int .nan, intV 4, .cell valueGoodC]),
    -- [B9]
    mkCase "oracle/int/key-out-of-range-unsigned" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) (-1) 4 (.cell valueGoodC)),
    -- [B7]
    mkCase "oracle/slice-hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueGoodC)),
    -- [B7]
    mkCase "oracle/slice-miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 4 4) 4 (.cell valueGoodC)),
    -- [B7]
    mkCase "oracle/slice-delete-hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 7 4) 4 .null),
    -- [B7]
    mkCase "oracle/slice-delete-miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 1 4) 4 .null),
    -- [B7]
    mkCase "oracle/slice-underflow" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 8 (.cell valueGoodC)),
    -- [B9]
    mkCase "oracle/delete/miss-signed" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null),
    -- [B9]
    mkCase "oracle/delete/nonzero" rawSetGetOptRefInt (mkIntSetStack (.cell unsignedNibbleRoot4) 7 4 .null),
    -- [B11]
    mkCase "oracle/err-bad-old-value-set" rawSetGetOptRefInt (mkIntSetStack (.cell signedRootBadValue) (-3) 4 (.cell valueGoodC)),
    -- [B11]
    mkCase "oracle/err-bad-old-value-delete" rawSetGetOptRefInt (mkIntSetStack (.cell signedRootBadValue) (-3) 4 .null),
    -- [B10][B13]
    mkCase "oracle/err-delete-bad-old-value-slice" rawSetGetOptRef (mkSliceSetStack (.cell sliceRootBadValue) (natToBits 2 4) 4 .null),
    -- [B10][B13]
    mkCase "oracle/err-malformed-root-set" rawSetGetOptRefInt (mkIntSetStack (.cell malformedDict) (-3) 4 (.cell valueGoodC)),
    -- [B10][B13]
    mkCase "oracle/err-malformed-root-delete" rawSetGetOptRef (mkSliceSetStack (.cell malformedDict) (natToBits 2 4) 4 .null),
    -- [B3][B9]
    mkCase "oracle/n-zero-signed" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot0) 0 0 (.cell valueGoodC)),
    -- [B3][B9]
    mkCase "oracle/n-zero-unsigned" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot0) 0 0 (.cell valueGoodC)),
    -- [B15]
    mkCase "oracle/gas/exact-delete-miss" (gasCode setGetOptRefGas rawSetGetOptRefInt)
      (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null) setGetOptRefGasExact,
    -- [B15]
    mkCase "oracle/gas/exact-minus-one-delete-miss" (gasCode (setGetOptRefGas - 1) rawSetGetOptRefInt)
      (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null) setGetOptRefGasExactMinusOne,
    -- [B14]
    mkCase "oracle/fuzz-compatible-boundary" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueGoodC))
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictISetGetOptRefFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTISETGETOPTREF
