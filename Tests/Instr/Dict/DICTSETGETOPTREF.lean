import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTSETGETOPTREF

/-!
INSTRUCTION: DICTSETGETOPTREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictExt` must route `.dictExt (.setGetOptRef ...)` to a dedicated runtime branch.
   - Any other opcode follows `next`/fallback dispatch behavior.

2. [B2] Runtime arity check (`checkUnderflow 4`).
   - Missing any of `n`, `D`, `k`/`i`, or `c?` throws `.stkUnd`.

3. [B3] `n` validation (`popNatUpTo 1023`).
   - `.nan`, negative, and too-large `n` throw `.rangeChk`.
   - `n = 0` is valid.

4. [B4] Dictionary argument parsing (`popMaybeCell`).
   - `.null` is accepted as empty root.
   - malformed non-cell root throws `.typeChk`.

5. [B5] Slice-key path (`intKey = false`).
   - Pops a slice and attempts to read `n` bits.
   - If insufficient bits, throws `.cellUnd` from key materialization.

6. [B6] Integer-key path (`intKey = true`).
   - Uses `popInt` (not `popIntFinite`).
   - `.nan` and out-of-range integers produce `.rangeChk`.
   - Signed/unsigned bounds are enforced by `dictKeyBits?`.

7. [B7] Mutation mode dispatch from `newValue` (`newValue?`).
   - `newValue = .null` ⇒ delete path (`dictDeleteWithCells`).
   - `newValue = .cell _` ⇒ set path (`dictLookupSetRefWithCells`).
   - `newValue` non-cell/non-null is impossible due `popMaybeCell` type checks.

8. [B8] Set-path outcomes.
   - Success returns new root and optional old value:
     - key-miss pushes `.null` as old value;
     - key-hit pushes old value ref when encoded as a single-ref slice;
     - malformed old value shape pushes `.dictErr`.
   - May consume `cellCreateGasPrice` units when creation occurred.

9. [B10] Delete-path outcomes.
   - Similar structure to set-path: new root + old-value/null.
   - Malformed payload for old value also yields `.dictErr`.

10. [B11] Traversal/type errors.
    - Malformed dictionary structure on lookup/delete/set propagation produces `.dictErr`.

11. [B12] Assembler behavior.
    - `.dictExt` encoding is unsupported in this path; all `.dictExt (.setGetOptRef ...)` forms must throw `.invOpcode`.

12. [B13] Decoder behavior.
    - Raw opcodes:
      - `0xF46D` → `.dictExt (.setGetOptRef false false)`;
      - `0xF46E` → `.dictExt (.setGetOptRef true false)`;
      - `0xF46F` → `.dictExt (.setGetOptRef true true)`.
    - Adjacent words `0xF46C` and `0xF470` must decode as `.invOpcode`.
    - Boundary checks include aliasing with neighboring DICT*GETOPTREF opcodes (`0xF469..0xF46B`).

13. [B14] Gas accounting.
    - No visible variable gas formula besides base gas and optional create penalties from dictionary updates.
    - Exact and exact-minus-one limit checks must be tested on a stable branch.

TOTAL BRANCHES: 14

Assembler/gas notes:
- No parameterized assembler encoding/validation exists for these opcodes (always `.invOpcode` in Asm), so category B12 is a pure rejection category.
- Gas branches are base-constant in this suite's tested non-creating paths.
-/

private def suiteId : InstrId :=
  { name := "DICTSETGETOPTREF" }

private def dictSetGetOptRefInstr (intKey unsigned : Bool) : Instr :=
  .dictExt (.setGetOptRef intKey unsigned)

private def rawSetGetOptRef : Cell :=
  Cell.mkOrdinary (natToBits 0xF46D 16) #[]

private def rawSetGetOptRefInt : Cell :=
  Cell.mkOrdinary (natToBits 0xF46E 16) #[]

private def rawSetGetOptRefUInt : Cell :=
  Cell.mkOrdinary (natToBits 0xF46F 16) #[]

private def rawGetOptRef : Cell :=
  Cell.mkOrdinary (natToBits 0xF469 16) #[]

private def rawGetOptRefInt : Cell :=
  Cell.mkOrdinary (natToBits 0xF46A 16) #[]

private def rawGetOptRefUInt : Cell :=
  Cell.mkOrdinary (natToBits 0xF46B 16) #[]

private def rawSetGetOptRefBelow : Cell :=
  Cell.mkOrdinary (natToBits 0xF46C 16) #[]

private def rawSetGetOptRefAbove : Cell :=
  Cell.mkOrdinary (natToBits 0xF470 16) #[]

private def rawTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def dispatchSentinel : Int := 771_001

private def mkGasPrefix (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok c => c
  | .error e => panic! s!"failed to assemble gas prefix for DICTSETGETOPTREF: {reprStr e}"

private def gasCode (gas : Int) (opcode : Cell) : Cell :=
  let p := mkGasPrefix gas
  Cell.mkOrdinary (p.bits ++ opcode.bits) (p.refs ++ opcode.refs)

private def assembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr c}")
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {reprStr e}")

private def mkDictSetRefRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n unsigned with
        | some bits => bits
        | none => panic! s!"{label}: out-of-range key for dictionary setup ({k}, n={n}, unsigned={unsigned})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some r, _old, _created, _loaded) => root := r
      | .ok (none, _old, _created, _loaded) => panic! s!"{label}: unexpected empty root during dictionary setup"
      | .error e => panic! s!"{label}: dict set failed with {reprStr e}"
    pure <| match root with
      | some r => r
      | none => panic! s!"{label}: empty dictionary construction"

private def mkDictSetSliceRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetSliceWithCells root k (Slice.ofCell v) .set with
        | .ok (some r, _old, _created, _loaded) => root := r
        | .ok (none, _old, _created, _loaded) => panic! s!"{label}: unexpected empty root during slice-dictionary setup"
        | .error e => panic! s!"{label}: slice dict set failed with {reprStr e}"
    pure <| match root with
      | some r => r
      | none => panic! s!"{label}: empty dictionary construction"

private def mkSetRoot (label : String) (root : Option Cell) (keyBits : BitString) (value : Cell) : Cell :=
  let result := dictLookupSetRefWithCells root keyBits value .set
  match result with
  | .ok (_, newRoot, _ok, _created, _loaded) =>
      match newRoot with
      | some c => c
      | none => panic! s!"{label}: expected non-empty root on set success"
  | .error e => panic! s!"{label}: expected set success, got {reprStr e}"

private def mkDeleteRoot (label : String) (root : Option Cell) (keyBits : BitString) : Cell :=
  let result := dictDeleteWithCells root keyBits
  match result with
  | .ok (_, newRoot, _created, _loaded) =>
      match newRoot with
      | some c => c
      | none => panic! s!"{label}: expected non-empty root on delete success"
  | .error e => panic! s!"{label}: expected delete success, got {reprStr e}"

private def mkKeyBits (label : String) (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid key {idx} for n={n}, unsigned={unsigned}"

private def storedRefA : Cell :=
  Cell.mkOrdinary (natToBits 0xA4 8) #[]

private def storedRefB : Cell :=
  Cell.mkOrdinary (natToBits 0xB7 8) #[]

private def storedRefC : Cell :=
  Cell.mkOrdinary (natToBits 0xC9 8) #[]

private def storedRefD : Cell :=
  Cell.mkOrdinary (natToBits 0xD3 8) #[]

private def valueA : Cell :=
  Cell.mkOrdinary #[] #[storedRefA]

private def valueB : Cell :=
  Cell.mkOrdinary #[] #[storedRefB]

private def valueC : Cell :=
  Cell.mkOrdinary #[] #[storedRefC]

private def valueD : Cell :=
  Cell.mkOrdinary #[] #[storedRefD]

private def badValueBitsOnly : Cell :=
  Cell.mkOrdinary (natToBits 0xF0 8) #[]

private def badValueBitsAndRefs : Cell :=
  Cell.mkOrdinary (natToBits 0x55 8) #[storedRefA, storedRefB]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0xF 4) #[]

private def signedNibbleRoot4 : Cell :=
  mkDictSetRefRoot! "signedNibbleRoot4" 4 false #[
    (-3, valueA),
    (7, valueB)
  ]

private def unsignedNibbleRoot4 : Cell :=
  mkDictSetRefRoot! "unsignedNibbleRoot4" 4 true #[
    (5, valueA),
    (9, valueB)
  ]

private def sliceNibbleRoot4 : Cell :=
  mkDictSetSliceRoot! "sliceNibbleRoot4" #[
    (natToBits 2 4, valueA),
    (natToBits 7 4, valueB)
  ]

private def signedNibbleRoot0 : Cell :=
  mkDictSetRefRoot! "signedNibbleRoot0" 0 false #[(0, valueA)]

private def unsignedNibbleRoot0 : Cell :=
  mkDictSetRefRoot! "unsignedNibbleRoot0" 0 true #[(0, valueA)]

private def signedBadValueRoot4 : Cell :=
  mkDictSetRefRoot! "signedBadValueRoot4" 4 false #[
    (-3, badValueBitsOnly)
  ]

private def unsignedBadValueRoot4 : Cell :=
  mkDictSetRefRoot! "unsignedBadValueRoot4" 4 true #[
    (5, badValueBitsAndRefs)
  ]

private def sliceBadValueRoot4 : Cell :=
  mkDictSetSliceRoot! "sliceBadValueRoot4" #[
    (natToBits 2 4, badValueBitsOnly),
    (natToBits 7 4, badValueBitsAndRefs)
  ]

private def expectedSignedSetHit : Cell :=
  mkSetRoot "signedSetHit" (some signedNibbleRoot4) (mkKeyBits "signedSetHit" (-3) 4 false) valueC

private def expectedSignedSetMiss : Cell :=
  mkSetRoot "signedSetMiss" (some signedNibbleRoot4) (mkKeyBits "signedSetMiss" 6 4 false) valueC

private def expectedUnsignedSetHit : Cell :=
  mkSetRoot "unsignedSetHit" (some unsignedNibbleRoot4) (mkKeyBits "unsignedSetHit" 5 4 true) valueC

private def expectedUnsignedSetMiss : Cell :=
  mkSetRoot "unsignedSetMiss" (some unsignedNibbleRoot4) (mkKeyBits "unsignedSetMiss" 11 4 true) valueC

private def expectedSliceSetHit : Cell :=
  mkSetRoot "sliceSetHit" (some sliceNibbleRoot4) (natToBits 2 4) valueC

private def expectedSliceSetMiss : Cell :=
  mkSetRoot "sliceSetMiss" (some sliceNibbleRoot4) (natToBits 4 4) valueC

private def expectedSignedDeleteHit : Cell :=
  mkDeleteRoot "signedDeleteHit" (some signedNibbleRoot4) (mkKeyBits "signedDeleteHit" 7 4 false)

private def expectedSignedDeleteMiss : Cell :=
  mkDeleteRoot "signedDeleteMiss" (some signedNibbleRoot4) (mkKeyBits "signedDeleteMiss" 6 4 false)

private def expectedUnsignedDeleteHit : Cell :=
  mkDeleteRoot "unsignedDeleteHit" (some unsignedNibbleRoot4) (mkKeyBits "unsignedDeleteHit" 9 4 true)

private def expectedUnsignedDeleteMiss : Cell :=
  mkDeleteRoot "unsignedDeleteMiss" (some unsignedNibbleRoot4) (mkKeyBits "unsignedDeleteMiss" 1 4 true)

private def expectedSliceDeleteHit : Cell :=
  mkDeleteRoot "sliceDeleteHit" (some sliceNibbleRoot4) (natToBits 7 4)

private def expectedSliceDeleteMiss : Cell :=
  mkDeleteRoot "sliceDeleteMiss" (some sliceNibbleRoot4) (natToBits 1 4)

private def mkIntSetStack (dict : Value) (key : Int) (n : Int) (newValue : Value) : Array Value :=
  #[(dict), intV key, intV n, newValue]

private def mkSliceSetStack (dict : Value) (keyBits : BitString) (n : Int) (newValue : Value) : Array Value :=
  #[(dict), .slice (mkSliceFromBits keyBits), intV n, newValue]

private def mkCase
    (name : String)
    (code : Cell)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[]
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictSetGetOptRefFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (.int (.num dispatchSentinel))) stack

private def runDictSetGetOptRefDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell <| Cell.mkOrdinary (natToBits opcode 16) #[]) with
  | .ok (i, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def setGetOptRefGas : Int :=
  computeExactGasBudget (dictSetGetOptRefInstr false false)

private def setGetOptRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact setGetOptRefGas

private def setGetOptRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne setGetOptRefGas

private def underflowOneStack : Array Value :=
  #[] |>.push (.slice (mkSliceFromBits (natToBits 1 8)))

private def underflowTwoStack : Array Value :=
  #[] |>.push (.slice (mkSliceFromBits (natToBits 1 8))) |>.push (.cell signedNibbleRoot4)

private def genDictSetGetOptRefFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 34
  let (case0, rng2) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase "fuzz/signed/set/hit" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueD)), rng1)
    else if shape = 1 then
      (mkCase "fuzz/signed/set/miss" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 6 4 (.cell valueD)), rng1)
    else if shape = 2 then
      (mkCase "fuzz/signed/delete/hit" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 7 4 .null), rng1)
    else if shape = 3 then
      (mkCase "fuzz/signed/delete/miss" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null), rng1)
    else if shape = 4 then
      (mkCase "fuzz/unsigned/set/hit" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueD)), rng1)
    else if shape = 5 then
      (mkCase "fuzz/unsigned/set/miss" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 11 4 (.cell valueD)), rng1)
    else if shape = 6 then
      (mkCase "fuzz/unsigned/delete/hit" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 9 4 .null), rng1)
    else if shape = 7 then
      (mkCase "fuzz/unsigned/delete/miss" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 1 4 .null), rng1)
    else if shape = 8 then
      (mkCase "fuzz/slice/set/hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueD)), rng1)
    else if shape = 9 then
      (mkCase "fuzz/slice/set/miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 1 4) 4 (.cell valueD)), rng1)
    else if shape = 10 then
      (mkCase "fuzz/slice/delete/hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 7 4) 4 .null), rng1)
    else if shape = 11 then
      (mkCase "fuzz/slice/delete/miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 1 4) 4 .null), rng1)
    else if shape = 12 then
      (mkCase "fuzz/int-key-nan" rawSetGetOptRefInt
        (#[.cell signedNibbleRoot4, .int .nan, intV 4, .cell valueD]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/n-negative" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 3 (-1) (.cell valueD)), rng1)
    else if shape = 14 then
      (mkCase "fuzz/n-too-large" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 1024 (.cell valueD)), rng1)
    else if shape = 15 then
      (mkCase "fuzz/slice-key-short" rawSetGetOptRef (mkSliceSetStack (.cell signedNibbleRoot4) (natToBits 1 4) 8 (.cell valueD)), rng1)
    else if shape = 16 then
      (mkCase "fuzz/type-dict" rawSetGetOptRefInt (mkIntSetStack (.tuple #[]) 7 4 (.cell valueD)), rng1)
    else if shape = 17 then
      (mkCase "fuzz/type-key-int" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueD)), rng1)
    else if shape = 18 then
      (mkCase "fuzz/type-key-slice" rawSetGetOptRefInt #[(.cell signedNibbleRoot4), .slice (mkSliceFromBits (natToBits 2 4)), intV 4, .cell valueD], rng1)
    else if shape = 19 then
      (mkCase "fuzz/type-value" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 7 4 (.int (.num 7))), rng1)
    else if shape = 20 then
      (mkCase "fuzz/newvalue-null/delete-signed" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 .null), rng1)
    else if shape = 21 then
      (mkCase "fuzz/dicterr/bad-old-set-signed" rawSetGetOptRefInt (mkIntSetStack (.cell signedBadValueRoot4) (-3) 4 (.cell valueD)), rng1)
    else if shape = 22 then
      (mkCase "fuzz/dicterr/bad-old-del-signed" rawSetGetOptRefInt (mkIntSetStack (.cell signedBadValueRoot4) (-3) 4 .null), rng1)
    else if shape = 23 then
      (mkCase "fuzz/dicterr/bad-old-set-unsigned" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 (.cell valueD)), rng1)
    else if shape = 24 then
      (mkCase "fuzz/dicterr/bad-old-del-slice" rawSetGetOptRef (mkSliceSetStack (.cell sliceBadValueRoot4) (natToBits 2 4) 4 .null), rng1)
    else if shape = 25 then
      (mkCase "fuzz/dicterr/malformed-root" rawSetGetOptRefInt (mkIntSetStack (.cell malformedDict) 1 4 (.cell valueD)), rng1)
    else if shape = 26 then
      (mkCase "fuzz/int/out-of-range-signed-high" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 8 4 (.cell valueD)), rng1)
    else if shape = 27 then
      (mkCase "fuzz/int/out-of-range-signed-low" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-9) 4 (.cell valueD)), rng1)
    else if shape = 28 then
      (mkCase "fuzz/int/out-of-range-uint-low" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) (-1) 4 (.cell valueD)), rng1)
    else if shape = 29 then
      (mkCase "fuzz/int/out-of-range-uint-high" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 16 4 (.cell valueD)), rng1)
    else if shape = 30 then
      (mkCase "fuzz/zs" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot0) 0 0 (.cell valueD)), rng1)
    else if shape = 31 then
      (mkCase "fuzz/uint-zero-width" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot0) 0 0 (.cell valueD)), rng1)
    else if shape = 32 then
      (mkCase "fuzz/gas/exact-delete-miss" (gasCode setGetOptRefGas rawSetGetOptRefInt)
        (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null) setGetOptRefGasExact, rng1)
    else if shape = 33 then
      (mkCase "fuzz/gas/exact-minus-one-delete-miss" (gasCode (setGetOptRefGas - 1) rawSetGetOptRefInt)
        (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null) setGetOptRefGasExactMinusOne, rng1)
    else if shape = 34 then
      (mkCase "fuzz/alias-getoptref-compat" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueD)), rng1)
    else
      (mkCase "fuzz/fallback" rawSetGetOptRef (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueD)), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runDictSetGetOptRefFallback (dictSetGetOptRefInstr false false) #[])
          #[.int (.num dispatchSentinel)]
    },
    { name := "unit/decode/raw-slice"
      run := do
        let _ ← expectDecodeStep "decode/0xf46d" (mkSliceFromBits (natToBits 0xF46D 16))
          (dictSetGetOptRefInstr false false) 16
        pure ()
    },
    { name := "unit/decode/raw-int"
      run := do
        let _ ← expectDecodeStep "decode/0xf46e" (mkSliceFromBits (natToBits 0xF46E 16))
          (dictSetGetOptRefInstr true false) 16
        pure ()
    },
    { name := "unit/decode/raw-uint"
      run := do
        let _ ← expectDecodeStep "decode/0xf46f" (mkSliceFromBits (natToBits 0xF46F 16))
          (dictSetGetOptRefInstr true true) 16
        pure ()
    },
    { name := "unit/assemble/invopcode-slice"
      run := do
        assembleInvOpcode "slice" (dictSetGetOptRefInstr false false)
    },
    { name := "unit/assemble/invopcode-int"
      run := do
        assembleInvOpcode "int" (dictSetGetOptRefInstr true false)
    },
    { name := "unit/assemble/invopcode-uint"
      run := do
        assembleInvOpcode "uint" (dictSetGetOptRefInstr true true)
    },
    { name := "unit/decode/stream"
      run := do
        let stream : Slice :=
          Slice.ofCell <|
            Cell.mkOrdinary
              (rawSetGetOptRef.bits ++ rawSetGetOptRefInt.bits ++ rawSetGetOptRefUInt.bits ++
                rawGetOptRef.bits ++ rawGetOptRefInt.bits ++ rawGetOptRefUInt.bits)
              (rawSetGetOptRef.refs ++ rawSetGetOptRefInt.refs ++ rawSetGetOptRefUInt.refs ++
                rawGetOptRef.refs ++ rawGetOptRefInt.refs ++ rawGetOptRefUInt.refs)
        let s1 ← expectDecodeStep "decode/stream/f46d" stream (dictSetGetOptRefInstr false false) 16
        let s2 ← expectDecodeStep "decode/stream/f46e" s1 (dictSetGetOptRefInstr true false) 16
        let s3 ← expectDecodeStep "decode/stream/f46f" s2 (dictSetGetOptRefInstr true true) 16
        let s4 ← expectDecodeStep "decode/stream/f469" s3 (dictSetGetOptRefInstr false false) 16
        let s5 ← expectDecodeStep "decode/stream/f46a" s4 (dictSetGetOptRefInstr true false) 16
        let _ ← expectDecodeStep "decode/stream/f46b" s5 (dictSetGetOptRefInstr true true) 16
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
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr false false) (mkSliceSetStack (.cell signedNibbleRoot4) (natToBits 2 4) 4 .null))
          .stkUnd
    },
    { name := "unit/runtime/set/signed-hit"
      run := do
        expectOkStack "runtime/signed/hit"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueD)))
          #[.cell expectedSignedSetHit, .cell storedRefA]
    },
    { name := "unit/runtime/set/unsigned-hit"
      run := do
        expectOkStack "runtime/unsigned/hit"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr true true)
            (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueD)))
          #[.cell expectedUnsignedSetHit, .cell storedRefA]
    },
    { name := "unit/runtime/delete/signed-hit"
      run := do
        expectOkStack "runtime/signed/delete-hit"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) 7 4 .null))
          #[.cell expectedSignedDeleteHit, .cell storedRefB]
    },
    { name := "unit/runtime/delete/slice-hit"
      run := do
        expectOkStack "runtime/slice/delete-hit"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr false false)
            (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 7 4) 4 .null))
          #[.cell expectedSliceDeleteHit, .cell storedRefB]
    },
    { name := "unit/runtime/set/slice-hit"
      run := do
        expectOkStack "runtime/slice/hit"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr false false)
            (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueD)))
          #[.cell expectedSliceSetHit, .cell storedRefA]
    },
    { name := "unit/runtime/set/int-range"
      run := do
        expectErr "runtime/int-range"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedNibbleRoot4) 8 4 (.cell valueD)))
          .rangeChk
    },
    { name := "unit/runtime/set/slice-underflow"
      run := do
        expectErr "runtime/slice-underflow"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr false false)
            (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 8 (.cell valueD)))
          .cellUnd
    },
    { name := "unit/runtime/dict-err-old-set"
      run := do
        expectErr "runtime/dict-err-old-set"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedBadValueRoot4) (-3) 4 (.cell valueD)))
          .dictErr
    },
    { name := "unit/runtime/dict-err-old-delete"
      run := do
        expectErr "runtime/dict-err-old-delete"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr true false)
            (mkIntSetStack (.cell signedBadValueRoot4) (-3) 4 .null))
          .dictErr
    },
    { name := "unit/runtime/malformed-root"
      run := do
        expectErr "runtime/malformed-root"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr false false)
            (mkSliceSetStack (.cell malformedDict) (natToBits 7 4) 4 .null))
          .dictErr
    },
    { name := "unit/runtime/type-key-nan"
      run := do
        expectErr "runtime/type-key-nan"
          (runDictSetGetOptRefDirect (dictSetGetOptRefInstr true false)
            (#[(.cell signedNibbleRoot4), .int .nan, intV 4, .cell valueD]))
          .rangeChk
    }
  ]
  oracle := #[
    -- [B1][B2][B7]
    mkCase "oracle/underflow/empty" rawSetGetOptRef #[],
    -- [B1][B2]
    mkCase "oracle/underflow/one" rawSetGetOptRefInt underflowOneStack,
    -- [B1][B2]
    mkCase "oracle/underflow/two" rawSetGetOptRef underflowTwoStack,
    -- [B3][B7]
    mkCase "oracle/n-negative" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 0 (-1) (.cell valueD)),
    -- [B3][B7]
    mkCase "oracle/n-overflow" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 0 1024 (.cell valueD)),
    -- [B3][B7]
    mkCase "oracle/n-nan" rawSetGetOptRefUInt
      (#[.cell unsignedNibbleRoot4, intV 0, .int .nan, .cell valueD]),
    -- [B4][B7]
    mkCase "oracle/type-dict" rawSetGetOptRefInt (mkIntSetStack (.tuple #[]) 3 4 (.cell valueD)),
    -- [B5][B6]
    mkCase "oracle/type-key-int" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 .null),
    -- [B5][B6]
    mkCase "oracle/type-key-slice" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 3 4 .null),
    -- [B7][B8]
    mkCase "oracle/type-new-value" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 3 4 (.int (.num 7))),
    -- [B6][B10]
    mkCase "oracle/int-nan" rawSetGetOptRefInt
      (#[.cell signedNibbleRoot4, .int .nan, intV 4, .cell valueD]),
    -- [B6][B9]
    mkCase "oracle/int-signed-out-of-range-high" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 8 4 (.cell valueD)),
    -- [B6][B9]
    mkCase "oracle/int-signed-out-of-range-low" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-9) 4 (.cell valueD)),
    -- [B6][B9]
    mkCase "oracle/int-unsigned-out-of-range-low" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) (-1) 4 (.cell valueD)),
    -- [B6][B9]
    mkCase "oracle/int-unsigned-out-of-range-high" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 16 4 (.cell valueD)),
    -- [B8][B9]
    mkCase "oracle/int-signed-hit" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) (-3) 4 (.cell valueD)),
    -- [B8][B9]
    mkCase "oracle/int-signed-miss" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 6 4 (.cell valueD)),
    -- [B8][B9]
    mkCase "oracle/int-unsigned-hit" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueD)),
    -- [B8][B9]
    mkCase "oracle/int-unsigned-miss" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 11 4 (.cell valueD)),
    -- [B8][B10]
    mkCase "oracle/int-delete-signed-hit" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 7 4 .null),
    -- [B8][B10]
    mkCase "oracle/int-delete-signed-miss" rawSetGetOptRefInt (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null),
    -- [B8][B10]
    mkCase "oracle/int-delete-unsigned-hit" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 9 4 .null),
    -- [B8][B10]
    mkCase "oracle/int-delete-unsigned-miss" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 1 4 .null),
    -- [B8][B9]
    mkCase "oracle/slice-hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueD)),
    -- [B8][B9]
    mkCase "oracle/slice-miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 1 4) 4 (.cell valueD)),
    -- [B8][B10]
    mkCase "oracle/slice-delete-hit" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 7 4) 4 .null),
    -- [B8][B10]
    mkCase "oracle/slice-delete-miss" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 1 4) 4 .null),
    -- [B5][B7]
    mkCase "oracle/slice-underflow" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 8 (.cell valueD)),
    -- [B9][B11]
    mkCase "oracle/dict-err-bad-old-set-signed" rawSetGetOptRefInt (mkIntSetStack (.cell signedBadValueRoot4) (-3) 4 (.cell valueD)),
    -- [B10][B11]
    mkCase "oracle/dict-err-bad-old-delete-signed" rawSetGetOptRefInt (mkIntSetStack (.cell signedBadValueRoot4) (-3) 4 .null),
    -- [B9][B11]
    mkCase "oracle/dict-err-bad-old-set-unsigned" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 (.cell valueD)),
    -- [B10][B11]
    mkCase "oracle/dict-err-bad-old-delete-slice" rawSetGetOptRef (mkSliceSetStack (.cell sliceBadValueRoot4) (natToBits 2 4) 4 .null),
    -- [B11]
    mkCase "oracle/dict-err-malformed-root" rawSetGetOptRefInt (mkIntSetStack (.cell malformedDict) 3 4 (.cell valueD)),
    -- [B11]
    mkCase "oracle/dicterr-unsigned-delete-malformed-root" rawSetGetOptRef (mkSliceSetStack (.cell malformedDict) (natToBits 7 4) 4 .null),
    -- [B14]
    mkCase "oracle/gas/exact-delete-miss" (gasCode setGetOptRefGas rawSetGetOptRefInt)
      (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null) setGetOptRefGasExact,
    -- [B14]
    mkCase "oracle/gas/exact-minus-one-delete-miss" (gasCode (setGetOptRefGas - 1) rawSetGetOptRefInt)
      (mkIntSetStack (.cell signedNibbleRoot4) 6 4 .null) setGetOptRefGasExactMinusOne,
    -- [B11][B13]
    mkCase "oracle/decode-compat/getoptref" rawSetGetOptRef (mkSliceSetStack (.cell sliceNibbleRoot4) (natToBits 2 4) 4 (.cell valueD)),
    -- [B12][B13]
    mkCase "oracle/gas/exact-delete-signed-zero-width" (gasCode setGetOptRefGas rawSetGetOptRefInt)
      (mkIntSetStack (.cell signedNibbleRoot0) 0 0 (.cell valueD)) setGetOptRefGasExact,
    -- [B9][B10]
    mkCase "oracle/n0-unsigned-zero-width" rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot0) 0 0 (.cell valueD)),
    -- [B13]
    mkCase "oracle/fuzz/safe-random"
      rawSetGetOptRefUInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueD))
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictSetGetOptRefFuzz
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTSETGETOPTREF
