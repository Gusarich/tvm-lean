import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUSETGETOPTREF

/-!
INSTRUCTION: DICTUSETGETOPTREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictExt` must route `.dictExt (.setGetOptRef true true)` to this opcode branch.
   - Any other opcode goes through to `next` via `runHandlerDirectWithNext`.

2. [B2] Stack underflow (`checkUnderflow 4`).
   - Any missing of (`dict`, `i`, `n`, `newValue`) enters `.stkUnd`.
   - One and two element cases are separate arity-reduction states.

3. [B3] `n` bounds (`popNatUpTo 1023`).
   - `n = .nan`, negative, and `n > 1023` become `.rangeChk`.
   - `n = 0` is valid.

4. [B4] Dictionary argument (`popMaybeCell`).
   - `.null` means empty dictionary.
   - Non-cell/non-null values become `.typeChk`.

5. [B5] Integer key parsing (`intKey = true`, `unsigned = true`).
   - `popInt` is used.
   - `.nan` key is `.rangeChk`.
   - Key is accepted only if `dictKeyBits?` for requested unsigned width succeeds.
   - For unsigned keys: negative or >= `2^n` becomes `.cellUnd`.

6. [B6] Mutation-mode selection by `newValue`.
   - `newValue = .null` => delete branch.
   - `newValue = cell` => set/lookup branch.
   - Type error in `newValue` is already blocked by `popMaybeCell`.

7. [B7] Set branch behavior.
   - Dictionary miss => push new root and `.null`.
   - Dictionary hit => push new root and previous value as a direct ref.
   - Malformed old value shape becomes `.dictErr`.

8. [B8] Delete branch behavior.
   - Dictionary miss => push new root and `.null`.
   - Dictionary hit => push new root and removed value as a direct ref.
   - Malformed old value shape becomes `.dictErr`.

9. [B9] Structural errors.
   - Malformed root/value internal dictionaries propagate `.dictErr`.

10. [B10] Assembler behavior.
    - `.dictExt (.setGetOptRef true true)` has no assembler encoding.
    - `assembleCp0` must produce `.invOpcode`.

11. [B11] Decoder behavior.
    - `0xF46F` decodes to `.dictExt (.setGetOptRef true true)`.
    - `0xF46E` and `0xF46D` are other set-getoptref variants.
    - `0xF46C` and `0xF470` are invalid and should decode as `.invOpcode`.

12. [B12] Gas behavior.
    - No explicit per-branch variable surcharge in this opcode decoding path.
    - Base-cost exact and exact-minus-one limits should be covered on stable branches.

TOTAL BRANCHES: 12

Assembler/gas notes:
- Assembler rejection is represented as `[B10]`; no dedicated parameter encoding checks happen here.
- Gas branch coverage uses exact and exact-minus-one at the instruction level.
-/

private def suiteId : InstrId :=
  { name := "DICTUSETGETOPTREF" }

private def dictUSetGetOptRefInstr : Instr :=
  .dictExt (.setGetOptRef true true)

private def rawSetGetOptRef : Cell :=
  Cell.mkOrdinary (natToBits 0xF46F 16) #[]

private def rawSetGetOptRefInt : Cell :=
  Cell.mkOrdinary (natToBits 0xF46E 16) #[]

private def rawSetGetOptRefSlice : Cell :=
  Cell.mkOrdinary (natToBits 0xF46D 16) #[]

private def rawPfxSet : Cell :=
  Cell.mkOrdinary (natToBits 0xF470 16) #[]

private def rawBelow : Cell :=
  Cell.mkOrdinary (natToBits 0xF46C 16) #[]

private def rawTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def dispatchSentinel : Int := 771_001

private def mkGasPrefix (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok c => c
  | .error e => panic! s!"failed to assemble gas prefix for DICTUSETGETOPTREF: {reprStr e}"

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

private def mkKeyBits (label : String) (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid key ({idx}, n={n}, unsigned={unsigned})"

private def mkDictSetRefRoot!
    (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits := mkKeyBits label k n unsigned
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some r, _old, _created, _loaded) => root := r
      | .ok (none, _old, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root during dictionary construction"
      | .error e => panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def mkSetRoot (label : String) (root : Option Cell) (keyBits : BitString) (value : Cell) : Cell :=
  let result := dictLookupSetRefWithCells root keyBits value .set
  match result with
  | .ok (_, newRoot, _ok, _created, _loaded) =>
      match newRoot with
      | some c => c
      | none => panic! s!"{label}: expected non-empty root on set"
  | .error e => panic! s!"{label}: expected set success, got {reprStr e}"

private def mkDeleteRoot (label : String) (root : Option Cell) (keyBits : BitString) : Cell :=
  let result := dictDeleteWithCells root keyBits
  match result with
  | .ok (_, newRoot, _created, _loaded) =>
      match newRoot with
      | some c => c
      | none => panic! s!"{label}: expected non-empty root on delete"
  | .error e => panic! s!"{label}: expected delete success, got {reprStr e}"

private def storedRefA : Cell :=
  Cell.mkOrdinary (natToBits 0xA4 8) #[]

private def storedRefB : Cell :=
  Cell.mkOrdinary (natToBits 0xB7 8) #[]

private def storedRefC : Cell :=
  Cell.mkOrdinary (natToBits 0xC9 8) #[]

private def valueA : Cell :=
  Cell.mkOrdinary #[] #[storedRefA]

private def valueB : Cell :=
  Cell.mkOrdinary #[] #[storedRefB]

private def valueC : Cell :=
  Cell.mkOrdinary #[] #[storedRefC]

private def badValueBitsOnly : Cell :=
  Cell.mkOrdinary (natToBits 0xF0 8) #[]

private def badValueBitsAndRefs : Cell :=
  Cell.mkOrdinary #[] #[storedRefA, storedRefB]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0xF 4) #[]

private def unsignedNibbleRoot4 : Cell :=
  mkDictSetRefRoot! "unsignedNibbleRoot4" 4 true #[(5, valueA), (9, valueB)]

private def unsignedNibbleRoot0 : Cell :=
  mkDictSetRefRoot! "unsignedNibbleRoot0" 0 true #[(0, valueA)]

private def unsignedBadValueRoot4 : Cell :=
  mkDictSetRefRoot! "unsignedBadValueRoot4" 4 true #[(5, badValueBitsOnly)]

private def expectedUnsignedSetHit : Cell :=
  mkSetRoot "expectedUnsignedSetHit" (some unsignedNibbleRoot4) (mkKeyBits "set-hit-key5" 5 4 true) valueC

private def expectedUnsignedSetMiss : Cell :=
  mkSetRoot "expectedUnsignedSetMiss" (some unsignedNibbleRoot4) (mkKeyBits "set-miss-key6" 6 4 true) valueC

private def expectedUnsignedSetZero : Cell :=
  mkSetRoot "expectedUnsignedSetZero" (some unsignedNibbleRoot0) (mkKeyBits "set-zero-key0" 0 0 true) valueC

private def expectedUnsignedDeleteHit : Cell :=
  mkDeleteRoot "expectedUnsignedDeleteHit" (some unsignedNibbleRoot4) (mkKeyBits "delete-hit-key5" 5 4 true)

private def expectedUnsignedDeleteMiss : Cell :=
  mkDeleteRoot "expectedUnsignedDeleteMiss" (some unsignedNibbleRoot4) (mkKeyBits "delete-miss-key6" 6 4 true)

private def mkIntSetStack (dict : Value) (key : Int) (n : Int) (newValue : Value) : Array Value :=
  #[newValue, intV key, dict, intV n]

private def expectedUnsignedSetBadOld : Cell :=
  mkSetRoot "expectedUnsignedSetBadOld" (some unsignedBadValueRoot4) (mkKeyBits "set-bad-old-key5" 5 4 true) valueC

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

private def runDictUSetGetOptRefFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (.int (.num dispatchSentinel))) stack

private def runDictUSetGetOptRefDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell <| Cell.mkOrdinary (natToBits opcode 16) #[]) with
  | .ok (i, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def setGetOptRefGas : Int :=
  computeExactGasBudget dictUSetGetOptRefInstr

private def setGetOptRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact setGetOptRefGas

private def setGetOptRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne setGetOptRefGas

private def genDictUSetGetOptRefFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 34
  let (case0, rng2) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase "fuzz/unsigned/set-hit" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)), rng1)
    else if shape = 1 then
      (mkCase "fuzz/unsigned/set-miss" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 (.cell valueC)), rng1)
    else if shape = 2 then
      (mkCase "fuzz/unsigned/delete-hit" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 .null), rng1)
    else if shape = 3 then
      (mkCase "fuzz/unsigned/delete-miss" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 .null), rng1)
    else if shape = 4 then
      (mkCase "fuzz/zero-width-set-hit" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot0) 0 0 (.cell valueC)), rng1)
    else if shape = 5 then
      (mkCase "fuzz/zero-width-delete-hit" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot0) 0 0 .null), rng1)
    else if shape = 6 then
      (mkCase "fuzz/key-nan" rawSetGetOptRef
        #[.cell valueC, .int .nan, .cell unsignedNibbleRoot4, intV 4], rng1)
    else if shape = 7 then
      (mkCase "fuzz/key-out-of-range-low" rawSetGetOptRef
        (mkIntSetStack (.cell unsignedNibbleRoot4) (-1) 4 (.cell valueC)), rng1)
    else if shape = 8 then
      (mkCase "fuzz/key-out-of-range-high" rawSetGetOptRef
        (mkIntSetStack (.cell unsignedNibbleRoot4) 16 4 (.cell valueC)), rng1)
    else if shape = 9 then
      (mkCase "fuzz/n-negative" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 (-1) (.cell valueC)), rng1)
    else if shape = 10 then
      (mkCase "fuzz/n-over" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 1024 (.cell valueC)), rng1)
    else if shape = 11 then
      (mkCase "fuzz/n-nan" rawSetGetOptRef
        #[.cell valueC, intV 5, .cell unsignedNibbleRoot4, .int .nan], rng1)
    else if shape = 12 then
      (mkCase "fuzz/type-dict" rawSetGetOptRef (mkIntSetStack (.tuple #[]) 5 4 (.cell valueC)), rng1)
    else if shape = 13 then
      (mkCase "fuzz/type-key" rawSetGetOptRef
        #[.cell valueC, .cell storedRefA, .cell unsignedNibbleRoot4, intV 4], rng1)
    else if shape = 14 then
      (mkCase "fuzz/type-new-value" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.int (.num 7))), rng1)
    else if shape = 15 then
      (mkCase "fuzz/dicterr/bad-old-set" rawSetGetOptRef (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 (.cell valueC)), rng1)
    else if shape = 16 then
      (mkCase "fuzz/dicterr/bad-old-delete" rawSetGetOptRef (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 .null), rng1)
    else if shape = 17 then
      (mkCase "fuzz/dicterr/malformed-root-set" rawSetGetOptRef (mkIntSetStack (.cell malformedDict) 5 4 (.cell valueC)), rng1)
    else if shape = 18 then
      (mkCase "fuzz/dicterr/malformed-root-delete" rawSetGetOptRef (mkIntSetStack (.cell malformedDict) 5 4 .null), rng1)
    else if shape = 19 then
      (mkCase "fuzz/gas/exact-delete-miss" (gasCode setGetOptRefGas rawSetGetOptRef)
        (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 .null) setGetOptRefGasExact, rng1)
    else if shape = 20 then
      (mkCase "fuzz/gas/exact-minus-one-delete-miss" (gasCode (setGetOptRefGas - 1) rawSetGetOptRef)
        (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 .null) setGetOptRefGasExactMinusOne, rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/exact-set-hit" (gasCode setGetOptRefGas rawSetGetOptRef)
        (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)) setGetOptRefGasExact, rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/exact-minus-one-set-hit" (gasCode (setGetOptRefGas - 1) rawSetGetOptRef)
        (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)) setGetOptRefGasExactMinusOne, rng1)
    else if shape = 23 then
      (mkCase "fuzz/decode/compat-int" rawSetGetOptRefInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)), rng1)
    else if shape = 24 then
      (mkCase "fuzz/decode/compat-slice" rawSetGetOptRefSlice (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)), rng1)
    else if shape = 25 then
      (mkCase "fuzz/decode/compat-pfx" rawPfxSet (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)), rng1)
    else if shape = 26 then
      (mkCase "fuzz/key-boundary-low" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 0 4 (.cell valueC)), rng1)
    else if shape = 27 then
      (mkCase "fuzz/key-boundary-high" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 15 4 (.cell valueC)), rng1)
    else if shape = 28 then
      (mkCase "fuzz/type-key-bits-only" rawSetGetOptRef
        #[.cell badValueBitsAndRefs, .slice (mkSliceFromBits (natToBits 5 4)), .cell unsignedNibbleRoot4, intV 4], rng1)
    else if shape = 29 then
      (mkCase "fuzz/underflow-empty" rawSetGetOptRef #[], rng1)
    else if shape = 30 then
      (mkCase "fuzz/underflow-one" rawSetGetOptRef #[(.int (.num 4)),], rng1)
    else if shape = 31 then
      (mkCase "fuzz/underflow-two" rawSetGetOptRef #[(.int (.num 4)), (.int (.num 5)),], rng1)
    else if shape = 32 then
      (mkCase "fuzz/underflow-three" rawSetGetOptRef #[(.cell unsignedNibbleRoot4), (.int (.num 4)),], rng1)
    else if shape = 33 then
      (mkCase "fuzz/decode/stream-safe" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)), rng1)
    else
      (mkCase "fuzz/decode/truncated8" rawTruncated8 #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runDictUSetGetOptRefFallback .add #[])
          #[.int (.num dispatchSentinel)]
    },
    { name := "unit/decode/raw"
      run := do
        let _ ← expectDecodeStep "decode/0xf46f" (mkSliceFromBits (natToBits 0xF46F 16))
          dictUSetGetOptRefInstr 16
        pure ()
    },
    { name := "unit/decode/adjacent-below"
      run := do
        let _ ← expectDecodeStep "decode/0xf46e" (mkSliceFromBits (natToBits 0xF46E 16))
          (.dictExt (.setGetOptRef true false)) 16
        pure ()
    },
    { name := "unit/decode/adjacent-below2"
      run := do
        let _ ← expectDecodeStep "decode/0xf46d" (mkSliceFromBits (natToBits 0xF46D 16))
          (.dictExt (.setGetOptRef false false)) 16
        pure ()
    },
    { name := "unit/decode/adjacent-above"
      run := do
        let _ ← expectDecodeStep "decode/0xf470" (mkSliceFromBits (natToBits 0xF470 16))
          (.dictExt (.pfxSet .set)) 16
        pure ()
    },
    { name := "unit/decode/stream"
      run := do
        let stream : Slice :=
          Slice.ofCell <|
          Cell.mkOrdinary
              (rawSetGetOptRefSlice.bits ++ rawSetGetOptRefInt.bits ++ rawSetGetOptRef.bits)
              (rawSetGetOptRefSlice.refs ++ rawSetGetOptRefInt.refs ++ rawSetGetOptRef.refs)
        let s1 ← expectDecodeStep "decode/stream/f46d" stream (.dictExt (.setGetOptRef false false)) 16
        let s2 ← expectDecodeStep "decode/stream/f46e" s1 (.dictExt (.setGetOptRef true false)) 16
        let _ ← expectDecodeStep "decode/stream/f46f" s2 (.dictExt (.setGetOptRef true true)) 16
        pure ()
    },
    { name := "unit/decode/adjacent-below-invopcode"
      run := do
        expectDecodeInvOpcode "decode/0xf46c" 0xF46C
    },
    { name := "unit/decode/truncated8"
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated8 expected failure")
    },
    { name := "unit/assemble/invopcode"
      run := do
        assembleInvOpcode "assemble" dictUSetGetOptRefInstr
    },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "runtime/underflow"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr #[])
          .stkUnd
    },
    { name := "unit/runtime/unsigned-hit"
      run := do
        expectOkStack "runtime/unsigned-hit"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)))
          #[.cell expectedUnsignedSetHit, .cell valueA]
    },
    { name := "unit/runtime/unsigned-miss"
      run := do
        expectOkStack "runtime/unsigned-miss"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 (.cell valueC))
          )
          #[.cell expectedUnsignedSetMiss, .null]
    },
    { name := "unit/runtime/unsigned-delete-hit"
      run := do
        expectOkStack "runtime/unsigned-delete-hit"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 .null))
          #[.cell expectedUnsignedDeleteHit, .cell valueA]
    },
    { name := "unit/runtime/unsigned-delete-miss"
      run := do
        expectOkStack "runtime/unsigned-delete-miss"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 .null))
          #[.cell expectedUnsignedDeleteMiss, .null]
    },
    { name := "unit/runtime/zero-width-hit"
      run := do
        expectOkStack "runtime/zero-width-hit"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot0) 0 0 (.cell valueC))
          )
          #[.cell expectedUnsignedSetZero, .cell valueA]
    },
    { name := "unit/runtime/key-out-of-range-negative"
      run := do
        expectErr "runtime/key-out-of-range-negative"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) (-1) 4 (.cell valueC)))
          .rangeChk
    },
    { name := "unit/runtime/key-out-of-range-high"
      run := do
        expectErr "runtime/key-out-of-range-high"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 16 4 (.cell valueC)))
          .rangeChk
    },
    { name := "unit/runtime/key-nan"
      run := do
        expectErr "runtime/key-nan"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr #[.cell valueC, .int .nan, .cell unsignedNibbleRoot4, intV 4])
          .rangeChk
    },
    { name := "unit/runtime/n-negative"
      run := do
        expectErr "runtime/n-negative"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 5 (-1) (.cell valueC)))
          .rangeChk
    },
    { name := "unit/runtime/n-over"
      run := do
        expectErr "runtime/n-over"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 5 1024 (.cell valueC)))
          .rangeChk
    },
    { name := "unit/runtime/n-nan"
      run := do
        expectErr "runtime/n-nan"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr #[.cell valueC, intV 5, .cell unsignedNibbleRoot4, .int .nan])
          .rangeChk
    },
    { name := "unit/runtime/type-dict"
      run := do
        expectErr "runtime/type-dict"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.tuple #[]) 5 4 (.cell valueC)))
          .typeChk
    },
    { name := "unit/runtime/type-key"
      run := do
        expectErr "runtime/type-key"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr #[.cell valueC, .cell storedRefA, .cell unsignedNibbleRoot4, intV 4])
          .typeChk
    },
    { name := "unit/runtime/type-new-value"
      run := do
        expectErr "runtime/type-new-value"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.int (.num 7))))
          .typeChk
    },
    { name := "unit/runtime/dict-err-old-set"
      run := do
        expectOkStack "runtime/dict-err-old-set"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 (.cell valueC)))
          #[.cell expectedUnsignedSetBadOld, .cell badValueBitsOnly]
    },
    { name := "unit/runtime/dict-err-old-delete"
      run := do
        expectOkStack "runtime/dict-err-old-delete"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 .null))
          #[.null, .cell badValueBitsOnly]
    },
    { name := "unit/runtime/dict-err-malformed-root"
      run := do
        expectErr "runtime/dict-err-malformed-root"
          (runDictUSetGetOptRefDirect dictUSetGetOptRefInstr (mkIntSetStack (.cell malformedDict) 5 4 (.cell valueC)))
          .cellUnd
    }
  ]
  oracle := #[
    -- [B2][B3][B4][B6]
    mkCase "oracle/underflow/empty" rawSetGetOptRef #[],
    -- [B2][B3][B4][B6]
    mkCase "oracle/underflow/one" rawSetGetOptRef #[(.int (.num 4))],
    -- [B2]
    mkCase "oracle/underflow/two" rawSetGetOptRef #[(.int (.num 4)), (.int (.num 5))],
    -- [B2][B3][B6]
    mkCase "oracle/underflow/three" rawSetGetOptRef #[(.cell unsignedNibbleRoot4), (.int (.num 4))],
    -- [B3]
    mkCase "oracle/err/n-negative" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 (-1) (.cell valueC)),
    -- [B3]
    mkCase "oracle/err/n-over" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 1024 (.cell valueC)),
    -- [B3]
    mkCase "oracle/err/n-nan" rawSetGetOptRef #[.cell valueC, intV 5, .cell unsignedNibbleRoot4, .int .nan],
    -- [B4]
    mkCase "oracle/err/type-dict" rawSetGetOptRef (mkIntSetStack (.tuple #[]) 5 4 (.cell valueC)),
    -- [B5]
    mkCase "oracle/err/type-key" rawSetGetOptRef #[.cell valueC, .cell storedRefA, .cell unsignedNibbleRoot4, intV 4],
    -- [B5]
    mkCase "oracle/err/type-new-value" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.int (.num 7))),
    -- [B5]
    mkCase "oracle/err/key-nan" rawSetGetOptRef #[.cell valueC, .int .nan, .cell unsignedNibbleRoot4, intV 4],
    -- [B5]
    mkCase "oracle/err/key-out-of-range-low" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) (-1) 4 (.cell valueC)),
    -- [B5]
    mkCase "oracle/err/key-out-of-range-high" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 16 4 (.cell valueC)),
    -- [B7][B8]
    mkCase "oracle/set-hit" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)),
    -- [B7][B8]
    mkCase "oracle/set-miss" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 (.cell valueC)),
    -- [B7][B9]
    mkCase "oracle/delete-hit" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 .null),
    -- [B7][B9]
    mkCase "oracle/delete-miss" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 .null),
    -- [B8][B10]
    mkCase "oracle/set-hit-alt" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 15 4 (.cell valueC)),
    -- [B9]
    mkCase "oracle/dict-err-bad-old-set" rawSetGetOptRef (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 (.cell valueC)),
    -- [B9]
    mkCase "oracle/dict-err-bad-old-delete" rawSetGetOptRef (mkIntSetStack (.cell unsignedBadValueRoot4) 5 4 .null),
    -- [B10]
    mkCase "oracle/dict-err-malformed-root" rawSetGetOptRef (mkIntSetStack (.cell malformedDict) 5 4 (.cell valueC)),
    -- [B10]
    mkCase "oracle/dict-err-malformed-root-delete" rawSetGetOptRef (mkIntSetStack (.cell malformedDict) 5 4 .null),
    -- [B11]
    mkCase "oracle/gas/exact-delete-miss" (gasCode setGetOptRefGas rawSetGetOptRef)
      (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 .null) setGetOptRefGasExact,
    -- [B11]
    mkCase "oracle/gas/exact-minus-one-delete-miss" (gasCode (setGetOptRefGas - 1) rawSetGetOptRef)
      (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 .null) setGetOptRefGasExactMinusOne,
    -- [B11]
    mkCase "oracle/gas/exact-set-miss" (gasCode setGetOptRefGas rawSetGetOptRef)
      (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 (.cell valueC)) setGetOptRefGasExact,
    -- [B11]
    mkCase "oracle/gas/exact-minus-one-set-miss" (gasCode (setGetOptRefGas - 1) rawSetGetOptRef)
      (mkIntSetStack (.cell unsignedNibbleRoot4) 6 4 (.cell valueC)) setGetOptRefGasExactMinusOne,
    -- [B12]
    mkCase "oracle/decode/compat-int" rawSetGetOptRefInt (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)),
    -- [B12]
    mkCase "oracle/decode/compat-slice" rawSetGetOptRefSlice (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)),
    -- [B12]
    mkCase "oracle/decode/compat-pfx" rawPfxSet (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC)),
    -- [B10]
    mkCase "oracle/assemble/invopcode" rawSetGetOptRef (mkIntSetStack (.cell unsignedNibbleRoot4) 5 4 (.cell valueC))
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictUSetGetOptRefFuzz
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSETGETOPTREF
