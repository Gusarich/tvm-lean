import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTSETGETREF

/--!
INSTRUCTION: DICTSETGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `.dictExt` instructions are handled by `execInstrDictExt`.
   - Non-matching instructions must pass through via `next`.

2. [B2] Arity and `n` validation.
   - `checkUnderflow 4` requires `[newValueRef, keySlice, dict, n]`.
   - `n` is restricted by `popNatUpTo 1023`.
   - Negative / NaN / `>1023` produce `.rangeChk`.

3. [B3] Slice-key validation.
   - `key` must be a slice.
   - If `key` has fewer than `n` bits then `.cellUnd` is raised for non-empty miss branches
     when executing `.set` mode.

4. [B4] Typing branch.
   - `newValueRef` must be `.cell`; `.typeChk` on non-cell values.
   - `dict` must be `.null` or `.cell` (`.typeChk` otherwise).

5. [B5] Runtime hit/miss outcome.
   - On miss: `newRoot, 0`.
   - On hit: `newRoot, oldValueAsCell, -1`.

6. [B7] By-ref shape checks.
   - On hit, old value slice must be exactly one reference with no remaining bits.
   - Violations return `.dictErr`.

7. [B8] Dictionary integrity branch.
   - Malformed dictionary roots return `.dictErr`.

8. [B9] Assembler/decoder behavior.
   - `assembleCp0` encodes this opcode (16-bit), matching the `0xF41A..0xF41F` decoder family.
   - `0xF41A..0xF41F` decode as `.dictExt (.mutGet ... .set)` variants.
   - `0xF419`, `0xF420`, and truncated `0xF4` must decode as `.invOpcode`.

9. [B10] Gas accounting.
   - Base budget is `computeExactGasBudget instr`.
   - `.set` mutations charge `created * cellCreateGasPrice`.
   - Exact and exact-minus-one cases are tested.

TOTAL BRANCHES: 9
-/

private def suiteId : InstrId :=
  { name := "DICTSETGETREF" }

private def instr : Instr :=
  .dictExt (.mutGet false false true .set)

private def dispatchSentinel : Int :=
  909

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawF41A : Cell := raw16 0xF41A
private def rawF41B : Cell := raw16 0xF41B
private def rawF41C : Cell := raw16 0xF41C
private def rawF41D : Cell := raw16 0xF41D
private def rawF41E : Cell := raw16 0xF41E
private def rawF41F : Cell := raw16 0xF41F
private def rawF419 : Cell := raw16 0xF419
private def rawF420 : Cell := raw16 0xF420
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def valueD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]
private def valueE : Cell := Cell.mkOrdinary (natToBits 0xE5 8) #[]
private def valueF : Cell := Cell.mkOrdinary (natToBits 0xF6 8) #[]
private def valueG : Cell := Cell.mkOrdinary (natToBits 0x77 8) #[]
private def valueASlice : Slice := Slice.ofCell valueA

private def key0 : BitString := #[]
private def key3 : BitString := natToBits 0x1 3
private def key4A : BitString := natToBits 0xA 4
private def key4B : BitString := natToBits 0xB 4
private def key4C : BitString := natToBits 0xC 4
private def key4D : BitString := natToBits 0xD 4
private def key4E : BitString := natToBits 0xE 4
private def key4F : BitString := natToBits 0xF 4
private def key1023 : BitString := Array.replicate 1023 true
private def key8A : BitString := natToBits 0xA5 8

private def slice3 : Slice := mkSliceFromBits key3
private def slice4A : Slice := mkSliceFromBits key4A
private def slice4B : Slice := mkSliceFromBits key4B
private def slice4C : Slice := mkSliceFromBits key4C
private def slice4D : Slice := mkSliceFromBits key4D
private def slice4E : Slice := mkSliceFromBits key4E
private def slice4F : Slice := mkSliceFromBits key4F
private def slice0 : Slice := mkSliceFromBits key0
private def slice1023 : Slice := mkSliceFromBits key1023
private def slice8A : Slice := mkSliceFromBits key8A

private def malformedValueBits : Slice := mkSliceFromBits (natToBits 1 1)
private def malformedValueTwoRefs : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[valueA, valueB])
private def malformedValueNoRef : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[])

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkDictSetRefBitsRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetRefWithCells root k v .set with
      | .ok (some nextRoot, _ok, _created, _loaded) =>
          root := nextRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: no entries to build dict"

private def mkDictSetSliceBitsRoot! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetSliceWithCells root k v .set with
      | .ok (some nextRoot, _ok, _created, _loaded) =>
          root := nextRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: no entries to build dict"

private def dict4Single : Cell :=
  mkDictSetRefBitsRoot! "DICTSETGETREF/dict4/single" #[(key4A, valueA)]

private def dict4Pair : Cell :=
  mkDictSetRefBitsRoot! "DICTSETGETREF/dict4/pair" #[(key4A, valueA), (key4B, valueB)]

private def dict4Triple : Cell :=
  mkDictSetRefBitsRoot! "DICTSETGETREF/dict4/triple" #[(key4A, valueA), (key4B, valueB), (key4C, valueC)]

private def dict4NoMatch : Cell :=
  mkDictSetRefBitsRoot! "DICTSETGETREF/dict4/nomatch" #[(key4E, valueE)]

private def dict0Single : Cell :=
  mkDictSetRefBitsRoot! "DICTSETGETREF/dict0/single" #[(key0, valueA)]

private def dict1023Single : Cell :=
  mkDictSetRefBitsRoot! "DICTSETGETREF/dict1023/single" #[(key1023, valueE)]

private def dictBadBits : Cell :=
  mkDictSetSliceBitsRoot! "DICTSETGETREF/dict/bad/bits" #[(key4A, malformedValueBits)]

private def dictBadTwoRefs : Cell :=
  mkDictSetSliceBitsRoot! "DICTSETGETREF/dict/bad/two-refs" #[(key4A, malformedValueTwoRefs)]

private def dictBadNoRef : Cell :=
  mkDictSetSliceBitsRoot! "DICTSETGETREF/dict/bad/no-ref" #[(key4A, malformedValueNoRef)]

private def expectSetRoot
    (label : String)
    (root : Option Cell)
    (key : BitString)
    (newValue : Cell) : Cell :=
  match dictLookupSetRefWithCells root key newValue .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected new root, got none"
  | .error e =>
      panic! s!"{label}: dictLookupSetRefWithCells failed ({reprStr e})"

private def expectSetCreated
    (label : String)
    (root : Option Cell)
    (key : BitString)
    (newValue : Cell) : Nat :=
  match dictLookupSetRefWithCells root key newValue .set with
  | .ok (_, _root, _ok, created, _loaded) => created
  | .error e =>
      panic! s!"{label}: dictLookupSetRefWithCells failed ({reprStr e})"

private def expectedSetReplace4A : Cell :=
  expectSetRoot "DICTSETGETREF/expected/replace/4A" (some dict4Single) key4A valueD

private def expectedSetReplace4B : Cell :=
  expectSetRoot "DICTSETGETREF/expected/replace/4B" (some dict4Pair) key4B valueE

private def expectedSetInsert4D : Cell :=
  expectSetRoot "DICTSETGETREF/expected/insert/4D" (some dict4Triple) key4D valueA

private def expectedSetInsertNull : Cell :=
  expectSetRoot "DICTSETGETREF/expected/insert/null" none key4D valueB

private def expectedSetNull0 : Cell :=
  expectSetRoot "DICTSETGETREF/expected/insert/null/0" none key0 valueC

private def expectedSetInsert1023 : Cell :=
  expectSetRoot "DICTSETGETREF/expected/insert/1023" none key1023 valueF

private def createdSetReplace4A : Nat :=
  expectSetCreated "DICTSETGETREF/created/replace/4A" (some dict4Single) key4A valueD

private def createdSetReplace4B : Nat :=
  expectSetCreated "DICTSETGETREF/created/replace/4B" (some dict4Pair) key4B valueE

private def createdSetInsert4D : Nat :=
  expectSetCreated "DICTSETGETREF/created/insert/4D" (some dict4Triple) key4D valueA

private def createdSetInsertNull : Nat :=
  expectSetCreated "DICTSETGETREF/created/insert/null" none key4D valueB

private def createdSetNull0 : Nat :=
  expectSetCreated "DICTSETGETREF/created/insert/null/0" none key0 valueC

private def createdSetInsert1023 : Nat :=
  expectSetCreated "DICTSETGETREF/created/insert/1023" none key1023 valueF

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  if baseGas > 0 then baseGas - 1 else 0

private def exactGasReplace4A : Int :=
  baseGas + Int.ofNat createdSetReplace4A * cellCreateGasPrice

private def exactGasReplace4B : Int :=
  baseGas + Int.ofNat createdSetReplace4B * cellCreateGasPrice

private def exactGasInsert4D : Int :=
  baseGas + Int.ofNat createdSetInsert4D * cellCreateGasPrice

private def exactGasInsert4Null : Int :=
  baseGas + Int.ofNat createdSetInsertNull * cellCreateGasPrice

private def exactGasNull0 : Int :=
  baseGas + Int.ofNat createdSetNull0 * cellCreateGasPrice

private def exactGasInsert1023 : Int :=
  baseGas + Int.ofNat createdSetInsert1023 * cellCreateGasPrice

private def exactGasReplace4AMinusOne : Int :=
  if exactGasReplace4A > 0 then exactGasReplace4A - 1 else 0

private def exactGasInsert4DMinusOne : Int :=
  if exactGasInsert4D > 0 then exactGasInsert4D - 1 else 0

private def exactGasInsert4NullMinusOne : Int :=
  if exactGasInsert4Null > 0 then exactGasInsert4Null - 1 else 0

private def exactGasNull0MinusOne : Int :=
  if exactGasNull0 > 0 then exactGasNull0 - 1 else 0

private def exactGasInsert1023MinusOne : Int :=
  if exactGasInsert1023 > 0 then exactGasInsert1023 - 1 else 0

private def gasBaseExact : OracleGasLimits :=
  oracleGasLimitsExact baseGas

private def gasBaseExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne baseGasMinusOne

private def gasReplace4A : OracleGasLimits :=
  { gasLimit := exactGasReplace4A, gasMax := exactGasReplace4A, gasCredit := 0 }

private def gasReplace4AMinusOne : OracleGasLimits :=
  { gasLimit := exactGasReplace4AMinusOne, gasMax := exactGasReplace4AMinusOne, gasCredit := 0 }

private def gasInsert4D : OracleGasLimits :=
  { gasLimit := exactGasInsert4D, gasMax := exactGasInsert4D, gasCredit := 0 }

private def gasInsert4DMinusOne : OracleGasLimits :=
  { gasLimit := exactGasInsert4DMinusOne, gasMax := exactGasInsert4DMinusOne, gasCredit := 0 }

private def gasInsert4Null : OracleGasLimits :=
  { gasLimit := exactGasInsert4Null, gasMax := exactGasInsert4Null, gasCredit := 0 }

private def gasInsert4NullMinusOne : OracleGasLimits :=
  { gasLimit := exactGasInsert4NullMinusOne, gasMax := exactGasInsert4NullMinusOne, gasCredit := 0 }

private def gasInsert0 : OracleGasLimits :=
  { gasLimit := exactGasNull0, gasMax := exactGasNull0, gasCredit := 0 }

private def gasInsert0MinusOne : OracleGasLimits :=
  { gasLimit := exactGasNull0MinusOne, gasMax := exactGasNull0MinusOne, gasCredit := 0 }

private def gasInsert1023 : OracleGasLimits :=
  { gasLimit := exactGasInsert1023, gasMax := exactGasInsert1023, gasCredit := 0 }

private def gasInsert1023MinusOne : OracleGasLimits :=
  { gasLimit := exactGasInsert1023MinusOne, gasMax := exactGasInsert1023MinusOne, gasCredit := 0 }

private def mkGasProgram (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok p =>
      Cell.mkOrdinary (p.bits ++ rawF41B.bits) (p.refs ++ rawF41B.refs)
  | .error e =>
      panic! s!"DICTSETGETREF: failed to assemble gas program ({reprStr e})"

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some rawF41B
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (_code : Cell)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some (mkGasProgram gas)
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected {expected}, got decode error {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected || bits != 16 || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: unexpected decode result {reprStr instr}, bits={bits}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected error {expected}, got {reprStr instr}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectAssembleInvOpcode
    (label : String)
    (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected invOpcode")
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleOk16
    (label : String)
    (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok cell =>
      expectDecodeOk label cell i

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.add) (VM.push (intV dispatchSentinel)) stack

private def runDICTSETGETREF (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def expectOkCellFlag0 (label : String) (res : Except Excno (Array Value)) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.size != 2 then
        throw (IO.userError s!"{label}: expected 2 stack items, got {st.size}")
      match st[0]?, st[1]? with
      | some (Value.cell _), some (Value.int (IntVal.num flag)) =>
          if flag != 0 then
            throw (IO.userError s!"{label}: expected miss flag 0, got {flag}")
      | _, _ =>
          throw (IO.userError s!"{label}: unexpected stack shape {reprStr st}")

private def mkStack
    (newValue : Cell)
    (keySlice : Slice)
    (dict : Value)
    (n : Int) : Array Value :=
  #[.cell newValue, .slice keySlice, dict, intV n]

private def genDICTSETGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
    let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  let (base, rng3) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase s!"fuzz/err/underflow-empty/{tag}" #[], rng2)
    else if shape = 1 then
      (mkCase s!"fuzz/err/underflow-one/{tag}" #[.cell valueA], rng2)
    else if shape = 2 then
      (mkCase s!"fuzz/err/underflow-two/{tag}" (mkStack valueA slice4A .null 4), rng2)
    else if shape = 3 then
      (mkCase s!"fuzz/err/underflow-three/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4), rng2)
    else if shape = 4 then
      (mkCase s!"fuzz/err/n-negative/{tag}" (mkStack valueA slice4A (.cell dict4Single) (-1)), rng2)
    else if shape = 5 then
      (mkCase s!"fuzz/err/n-too-large/{tag}" (mkStack valueA slice4A (.cell dict4Single) 1024), rng2)
    else if shape = 6 then
      (mkCase s!"fuzz/err/n-nan/{tag}" (#[.cell valueA, .slice slice4A, .cell dict4Single, .int .nan]), rng2)
    else if shape = 7 then
      (mkCase s!"fuzz/err/type-value/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4), rng2)
      
    else if shape = 8 then
      (mkCase s!"fuzz/err/type-key/{tag}" (#[.slice valueASlice, .slice slice4A, .cell dict4Single, intV 4]), rng2)
    else if shape = 9 then
      (mkCase s!"fuzz/err/type-dict/{tag}" (mkStack valueA slice4A (.tuple #[]) 4), rng2)
    else if shape = 10 then
      (mkCase s!"fuzz/err/key-short/{tag}" (mkStack valueA slice3 (.cell dict4Single) 4), rng2)
    else if shape = 11 then
      (mkCase s!"fuzz/ok/hit/4A/{tag}" (mkStack valueD slice4A (.cell dict4Single) 4), rng2)
    else if shape = 12 then
      (mkCase s!"fuzz/ok/hit/4B/{tag}" (mkStack valueE slice4B (.cell dict4Pair) 4), rng2)
    else if shape = 13 then
      (mkCase s!"fuzz/ok/hit/4C/{tag}" (mkStack valueA slice4C (.cell dict4Triple) 4), rng2)
    else if shape = 14 then
      (mkCase s!"fuzz/ok/hit/n0/{tag}" (mkStack valueC slice0 (.cell dict0Single) 0), rng2)
    else if shape = 15 then
      (mkCase s!"fuzz/ok/miss/null4D/{tag}" (mkStack valueB slice4D .null 4), rng2)
    else if shape = 16 then
      (mkCase s!"fuzz/ok/miss/pair4D/{tag}" (mkStack valueA slice4D (.cell dict4NoMatch) 4), rng2)
    else if shape = 17 then
      (mkCase s!"fuzz/ok/miss/1023/{tag}" (mkStack valueF slice1023 .null 1023), rng2)
    else if shape = 18 then
      (mkCodeCase s!"fuzz/raw/f41a/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41A, rng2)
    else if shape = 19 then
      (mkCodeCase s!"fuzz/raw/f41c/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41C, rng2)
    else if shape = 20 then
      (mkCodeCase s!"fuzz/raw/f41d/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41D, rng2)
    else if shape = 21 then
      (mkCodeCase s!"fuzz/raw/f41e/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41E, rng2)
    else if shape = 22 then
      (mkCodeCase s!"fuzz/raw/f41f/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41F, rng2)
    else if shape = 23 then
      (mkCodeCase s!"fuzz/raw/f419/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF419, rng2)
    else if shape = 24 then
      (mkCodeCase s!"fuzz/raw/f420/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF420, rng2)
    else if shape = 25 then
      (mkCodeCase s!"fuzz/raw/f4/{tag}" (mkStack valueA slice4A (.cell dict4Single) 4) rawF4, rng2)
    else if shape = 26 then
      (mkCodeCase s!"fuzz/ref/bad-bits/{tag}" (mkStack valueA slice4A (.cell dictBadBits) 4) rawF41B, rng2)
    else if shape = 27 then
      (mkCodeCase s!"fuzz/ref/bad-two-refs/{tag}" (mkStack valueA slice4A (.cell dictBadTwoRefs) 4) rawF41B, rng2)
    else if shape = 28 then
      (mkCodeCase s!"fuzz/ref/bad-no-ref/{tag}" (mkStack valueA slice4A (.cell dictBadNoRef) 4) rawF41B, rng2)
    else if shape = 29 then
      (mkCodeCase s!"fuzz/malformed-root/{tag}" (mkStack valueA slice4A (.cell malformedDict) 4) rawF41B, rng2)
    else if shape = 30 then
      (mkGasCase
        s!"fuzz/gas/exact/hit4A/{tag}"
        (mkStack valueD slice4A (.cell dict4Single) 4)
        rawF41B
        exactGasReplace4A
        gasReplace4A,
        rng2)
    else if shape = 31 then
      (mkGasCase
        s!"fuzz/gas/exact-minus-one/hit4A/{tag}"
        (mkStack valueD slice4A (.cell dict4Single) 4)
        rawF41B
        exactGasReplace4AMinusOne
        gasReplace4AMinusOne,
        rng2)
    else if shape = 32 then
      (mkGasCase
        s!"fuzz/gas/exact/insert4D/{tag}"
        (mkStack valueA slice4D (.cell dict4Triple) 4)
        rawF41B
        exactGasInsert4D
        gasInsert4D,
        rng2)
    else if shape = 33 then
      (mkGasCase
        s!"fuzz/gas/exact-minus-one/insert4D/{tag}"
        (mkStack valueA slice4D (.cell dict4Triple) 4)
        rawF41B
        exactGasInsert4DMinusOne
        gasInsert4DMinusOne,
        rng2)
    else if shape = 34 then
      (mkGasCase
        s!"fuzz/gas/exact/miss-null/{tag}"
        (mkStack valueB slice4D .null 4)
        rawF41B
        exactGasInsert4Null
        gasInsert4Null,
        rng2)
    else if shape = 35 then
      (mkGasCase
        s!"fuzz/gas/exact-minus-one/miss-null/{tag}"
        (mkStack valueB slice4D .null 4)
        rawF41B
        exactGasInsert4NullMinusOne
        gasInsert4NullMinusOne,
        rng2)
    else if shape = 36 then
      (mkGasCase
        s!"fuzz/gas/exact/insert-0/{tag}"
        (mkStack valueC slice0 .null 0)
        rawF41B
        exactGasNull0
        gasInsert0,
        rng2)
    else if shape = 37 then
      (mkGasCase
        s!"fuzz/gas/exact-minus-one/insert-0/{tag}"
        (mkStack valueC slice0 .null 0)
        rawF41B
        exactGasNull0MinusOne
        gasInsert0MinusOne,
        rng2)
    else if shape = 38 then
      (mkGasCase
        s!"fuzz/gas/exact/insert-1023/{tag}"
        (mkStack valueF slice1023 .null 1023)
        rawF41B
        exactGasInsert1023
        gasInsert1023,
        rng2)
    else
      (mkGasCase
        s!"fuzz/gas/exact-minus-one/insert-1023/{tag}"
        (mkStack valueF slice1023 .null 1023)
        rawF41B
        exactGasInsert1023MinusOne
        gasInsert1023MinusOne,
        rng2)
  ({ base with name := base.name }, rng3)

private def exactMinusOne (g : Int) : Int := if g > 0 then g - 1 else 0

private def exactGasLimit : Int :=
  baseGas

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let out := runDispatchFallback #[.cell valueA, .slice slice4A, .cell dict4Pair, intV 4]
        expectOkStack "unit/dispatch/fallback" out #[.cell valueA, .slice slice4A, .cell dict4Pair, intV 4, intV dispatchSentinel] },
    { name := "unit/decode/f41a" -- [B9]
      run := do
        expectDecodeOk "unit/decode/f41a" rawF41A (.dictExt (.mutGet false false false .set)) },
    { name := "unit/decode/f41b" -- [B9]
      run := do
        expectDecodeOk "unit/decode/f41b" rawF41B (.dictExt (.mutGet false false true .set)) },
    { name := "unit/decode/f41c" -- [B9]
      run := do
        expectDecodeOk "unit/decode/f41c" rawF41C (.dictExt (.mutGet true false false .set)) },
    { name := "unit/decode/f41d" -- [B9]
      run := do
        expectDecodeOk "unit/decode/f41d" rawF41D (.dictExt (.mutGet true false true .set)) },
    { name := "unit/decode/f41e" -- [B9]
      run := do
        expectDecodeOk "unit/decode/f41e" rawF41E (.dictExt (.mutGet true true false .set)) },
    { name := "unit/decode/f41f" -- [B9]
      run := do
        expectDecodeOk "unit/decode/f41f" rawF41F (.dictExt (.mutGet true true true .set)) },
    { name := "unit/decode/gaps" -- [B9]
      run := do
        expectDecodeErr "unit/decode/gap/f419" rawF419 .invOpcode
        expectDecodeErr "unit/decode/gap/f420" rawF420 .invOpcode
        expectDecodeErr "unit/decode/gap/f4" rawF4 .invOpcode },
    { name := "unit/asm/encodes" -- [B9]
      run := do
        expectAssembleOk16 "unit/asm/encodes" instr },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-empty" (runDICTSETGETREF #[]) .stkUnd },
    { name := "unit/runtime/underflow-one" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-one" (runDICTSETGETREF (#[.cell valueA])) .stkUnd },
    { name := "unit/runtime/underflow-two" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-two" (runDICTSETGETREF #[.cell valueA, .slice slice4A]) .stkUnd },
    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "unit/runtime/underflow-three" (runDICTSETGETREF #[.cell valueA, .slice slice4A, .cell dict4Single]) .stkUnd },
    { name := "unit/runtime/n-negative" -- [B3]
      run := do
        expectErr "unit/runtime/n-negative" (runDICTSETGETREF (mkStack valueA slice4A (.cell dict4Single) (-1))) .rangeChk },
    { name := "unit/runtime/n-too-large" -- [B3]
      run := do
        expectErr "unit/runtime/n-too-large" (runDICTSETGETREF (mkStack valueA slice4A (.cell dict4Single) 1024)) .rangeChk },
    { name := "unit/runtime/n-nan" -- [B3]
      run := do
        expectErr "unit/runtime/n-nan" (runDICTSETGETREF (#[.cell valueA, .slice slice4A, .cell dict4Single, .int .nan])) .rangeChk },
    { name := "unit/runtime/type-value" -- [B4]
      run := do
        expectErr "unit/runtime/type-value" (runDICTSETGETREF #[.slice valueASlice, .slice slice4A, .cell dict4Single, intV 4]) .typeChk },
    { name := "unit/runtime/type-key" -- [B4]
      run := do
        expectErr "unit/runtime/type-key" (runDICTSETGETREF #[.cell valueA, .int (.num 7), .cell dict4Single, intV 4]) .typeChk },
    { name := "unit/runtime/type-dict" -- [B4]
      run := do
        expectErr "unit/runtime/type-dict" (runDICTSETGETREF (mkStack valueA slice4A (.tuple #[]) 4)) .typeChk },
    { name := "unit/runtime/key-short" -- [B3]
      run := do
        expectErr "unit/runtime/key-short" (runDICTSETGETREF (mkStack valueA slice3 (.cell dict4Single) 4)) .cellUnd },
    { name := "unit/runtime/hit/4A" -- [B5]
      run := do
        expectOkStack
          "unit/runtime/hit/4A"
          (runDICTSETGETREF (mkStack valueD slice4A (.cell dict4Single) 4))
          #[.cell expectedSetReplace4A, .cell valueA, intV (-1)] },
    { name := "unit/runtime/hit/4B" -- [B5]
      run := do
        expectOkStack
          "unit/runtime/hit/4B"
          (runDICTSETGETREF (mkStack valueE slice4B (.cell dict4Pair) 4))
          #[.cell expectedSetReplace4B, .cell valueB, intV (-1)] },
    { name := "unit/runtime/hit/0" -- [B5]
      run := do
        expectOkStack
          "unit/runtime/hit/0"
          (runDICTSETGETREF (mkStack valueC slice0 (.cell dict0Single) 0))
          #[.cell expectedSetNull0, .cell valueA, intV (-1)] },
    { name := "unit/runtime/miss/null4D" -- [B6]
      run := do
        expectOkStack
          "unit/runtime/miss/null4D"
          (runDICTSETGETREF (mkStack valueB slice4D .null 4))
          #[.cell expectedSetInsertNull, intV 0] },
    { name := "unit/runtime/miss/nonroot4D" -- [B6]
      run := do
        expectOkCellFlag0
          "unit/runtime/miss/nonroot4D"
          (runDICTSETGETREF (mkStack valueA slice4D (.cell dict4NoMatch) 4)) },
    { name := "unit/runtime/miss/1023" -- [B6]
      run := do
        expectOkStack
          "unit/runtime/miss/1023"
          (runDICTSETGETREF (mkStack valueF slice1023 .null 1023))
          #[.cell expectedSetInsert1023, intV 0] },
    { name := "unit/runtime/ref-shape-bits" -- [B7]
      run := do
        expectErr "unit/runtime/ref-shape-bits" (runDICTSETGETREF (mkStack valueA slice4A (.cell dictBadBits) 4)) .dictErr },
    { name := "unit/runtime/ref-shape-two-refs" -- [B7]
      run := do
        expectErr "unit/runtime/ref-shape-two-refs" (runDICTSETGETREF (mkStack valueA slice4A (.cell dictBadTwoRefs) 4)) .dictErr },
    { name := "unit/runtime/ref-shape-no-ref" -- [B7]
      run := do
        expectErr "unit/runtime/ref-shape-no-ref" (runDICTSETGETREF (mkStack valueA slice4A (.cell dictBadNoRef) 4)) .dictErr },
    { name := "unit/runtime/malformed-root" -- [B8]
      run := do
        expectErr "unit/runtime/malformed-root" (runDICTSETGETREF (mkStack valueA slice4A (.cell malformedDict) 4)) .cellUnd },
    { name := "unit/runtime/type-value-null" -- [B4]
      run := do
        expectErr "unit/runtime/type-value-null" (runDICTSETGETREF #[.slice valueASlice, .slice slice4A, .null, intV 4]) .typeChk },
    { name := "unit/runtime/gas/replace4A" -- [B10]
      run := do
        expectOkStack
          "unit/runtime/gas/replace4A"
          (runDICTSETGETREF (mkStack valueD slice4A (.cell dict4Single) 4))
          #[.cell expectedSetReplace4A, .cell valueA, intV (-1)] },
    { name := "unit/runtime/gas/miss-null" -- [B10]
      run := do
        expectOkStack
          "unit/runtime/gas/miss-null"
          (runDICTSETGETREF (mkStack valueB slice4D .null 4))
          #[.cell expectedSetInsertNull, intV 0] }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow-empty" #[],
    mkCase "oracle/underflow-one" #[.cell valueA],
    mkCase "oracle/underflow-two" (mkStack valueA slice4A .null 4),
    mkCase "oracle/underflow-three" (mkStack valueA slice4A (.cell dict4Single) 4),
    -- [B3]
    mkCase "oracle/err/n-negative" (mkStack valueA slice4A (.cell dict4Single) (-1)),
    mkCase "oracle/err/n-too-large" (mkStack valueA slice4A (.cell dict4Single) 1024),
    mkCase "oracle/err/n-nan" (#[.cell valueA, .slice slice4A, .cell dict4Single, .int .nan]),
    -- [B4]
    mkCase "oracle/err/type-value" (mkStack valueA slice4A (.cell dict4Single) 4),
    mkCase "oracle/err/type-key" (mkStack valueA (mkSliceFromBits key3) (.cell dict4Single) 4),
    mkCase "oracle/err/type-dict" (mkStack valueA slice4A (.tuple #[]) 4),
    -- [B5]
    mkCase "oracle/err/key-short" (mkStack valueA slice3 (.cell dict4Single) 4),
    -- [B5]
    mkCase "oracle/ok/hit/4A" (mkStack valueD slice4A (.cell dict4Single) 4),
    mkCase "oracle/ok/hit/4B" (mkStack valueE slice4B (.cell dict4Pair) 4),
    mkCase "oracle/ok/hit/0" (mkStack valueC slice0 (.cell dict0Single) 0),
    -- [B6]
    mkCase "oracle/ok/miss/null/4D" (mkStack valueB slice4D .null 4),
    mkCase "oracle/ok/miss/nonroot/4D" (mkStack valueA slice4D (.cell dict4NoMatch) 4),
    mkCase "oracle/ok/miss/1023" (mkStack valueF slice1023 .null 1023),
    -- [B7]
    mkCodeCase "oracle/ref/bad-bits" (mkStack valueA slice4A (.cell dictBadBits) 4) rawF41B,
    mkCodeCase "oracle/ref/bad-two-refs" (mkStack valueA slice4A (.cell dictBadTwoRefs) 4) rawF41B,
    mkCodeCase "oracle/ref/bad-no-ref" (mkStack valueA slice4A (.cell dictBadNoRef) 4) rawF41B,
    -- [B8]
    mkCase "oracle/err/malformed-root" (mkStack valueA slice4A (.cell malformedDict) 4),
    -- [B9]
    mkCodeCase "oracle/raw/f41a" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41A,
    mkCodeCase "oracle/raw/f41b" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41B,
    mkCodeCase "oracle/raw/f41c" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41C,
    mkCodeCase "oracle/raw/f41d" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41D,
    mkCodeCase "oracle/raw/f41e" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41E,
    mkCodeCase "oracle/raw/f41f" (mkStack valueA slice4A (.cell dict4Single) 4) rawF41F,
    mkCodeCase "oracle/raw/f419" (mkStack valueA slice4A (.cell dict4Single) 4) rawF419,
    mkCodeCase "oracle/raw/f420" (mkStack valueA slice4A (.cell dict4Single) 4) rawF420,
    mkCodeCase "oracle/raw/f4" (mkStack valueA slice4A (.cell dict4Single) 4) rawF4,
    -- [B10]
    mkGasCase "oracle/gas/exact/hit4A" (mkStack valueD slice4A (.cell dict4Single) 4) rawF41B exactGasReplace4A gasReplace4A,
    mkGasCase "oracle/gas/exact-minus-one/hit4A" (mkStack valueD slice4A (.cell dict4Single) 4) rawF41B exactGasReplace4AMinusOne gasReplace4AMinusOne,
    mkGasCase "oracle/gas/exact/insert4D" (mkStack valueA slice4D (.cell dict4Triple) 4) rawF41B exactGasInsert4D gasInsert4D,
    mkGasCase "oracle/gas/exact-minus-one/insert4D" (mkStack valueA slice4D (.cell dict4Triple) 4) rawF41B exactGasInsert4DMinusOne gasInsert4DMinusOne,
    mkGasCase "oracle/gas/exact/miss-null" (mkStack valueB slice4D .null 4) rawF41B exactGasInsert4Null gasInsert4Null,
    mkGasCase "oracle/gas/exact-minus-one/miss-null" (mkStack valueB slice4D .null 4) rawF41B exactGasInsert4NullMinusOne gasInsert4NullMinusOne,
    mkGasCase "oracle/gas/exact/insert0" (mkStack valueC slice0 .null 0) rawF41B exactGasNull0 gasInsert0,
    mkGasCase "oracle/gas/exact-minus-one/insert0" (mkStack valueC slice0 .null 0) rawF41B exactGasNull0MinusOne gasInsert0MinusOne,
    mkGasCase "oracle/gas/exact/insert1023" (mkStack valueF slice1023 .null 1023) rawF41B exactGasInsert1023 gasInsert1023,
    mkGasCase "oracle/gas/exact-minus-one/insert1023" (mkStack valueF slice1023 .null 1023) rawF41B exactGasInsert1023MinusOne gasInsert1023MinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTSETGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTSETGETREF
