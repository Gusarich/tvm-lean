import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREPLACE

/-
INSTRUCTION: DICTIREPLACE

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime preamble.
   - `execInstrDictDictSet` executes `checkUnderflow 4` for this instruction family.
   - Stack pop order is `value`, `key`, `dict`, `n`.
2. [B2] Range check for `n`.
   - `popNatUpTo 1023` accepts `0..1023`.
   - Negative, too-large, or NaN `n` produces `.rangeChk`.
3. [B3] Non-int key (slice mode) boundary.
   - For `.dictSet false _ false .replace`, key is a `slice`.
   - If `slice.haveBits n` is false, execution throws `.cellUnd`.
4. [B4] Int-key conversion bounds.
   - For `.dictSet true unsigned false .replace`, keys must satisfy signed bounds for width `n`.
   - For `.dictSet true true .replace`, keys must satisfy unsigned bounds for width `n`.
   - Violation produces `.rangeChk`.
5. [B5] Value type checks.
   - `.byRef == false` requires a `slice` value.
   - `.byRef == true` requires a `cell` value.
6. [B6] Dictionary root and key-type checks.
   - `dict` must be `.null` or `.cell`.
   - Key type must match `intKey` mode.
   - Violations are `typeChk`.
7. [B7] Replace semantics.
   - Hit path: existing key returns rebuilt dictionary and `-1`.
   - Miss path: returns unchanged dictionary (or `.null`) and `0`.
8. [B8] Malformed dictionary path.
   - `dictSet*WithCells` can raise `.dictErr` for invalid existing roots.
9. [B9] Assembler encoding for the six valid variants.
   - 0xF422, 0xF423, 0xF424, 0xF425, 0xF426, 0xF427.
   - `.dictSet false true _ .replace` is invalid (`invOpcode`).
10. [B10] Decoder boundaries.
   - 0xF422..0xF427 decode to the expected variants.
   - Adjacent opcodes in the range (0xF421, 0xF428, 0xF429) must be invalid and truncation must fail.
11. [B11] Gas accounting.
   - Base gas from `computeExactGasBudget`.
   - Hit and miss paths must work at exact-gas.
   - `exact-1` should fail as expected.
   - Hit path must account for `created * cellCreateGasPrice`.

TOTAL BRANCHES: 11
-/

private def dictReplaceId : InstrId :=
  { name := "DICTIREPLACE" }

private def instrSlice : Instr := .dictSet false false false .replace
private def instrSliceRef : Instr := .dictSet false false true .replace
private def instrSigned : Instr := .dictSet true false false .replace
private def instrSignedRef : Instr := .dictSet true false true .replace
private def instrUnsigned : Instr := .dictSet true true false .replace
private def instrUnsignedRef : Instr := .dictSet true true true .replace

private def raw422 : Cell :=
  Cell.mkOrdinary (natToBits 0xF422 16) #[]
private def raw423 : Cell :=
  Cell.mkOrdinary (natToBits 0xF423 16) #[]
private def raw424 : Cell :=
  Cell.mkOrdinary (natToBits 0xF424 16) #[]
private def raw425 : Cell :=
  Cell.mkOrdinary (natToBits 0xF425 16) #[]
private def raw426 : Cell :=
  Cell.mkOrdinary (natToBits 0xF426 16) #[]
private def raw427 : Cell :=
  Cell.mkOrdinary (natToBits 0xF427 16) #[]
private def raw421 : Cell :=
  Cell.mkOrdinary (natToBits 0xF421 16) #[]
private def raw428 : Cell :=
  Cell.mkOrdinary (natToBits 0xF428 16) #[]
private def raw429 : Cell :=
  Cell.mkOrdinary (natToBits 0xF429 16) #[]
private def rawF4 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def sampleSliceA : Slice := mkSliceFromBits (natToBits 0xAA 8)
private def sampleSliceB : Slice := mkSliceFromBits (natToBits 0xBB 8)
private def sampleSliceC : Slice := mkSliceFromBits (natToBits 0xCC 8)
private def sampleSliceD : Slice := mkSliceFromBits (natToBits 0xDD 8)

private def sampleCellA : Cell := Cell.mkOrdinary (natToBits 0x11 8) #[]
private def sampleCellB : Cell := Cell.mkOrdinary (natToBits 0x22 8) #[]
private def sampleCellC : Cell := Cell.mkOrdinary (natToBits 0x33 8) #[]

private def malformedCell : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def requireBits (label : String) (k : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? k n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid key k={k}, n={n}, unsigned={unsigned}"

private def mkSliceKey (n : Nat) (value : Nat) : Slice :=
  mkSliceFromBits (natToBits value n)

private def mkSliceDictRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let bits : BitString := requireBits label k n unsigned
      match dictSetSliceWithCells root bits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root while building dictionary"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some c => c
    | none => panic! s!"{label}: empty dictionary"

private def mkRefDictRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let bits : BitString := requireBits label k n unsigned
      match dictSetRefWithCells root bits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root while building dictionary"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some c => c
    | none => panic! s!"{label}: empty dictionary"

private def replaceSliceCreated (root : Cell) (n : Nat) (unsigned : Bool) (key : Int) (value : Slice) : Nat :=
  match dictSetSliceWithCells (some root) (requireBits "replaceSliceCreated" key n unsigned) value .replace with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def replaceRefCreated (root : Cell) (n : Nat) (unsigned : Bool) (key : Int) (value : Cell) : Nat :=
  match dictSetRefWithCells (some root) (requireBits "replaceRefCreated" key n unsigned) value .replace with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def dictSliceSigned4 : Cell :=
  mkSliceDictRoot! "dictSliceSigned4" 4 false #[(3, sampleSliceA), (-1, sampleSliceB), (0, sampleSliceC)]

private def dictSliceUnsigned4 : Cell :=
  mkSliceDictRoot! "dictSliceUnsigned4" 4 true #[(0, sampleSliceA), (1, sampleSliceB), (5, sampleSliceC)]

private def dictRefSigned4 : Cell :=
  mkRefDictRoot! "dictRefSigned4" 4 false #[(3, sampleCellA), (-1, sampleCellB), (0, sampleCellC)]

private def dictRefUnsigned4 : Cell :=
  mkRefDictRoot! "dictRefUnsigned4" 4 true #[(0, sampleCellA), (1, sampleCellB), (5, sampleCellC)]

private def dictSliceSigned0 : Cell :=
  mkSliceDictRoot! "dictSliceSigned0" 0 false #[(0, sampleSliceA)]

private def dictUnsigned8Boundary : Cell :=
  mkSliceDictRoot! "dictUnsigned8Boundary" 8 true #[(0, sampleSliceA), (255, sampleSliceB)]

private def dictSliceSigned4Replace : Cell :=
  match dictSetSliceWithCells (some dictSliceSigned4) (requireBits "dictSliceSigned4Replace" 3 4 false) sampleSliceD .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictSliceSigned4Replace: unexpected"

private def dictSliceUnsigned4Replace : Cell :=
  match dictSetSliceWithCells (some dictSliceUnsigned4) (requireBits "dictSliceUnsigned4Replace" 5 4 true) sampleSliceD .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictSliceUnsigned4Replace: unexpected"

private def dictRefSigned4Replace : Cell :=
  match dictSetRefWithCells (some dictRefSigned4) (requireBits "dictRefSigned4Replace" 3 4 false) sampleCellC .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictRefSigned4Replace: unexpected"

private def dictRefUnsigned4Replace : Cell :=
  match dictSetRefWithCells (some dictRefUnsigned4) (requireBits "dictRefUnsigned4Replace" 5 4 true) sampleCellC .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictRefUnsigned4Replace: unexpected"

private def createdSliceSignedHit : Nat :=
  replaceSliceCreated dictSliceSigned4 4 false 3 sampleSliceD
private def createdSliceUnsignedHit : Nat :=
  replaceSliceCreated dictSliceUnsigned4 4 true 5 sampleSliceD
private def createdRefSignedHit : Nat :=
  replaceRefCreated dictRefSigned4 4 false 3 sampleCellC
private def createdRefUnsignedHit : Nat :=
  replaceRefCreated dictRefUnsigned4 4 true 5 sampleCellC

private def baseGasSlice : Int :=
  computeExactGasBudget instrSlice
private def baseGasSliceRef : Int :=
  computeExactGasBudget instrSliceRef
private def baseGasSigned : Int :=
  computeExactGasBudget instrSigned
private def baseGasSignedRef : Int :=
  computeExactGasBudget instrSignedRef
private def baseGasUnsigned : Int :=
  computeExactGasBudget instrUnsigned
private def baseGasUnsignedRef : Int :=
  computeExactGasBudget instrUnsignedRef

private def missGasSlice : Int := baseGasSlice
private def missGasSliceMinusOne : Int :=
  computeExactGasBudgetMinusOne instrSlice
private def missGasSigned : Int := baseGasSigned
private def missGasUnsigned : Int := baseGasUnsigned

private def hitGasSliceSigned : Int :=
  baseGasSigned + Int.ofNat createdSliceSignedHit * cellCreateGasPrice
private def hitGasSliceUnsigned : Int :=
  baseGasUnsigned + Int.ofNat createdSliceUnsignedHit * cellCreateGasPrice
private def hitGasRefSigned : Int :=
  baseGasSignedRef + Int.ofNat createdRefSignedHit * cellCreateGasPrice
private def hitGasRefUnsigned : Int :=
  baseGasUnsignedRef + Int.ofNat createdRefUnsignedHit * cellCreateGasPrice

private def hitGasSliceSignedMinusOne : Int :=
  if hitGasSliceSigned > 0 then hitGasSliceSigned - 1 else 0
private def hitGasRefSignedMinusOne : Int :=
  if hitGasRefSigned > 0 then hitGasRefSigned - 1 else 0

private def mkSliceStack (value : Slice) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[.slice value, .slice key, dict, intV n]

private def mkIntStack (value : Value) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[value, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictReplaceId
    program := program
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
    instr := dictReplaceId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasProgram (gas : Int) (instr : Instr) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]

private def expectDecodeInv (label : String) (cell : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr i} with {bits} bits")

private def expectAssembleErr (label : String) (expected : Excno) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def expectDecodeStepPair (labelA : String) (code : Cell) (expected : Instr) : IO Unit := do
  let s : Slice := Slice.ofCell code
  let _ ← expectDecodeStep labelA s expected 16
  pure ()

private def runReplaceDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr dictReplaceId

private def genDICTIREPLACEFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (randBool0, rng2) := randBool rng1
  let (randBool1, rng3) := randBool rng2
  if shape = 0 then
    (mkCase "fuzz/underflow/empty" #[], rng3)
  else if shape = 1 then
    (mkCase "fuzz/underflow/one" #[.slice sampleSliceA], rng3)
  else if shape = 2 then
    (mkCase "fuzz/underflow/two" #[.slice sampleSliceA, .slice (mkSliceKey 4 3)], rng3)
  else if shape = 3 then
    (mkCase "fuzz/underflow/three" #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null], rng3)
  else if shape = 4 then
    (mkCase "fuzz/slice/miss-null" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4) (#[instrSlice]), rng3)
  else if shape = 5 then
    (mkCase "fuzz/slice/hit" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSliceSigned4) 4) (#[instrSlice]), rng3)
  else if shape = 6 then
    (mkCase "fuzz/slice/miss-short-key" (mkSliceStack sampleSliceD (mkSliceKey 3 3) (.cell dictSliceSigned4) 4) (#[instrSlice]), rng3)
  else if shape = 7 then
    (mkCase "fuzz/signed/replacement-hit" (mkIntStack (.slice sampleSliceD) 3 (.cell dictSliceSigned4) 4) (#[instrSigned]), rng3)
  else if shape = 8 then
    (mkCase "fuzz/signed/replacement-hit-ref" (mkIntStack (.cell sampleCellC) 3 (.cell dictRefSigned4) 4) (#[instrSignedRef]), rng3)
  else if shape = 9 then
    (mkCase "fuzz/signed/replacement-miss" (mkIntStack (.slice sampleSliceD) 6 (.cell dictSliceSigned4) 4) (#[instrSigned]), rng3)
  else if shape = 10 then
    (mkCase "fuzz/unsigned/replacement-hit" (mkIntStack (.slice sampleSliceD) 5 (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]), rng3)
  else if shape = 11 then
    (mkCase "fuzz/unsigned/replacement-hit-ref" (mkIntStack (.cell sampleCellC) 5 (.cell dictRefUnsigned4) 4) (#[instrUnsignedRef]), rng3)
  else if shape = 12 then
    (mkCase "fuzz/unsigned/replacement-miss" (mkIntStack (.slice sampleSliceD) 6 (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]), rng3)
  else if shape = 13 then
    (mkCase "fuzz/int/key-oob-signed-high" (mkIntStack (.slice sampleSliceD) 8 (.cell dictSliceSigned4) 4) (#[instrSigned]), rng3)
  else if shape = 14 then
    (mkCase "fuzz/int/key-oob-signed-low" (mkIntStack (.slice sampleSliceD) (-9) (.cell dictSliceSigned4) 4) (#[instrSigned]), rng3)
  else if shape = 15 then
    (mkCase "fuzz/int/key-oob-unsigned" (mkIntStack (.slice sampleSliceD) (-1) (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]), rng3)
  else if shape = 16 then
    (mkCase "fuzz/int/key-oob-unsigned-high" (mkIntStack (.slice sampleSliceD) 16 (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]), rng3)
  else if shape = 17 then
    (mkCase "fuzz/type/key-not-int" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSliceSigned4) 4) (#[instrSigned]), rng3)
  else if shape = 18 then
    (mkCase "fuzz/type/value-not-slice" (mkIntStack (.cell sampleCellA) 3 (.cell dictSliceSigned4) 4) (#[instrSigned]), rng3)
  else if shape = 19 then
    (mkCase "fuzz/type/value-not-cell" (mkIntStack (.slice sampleSliceD) 3 (.cell dictRefSigned4) 4) (#[instrSignedRef]), rng3)
  else if shape = 20 then
    (mkCase "fuzz/type/dict-not-maybe-cell" (mkIntStack (.slice sampleSliceD) 3 (.tuple #[]) 4) (#[instrSigned]), rng3)
  else if shape = 21 then
    (mkCase "fuzz/malformed-dict" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell malformedCell) 4) (#[instrSlice]), rng3)
  else if shape = 22 then
    (mkCase "fuzz/gas/miss-slice-exact" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4) (mkGasProgram missGasSlice instrSlice)
      (oracleGasLimitsExact missGasSlice), rng3)
  else if shape = 23 then
    (mkCase "fuzz/gas/miss-slice-minus-one" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasSliceMinusOne instrSlice) (oracleGasLimitsExact missGasSliceMinusOne), rng3)
  else if shape = 24 then
    if randBool0 then
      (mkCase "fuzz/gas/hit-signed-slice-exact" (mkIntStack (.slice sampleSliceD) 3 (.cell dictSliceSigned4) 4)
        (mkGasProgram hitGasSliceSigned instrSigned) (oracleGasLimitsExact hitGasSliceSigned), rng3)
    else
      (mkCase "fuzz/gas/hit-ref-signed-exact" (mkIntStack (.cell sampleCellC) 3 (.cell dictRefSigned4) 4)
        (mkGasProgram hitGasRefSigned instrSignedRef) (oracleGasLimitsExact hitGasRefSigned), rng3)
  else if shape = 25 then
    if randBool1 then
      (mkCase "fuzz/gas/hit-signed-slice-minus-one" (mkIntStack (.slice sampleSliceD) 3 (.cell dictSliceSigned4) 4)
        (mkGasProgram hitGasSliceSignedMinusOne instrSigned) (oracleGasLimitsExact hitGasSliceSignedMinusOne), rng3)
    else
      (mkCase "fuzz/gas/hit-ref-signed-minus-one" (mkIntStack (.cell sampleCellC) 3 (.cell dictRefSigned4) 4)
        (mkGasProgram hitGasRefSignedMinusOne instrSignedRef) (oracleGasLimitsExact hitGasRefSignedMinusOne), rng3)
  else if shape = 26 then
    (mkCodeCase "fuzz/decode-422" #[] raw422, rng3)
  else
    (mkCase "fuzz/decode-adjacent" #[] (#[instrSlice]), rng3)


def suite : InstrSuite where
  id := dictReplaceId
  unit := #[
    { name := "unit/asm/valid/422"
      run := do
        match assembleCp0 [instrSlice] with
        | .ok c =>
            if c.bits = raw422.bits then
              pure ()
            else
              throw (IO.userError "unit/asm/valid/422: wrong opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/valid/422: expected success, got {e}") }
    , { name := "unit/asm/valid/423"
        run := do
          match assembleCp0 [instrSliceRef] with
          | .ok c =>
              if c.bits = raw423.bits then
                pure ()
              else
                throw (IO.userError "unit/asm/valid/423: wrong opcode")
          | .error e =>
              throw (IO.userError s!"unit/asm/valid/423: expected success, got {e}") }
    , { name := "unit/asm/valid/424"
        run := do
          match assembleCp0 [instrSigned] with
          | .ok c =>
              if c.bits = raw424.bits then
                pure ()
              else
                throw (IO.userError "unit/asm/valid/424: wrong opcode")
          | .error e =>
              throw (IO.userError s!"unit/asm/valid/424: expected success, got {e}") }
    , { name := "unit/asm/valid/425"
        run := do
          match assembleCp0 [instrSignedRef] with
          | .ok c =>
              if c.bits = raw425.bits then
                pure ()
              else
                throw (IO.userError "unit/asm/valid/425: wrong opcode")
          | .error e =>
              throw (IO.userError s!"unit/asm/valid/425: expected success, got {e}") }
    , { name := "unit/asm/valid/426"
        run := do
          match assembleCp0 [instrUnsigned] with
          | .ok c =>
              if c.bits = raw426.bits then
                pure ()
              else
                throw (IO.userError "unit/asm/valid/426: wrong opcode")
          | .error e =>
              throw (IO.userError s!"unit/asm/valid/426: expected success, got {e}") }
    , { name := "unit/asm/valid/427"
        run := do
          match assembleCp0 [instrUnsignedRef] with
          | .ok c =>
              if c.bits = raw427.bits then
                pure ()
              else
                throw (IO.userError "unit/asm/valid/427: wrong opcode")
          | .error e =>
              throw (IO.userError s!"unit/asm/valid/427: expected success, got {e}") }
    , { name := "unit/asm/invalid/unsigned-slice"
        run := do
          expectAssembleErr "unit/asm/invalid/unsigned-slice" .invOpcode (i:=.dictSet false true false .replace)
    }
    , { name := "unit/decode/valid-ranges"
        run := do
          let s0 : Slice := Slice.ofCell raw422
          let _ ← expectDecodeStep "unit/decode/422" s0 instrSlice 16
          let s1 : Slice := Slice.ofCell raw423
          let _ ← expectDecodeStep "unit/decode/423" s1 instrSliceRef 16
          let s2 : Slice := Slice.ofCell raw424
          let _ ← expectDecodeStep "unit/decode/424" s2 instrSigned 16
          let s3 : Slice := Slice.ofCell raw425
          let _ ← expectDecodeStep "unit/decode/425" s3 instrSignedRef 16
          let s4 : Slice := Slice.ofCell raw426
          let _ ← expectDecodeStep "unit/decode/426" s4 instrUnsigned 16
          let s5 : Slice := Slice.ofCell raw427
          let _ ← expectDecodeStep "unit/decode/427" s5 instrUnsignedRef 16
          pure () }
    , { name := "unit/decode/bounds/invalid"
        run := do
          expectDecodeInv "unit/decode/421" raw421
          expectDecodeInv "unit/decode/428" raw428
          expectDecodeInv "unit/decode/429" raw429
          expectDecodeInv "unit/decode/truncated" rawF4
    }
    , { name := "unit/runtime/slice-hit"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSliceSigned4) 4
          expectOkStack
            "unit/runtime/slice-hit"
            (runReplaceDirect instrSlice st)
            #[.cell dictSliceSigned4Replace, intV (-1)] }
    , { name := "unit/runtime/slice-miss-null"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4
          expectOkStack
            "unit/runtime/slice-miss-null"
            (runReplaceDirect instrSlice st)
            #[.null, intV 0] }
    , { name := "unit/runtime/slice-miss-nonnull"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceKey 4 2) (.cell dictSliceSigned4) 4
          expectOkStack
            "unit/runtime/slice-miss-nonnull"
            (runReplaceDirect instrSlice st)
            #[.cell dictSliceSigned4, intV 0] }
    , { name := "unit/runtime/int-hit"
        run := do
          expectOkStack
            "unit/runtime/int-hit"
            (runReplaceDirect instrSigned (mkIntStack (.slice sampleSliceC) 3 (.cell dictSliceSigned4) 4))
            #[.cell dictSliceSigned4Replace, intV (-1)] }
    , { name := "unit/runtime/int-hit-ref"
        run := do
          expectOkStack
            "unit/runtime/int-hit-ref"
            (runReplaceDirect instrSignedRef (mkIntStack (.cell sampleCellC) 3 (.cell dictRefSigned4) 4))
            #[.cell dictRefSigned4Replace, intV (-1)] }
    , { name := "unit/runtime/unsigned-hit"
        run := do
          expectOkStack
            "unit/runtime/unsigned-hit"
            (runReplaceDirect instrUnsigned (mkIntStack (.slice sampleSliceC) 5 (.cell dictSliceUnsigned4) 4))
            #[.cell dictSliceUnsigned4Replace, intV (-1)] }
    , { name := "unit/runtime/underflow-empty"
        run := do
          expectErr "unit/runtime/underflow-empty" (runReplaceDirect instrSlice #[]) .stkUnd }
    , { name := "unit/runtime/underflow-two"
        run := do
          expectErr "unit/runtime/underflow-two" (runReplaceDirect instrSlice #[.slice sampleSliceA, .slice (mkSliceKey 4 3)]) .stkUnd }
    , { name := "unit/runtime/underflow-three"
        run := do
          expectErr "unit/runtime/underflow-three" (runReplaceDirect instrSlice #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null]) .stkUnd }
    , { name := "unit/runtime/range/n-negative"
        run := do
          expectErr "unit/runtime/range/n-negative" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null (-1)) ) .rangeChk }
    , { name := "unit/runtime/range/n-too-large"
        run := do
          expectErr "unit/runtime/range/n-too-large" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 1024)) .rangeChk }
    , { name := "unit/runtime/range/n-nan"
        run := do
          let stack : Array Value := #[.slice sampleSliceD, .slice (mkSliceKey 4 3), .null, .int .nan]
          expectErr "unit/runtime/range/n-nan" (runReplaceDirect instrSlice stack) .rangeChk }
    , { name := "unit/runtime/type/slice-key-too-short"
        run := do
          expectErr "unit/runtime/type/slice-key-too-short" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 3 1) (.cell dictSliceSigned4) 4)) .cellUnd }
    , { name := "unit/runtime/type/int-key-out-of-range"
        run := do
          expectErr "unit/runtime/type/int-key-out-of-range" (runReplaceDirect instrSigned (mkIntStack (.slice sampleSliceD) 8 (.cell dictSliceSigned4) 4)) .rangeChk }
    , { name := "unit/runtime/type/key-wrong-kind"
        run := do
          expectErr "unit/runtime/type/key-wrong-kind" (runReplaceDirect instrSigned (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSliceSigned4) 4)) .typeChk }
    , { name := "unit/runtime/type/value-not-slice"
        run := do
          expectErr "unit/runtime/type/value-not-slice" (runReplaceDirect instrSigned (mkIntStack (.cell sampleCellA) 3 (.cell dictSliceSigned4) 4)) .typeChk }
    , { name := "unit/runtime/type/value-not-cell"
        run := do
          expectErr "unit/runtime/type/value-not-cell" (runReplaceDirect instrSignedRef (mkIntStack (.slice sampleSliceD) 3 (.cell dictRefSigned4) 4)) .typeChk }
    , { name := "unit/runtime/type/dict-not-maybe-cell"
        run := do
          expectErr "unit/runtime/type/dict-not-maybe-cell" (runReplaceDirect instrSigned (mkIntStack (.slice sampleSliceD) 3 (.tuple #[]) 4)) .typeChk }
    , { name := "unit/runtime/dict-err"
        run := do
          expectErr "unit/runtime/dict-err" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell malformedCell) 4)) .dictErr
    }
    , { name := "unit/runtime/dict-err-ref"
        run := do
          expectErr "unit/runtime/dict-err-ref" (runReplaceDirect instrSignedRef (mkIntStack (.cell sampleCellC) 3 (.cell malformedCell) 4)) .dictErr
    }
    , { name := "unit/gas/slice-miss-exact"
        run := do
            expectOkStack
              "unit/gas/slice-miss-exact"
              (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4))
              #[.null, intV 0]
    }
    , { name := "unit/gas/hit-signed-exact"
        run := do
          expectOkStack
            "unit/gas/hit-signed-exact"
            (runReplaceDirect instrSigned (mkIntStack (.slice sampleSliceD) 3 (.cell dictSliceSigned4) 4))
            #[.cell dictSliceSigned4Replace, intV (-1)]
    }
  ]
  oracle := #[
    -- [B7]
    mkCase "oracle/slice-hit" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSliceSigned4) 4) (#[instrSlice]),
    mkCase "oracle/slice-miss-null" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4) (#[instrSlice]),
    mkCase "oracle/slice-miss-nonnull" (mkSliceStack sampleSliceD (mkSliceKey 2 3) (.cell dictSliceSigned4) 4) (#[instrSlice]),
    mkCase "oracle/slice-zero-width-hit" (mkSliceStack sampleSliceD (mkSliceFromBits #[]) (.cell dictSliceSigned0) 0) (#[instrSlice]),

    -- [B8]
    mkCase "oracle/signed-hit-slice" (mkIntStack (.slice sampleSliceD) 3 (.cell dictSliceSigned4) 4) (#[instrSigned]),
    mkCase "oracle/signed-hit-ref" (mkIntStack (.cell sampleCellC) 3 (.cell dictRefSigned4) 4) (#[instrSignedRef]),
    mkCase "oracle/signed-miss" (mkIntStack (.slice sampleSliceD) 6 (.cell dictSliceSigned4) 4) (#[instrSigned]),
    mkCase "oracle/unsigned-hit-slice" (mkIntStack (.slice sampleSliceD) 5 (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]),
    mkCase "oracle/unsigned-hit-ref" (mkIntStack (.cell sampleCellC) 5 (.cell dictRefUnsigned4) 4) (#[instrUnsignedRef]),
    mkCase "oracle/unsigned-miss" (mkIntStack (.slice sampleSliceD) 6 (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]),

    -- [B3]
    mkCase "oracle/err/n-negative" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null (-1)) (#[instrSlice]),
    mkCase "oracle/err/n-too-large" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 1024) (#[instrSlice]),
    mkCase "oracle/err/n-nan" (#[.slice sampleSliceD, .slice (mkSliceKey 4 3), .null, .int .nan]) (#[instrSlice]),

    -- [B4]
    mkCase "oracle/err/slice-key-short" (mkSliceStack sampleSliceD (mkSliceKey 3 5) (.cell dictSliceSigned4) 4) (#[instrSlice]),
    mkCase "oracle/err/int-signed-high" (mkIntStack (.slice sampleSliceD) 8 (.cell dictSliceSigned4) 4) (#[instrSigned]),
    mkCase "oracle/err/int-signed-low" (mkIntStack (.slice sampleSliceD) (-9) (.cell dictSliceSigned4) 4) (#[instrSigned]),
    mkCase "oracle/err/int-unsigned-neg" (mkIntStack (.slice sampleSliceD) (-1) (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]),
    mkCase "oracle/err/int-unsigned-high" (mkIntStack (.slice sampleSliceD) 16 (.cell dictSliceUnsigned4) 4) (#[instrUnsigned]),

    -- [B6]
    mkCase "oracle/err/key-type" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSliceSigned4) 4) (#[instrSigned]),
    mkCase "oracle/err/value-slice" (mkIntStack (.cell sampleCellA) 3 (.cell dictSliceSigned4) 4) (#[instrSigned]),
    mkCase "oracle/err/value-cell" (mkIntStack (.slice sampleSliceD) 3 (.cell dictRefSigned4) 4) (#[instrSignedRef]),
    mkCase "oracle/err/dict-type" (mkIntStack (.slice sampleSliceD) 3 (.tuple #[]) 4) (#[instrSigned]),

    -- [B7]
    mkCase "oracle/err/malformed" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell malformedCell) 4) (#[instrSlice]),
    mkCase "oracle/err/malformed-ref" (mkIntStack (.cell sampleCellC) 3 (.cell malformedCell) 4) (#[instrSignedRef]),

    -- [B8]
    mkCodeCase "oracle/decode/422" #[] raw422,
    mkCodeCase "oracle/decode/423" #[] raw423,
    mkCodeCase "oracle/decode/424" #[] raw424,
    mkCodeCase "oracle/decode/425" #[] raw425,
    mkCodeCase "oracle/decode/426" #[] raw426,
    mkCodeCase "oracle/decode/427" #[] raw427,
    mkCodeCase "oracle/decode/invalid-421" #[] raw421,
    mkCodeCase "oracle/decode/invalid-428" #[] raw428,
    mkCodeCase "oracle/decode/invalid-429" #[] raw429,
    mkCodeCase "oracle/decode/invalid-truncated" #[] rawF4,

    -- [B9]/[B11]
    mkCase "oracle/gas/slice-miss-exact"
      (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasSlice instrSlice)
      (oracleGasLimitsExact missGasSlice),
    mkCase "oracle/gas/slice-miss-exact-minus-one"
      (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasSliceMinusOne instrSlice)
      (oracleGasLimitsExact missGasSliceMinusOne),
    mkCase "oracle/gas/signed-hit-slice-exact"
      (mkIntStack (.slice sampleSliceD) 3 (.cell dictSliceSigned4) 4)
      (mkGasProgram hitGasSliceSigned instrSigned)
      (oracleGasLimitsExact hitGasSliceSigned),
    mkCase "oracle/gas/signed-hit-slice-exact-minus-one"
      (mkIntStack (.slice sampleSliceD) 3 (.cell dictSliceSigned4) 4)
      (mkGasProgram hitGasSliceSignedMinusOne instrSigned)
      (oracleGasLimitsExact hitGasSliceSignedMinusOne),
    mkCase "oracle/gas/signed-hit-ref-exact"
      (mkIntStack (.cell sampleCellC) 3 (.cell dictRefSigned4) 4)
      (mkGasProgram hitGasRefSigned instrSignedRef)
      (oracleGasLimitsExact hitGasRefSigned),
    mkCase "oracle/gas/signed-hit-ref-exact-minus-one"
      (mkIntStack (.cell sampleCellC) 3 (.cell dictRefSigned4) 4)
      (mkGasProgram hitGasRefSignedMinusOne instrSignedRef)
      (oracleGasLimitsExact hitGasRefSignedMinusOne),
    mkCase "oracle/gas/unsigned-hit-exact"
      (mkIntStack (.slice sampleSliceD) 5 (.cell dictSliceUnsigned4) 4)
      (mkGasProgram hitGasSliceUnsigned instrUnsigned)
      (oracleGasLimitsExact hitGasSliceUnsigned),
    mkCase "oracle/gas/unsigned-hit-ref-exact"
      (mkIntStack (.cell sampleCellC) 5 (.cell dictRefUnsigned4) 4)
      (mkGasProgram hitGasRefUnsigned instrUnsignedRef)
      (oracleGasLimitsExact hitGasRefUnsigned)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTIREPLACEFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACE
