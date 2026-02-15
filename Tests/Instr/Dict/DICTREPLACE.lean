import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREPLACE

/-
INSTRUCTION: DICTREPLACE

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime preamble:
   - `execInstrDictDictSet` requires exact underflow size `4` for `DICTREPLACE`.
   - Pop order is `value`, `key`, `dict`, `n`.
2. [B2] `n` range validation:
   - `n` is read via `popNatUpTo 1023`, so non-finite int, negatives, and values >1023 produce `.rangeChk`.
3. [B3] Key extraction for non-int key mode:
   - Key must be a slice.
   - `n` bits are required: if `key.haveBits n` is false, execution raises `.cellUnd`.
4. [B4] Value type validation (slice form):
   - For non-ref `DICTREPLACE`, value must be a slice; a cell value raises `.typeChk`.
5. [B5] Dictionary root type validation:
   - Root must be `maybe cell` (`null` accepted, malformed non-cell types are `.typeChk`).
6. [B6] Replace runtime semantics:
   - Empty or missing key returns unchanged dictionary and `0`.
   - Existing key replaces value and pushes `-1`.
7. [B7] Dictionary structure errors:
   - Malformed dictionary roots produce `.dictErr` after loading visited nodes.
8. [B8] Assembler encoding validation:
   - Valid opcodes: `0xF422` (slice) and `0xF423` (slice ref).
   - Invalid unsigned-slice form throws `.invOpcode` in assembly.
9. [B9] Decoder boundaries and aliasing:
   - `0xF422..0xF423` decode to `DICTREPLACE` / `DICTREPLACEREF`.
   - Adjacent non-matching opcodes (`0xF421`, `0xF424`) must not decode to `DICTREPLACE` and are checked with explicit boundaries.
   - Truncated prefixes must decode as invalid.
10. [B10] Gas accounting:
   - Base gas comes from `computeExactGasBudget`.
   - Miss paths use base gas only.
   - Hit paths consume extra `created * cellCreateGasPrice`.
11. [B11] Gas underflow behavior:
   - Exact-minus-one limits should fail at the correct branches for miss/hit flows.

TOTAL BRANCHES: 11
-/

private def dictReplaceId : InstrId :=
  { name := "DICTREPLACE" }

private def instrSlice : Instr := .dictSet false false false .replace
private def instrSliceRef : Instr := .dictSet false false true .replace
private def instrSigned : Instr := .dictSet true false false .replace

private def raw422 : Cell :=
  Cell.mkOrdinary (natToBits 0xF422 16) #[]
private def raw423 : Cell :=
  Cell.mkOrdinary (natToBits 0xF423 16) #[]
private def raw421 : Cell :=
  Cell.mkOrdinary (natToBits 0xF421 16) #[]
private def raw424 : Cell :=
  Cell.mkOrdinary (natToBits 0xF424 16) #[]
private def raw425 : Cell :=
  Cell.mkOrdinary (natToBits 0xF425 16) #[]
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
private def sampleCellD : Cell := Cell.mkOrdinary (natToBits 0x44 8) #[]

private def malformedCell : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def requireBits (label : String) (k : Int) (n : Nat) : BitString :=
  match dictKeyBits? k n true with
  | some bits => bits
  | none => panic! s!"{label}: invalid key k={k}, n={n}"

private def mkSliceKey (n : Nat) (value : Nat) : Slice :=
  mkSliceFromBits (natToBits value n)

private def mkSliceDictRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let bits : BitString := requireBits label k n
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

private def mkRefDictRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for e in entries do
      let (k, v) := e
      let bits : BitString := requireBits label k n
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

private def replaceSliceCreated (root : Cell) (n : Nat) (key : Int) (value : Slice) : Nat :=
  match dictSetSliceWithCells (some root) (requireBits "replaceSliceCreated" key n) value .replace with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def replaceRefCreated (root : Cell) (n : Nat) (key : Int) (value : Cell) : Nat :=
  match dictSetRefWithCells (some root) (requireBits "replaceRefCreated" key n) value .replace with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def dictSlice4 : Cell :=
  mkSliceDictRoot! "dictSlice4" 4 #[(3, sampleSliceA), (7, sampleSliceB), (12, sampleSliceC)]
private def dictRef4 : Cell :=
  mkRefDictRoot! "dictRef4" 4 #[(3, sampleCellA), (7, sampleCellB), (12, sampleCellC)]
private def dictSlice0 : Cell :=
  mkSliceDictRoot! "dictSlice0" 0 #[(0, sampleSliceA)]

private def dictSlice0Replace : Cell :=
  match dictSetSliceWithCells (some dictSlice0) (requireBits "dictSlice0Replace" 0 0) sampleSliceD .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictSlice0Replace: unexpected"

private def dictSlice4Replace : Cell :=
  match dictSetSliceWithCells (some dictSlice4) (requireBits "dictSlice4Replace" 3 4) sampleSliceD .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictSlice4Replace: unexpected"

private def dictRef4Replace : Cell :=
  match dictSetRefWithCells (some dictRef4) (requireBits "dictRef4Replace" 3 4) sampleCellC .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictRef4Replace: unexpected"

private def createdSliceHit : Nat :=
  replaceSliceCreated dictSlice4 4 3 sampleSliceD
private def createdRefHit : Nat :=
  replaceRefCreated dictRef4 4 3 sampleCellC

private def baseGasSlice : Int :=
  computeExactGasBudget instrSlice
private def baseGasSliceRef : Int :=
  computeExactGasBudget instrSliceRef

private def missGasSlice : Int := baseGasSlice
private def missGasSliceMinusOne : Int :=
  computeExactGasBudgetMinusOne instrSlice
private def missGasRef : Int := baseGasSliceRef
private def missGasRefMinusOne : Int :=
  computeExactGasBudgetMinusOne instrSliceRef

private def hitGasSlice : Int :=
  baseGasSlice + Int.ofNat createdSliceHit * cellCreateGasPrice
private def hitGasRef : Int :=
  baseGasSliceRef + Int.ofNat createdRefHit * cellCreateGasPrice

private def hitGasSliceMinusOne : Int :=
  if hitGasSlice > 0 then hitGasSlice - 1 else 0
private def hitGasRefMinusOne : Int :=
  if hitGasRef > 0 then hitGasRef - 1 else 0

private def mkSliceStack (value : Slice) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[.slice value, .slice key, dict, intV n]

private def mkRefStack (value : Cell) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[.cell value, .slice key, dict, intV n]

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
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictReplaceId
    codeCell? := some code
    initStack := #[]
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasProgram (gas : Int) (instr : Instr) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]

private def expectDecodeStepPair (labelA : String) (code : Cell) (expected : Instr) : IO Unit := do
  let s : Slice := Slice.ofCell code
  let _ ← expectDecodeStep labelA s expected 16
  pure ()

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

private def runReplaceDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr dictReplaceId

private def genDICTREPLACEFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (randBool0, rng2) := randBool rng1
  if shape = 0 then
    (mkCase "fuzz/underflow-empty" #[], rng2) -- [B1]
  else if shape = 1 then
    (mkCase "fuzz/underflow-one" #[.slice sampleSliceA], rng2) -- [B1]
  else if shape = 2 then
    (mkCase "fuzz/underflow-two" #[.slice sampleSliceA, .slice (mkSliceKey 4 3)], rng2) -- [B1]
  else if shape = 3 then
    (mkCase "fuzz/underflow-three" #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null], rng2) -- [B1]
  else if shape = 4 then
    (mkCase "fuzz/slice/miss-null" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4) (#[instrSlice]), rng2) -- [B6]
  else if shape = 5 then
    (mkCase "fuzz/slice/miss-nonnull" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4) (#[instrSlice]), rng2) -- [B6]
  else if shape = 6 then
    (mkCase "fuzz/slice/hit" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4) (#[instrSlice]), rng2) -- [B6]
  else if shape = 7 then
    (mkCase "fuzz/ref/hit" (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell dictRef4) 4) (#[instrSliceRef]), rng2) -- [B6]
  else if shape = 8 then
    (mkCase "fuzz/key-short" (mkSliceStack sampleSliceD (mkSliceKey 3 3) (.cell dictSlice4) 4) (#[instrSlice]), rng2) -- [B3]
  else if shape = 9 then
    (mkCase "fuzz/int-key-type" (mkSliceStack sampleSliceD sampleSliceA (.cell dictSlice4) 4) (#[instrSlice]), rng2) -- [B4]
  else if shape = 10 then
    (mkCase "fuzz/value-not-slice" (mkSliceStack sampleSliceA (mkSliceKey 4 3) (.cell dictSlice4) 4) (#[instrSlice]), rng2) -- [B4]
  else if shape = 11 then
    (mkCase "fuzz/value-not-cell" (mkRefStack sampleCellA (mkSliceKey 4 3) (.cell dictRef4) 4) (#[instrSliceRef]), rng2) -- [B4]
  else if shape = 12 then
    (mkCase "fuzz/dict-not-maybe-cell" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.tuple #[]) 4) (#[instrSlice]), rng2) -- [B5]
  else if shape = 13 then
    (mkCase "fuzz/malformed-dict" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell malformedCell) 4) (#[instrSlice]), rng2) -- [B7]
  else if shape = 14 then
    (mkCase "fuzz/malformed-ref-dict" (mkRefStack sampleCellA (mkSliceKey 4 3) (.cell malformedCell) 4) (#[instrSliceRef]), rng2) -- [B7]
  else if shape = 15 then
    (mkCase "fuzz/range/n-negative" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null (-1)) (#[instrSlice]), rng2) -- [B2]
  else if shape = 16 then
    (mkCase "fuzz/range/n-too-large" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 1024) (#[instrSlice]), rng2) -- [B2]
  else if shape = 17 then
    (mkCase "fuzz/range/n-nan" #[(.slice sampleSliceD), (.slice (mkSliceKey 4 3)), .null, .int .nan] (#[instrSlice]), rng2) -- [B2]
  else if shape = 18 then
    (mkCase "fuzz/gas/miss-slice-exact" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasSlice instrSlice) (oracleGasLimitsExact missGasSlice), rng2) -- [B10] [B11]
  else if shape = 19 then
    (mkCase "fuzz/gas/miss-slice-minus-one" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasSliceMinusOne instrSlice) (oracleGasLimitsExact missGasSliceMinusOne), rng2) -- [B11]
  else if shape = 20 then
    if randBool0 then
      (mkCase "fuzz/gas/hit-slice-exact" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4)
        (mkGasProgram hitGasSlice instrSlice) (oracleGasLimitsExact hitGasSlice), rng2) -- [B10] [B11]
    else
      (mkCase "fuzz/gas/hit-ref-exact" (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell dictRef4) 4)
        (mkGasProgram hitGasRef instrSliceRef) (oracleGasLimitsExact hitGasRef), rng2) -- [B10] [B11]
  else if shape = 21 then
    if randBool0 then
      (mkCase "fuzz/gas/hit-slice-minus-one" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4)
        (mkGasProgram hitGasSliceMinusOne instrSlice) (oracleGasLimitsExact hitGasSliceMinusOne), rng2) -- [B11]
    else
      (mkCase "fuzz/gas/hit-ref-minus-one" (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell dictRef4) 4)
        (mkGasProgram hitGasRefMinusOne instrSliceRef) (oracleGasLimitsExact hitGasRefMinusOne), rng2) -- [B11]
  else if shape = 22 then
    (mkCase "fuzz/zero-width-hit" (mkSliceStack sampleSliceD (mkSliceFromBits #[]) (.cell dictSlice0) 0) (#[instrSlice]), rng2) -- [B6]
  else if shape = 23 then
    (mkCase "fuzz/zero-width-miss" (mkSliceStack sampleSliceD (mkSliceFromBits #[]) .null 0) (#[instrSlice]), rng2) -- [B6]
  else if shape = 24 then
    (mkCodeCase "fuzz/decode/422" raw422, rng2)
  else if shape = 25 then
    (mkCodeCase "fuzz/decode/423" raw423, rng2)
  else if shape = 26 then
    (mkCodeCase "fuzz/decode/421" raw421, rng2)
  else if shape = 27 then
    (mkCodeCase "fuzz/decode/424" raw424, rng2)
  else if shape = 28 then
    (mkCodeCase "fuzz/alias/425" raw425, rng2)
  else if shape = 29 then
    (mkCodeCase "fuzz/decode/428" raw428, rng2)
  else if shape = 30 then
    (mkCodeCase "fuzz/decode/429" raw429, rng2)
  else if shape = 31 then
    (mkCodeCase "fuzz/decode/truncated" rawF4, rng2)
  else
    (mkCase "fuzz/encode-invalid-unsigned-slice" #[], rng2)



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

    , { name := "unit/asm/invalid/unsigned-slice"
        run := do
          expectAssembleErr "unit/asm/invalid/unsigned-slice" .invOpcode (.dictSet false true false .replace) }

    , { name := "unit/decode/valid/422"
        run := do
          let s : Slice := Slice.ofCell raw422
          let _ ← expectDecodeStep "unit/decode/422" s instrSlice 16
          pure () }

    , { name := "unit/decode/valid/423"
        run := do
          let s : Slice := Slice.ofCell raw423
          let _ ← expectDecodeStep "unit/decode/423" s instrSliceRef 16
          pure () }

    , { name := "unit/decode/adjacent/low"
        run := do
          expectDecodeInv "unit/decode/421" raw421
          expectDecodeInv "unit/decode/428" raw428
          expectDecodeInv "unit/decode/429" raw429
          expectDecodeInv "unit/decode/truncated" rawF4
          pure () }

    , { name := "unit/decode/alias/424-to-ireplace"
        run := do
          expectDecodeStepPair "unit/decode/alias/424" raw424 (.dictSet true false false .replace) }

    , { name := "unit/decode/alias/425-to-ireplace-ref"
        run := do
          expectDecodeStepPair "unit/decode/alias/425" raw425 (.dictSet true false true .replace) }

    , { name := "unit/runtime/slice-hit"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4
          expectOkStack
            "unit/runtime/slice-hit"
            (runReplaceDirect instrSlice st)
            #[.cell dictSlice4Replace, intV (-1)] }

    , { name := "unit/runtime/slice-miss-null"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4
          expectOkStack
            "unit/runtime/slice-miss-null"
            (runReplaceDirect instrSlice st)
            #[.null, intV 0] }

    , { name := "unit/runtime/slice-miss-nonnull"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceKey 4 2) (.cell dictSlice4) 4
          expectOkStack
            "unit/runtime/slice-miss-nonnull"
            (runReplaceDirect instrSlice st)
            #[.cell dictSlice4, intV 0] }

    , { name := "unit/runtime/ref-hit"
        run := do
          let st := mkRefStack sampleCellC (mkSliceKey 4 3) (.cell dictRef4) 4
          expectOkStack
            "unit/runtime/ref-hit"
            (runReplaceDirect instrSliceRef st)
            #[.cell dictRef4Replace, intV (-1)] }

    , { name := "unit/runtime/zero-width-hit"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceFromBits #[]) (.cell dictSlice0) 0
          expectOkStack
            "unit/runtime/zero-width-hit"
            (runReplaceDirect instrSlice st)
            #[.cell dictSlice0Replace, intV (-1)] }

    , { name := "unit/runtime/zero-width-miss"
        run := do
          let st := mkSliceStack sampleSliceD (mkSliceFromBits #[]) .null 0
          expectOkStack
            "unit/runtime/zero-width-miss"
            (runReplaceDirect instrSlice st)
            #[.null, intV 0] }

    , { name := "unit/runtime/underflow-empty"
        run := do
          expectErr "unit/runtime/underflow-empty" (runReplaceDirect instrSlice #[]) .stkUnd }

    , { name := "unit/runtime/underflow-two"
        run := do
          expectErr "unit/runtime/underflow-two" (runReplaceDirect instrSlice #[.slice sampleSliceA, .slice (mkSliceKey 4 3)]) .stkUnd }

    , { name := "unit/runtime/range/n-negative"
        run := do
          expectErr "unit/runtime/range/n-negative" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null (-1))) .rangeChk }

    , { name := "unit/runtime/range/n-too-large"
        run := do
          expectErr "unit/runtime/range/n-too-large" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 1024)) .rangeChk }

    , { name := "unit/runtime/type/slice-key-short"
        run := do
          expectErr "unit/runtime/type/slice-key-short" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 3 3) (.cell dictSlice4) 4)) .cellUnd }

    , { name := "unit/runtime/type/value-not-slice"
        run := do
          expectOkStack
            "unit/runtime/type/value-not-slice"
            (runReplaceDirect instrSlice (mkSliceStack sampleSliceA (mkSliceKey 4 3) (.cell dictSlice4) 4))
            #[.cell dictSlice4, intV (-1)] }

    , { name := "unit/runtime/type/value-not-cell"
        run := do
          expectErr "unit/runtime/type/value-not-cell" (runReplaceDirect instrSliceRef (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictRef4) 4)) .typeChk }

    , { name := "unit/runtime/type/dict-not-maybe-cell"
        run := do
          expectErr "unit/runtime/type/dict-not-maybe-cell" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.tuple #[]) 4)) .typeChk }

    , { name := "unit/runtime/dict-err"
        run := do
          expectErr "unit/runtime/dict-err" (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell malformedCell) 4)) .cellUnd }

    , { name := "unit/runtime/dict-err-ref"
        run := do
          expectErr "unit/runtime/dict-err-ref" (runReplaceDirect instrSliceRef (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell malformedCell) 4)) .cellUnd }

    , { name := "unit/runtime/inline-gas-coverage"
        run := do
          expectOkStack
            "unit/runtime/inline-gas-coverage"
            (runReplaceDirect instrSlice (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4))
            #[.null, intV 0] }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/underflow-empty" #[],
    mkCase "oracle/underflow-one" #[.slice sampleSliceA],
    mkCase "oracle/underflow-two" #[.slice sampleSliceA, .slice (mkSliceKey 4 3)],

    -- [B2]
    mkCase "oracle/range/n-negative" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null (-1)),
    mkCase "oracle/range/n-too-large" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 1024),
    mkCase "oracle/range/n-nan" #[(.slice sampleSliceD), (.slice (mkSliceKey 4 3)), .null, .int .nan],

    -- [B3]
    mkCase "oracle/key-short" (mkSliceStack sampleSliceD (mkSliceKey 3 3) (.cell dictSlice4) 4),
    mkCase "oracle/key-short-ref" (mkSliceStack sampleSliceD (mkSliceKey 3 3) (.cell dictRef4) 4),

    -- [B4]
    mkCase "oracle/type/value-not-slice" (mkSliceStack sampleSliceA (mkSliceKey 4 3) (.cell dictSlice4) 4),
    mkCase "oracle/type/value-not-cell" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictRef4) 4),
    mkCase "oracle/type/key-int" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4) (#[instrSigned]),

    -- [B5]
    mkCase "oracle/type/dict-not-maybe-cell" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.tuple #[]) 4),

    -- [B6]
    mkCase "oracle/slice-miss-null" (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4),
    mkCase "oracle/slice-miss-nonnull" (mkSliceStack sampleSliceD (mkSliceKey 4 2) (.cell dictSlice4) 4),
    mkCase "oracle/slice-hit" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4),
    mkCase "oracle/ref-hit" (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell dictRef4) 4) (#[instrSliceRef]),
    mkCase "oracle/zero-width-hit" (mkSliceStack sampleSliceD (mkSliceFromBits #[]) (.cell dictSlice0) 0),
    mkCase "oracle/zero-width-miss" (mkSliceStack sampleSliceD (mkSliceFromBits #[]) .null 0),

    -- [B7]
    mkCase "oracle/dict-err" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell malformedCell) 4),
    mkCase "oracle/dict-err-ref" (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell malformedCell) 4) (#[instrSliceRef]),

    -- [B8] [B9]
    mkCase "oracle/asm-valid-422" (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4) (#[instrSlice]),
    mkCase "oracle/asm-valid-423" (mkRefStack sampleCellB (mkSliceKey 4 3) (.cell dictRef4) 4) (#[instrSliceRef]),
    mkCodeCase "oracle/encode-invalid-unsigned" raw422,
    mkCodeCase "oracle/decode-422" raw422,
    mkCodeCase "oracle/decode-423" raw423,
    mkCodeCase "oracle/decode-421" raw421,
    mkCodeCase "oracle/decode-428" raw428,
    mkCodeCase "oracle/decode-truncated" rawF4,

    -- [B10] [B11]
    mkCase "oracle/gas/slice-miss-exact"
      (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasSlice instrSlice)
      (oracleGasLimitsExact missGasSlice),
    mkCase "oracle/gas/slice-miss-exact-minus-one"
      (mkSliceStack sampleSliceD (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasSliceMinusOne instrSlice)
      (oracleGasLimitsExact missGasSliceMinusOne),
    mkCase "oracle/gas/slice-hit-exact"
      (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4)
      (mkGasProgram hitGasSlice instrSlice)
      (oracleGasLimitsExact hitGasSlice),
    mkCase "oracle/gas/slice-hit-exact-minus-one"
      (mkSliceStack sampleSliceD (mkSliceKey 4 3) (.cell dictSlice4) 4)
      (mkGasProgram hitGasSliceMinusOne instrSlice)
      (oracleGasLimitsExact hitGasSliceMinusOne),
    mkCase "oracle/gas/ref-hit-exact"
      (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell dictRef4) 4)
      (mkGasProgram hitGasRef instrSliceRef)
      (oracleGasLimitsExact hitGasRef),
    mkCase "oracle/gas/ref-hit-exact-minus-one"
      (mkRefStack sampleCellC (mkSliceKey 4 3) (.cell dictRef4) 4)
      (mkGasProgram hitGasRefMinusOne instrSliceRef)
      (oracleGasLimitsExact hitGasRefMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTREPLACEFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREPLACE
