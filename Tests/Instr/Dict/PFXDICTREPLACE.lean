import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTREPLACE

/-
INSTRUCTION: PFXDICTREPLACE

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime preamble:
   - `execInstrDictExt` for `.pfxSet .replace` checks stack underflow (4 values).
   - Stack pop order is `newValue`, `key`, `dict`, `n`.
   - `n` is read with `popNatUpTo 1023`.
2. [B2] Range validation branch:
   - `n` must be in `0..1023`.
   - Negative, too-large, or NaN values for `n` raise `.rangeChk`.
3. [B3] Key-length bypass:
   - `keyBits.size > n` returns `(dict, false)` without touching dictionary nodes.
4. [B4] Type-path checks:
   - `key` must be a slice.
   - `newValue` must be a slice (not integer/cell).
   - `dict` must be `null` or a cell.
5. [B5] Replace semantics:
   - Empty/missing key: returns unchanged dictionary and `0`.
   - Hit: returns rebuilt dictionary and `-1`.
   - Prefix mismatch in a replace path returns unchanged dictionary with `0`.
6. [B6] Malformed dictionary structure:
   - `dictSetSliceWithCells` errors can raise `.dictErr` for invalid prefix-dictionary cells.
7. [B7] Assembler encoding:
   - `0xF471` is the only `.dictExt (.pfxSet .replace)` encoding.
   - All other `.dictSet ...` variants are encoding errors.
8. [B8] Decoder boundaries and aliasing:
   - `0xF470`, `0xF471`, `0xF472`, `0xF473` decode to `.pfxSet set`, `.pfxSet replace`, `.pfxSet add`, `.pfxDel` respectively.
   - `0xF46C` is invalid; truncation (e.g. `0xF4` with only 8 bits) is invalid.
9. [B9] Gas accounting:
   - Base gas from `computeExactGasBudget`.
   - Hit path adds `created * cellCreateGasPrice`; miss path uses base only.
10. [B10] Gas underflow:
    - Exact gas budget must pass; exact-minus-one budgets fail on corresponding paths.

TOTAL BRANCHES: 10
-/

private def pfxDictReplaceId : InstrId :=
  { name := "PFXDICTREPLACE" }

private def instrReplace : Instr := .dictExt (.pfxSet .replace)

private def raw471 : Cell :=
  Cell.mkOrdinary (natToBits 0xF471 16) #[]
private def raw470 : Cell :=
  Cell.mkOrdinary (natToBits 0xF470 16) #[]
private def raw472 : Cell :=
  Cell.mkOrdinary (natToBits 0xF472 16) #[]
private def raw473 : Cell :=
  Cell.mkOrdinary (natToBits 0xF473 16) #[]
private def raw46C : Cell :=
  Cell.mkOrdinary (natToBits 0xF46C 16) #[]
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

private def dictSlice4Replace : Cell :=
  match dictSetSliceWithCells (some dictSlice4) (requireBits "dictSlice4Replace" 3 4) sampleSliceD .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictSlice4Replace: unexpected"

private def dictRef4Replace : Cell :=
  match dictSetRefWithCells (some dictRef4) (requireBits "dictRef4Replace" 3 4) sampleCellD .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictRef4Replace: unexpected"

private def dictSlice0Replace : Cell :=
  match dictSetSliceWithCells (some dictSlice0) (requireBits "dictSlice0Replace" 0 0) sampleSliceD .replace with
  | .ok (some r, _, _, _) => r
  | _ => panic! "dictSlice0Replace: unexpected"

private def createdSliceHit : Nat :=
  replaceSliceCreated dictSlice4 4 3 sampleSliceD
private def createdRefHit : Nat :=
  replaceRefCreated dictRef4 4 3 sampleCellD
private def createdSliceZeroWidthHit : Nat :=
  replaceSliceCreated dictSlice0 0 0 sampleSliceD

private def baseGas : Int :=
  computeExactGasBudget instrReplace

private def missGas : Int := baseGas
private def missGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instrReplace

private def hitGasSlice : Int :=
  baseGas + Int.ofNat createdSliceHit * cellCreateGasPrice
private def hitGasRef : Int :=
  baseGas + Int.ofNat createdRefHit * cellCreateGasPrice
private def hitGasSliceMinusOne : Int :=
  if hitGasSlice > 0 then hitGasSlice - 1 else 0
private def hitGasRefMinusOne : Int :=
  if hitGasRef > 0 then hitGasRef - 1 else 0

private def hitGasZeroWidth : Int :=
  baseGas + Int.ofNat createdSliceZeroWidthHit * cellCreateGasPrice
private def hitGasZeroWidthMinusOne : Int :=
  if hitGasZeroWidth > 0 then hitGasZeroWidth - 1 else 0

private def mkSliceStack (value : Value) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[value, .slice key, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrReplace])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pfxDictReplaceId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (code : Cell)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pfxDictReplaceId
    codeCell? := some code
    initStack := stack
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

private def runPfxReplaceDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr pfxDictReplaceId

private def genPFXDICTREPLACEFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (randBool0, rng2) := randBool rng1
  if shape = 0 then
    (mkCase "fuzz/underflow-empty" #[], rng2) -- [B1]
  else if shape = 1 then
    (mkCase "fuzz/underflow-one" #[.cell sampleCellA], rng2) -- [B1]
  else if shape = 2 then
    (mkCase "fuzz/underflow-two" #[.slice sampleSliceA, .slice (mkSliceKey 4 3)], rng2) -- [B1]
  else if shape = 3 then
    (mkCase "fuzz/underflow-three" #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null], rng2) -- [B1]
  else if shape = 4 then
    (mkCase "fuzz/range/n-negative" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null (-1)), rng2) -- [B2]
  else if shape = 5 then
    (mkCase "fuzz/range/n-too-large" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 1024), rng2) -- [B2]
  else if shape = 6 then
    (mkCase "fuzz/range/n-nan" #[(.slice sampleSliceD), (.slice (mkSliceKey 4 3)), .null, .int .nan], rng2) -- [B2]
  else if shape = 7 then
    (mkCase "fuzz/key-too-long" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 2), rng2) -- [B3]
  else if shape = 8 then
    (mkCase "fuzz/slice/miss-null" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4), rng2) -- [B5]
  else if shape = 9 then
    (mkCase "fuzz/slice/miss-nonnull" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 6) (.cell dictSlice4) 4), rng2) -- [B5]
  else if shape = 10 then
    (mkCase "fuzz/slice/hit" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4), rng2) -- [B5]
  else if shape = 11 then
    (mkCase "fuzz/ref/hit" (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell dictRef4) 4), rng2) -- [B5]
  else if shape = 12 then
    (mkCase "fuzz/type/key-int" #[.slice sampleSliceD, .int (.num 77), .cell dictSlice4, intV 4], rng2) -- [B4]
  else if shape = 13 then
    (mkCase "fuzz/type/value-int" (mkSliceStack (.int (.num 77)) (mkSliceKey 4 3) (.cell dictSlice4) 4), rng2) -- [B4]
  else if shape = 14 then
    (mkCase "fuzz/type/dict-tuple" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.tuple #[]) 4), rng2) -- [B4]
  else if shape = 15 then
    (mkCase "fuzz/malformed-dict" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell malformedCell) 4), rng2) -- [B6]
  else if shape = 16 then
    (mkCase "fuzz/malformed-ref-dict" (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell malformedCell) 4), rng2) -- [B6]
  else if shape = 17 then
    (mkCase "fuzz/zero-width-hit" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0), rng2) -- [B5]
  else if shape = 18 then
    (mkCase "fuzz/zero-width-miss" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0), rng2) -- [B5]
  else if shape = 19 then
    (mkCodeCase "fuzz/decode/471" raw471 (#[.slice sampleSliceD]), rng2) -- [B8]
  else if shape = 20 then
    (mkCodeCase "fuzz/decode/470" raw470 (#[]), rng2) -- [B8]
  else if shape = 21 then
    (mkCodeCase "fuzz/decode/472" raw472 (#[]), rng2) -- [B8]
  else if shape = 22 then
    (mkCodeCase "fuzz/decode/473" raw473 (#[]), rng2) -- [B8]
  else if shape = 23 then
    (mkCodeCase "fuzz/decode/46c" raw46C (#[]), rng2) -- [B8]
  else if shape = 24 then
    (mkCodeCase "fuzz/decode/truncated" rawF4 (#[]), rng2) -- [B8]
  else if shape = 25 then
    (mkCase "fuzz/gas/miss-slice-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGas instrReplace) (oracleGasLimitsExact missGas), rng2) -- [B9] [B10]
  else if shape = 26 then
    (mkCase "fuzz/gas/miss-slice-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasMinusOne instrReplace) (oracleGasLimitsExact missGasMinusOne), rng2) -- [B10]
  else if shape = 27 then
    if randBool0 then
      (mkCase "fuzz/gas/hit-slice-exact"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
        (mkGasProgram hitGasSlice instrReplace) (oracleGasLimitsExact hitGasSlice), rng2) -- [B9] [B10]
    else
      (mkCase "fuzz/gas/hit-ref-exact"
        (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell dictRef4) 4)
        (mkGasProgram hitGasRef instrReplace) (oracleGasLimitsExact hitGasRef), rng2) -- [B9] [B10]
  else if shape = 28 then
    if randBool0 then
      (mkCase "fuzz/gas/hit-slice-minus-one"
        (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
        (mkGasProgram hitGasSliceMinusOne instrReplace) (oracleGasLimitsExact hitGasSliceMinusOne), rng2) -- [B10]
    else
      (mkCase "fuzz/gas/hit-ref-minus-one"
        (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell dictRef4) 4)
        (mkGasProgram hitGasRefMinusOne instrReplace) (oracleGasLimitsExact hitGasRefMinusOne), rng2) -- [B10]
  else if shape = 29 then
    (mkCase "fuzz/gas/hit-zero-width-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0)
      (mkGasProgram hitGasZeroWidth instrReplace) (oracleGasLimitsExact hitGasZeroWidth), rng2) -- [B9] [B10]
  else if shape = 30 then
    (mkCase "fuzz/gas/hit-zero-width-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0)
      (mkGasProgram hitGasZeroWidthMinusOne instrReplace) (oracleGasLimitsExact hitGasZeroWidthMinusOne), rng2) -- [B10]
  else
    (mkCase "fuzz/asm-invalid" #[], rng2) -- [B7]

def suite : InstrSuite where
  id := pfxDictReplaceId
  unit := #[
    { name := "unit/asm/valid/471"
      run := do
        match assembleCp0 [instrReplace] with
        | .ok c =>
            if c.bits = raw471.bits then
              pure ()
            else
              throw (IO.userError "unit/asm/valid/471: wrong opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/valid/471: expected success, got {e}") }

    , { name := "unit/asm/invalid/dict-set"
        run := do
          expectAssembleErr "unit/asm/invalid/dict-set" .invOpcode (.dictSet false true false .replace) }

    , { name := "unit/decode/valid/471"
        run := do
          let s : Slice := Slice.ofCell raw471
          let _ ← expectDecodeStep "unit/decode/471" s instrReplace 16
          pure () }

    , { name := "unit/decode/alias/470"
        run := do
          expectDecodeStepPair "unit/decode/470" raw470 (.dictExt (.pfxSet .set)) }

    , { name := "unit/decode/alias/472"
        run := do
          expectDecodeStepPair "unit/decode/472" raw472 (.dictExt (.pfxSet .add)) }

    , { name := "unit/decode/alias/473"
        run := do
          expectDecodeStepPair "unit/decode/473" raw473 (.dictExt .pfxDel) }

    , { name := "unit/decode/adjacent/46c"
        run := do
          expectDecodeInv "unit/decode/46c" raw46C
          expectDecodeInv "unit/decode/truncated" rawF4
          pure () }

    , { name := "unit/runtime/slice-hit"
        run := do
          expectOkStack
            "unit/runtime/slice-hit"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4))
            #[.cell dictSlice4Replace, intV (-1)] }

    , { name := "unit/runtime/slice-miss-null"
        run := do
          expectOkStack
            "unit/runtime/slice-miss-null"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4))
            #[.null, intV 0] }

    , { name := "unit/runtime/slice-miss-nonnull"
        run := do
          expectOkStack
            "unit/runtime/slice-miss-nonnull"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 6) (.cell dictSlice4) 4))
            #[.cell dictSlice4, intV 0] }

    , { name := "unit/runtime/ref-hit"
        run := do
          expectOkStack
            "unit/runtime/ref-hit"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell dictRef4) 4))
            #[.cell dictRef4Replace, intV (-1)] }

    , { name := "unit/runtime/key-too-long"
        run := do
          expectOkStack
            "unit/runtime/key-too-long"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 2))
            #[.cell dictSlice4, intV 0] }

    , { name := "unit/runtime/zero-width-hit"
        run := do
          expectOkStack
            "unit/runtime/zero-width-hit"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0))
            #[.cell dictSlice0Replace, intV (-1)] }

    , { name := "unit/runtime/zero-width-miss"
        run := do
          expectOkStack
            "unit/runtime/zero-width-miss"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0))
            #[.null, intV 0] }

    , { name := "unit/runtime/underflow-empty"
        run := do
          expectErr "unit/runtime/underflow-empty" (runPfxReplaceDirect instrReplace #[]) .stkUnd }

    , { name := "unit/runtime/underflow-three"
        run := do
          expectErr "unit/runtime/underflow-three" (runPfxReplaceDirect instrReplace #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null]) .stkUnd }

    , { name := "unit/runtime/type/key-int"
        run := do
          expectErr "unit/runtime/type/key-int"
            (runPfxReplaceDirect instrReplace #[.slice sampleSliceA, .int (.num 77), .cell dictSlice4, intV 4])
            .typeChk }

    , { name := "unit/runtime/type/value-int"
        run := do
          expectErr "unit/runtime/type/value-int"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.int (.num 77)) (mkSliceKey 4 3) (.cell dictSlice4) 4))
            .typeChk }

    , { name := "unit/runtime/type/dict-tuple"
        run := do
          expectErr "unit/runtime/type/dict-tuple"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.tuple #[]) 4))
            .typeChk }

    , { name := "unit/runtime/dict-err"
        run := do
          expectErr "unit/runtime/dict-err"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell malformedCell) 4))
            .dictErr }

    , { name := "unit/runtime/range/n-negative"
        run := do
          expectErr "unit/runtime/range/n-negative"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null (-1)))
            .rangeChk }

    , { name := "unit/runtime/range/n-too-large"
        run := do
          expectErr "unit/runtime/range/n-too-large"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 1024))
            .rangeChk }

    , { name := "unit/runtime/range/n-nan"
        run := do
          expectErr "unit/runtime/range/n-nan"
            (runPfxReplaceDirect instrReplace #[(.slice sampleSliceD), (.slice (mkSliceKey 4 3)), .null, .int .nan])
            .rangeChk
        }

    , { name := "unit/runtime/dict-err-ref"
        run := do
          expectErr "unit/runtime/dict-err-ref"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell malformedCell) 4))
            .dictErr }

    , { name := "unit/runtime/inline-gas-coverage"
        run := do
          expectOkStack
            "unit/runtime/inline-gas-coverage"
            (runPfxReplaceDirect instrReplace (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4))
            #[.null, intV 0] }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/underflow-empty" #[],
    mkCase "oracle/underflow-one" #[.slice sampleSliceA],
    mkCase "oracle/underflow-two" #[.slice sampleSliceA, .slice (mkSliceKey 4 3)],
    mkCase "oracle/underflow-three" #[.slice sampleSliceA, .slice (mkSliceKey 4 3), .null],

    -- [B2]
    mkCase "oracle/range/n-negative" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null (-1)),
    mkCase "oracle/range/n-too-large" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 1024),
    mkCase "oracle/range/n-nan" #[(.slice sampleSliceD), (.slice (mkSliceKey 4 3)), .null, .int .nan],

    -- [B3]
    mkCase "oracle/key-too-long" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 2),

    -- [B4]
    mkCase "oracle/type/key-int" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits (natToBits 3 4)) (.cell dictSlice4) 4),
    mkCase "oracle/type/value-int" (mkSliceStack (.int (.num 77)) (mkSliceKey 4 3) (.cell dictSlice4) 4),
    mkCase "oracle/type/dict-tuple" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.tuple #[]) 4),

    -- [B5]
    mkCase "oracle/slice-miss-null" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4),
    mkCase "oracle/slice-miss-nonnull" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 6) (.cell dictSlice4) 4),
    mkCase "oracle/slice-hit" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4),
    mkCase "oracle/ref-hit" (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell dictRef4) 4),
    mkCase "oracle/zero-width-hit" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0),
    mkCase "oracle/zero-width-miss" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) .null 0),
    mkCase "oracle/type/key-int-short" #[.slice sampleSliceD, .cell sampleCellA, .cell dictSlice4, intV 4],

    -- [B6]
    mkCase "oracle/dict-err" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell malformedCell) 4),
    mkCase "oracle/dict-err-ref" (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell malformedCell) 4),

    -- [B7]
    mkCodeCase "oracle/decode/471" raw471,
    mkCodeCase "oracle/decode/470" raw470,
    mkCodeCase "oracle/decode/472" raw472,
    mkCodeCase "oracle/decode/473" raw473,
    mkCodeCase "oracle/decode/46c" raw46C,
    mkCodeCase "oracle/decode/truncated" rawF4,

    -- [B9]
    mkCase "oracle/gas-miss-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGas instrReplace)
      (oracleGasLimitsExact missGas),
    mkCase "oracle/gas-hit-slice-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
      (mkGasProgram hitGasSlice instrReplace)
      (oracleGasLimitsExact hitGasSlice),
    mkCase "oracle/gas-hit-ref-exact"
      (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell dictRef4) 4)
      (mkGasProgram hitGasRef instrReplace)
      (oracleGasLimitsExact hitGasRef),
    mkCase "oracle/gas-hit-zero-width-exact"
      (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0)
      (mkGasProgram hitGasZeroWidth instrReplace)
      (oracleGasLimitsExact hitGasZeroWidth),

    -- [B10]
    mkCase "oracle/gas-miss-exact-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) .null 4)
      (mkGasProgram missGasMinusOne instrReplace)
      (oracleGasLimitsExact missGasMinusOne),
    mkCase "oracle/gas-hit-slice-exact-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceKey 4 3) (.cell dictSlice4) 4)
      (mkGasProgram hitGasSliceMinusOne instrReplace)
      (oracleGasLimitsExact hitGasSliceMinusOne),
    mkCase "oracle/gas-hit-ref-exact-minus-one"
      (mkSliceStack (.cell sampleCellD) (mkSliceKey 4 3) (.cell dictRef4) 4)
      (mkGasProgram hitGasRefMinusOne instrReplace)
      (oracleGasLimitsExact hitGasRefMinusOne),
    mkCase "oracle/gas-hit-zero-width-exact-minus-one"
      (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0)
      (mkGasProgram hitGasZeroWidthMinusOne instrReplace)
      (oracleGasLimitsExact hitGasZeroWidthMinusOne),

    -- [B2] Extra boundary for type conversion parity
    mkCase "oracle/range-maximum-n" (mkSliceStack (.slice sampleSliceD) (mkSliceKey 3 5) (.cell dictSlice4) 1023),
    mkCase "oracle/range-zero-n" (mkSliceStack (.slice sampleSliceD) (mkSliceFromBits #[]) (.cell dictSlice0) 0)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genPFXDICTREPLACEFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTREPLACE
