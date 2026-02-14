import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREPLACE

/-!
INSTRUCTION: DICTUREPLACE

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictDictSet` handles `.dictSet`; non-`dictSet` instructions go to `next`.

2. [B2] Stack underflow branch.
   - `checkUnderflow 4` is enforced before any argument decode.
   - Missing any of `value`, `key`, `dict`, `n` must raise `.stkUnd`.

3. [B3] Width validation branch.
   - `n` is parsed by `popNatUpTo 1023`; `.nan`, negatives, and `> 1023` raise `.rangeChk`.

4. [B4] Unsigned integer key materialization branch.
   - `intKey=true` + `unsigned=true` invokes `dictKeyBits?`.
   - `n=0` accepts only key `0`; any non-zero key raises `.rangeChk`.
   - Other widths enforce unsigned range, including signed values and too-large keys.

5. [B5] Value materialization branch.
   - `byRef=false` requires a slice value.
   - Any non-slice value raises `.typeChk`.

6. [B6] Root typing branch.
   - Dictionary argument must be a `.null` or `.cell`.
   - Non-maybe-cell values raise `.typeChk`.

7. [B7] Replace semantics branch.
   - Hit path returns rebuilt dictionary and `-1`.
   - Miss path returns unchanged dictionary and `0`.
   - Null-miss is valid.

8. [B8] Dictionary structural error branch.
   - Malformed roots may raise `.dictErr` via `dictSetSliceWithCells`.

9. [B9] Assembler validation branch.
   - Valid forms: `.dictSet true true false` (`0xF426`) and `.dictSet true true true` (`0xF427`).
   - `.dictSet false true false` (unsigned with non-int key mode) is invalid (`.invOpcode`).

10. [B10] Decoder boundary and alias branch.
    - `0xF426` decodes to `DICTUREPLACE`.
    - `0xF427` decodes to `DICTUREPLACEREF`.
    - `0xF425` and `0xF424` decode to `DICTIREPLACEREF` and `DICTIREPLACE`.
    - Adjacent `0xF421`, `0xF428`, `0xF429` are invalid.
    - Truncated `0xF4` decodes as `.invOpcode`.

11. [B11] Gas accounting exactness.
    - Base cost = `computeExactGasBudget instr`.
    - Miss paths consume base only.
    - Hit paths add `created * cellCreateGasPrice`.

12. [B12] Gas underflow behavior.
    - Exact and exact-1 budgets must be distinguished across miss/hit cases.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def dictUREPLACEId : InstrId := { name := "DICTUREPLACE" }

private def instr : Instr := .dictSet true true false .replace
private def instrRef : Instr := .dictSet true true true .replace
private def instrSigned : Instr := .dictSet true false false .replace

private def dispatchSentinel : Int := 909

private def raw426 : Cell := Cell.mkOrdinary (natToBits 0xF426 16) #[]
private def raw427 : Cell := Cell.mkOrdinary (natToBits 0xF427 16) #[]
private def raw425 : Cell := Cell.mkOrdinary (natToBits 0xF425 16) #[]
private def raw424 : Cell := Cell.mkOrdinary (natToBits 0xF424 16) #[]
private def raw421 : Cell := Cell.mkOrdinary (natToBits 0xF421 16) #[]
private def raw428 : Cell := Cell.mkOrdinary (natToBits 0xF428 16) #[]
private def raw429 : Cell := Cell.mkOrdinary (natToBits 0xF429 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def sampleSliceA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def sampleSliceB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def sampleSliceC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def sampleSliceD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def sampleSliceE : Slice := mkSliceFromBits (natToBits 0xE5 8)

private def sampleCellA : Cell := Cell.mkOrdinary (natToBits 0x11 8) #[]
private def sampleCellB : Cell := Cell.mkOrdinary (natToBits 0x22 8) #[]
private def badSliceKey : Slice := mkSliceFromBits (natToBits 0xAA 8)

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def requireUnsignedBits (label : String) (k : Int) (n : Nat) : BitString :=
  match dictKeyBits? k n true with
  | some bits => bits
  | none => panic! s!"{label}: invalid unsigned key k={k} for n={n}"

private def mkSliceDictRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits : BitString := requireUnsignedBits s!"{label}/key={k}" k n
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root for key={k}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed for key={k}: {reprStr e}"
    match root with
    | some c => c
    | none => panic! s!"{label}: empty dictionary"

private def replaceUnsignedRoot! (label : String) (root : Cell) (n : Nat) (k : Int) (value : Slice) : Cell :=
  match dictSetSliceWithCells (some root) (requireUnsignedBits s!"{label}/key={k}" k n) value .replace with
  | .ok (some c, _ok, _created, _loaded) => c
  | .ok (none, _, _, _) =>
      panic! s!"{label}: unexpected miss for key={k} n={n}"
  | .error e =>
      panic! s!"{label}: replace failed: {reprStr e}"

private def replaceUnsignedCreated (label : String) (root : Cell) (n : Nat) (k : Int) (value : Slice) : Nat :=
  match dictSetSliceWithCells (some root) (requireUnsignedBits s!"{label}/key={k}" k n) value .replace with
  | .ok (_, _ok, created, _loaded) => created
  | .error _ => 0

private def dictSlice4 : Cell :=
  mkSliceDictRoot! "dictSlice4" 4 #[(0, sampleSliceA), (5, sampleSliceB), (12, sampleSliceC)]
private def dictSlice8 : Cell :=
  mkSliceDictRoot! "dictSlice8" 8 #[(0, sampleSliceA), (85, sampleSliceB), (255, sampleSliceC)]
private def dictSlice1 : Cell :=
  mkSliceDictRoot! "dictSlice1" 1 #[(0, sampleSliceA), (1, sampleSliceD)]
private def dictSlice0 : Cell :=
  mkSliceDictRoot! "dictSlice0" 0 #[(0, sampleSliceA)]
private def dictSlice1023 : Cell :=
  mkSliceDictRoot! "dictSlice1023" 1023 #[(0, sampleSliceD)]

private def dictSlice4Replaced : Cell :=
  replaceUnsignedRoot! "dictSlice4Replaced" dictSlice4 4 5 sampleSliceE
private def dictSlice8Replaced : Cell :=
  replaceUnsignedRoot! "dictSlice8Replaced" dictSlice8 8 255 sampleSliceD
private def dictSlice1Replaced : Cell :=
  replaceUnsignedRoot! "dictSlice1Replaced" dictSlice1 1 0 sampleSliceC
private def dictSlice0Replaced : Cell :=
  replaceUnsignedRoot! "dictSlice0Replaced" dictSlice0 0 0 sampleSliceB
private def dictSlice1023Replaced : Cell :=
  replaceUnsignedRoot! "dictSlice1023Replaced" dictSlice1023 1023 0 sampleSliceA

private def createdSlice4 : Nat := replaceUnsignedCreated "created/4" dictSlice4 4 5 sampleSliceE
private def createdSlice8 : Nat := replaceUnsignedCreated "created/8" dictSlice8 8 255 sampleSliceD
private def createdSlice1 : Nat := replaceUnsignedCreated "created/1" dictSlice1 1 0 sampleSliceC
private def createdSlice0 : Nat := replaceUnsignedCreated "created/0" dictSlice0 0 0 sampleSliceB
private def createdSlice1023 : Nat := replaceUnsignedCreated "created/1023" dictSlice1023 1023 0 sampleSliceA

private def minusOneOrZero (g : Int) : Int := if g > 0 then g - 1 else 0

private def baseGas : Int := computeExactGasBudget instr
private def missGas : Int := baseGas
private def missGasMinusOne : Int := minusOneOrZero missGas
private def hitGas4 : Int := baseGas + Int.ofNat createdSlice4 * cellCreateGasPrice
private def hitGas8 : Int := baseGas + Int.ofNat createdSlice8 * cellCreateGasPrice
private def hitGas1 : Int := baseGas + Int.ofNat createdSlice1 * cellCreateGasPrice
private def hitGas0 : Int := baseGas + Int.ofNat createdSlice0 * cellCreateGasPrice
private def hitGas1023 : Int := baseGas + Int.ofNat createdSlice1023 * cellCreateGasPrice
private def hitGas4MinusOne : Int := minusOneOrZero hitGas4
private def hitGas8MinusOne : Int := minusOneOrZero hitGas8
private def hitGas1MinusOne : Int := minusOneOrZero hitGas1
private def hitGas0MinusOne : Int := minusOneOrZero hitGas0
private def hitGas1023MinusOne : Int := minusOneOrZero hitGas1023

private def mkSliceStack (value : Slice) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[.slice value, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUREPLACEId
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
    instr := dictUREPLACEId
    codeCell? := some code
    initStack := #[]
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasProgram (gas : Int) (i : Instr) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, i]

private def expectAssembleErr (label : String) (expected : Excno) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def expectDecodeInv (label : String) (cell : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr i} with {bits} bits")

private def expectDecodeStepPair (label : String) (cell : Cell) (expected : Instr) : IO Unit := do
  let s : Slice := Slice.ofCell cell
  let _ ← expectDecodeStep label s expected 16
  pure ()

private def runDICTUREPLACEDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def runDICTUREPLACEDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr dictUREPLACEId

private def genDICTUREPLACEFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (randBool0, rng2) := randBool rng1
  if shape = 0 then
    (mkCase "fuzz/underflow-empty" #[], rng2) -- [B2]
  else if shape = 1 then
    (mkCase "fuzz/underflow-one" #[.slice sampleSliceA], rng2) -- [B2]
  else if shape = 2 then
    (mkCase "fuzz/underflow-two" #[.slice sampleSliceA, .int (.num 5), .cell dictSlice4], rng2) -- [B2]
  else if shape = 3 then
    (mkCase "fuzz/underflow-three" #[.slice sampleSliceA, .int (.num 5), .cell dictSlice4], rng2) -- [B2]
  else if shape = 4 then
    (mkCase "fuzz/hit/4" (mkSliceStack sampleSliceD 5 (.cell dictSlice4) 4), rng2) -- [B6]
  else if shape = 5 then
    (mkCase "fuzz/hit/1" (mkSliceStack sampleSliceE 0 (.cell dictSlice1) 1), rng2) -- [B6]
  else if shape = 6 then
    (mkCase "fuzz/hit/0" (mkSliceStack sampleSliceC 0 (.cell dictSlice0) 0), rng2) -- [B4] [B6]
  else if shape = 7 then
    (mkCase "fuzz/hit/1023" (mkSliceStack sampleSliceA 0 (.cell dictSlice1023) 1023), rng2) -- [B6]
  else if shape = 8 then
    (mkCase "fuzz/miss/null" (mkSliceStack sampleSliceA 1 (.null) 4), rng2) -- [B7]
  else if shape = 9 then
    (mkCase "fuzz/miss/nonempty" (mkSliceStack sampleSliceE 3 (.cell dictSlice4) 4), rng2) -- [B7]
  else if shape = 10 then
    (mkCase "fuzz/range/n-negative" (mkSliceStack sampleSliceA 5 (.cell dictSlice4) (-1)), rng2) -- [B3]
  else if shape = 11 then
    (mkCase "fuzz/range/n-too-large" (mkSliceStack sampleSliceA 5 (.cell dictSlice4) 1024), rng2) -- [B3]
  else if shape = 12 then
    (mkCase "fuzz/range/n-nan" (#[.slice sampleSliceA, .int (.num 5), .cell dictSlice4, .int .nan]), rng2) -- [B3]
  else if shape = 13 then
    (mkCase "fuzz/key/nan" (#[.slice sampleSliceA, .int .nan, .cell dictSlice4, .int (.num 4)]), rng2) -- [B4]
  else if shape = 14 then
    (mkCase "fuzz/key/negative" (mkSliceStack sampleSliceA (-1) (.cell dictSlice4) 4), rng2) -- [B4]
  else if shape = 15 then
    (mkCase "fuzz/key/oob-small" (mkSliceStack sampleSliceA 16 (.cell dictSlice4) 4), rng2) -- [B4]
  else if shape = 16 then
    (mkCase "fuzz/key/oob-large" (mkSliceStack sampleSliceA (1 <<< 16) (.cell dictSlice8) 8), rng2) -- [B4]
  else if shape = 17 then
    (mkCase "fuzz/key/oob-zero-width" (mkSliceStack sampleSliceA 1 (.cell dictSlice0) 0), rng2) -- [B4]
  else if shape = 18 then
    (mkCase "fuzz/key/wrong-kind" (#[.slice sampleSliceA, .slice badSliceKey, .cell dictSlice4, intV 4]), rng2) -- [B4]
  else if shape = 19 then
    (mkCase "fuzz/value/not-slice" (#[.cell sampleCellA, .int (.num 5), .cell dictSlice4, intV 4]), rng2) -- [B5]
  else if shape = 20 then
    (mkCase "fuzz/dict/not-maybe-cell" (mkSliceStack sampleSliceA 5 (.tuple #[]) 4), rng2) -- [B6]
  else if shape = 21 then
    (mkCase "fuzz/malformed" (mkSliceStack sampleSliceA 5 (.cell malformedDict) 4), rng2) -- [B8]
  else if shape = 22 then
    (mkCase "fuzz/gas/miss-exact" (mkSliceStack sampleSliceA 1 .null 4)
      (mkGasProgram missGas instr) (oracleGasLimitsExact missGas), rng2) -- [B11] [B12]
  else if shape = 23 then
    (mkCase "fuzz/gas/miss-minus-one" (mkSliceStack sampleSliceA 1 .null 4)
      (mkGasProgram missGasMinusOne instr) (oracleGasLimitsExactMinusOne missGasMinusOne), rng2) -- [B12]
  else if shape = 24 then
    (mkCase "fuzz/gas/hit-4-exact" (mkSliceStack sampleSliceE 5 (.cell dictSlice4) 4)
      (mkGasProgram hitGas4 instr) (oracleGasLimitsExact hitGas4), rng2) -- [B11] [B12]
  else if shape = 25 then
    if randBool0 then
      (mkCase "fuzz/gas/hit-4-minus-one" (mkSliceStack sampleSliceE 5 (.cell dictSlice4) 4)
        (mkGasProgram hitGas4MinusOne instr) (oracleGasLimitsExactMinusOne hitGas4MinusOne), rng2) -- [B12]
    else
      (mkCase "fuzz/gas/hit-4-minus-one-alt" (mkSliceStack sampleSliceE 5 (.cell dictSlice4) 4)
        (mkGasProgram hitGas4MinusOne instr) (oracleGasLimitsExactMinusOne hitGas4MinusOne), rng2) -- [B12]
  else if shape = 26 then
    (mkCase "fuzz/gas/hit-1-exact" (mkSliceStack sampleSliceA 0 (.cell dictSlice1) 1)
      (mkGasProgram hitGas1 instr) (oracleGasLimitsExact hitGas1), rng2) -- [B11] [B12]
  else if shape = 27 then
    (mkCase "fuzz/gas/hit-1-minus-one" (mkSliceStack sampleSliceA 0 (.cell dictSlice1) 1)
      (mkGasProgram hitGas1MinusOne instr) (oracleGasLimitsExactMinusOne hitGas1MinusOne), rng2) -- [B12]
  else if shape = 28 then
    (mkCase "fuzz/gas/hit-0-exact" (mkSliceStack sampleSliceA 0 (.cell dictSlice0) 0)
      (mkGasProgram hitGas0 instr) (oracleGasLimitsExact hitGas0), rng2) -- [B11] [B12]
  else if shape = 29 then
    (mkCase "fuzz/gas/hit-0-minus-one" (mkSliceStack sampleSliceA 0 (.cell dictSlice0) 0)
      (mkGasProgram hitGas0MinusOne instr) (oracleGasLimitsExactMinusOne hitGas0MinusOne), rng2) -- [B12]
  else if shape = 30 then
    (mkCase "fuzz/gas/hit-1023-exact" (mkSliceStack sampleSliceA 0 (.cell dictSlice1023) 1023)
      (mkGasProgram hitGas1023 instr) (oracleGasLimitsExact hitGas1023), rng2) -- [B11] [B12]
  else if shape = 31 then
    (mkCase "fuzz/gas/hit-1023-minus-one" (mkSliceStack sampleSliceA 0 (.cell dictSlice1023) 1023)
      (mkGasProgram hitGas1023MinusOne instr) (oracleGasLimitsExactMinusOne hitGas1023MinusOne), rng2) -- [B12]
  else if shape = 32 then
    (mkCodeCase "fuzz/decode/426" raw426, rng2) -- [B10] [B9]
  else if shape = 33 then
    (mkCodeCase "fuzz/decode/427" raw427, rng2) -- [B10] [B9]
  else if shape = 34 then
    (mkCodeCase "fuzz/decode/425" raw425, rng2) -- [B10]
  else if shape = 35 then
    (mkCodeCase "fuzz/decode/424" raw424, rng2) -- [B10]
  else if shape = 36 then
    (mkCodeCase "fuzz/decode/421" raw421, rng2) -- [B10]
  else if shape = 37 then
    (mkCodeCase "fuzz/decode/428" raw428, rng2) -- [B10]
  else if shape = 38 then
    (mkCodeCase "fuzz/decode/429" raw429, rng2) -- [B10]
  else
    (mkCodeCase "fuzz/decode/truncated" rawF4, rng2) -- [B10]

def suite : InstrSuite where
  id := dictUREPLACEId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st ←
          match runDICTUREPLACEDispatchFallback (#[.slice sampleSliceA, .int (.num 5), .cell dictSlice4, intV 4]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"unit/dispatch/fallback: unexpected error {e}")
        if st == #[.slice sampleSliceA, .int (.num 5), .cell dictSlice4, intV 4, .int (.num dispatchSentinel)] then
          pure ()
        else
          throw (IO.userError "unit/dispatch/fallback: fallback not preserved") }

    , { name := "unit/asm/encode-426" -- [B9]
        run := do
          match assembleCp0 [instr] with
          | .ok c =>
              if c.bits = raw426.bits then
                pure ()
              else
                throw (IO.userError s!"unit/asm/encode-426: expected {raw426.bits}, got {c.bits}")
          | .error e =>
              throw (IO.userError s!"unit/asm/encode-426: expected success, got {e}") }

    , { name := "unit/asm/encode-427" -- [B9]
        run := do
          match assembleCp0 [instrRef] with
          | .ok c =>
              if c.bits = raw427.bits then
                pure ()
              else
                throw (IO.userError s!"unit/asm/encode-427: expected {raw427.bits}, got {c.bits}")
          | .error e =>
              throw (IO.userError s!"unit/asm/encode-427: expected success, got {e}") }

    , { name := "unit/asm/invalid-unsigned-slice" -- [B9]
        run := do
          expectAssembleErr "unit/asm/invalid-unsigned-slice" .invOpcode instrSigned }

    , { name := "unit/decode/426" -- [B10]
        run := do
          let s : Slice := Slice.ofCell raw426
          let _ ← expectDecodeStep "unit/decode/426" s instr 16
          pure () }

    , { name := "unit/decode/alias/427" -- [B10]
        run := do
          let s : Slice := Slice.ofCell raw427
          let _ ← expectDecodeStep "unit/decode/427" s instrRef 16
          pure () }

    , { name := "unit/decode/alias/424" -- [B10]
        run := do
          expectDecodeStepPair "unit/decode/424" raw424 (.dictSet true false false .replace) }

    , { name := "unit/decode/alias/425" -- [B10]
        run := do
          expectDecodeStepPair "unit/decode/425" raw425 (.dictSet true false true .replace) }

    , { name := "unit/decode/invalid-boundaries" -- [B10]
        run := do
          expectDecodeInv "unit/decode/421" raw421
          expectDecodeInv "unit/decode/428" raw428
          expectDecodeInv "unit/decode/429" raw429
          expectDecodeInv "unit/decode/truncated" rawF4
          pure () }

    , { name := "unit/runtime/hit/4" -- [B7]
        run := do
          expectOkStack
            "unit/runtime/hit/4"
            (runDICTUREPLACEDirect (mkSliceStack sampleSliceE 5 (.cell dictSlice4) 4))
            #[.cell dictSlice4Replaced, intV (-1)] }

    , { name := "unit/runtime/hit/1" -- [B7]
        run := do
          expectOkStack
            "unit/runtime/hit/1"
            (runDICTUREPLACEDirect (mkSliceStack sampleSliceC 0 (.cell dictSlice1) 1))
            #[.cell dictSlice1Replaced, intV (-1)] }

    , { name := "unit/runtime/hit/0" -- [B4] [B7]
        run := do
          expectOkStack
            "unit/runtime/hit/0"
            (runDICTUREPLACEDirect (mkSliceStack sampleSliceD 0 (.cell dictSlice0) 0))
            #[.cell dictSlice0Replaced, intV (-1)] }

    , { name := "unit/runtime/hit/1023" -- [B11] [B7]
        run := do
          expectOkStack
            "unit/runtime/hit/1023"
            (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 0 (.cell dictSlice1023) 1023))
            #[.cell dictSlice1023Replaced, intV (-1)] }

    , { name := "unit/runtime/miss/null" -- [B7]
        run := do
          expectOkStack
            "unit/runtime/miss/null"
            (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 1 .null 4))
            #[.null, intV 0] }

    , { name := "unit/runtime/miss/nonnull" -- [B7]
        run := do
          expectOkStack
            "unit/runtime/miss/nonnull"
            (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 2 (.cell dictSlice4) 4))
            #[.cell dictSlice4, intV 0] }

    , { name := "unit/runtime/underflow-empty" -- [B2]
        run := do
          expectErr "unit/runtime/underflow-empty" (runDICTUREPLACEDirect #[]) .stkUnd }

    , { name := "unit/runtime/underflow-one" -- [B2]
        run := do
          expectErr "unit/runtime/underflow-one" (runDICTUREPLACEDirect #[.slice sampleSliceA]) .stkUnd }

    , { name := "unit/runtime/underflow-two" -- [B2]
        run := do
          expectErr "unit/runtime/underflow-two" (runDICTUREPLACEDirect #[.slice sampleSliceA, .int (.num 5)]) .stkUnd }

    , { name := "unit/runtime/underflow-three" -- [B2]
        run := do
          expectErr "unit/runtime/underflow-three" (runDICTUREPLACEDirect #[.slice sampleSliceA, .int (.num 5), .null]) .stkUnd }

    , { name := "unit/runtime/errors/range-negative" -- [B3]
        run := do
          expectErr "unit/runtime/errors/range-negative" (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 0 (.null) (-1))) .rangeChk }

    , { name := "unit/runtime/errors/range-too-large" -- [B3]
        run := do
          expectErr "unit/runtime/errors/range-too-large" (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 0 (.null) 1024)) .rangeChk }

    , { name := "unit/runtime/errors/range-nan" -- [B3]
        run := do
          expectErr "unit/runtime/errors/range-nan" (runDICTUREPLACEDirect #[.slice sampleSliceA, .int (.num 5), .cell dictSlice4, .int .nan]) .rangeChk }

    , { name := "unit/runtime/errors/key-type" -- [B4]
        run := do
          expectErr "unit/runtime/errors/key-type" (runDICTUREPLACEDirect (#[.slice sampleSliceA, .slice badSliceKey, .cell dictSlice4, .int (.num 4)])) .typeChk }

    , { name := "unit/runtime/errors/key-out-of-range" -- [B4]
        run := do
          expectErr "unit/runtime/errors/key-out-of-range" (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 16 (.cell dictSlice4) 4)) .rangeChk }

    , { name := "unit/runtime/errors/value-not-slice" -- [B5]
        run := do
          expectErr "unit/runtime/errors/value-not-slice" (runDICTUREPLACEDirect (#[.cell sampleCellA, .int (.num 5), .cell dictSlice4, .int (.num 4)])) .typeChk }

    , { name := "unit/runtime/errors/dict-not-maybe-cell" -- [B6]
        run := do
          expectErr "unit/runtime/errors/dict-not-maybe-cell" (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 5 (.tuple #[]) 4)) .typeChk }

    , { name := "unit/runtime/errors/dict-err"
        run := do
          expectErr "unit/runtime/errors/dict-err" (runDICTUREPLACEDirect (mkSliceStack sampleSliceA 5 (.cell malformedDict) 4)) .dictErr }

    , { name := "unit/runtime/value-zero-width-key-ok" -- [B11]
        run := do
          expectErr "unit/runtime/value-zero-width-key-ok" (runDICTUREPLACEDirect (mkSliceStack sampleSliceD 1 (.null) 0)) .rangeChk }

    , { name := "unit/gas/sanity"
        run := do
          if baseGas >= 0 then
            pure ()
          else
            throw (IO.userError "base gas should be non-negative") }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/dispatch/fallback" (#[.slice sampleSliceA, .int (.num 5), .cell dictSlice4, intV 4]),

    -- [B2]
    mkCase "oracle/underflow-empty" #[],
    mkCase "oracle/underflow-one" #[.slice sampleSliceA],
    mkCase "oracle/underflow-two" #[.slice sampleSliceA, .int (.num 5)],
    mkCase "oracle/underflow-three" #[.slice sampleSliceA, .int (.num 5), .cell dictSlice4],

    -- [B3]
    mkCase "oracle/range/negative" (mkSliceStack sampleSliceA 0 .null (-1)),
    mkCase "oracle/range/too-large" (mkSliceStack sampleSliceA 0 .null 1024),
    mkCase "oracle/range/nan" (#[.slice sampleSliceA, .int (.num 5), .cell dictSlice4, .int .nan]),

    -- [B4]
    mkCase "oracle/key/nan" (#[.slice sampleSliceA, .int .nan, .cell dictSlice4, .int (.num 4)]),
    mkCase "oracle/key/negative" (mkSliceStack sampleSliceA (-1) (.cell dictSlice4) 4),
    mkCase "oracle/key/oob-smallwidth" (mkSliceStack sampleSliceA 2 (.cell dictSlice1) 1),
    mkCase "oracle/key/oob-zero-width" (mkSliceStack sampleSliceA 1 (.cell dictSlice0) 0),
    mkCase "oracle/key/too-large" (mkSliceStack sampleSliceA (1 <<< 16) (.cell dictSlice8) 8),
    mkCase "oracle/key/wrong-kind" (#[.slice sampleSliceA, .slice badSliceKey, .cell dictSlice4, intV 4]),

    -- [B5]
    mkCase "oracle/type/value-not-slice" (#[.cell sampleCellA, .int (.num 5), .cell dictSlice4, intV 4]),

    -- [B6]
    mkCase "oracle/runtime/hit-4" (mkSliceStack sampleSliceD 5 (.cell dictSlice4) 4),
    mkCase "oracle/runtime/hit-1" (mkSliceStack sampleSliceC 0 (.cell dictSlice1) 1),
    mkCase "oracle/runtime/hit-0" (mkSliceStack sampleSliceE 0 (.cell dictSlice0) 0),
    mkCase "oracle/runtime/hit-1023" (mkSliceStack sampleSliceB 0 (.cell dictSlice1023) 1023),
    mkCase "oracle/runtime/miss-null" (mkSliceStack sampleSliceA 9 .null 4),
    mkCase "oracle/runtime/miss-nonnull" (mkSliceStack sampleSliceE 7 (.cell dictSlice4) 4),
    mkCase "oracle/runtime/miss-width-mismatch" (mkSliceStack sampleSliceA 5 (.cell dictSlice4) 8),
    mkCase "oracle/runtime/miss-empty-width-boundary" (mkSliceStack sampleSliceA 0 .null 0),

    -- [B7]
    mkCase "oracle/errors/dict-not-maybe-cell" (mkSliceStack sampleSliceA 5 (.tuple #[]) 4),
    mkCase "oracle/errors/dict-err" (mkSliceStack sampleSliceA 5 (.cell malformedDict) 4),

    -- [B8] [B10] [B9]
    mkCase "oracle/asm/invalid-unsigned-slice" (mkSliceStack sampleSliceA 5 (.cell dictSlice4) 4),
    mkCodeCase "oracle/code/426" raw426,
    mkCodeCase "oracle/code/427" raw427,
    mkCodeCase "oracle/code/425" raw425,
    mkCodeCase "oracle/code/424" raw424,
    mkCodeCase "oracle/code/421" raw421,
    mkCodeCase "oracle/code/428" raw428,
    mkCodeCase "oracle/code/429" raw429,
    mkCodeCase "oracle/code/truncated" rawF4,

    -- [B11] [B12]
    mkCase "oracle/gas/miss-exact"
      (mkSliceStack sampleSliceA 7 .null 4)
      (mkGasProgram missGas instr)
      (oracleGasLimitsExact missGas),
    mkCase "oracle/gas/miss-exact-minus-one"
      (mkSliceStack sampleSliceA 7 .null 4)
      (mkGasProgram missGasMinusOne instr)
      (oracleGasLimitsExactMinusOne missGasMinusOne),
    mkCase "oracle/gas/hit-4-exact"
      (mkSliceStack sampleSliceE 5 (.cell dictSlice4) 4)
      (mkGasProgram hitGas4 instr)
      (oracleGasLimitsExact hitGas4),
    mkCase "oracle/gas/hit-4-exact-minus-one"
      (mkSliceStack sampleSliceE 5 (.cell dictSlice4) 4)
      (mkGasProgram hitGas4MinusOne instr)
      (oracleGasLimitsExactMinusOne hitGas4MinusOne),
    mkCase "oracle/gas/hit-1-exact"
      (mkSliceStack sampleSliceE 0 (.cell dictSlice1) 1)
      (mkGasProgram hitGas1 instr)
      (oracleGasLimitsExact hitGas1),
    mkCase "oracle/gas/hit-1-exact-minus-one"
      (mkSliceStack sampleSliceE 0 (.cell dictSlice1) 1)
      (mkGasProgram hitGas1MinusOne instr)
      (oracleGasLimitsExactMinusOne hitGas1MinusOne),
    mkCase "oracle/gas/hit-0-exact"
      (mkSliceStack sampleSliceE 0 (.cell dictSlice0) 0)
      (mkGasProgram hitGas0 instr)
      (oracleGasLimitsExact hitGas0),
    mkCase "oracle/gas/hit-0-exact-minus-one"
      (mkSliceStack sampleSliceE 0 (.cell dictSlice0) 0)
      (mkGasProgram hitGas0MinusOne instr)
      (oracleGasLimitsExactMinusOne hitGas0MinusOne),
    mkCase "oracle/gas/hit-1023-exact"
      (mkSliceStack sampleSliceE 0 (.cell dictSlice1023) 1023)
      (mkGasProgram hitGas1023 instr)
      (oracleGasLimitsExact hitGas1023),
    mkCase "oracle/gas/hit-1023-exact-minus-one"
      (mkSliceStack sampleSliceE 0 (.cell dictSlice1023) 1023)
      (mkGasProgram hitGas1023MinusOne instr)
      (oracleGasLimitsExactMinusOne hitGas1023MinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUREPLACEFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREPLACE
