import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREPLACEGETB

/-
INSTRUCTION: DICTUREPLACEGETB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch/fallback behavior:
   - `execInstrDictExt` handles `.dictExt (.mutGetB true true .replace)`.
   - Non-`.dictExt` instructions are passed to `next`.

2. [B2] Stack and `n` validation:
   - The opcode requires 4 stack items (`newValue`, `key`, `dict`, `n`).
   - `n` is checked by `popNatUpTo 1023`.
   - Negative/too-large `.nan` in `n` must surface `.rangeChk`.

3. [B3] Unsigned integer-key acquisition:
   - Integer mode requires `popInt` for key value.
   - `dictKeyBits?` with `unsigned = true` defines success/failure.
   - Negative keys and keys >= `2^n` become `.rangeChk`.
   - `n` still controls accepted key bit length, including the boundary `n = 0`.

4. [B4] Type/value validation:
   - `popBuilder` requires `.builder` at value position (`.typeChk`).
   - Integer-key opcode requires key at integer slot (`.typeChk`).
   - Dictionary must be `.maybeCell`-compatible (`.typeChk`).

5. [B5] Replace-get runtime outcomes:
   - On hit, a new root is pushed and old value is pushed as slice, then `-1`.
   - On miss, pushed root is unchanged dictionary (or `.null`) and `0`.

6. [B6] Failure during traversal:
   - malformed dictionary root (`dictErr`) must propagate with loaded-cell accounting.
   - oversized replacement builder payload causes `.cellOv` in `dictReplaceBuilderWithCells`.

7. [B7] Assembler support:
   - `.dictExt (.mutGetB _ _ .replace)` is not CP0-assemable in this repo (`.invOpcode`).
   - There is no valid encoding path for direct assembly.

8. [B8] Decoder boundaries / aliasing:
   - `0xf44f` decodes to `.mutGetB true true .replace` (unsigned).
   - Adjacent/nearby opcodes (`0xf44d`, `0xf44e`, `0xf44e`, `0xf450`) must be rejected by decoder in this family range context.
   - Truncated 8-bit opcode payloads are rejected.

9. [B9] Gas accounting:
   - Exact gas budget is base budget from `computeExactGasBudget`.
   - Exact-minus-one must fail.
   - Hit paths add `created * cellCreateGasPrice` when dictionary rebuild happens.

10. [B10] Decoder/assembler/fuzzer overlap:
   - Any boundary/error behavior not directly covered by oracle cases must be represented in fuzz (including underflow, type/range errors, malformed root, and gas boundaries).

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/ 

private def suiteId : InstrId :=
  { name := "DICTUREPLACEGETB" }

private def instrUnsigned : Instr := .dictExt (.mutGetB true true .replace)

private def rawF44D : Cell := Cell.mkOrdinary (natToBits 0xF44D 16) #[]
private def rawF44E : Cell := Cell.mkOrdinary (natToBits 0xF44E 16) #[]
private def rawF44F : Cell := Cell.mkOrdinary (natToBits 0xF44F 16) #[]
private def rawF450 : Cell := Cell.mkOrdinary (natToBits 0xF450 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def valueA : Builder := Builder.empty.storeBits (natToBits 0xA1 8)
private def valueB : Builder := Builder.empty.storeBits (natToBits 0xB2 8)
private def valueC : Builder := Builder.empty.storeBits (natToBits 0xC3 8)
private def valueD : Builder := Builder.empty.storeBits (natToBits 0xD4 8)
private def valueHuge : Builder := Builder.empty.storeBits (Array.replicate 1024 false)
private def valueASlice : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueBSlice : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueCSlice : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueDSlice : Slice := mkSliceFromBits (natToBits 0xD4 8)

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]
private def keyBadSlice : Slice := mkSliceFromBits (natToBits 7 8)

private def mkDictUnsigned! (label : String) (n : Nat) (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      let keyBits :=
        match dictKeyBits? k n true with
        | some bs => bs
        | none => panic! s!"DICTUREPLACEGETB/{label}: out-of-range int key k={k} for n={n}"
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"DICTUREPLACEGETB/{label}: unexpected empty root during set"
      | .error e =>
          panic! s!"DICTUREPLACEGETB/{label}: dict build failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTUREPLACEGETB/{label}: empty dictionary"

private def dictUnsigned0 : Cell :=
  mkDictUnsigned! "dictUnsigned0" 0 #[(0, valueA)]

private def dictUnsigned4 : Cell :=
  mkDictUnsigned! "dictUnsigned4" 4 #[
    (0, valueA),
    (1, valueB),
    (7, valueC),
    (15, valueD)
  ]

private def dictUnsigned8 : Cell :=
  mkDictUnsigned! "dictUnsigned8" 8 #[
    (0, valueA),
    (1, valueB),
    (42, valueC),
    (255, valueD)
  ]

private def mkIntStack
    (key : Int)
    (dict : Value := .null)
    (value : Builder := valueA)
    (n : Int := 4) : Array Value :=
  #[.builder value, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (instr : Instr := instrUnsigned)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[instr]
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
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (instr : Instr := instrUnsigned)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure invOpcode")

private def expectDecodeInv (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits} bits)")

private def replaceCreated (root : Cell) (n : Nat) (key : Int) : Nat :=
  match dictKeyBits? key n true with
  | none => 0
  | some bits =>
      match dictLookupSetBuilderWithCells (some root) bits valueC .replace with
      | .ok (_old, _new, _ok, created, _loaded) => created
      | .error _ => 0

private def replaceResultRoot (root : Cell) (n : Nat) (key : Int) (value : Builder := valueC) : Option Cell :=
  match dictKeyBits? key n true with
  | none => none
  | some bits =>
      match dictLookupSetBuilderWithCells (some root) bits value .replace with
      | .ok (_old, newRoot, _ok, _created, _loaded) => newRoot
      | .error e => panic! s!"DICTUREPLACEGETB/replace-result-root failed ({reprStr e})"

private def baseGas : Int := computeExactGasBudget instrUnsigned
private def missGas : Int := baseGas
private def missGasMinusOne : Int := if missGas > 0 then missGas - 1 else 0

private def hitCreated4 : Nat := replaceCreated dictUnsigned4 4 15
private def hitCreated8 : Nat := replaceCreated dictUnsigned8 8 255
private def hitGas4 : Int := baseGas + Int.ofNat hitCreated4 * cellCreateGasPrice
private def hitGas8 : Int := baseGas + Int.ofNat hitCreated8 * cellCreateGasPrice
private def hitGas4MinusOne : Int := if hitGas4 > 0 then hitGas4 - 1 else 0
private def hitGas8MinusOne : Int := if hitGas8 > 0 then hitGas8 - 1 else 0

private def runDICTUREPLACEGETBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDICTUREPLACEGETBFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (.int (.num 777))) stack

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

private def genDICTUREPLACEGETBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 16 then
    let (idx, rng2) := randNat rng1 0 3
    let c : OracleCase :=
      if idx = 0 then
        mkCase (s!"fuzz/underflow/empty/{idx}") #[]
      else if idx = 1 then
        mkCase (s!"fuzz/underflow/one/{idx}") #[.builder valueA]
      else if idx = 2 then
        mkCase (s!"fuzz/underflow/two/{idx}") (#[.builder valueA, .int (.num 5)])
      else
        mkCase (s!"fuzz/underflow/three/{idx}") (mkIntStack 1 (.cell dictUnsigned4) valueA)
    (c, rng2)
  else if shape < 34 then
    let (idx, rng2) := randNat rng1 0 4
    let c : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/hit/unsigned-4-0" (mkIntStack 0 (.cell dictUnsigned4) valueA 4)
      else if idx = 1 then
        mkCase "fuzz/hit/unsigned-4-15" (mkIntStack 15 (.cell dictUnsigned4) valueB 4)
      else if idx = 2 then
        mkCase "fuzz/hit/unsigned-8-255" (mkIntStack 255 (.cell dictUnsigned8) valueC 8) instrUnsigned
      else if idx = 3 then
        mkCase "fuzz/miss/unsigned-4-2" (mkIntStack 2 (.cell dictUnsigned4) valueD 4)
      else
        mkCase "fuzz/miss/unsigned-null" (mkIntStack 7 .null valueA 8)
    (c, rng2)
  else if shape < 52 then
    let (idx, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/range/n-negative" (mkIntStack 0 (.cell dictUnsigned4) valueA (-1))
      else if idx = 1 then
        mkCase "fuzz/range/n-too-large" (mkIntStack 0 (.cell dictUnsigned4) valueA 1024)
      else if idx = 2 then
        mkCase "fuzz/range/n-nan" (#[.builder valueA, .int (.num 5), .cell dictUnsigned4, .int .nan])
      else if idx = 3 then
        mkCase "fuzz/range/key-negative" (mkIntStack (-1) (.cell dictUnsigned4) valueA 4)
      else if idx = 4 then
        mkCase "fuzz/range/key-high4" (mkIntStack 16 (.cell dictUnsigned4) valueA 4)
      else
        mkCase "fuzz/range/key-high8" (mkIntStack 256 (.cell dictUnsigned8) valueA 8)
    (c, rng2)
  else if shape < 68 then
    let (idx, rng2) := randNat rng1 0 4
    let c : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/type/value-not-builder" (#[.int (.num 7), .int (.num 4), .cell dictUnsigned4, intV 4])
      else if idx = 1 then
        mkCase "fuzz/type/key-not-int" (#[.builder valueA, .slice keyBadSlice, .cell dictUnsigned4, intV 4])
      else if idx = 2 then
        mkCase "fuzz/type/dict-not-cell" (mkIntStack 5 (.tuple #[]) valueA 4)
      else if idx = 3 then
        mkCase "fuzz/type/malformed-root" (mkIntStack 7 (.cell malformedDict) valueA 4)
      else
        mkCase "fuzz/type/overflow" (mkIntStack 1 (.cell dictUnsigned4) valueHuge 4)
    (c, rng2)
  else if shape < 84 then
    let (idx, rng2) := randNat rng1 0 2
    let c : OracleCase :=
      if idx = 0 then
        mkGasCase "fuzz/gas/miss-exact" (mkIntStack 7 .null valueA 4) missGas (oracleGasLimitsExact missGas)
      else if idx = 1 then
        mkGasCase "fuzz/gas/miss-exact-minus-one" (mkIntStack 7 .null valueA 4) missGasMinusOne
          (oracleGasLimitsExactMinusOne missGas)
      else
        mkGasCase "fuzz/gas/hit-exact" (mkIntStack 15 (.cell dictUnsigned4) valueA 4) hitGas4
          (oracleGasLimitsExact hitGas4)
    (c, rng2)
  else
    let (idx, rng2) := randNat rng1 0 4
    let c : OracleCase :=
      if idx = 0 then
        mkGasCase "fuzz/gas/hit-exact-minus-one" (mkIntStack 15 (.cell dictUnsigned4) valueA 4) hitGas4MinusOne
          (oracleGasLimitsExactMinusOne hitGas4)
      else if idx = 1 then
        mkCodeCase "fuzz/code/f44f" (mkIntStack 42 (.cell dictUnsigned8) valueA 8) rawF44F
      else if idx = 2 then
        mkCodeCase "fuzz/code/invalid-f44d" (mkIntStack 42 (.cell dictUnsigned8) valueA 8) rawF44D
      else if idx = 3 then
        mkCodeCase "fuzz/code/invalid-f44e" (mkIntStack 42 (.cell dictUnsigned8) valueA 8) rawF44E
      else
        mkCodeCase "fuzz/code/truncated" (mkIntStack 42 (.cell dictUnsigned8) valueA 8) rawTruncated8
    (c, rng2)



def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := mkIntStack 1 (.cell dictUnsigned4) valueA 4
        let expected := stack ++ #[.int (.num 777)]
        expectOkStack "dispatch/fallback" (runDICTUREPLACEGETBFallback stack) expected },
    { name := "unit/asm/reject" -- [B7]
      run := do
        expectAssembleInvOpcode "assemble/unsigned" instrUnsigned },
    { name := "unit/decode/valid" -- [B8]
      run := do
        let _ ← expectDecodeStep "decode/f44f" (Slice.ofCell rawF44F) instrUnsigned 16 },
    { name := "unit/decode/invalid-boundaries" -- [B8]
      run := do
        expectDecodeInv "decode/f44d" rawF44D
        expectDecodeInv "decode/f44e" rawF44E
        expectDecodeInv "decode/f450" rawF450
        expectDecodeInv "decode/truncated" rawTruncated8 },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow" (runDICTUREPLACEGETBDirect instrUnsigned #[]) .stkUnd },
    { name := "unit/runtime/n-range" -- [B2]
      run := do
        expectErr "n-negative" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 1 (.cell dictUnsigned4) valueA (-1))) .rangeChk
        expectErr "n-too-large" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 1 (.cell dictUnsigned4) valueA 1024)) .rangeChk
        expectErr "n-nan" (runDICTUREPLACEGETBDirect instrUnsigned (#[.builder valueA, .int (.num 1), .cell dictUnsigned4, .int .nan])) .rangeChk },
    { name := "unit/runtime/key-range" -- [B3]
      run := do
        expectErr "key-negative" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack (-1) (.cell dictUnsigned4) valueA 4)) .rangeChk
        expectErr "key-high-4" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 16 (.cell dictUnsigned4) valueA 4)) .rangeChk
        expectErr "key-high-8" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 256 (.cell dictUnsigned8) valueA 8)) .rangeChk
        expectErr "key-n-zero" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 1 (.cell dictUnsigned0) valueA 0)) .rangeChk },
    { name := "unit/runtime/type-errors" -- [B4]
      run := do
        expectErr "value-not-builder" (runDICTUREPLACEGETBDirect instrUnsigned (#[.int (.num 7), .int (.num 1), .cell dictUnsigned4, intV 4])) .typeChk
        expectErr "key-not-int" (runDICTUREPLACEGETBDirect instrUnsigned (#[.builder valueA, .slice keyBadSlice, .cell dictUnsigned4, intV 4])) .typeChk
        expectErr "dict-not-cell" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 4 (.tuple #[]) valueA 4)) .typeChk },
    { name := "unit/runtime/malformed-root" -- [B6]
      run := do
        expectErr "malformed-root" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 7 (.cell malformedDict) valueA 4)) .dictErr },
    { name := "unit/runtime/builder-overflow" -- [B6]
      run := do
        expectErr "builder-overflow" (runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 7 (.cell dictUnsigned4) valueHuge 4)) .cellOv },
    { name := "unit/runtime/replace-hit" -- [B5]
      run := do
        let got := runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 15 (.cell dictUnsigned4) valueC 4)
        let expectedRoot :=
          match replaceResultRoot dictUnsigned4 4 15 valueC with
          | some root => root
          | none => dictUnsigned4
        let expected := #[.cell expectedRoot, .slice valueDSlice, intV (-1)]
        expectOkStack "replace-hit" got expected },
    { name := "unit/runtime/replace-miss" -- [B5]
      run := do
        let got := runDICTUREPLACEGETBDirect instrUnsigned (mkIntStack 6 (.cell dictUnsigned4) valueA 4)
        expectOkStack "replace-miss" got (#[(.cell dictUnsigned4), .int (.num 0)] ) }
  ]
  oracle := #[
    -- [B2] [B3]
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one" #[.builder valueA],
    mkCase "oracle/underflow/two" (#[.builder valueA, .int (.num 5)]),
    mkCase "oracle/underflow/three" (mkIntStack 1 (.cell dictUnsigned4) valueA),

    -- [B2] Range checks
    mkCase "oracle/range/n-negative" (mkIntStack 1 (.cell dictUnsigned4) valueA (-1)),
    mkCase "oracle/range/n-too-large" (mkIntStack 1 (.cell dictUnsigned4) valueA 1024),
    mkCase "oracle/range/n-nan" (#[.builder valueA, .int (.num 1), .cell dictUnsigned4, .int .nan]),

    -- [B3] Unsigned key errors
    mkCase "oracle/key-negative" (mkIntStack (-1) (.cell dictUnsigned4) valueA 4),
    mkCase "oracle/key-too-high-4" (mkIntStack 16 (.cell dictUnsigned4) valueA 4),
    mkCase "oracle/key-too-high-8" (mkIntStack 256 (.cell dictUnsigned8) valueA 8),

    -- [B4] Type and key/value errors
    mkCase "oracle/type/value-not-builder" (#[.int (.num 7), .int (.num 4), .cell dictUnsigned4, intV 4]),
    mkCase "oracle/type/key-not-int" (#[.builder valueA, .slice keyBadSlice, .cell dictUnsigned4, intV 4]),
    mkCase "oracle/type/dict-not-cell" (mkIntStack 4 (.tuple #[]) valueA 4),

    -- [B3][B5] Positive hit/miss semantics
    mkCase "oracle/hit/unsigned-0" (mkIntStack 0 (.cell dictUnsigned4) valueC 4),
    mkCase "oracle/hit/unsigned-15" (mkIntStack 15 (.cell dictUnsigned4) valueD 4),
    mkCase "oracle/hit/unsigned-42" (mkIntStack 42 (.cell dictUnsigned8) valueA 8),
    mkCase "oracle/hit/unsigned-max" (mkIntStack 255 (.cell dictUnsigned8) valueB 8),
    mkCase "oracle/hit/unsigned-zero-keylen" (mkIntStack 0 (.cell dictUnsigned0) valueA 0),
    mkCase "oracle/miss/unsigned-null" (mkIntStack 6 .null valueB 4),
    mkCase "oracle/miss/unsigned-nonempty" (mkIntStack 6 (.cell dictUnsigned4) valueA 4),

    -- [B6] Malformed root / builder overflow
    mkCase "oracle/malformed-root" (mkIntStack 1 (.cell malformedDict) valueA 4),
    mkCase "oracle/builder-overflow" (mkIntStack 1 (.cell dictUnsigned4) valueHuge 4),

    -- [B8] Decoder and assembler boundaries
    mkCodeCase "oracle/code/f44f" (mkIntStack 255 (.cell dictUnsigned8) valueA 8) rawF44F,
    mkCodeCase "oracle/code/f44d-invalid" (mkIntStack 255 (.cell dictUnsigned8) valueA 8) rawF44D,
    mkCodeCase "oracle/code/f44e-invalid" (mkIntStack 255 (.cell dictUnsigned8) valueA 8) rawF44E,
    mkCodeCase "oracle/code/f450-invalid" (mkIntStack 255 (.cell dictUnsigned8) valueA 8) rawF450,
    mkCodeCase "oracle/code/truncated" (mkIntStack 255 (.cell dictUnsigned8) valueA 8) rawTruncated8,

    -- [B9] Gas exactness and minus-one
    mkGasCase "oracle/gas/miss-exact" (mkIntStack 7 .null valueA 4) missGas (oracleGasLimitsExact missGas),
    mkGasCase "oracle/gas/miss-exact-minus-one" (mkIntStack 7 .null valueA 4) missGasMinusOne
      (oracleGasLimitsExactMinusOne missGas),
    mkGasCase "oracle/gas/hit-exact-4" (mkIntStack 15 (.cell dictUnsigned4) valueA 4) hitGas4 (oracleGasLimitsExact hitGas4),
    mkGasCase "oracle/gas/hit-exact-minus-one-4" (mkIntStack 15 (.cell dictUnsigned4) valueA 4) hitGas4MinusOne
      (oracleGasLimitsExactMinusOne hitGas4),
    mkGasCase "oracle/gas/hit-exact-8" (mkIntStack 255 (.cell dictUnsigned8) valueA 8) hitGas8 (oracleGasLimitsExact hitGas8),
    mkGasCase "oracle/gas/hit-exact-minus-one-8" (mkIntStack 255 (.cell dictUnsigned8) valueA 8) hitGas8MinusOne
      (oracleGasLimitsExactMinusOne hitGas8)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUREPLACEGETBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREPLACEGETB
