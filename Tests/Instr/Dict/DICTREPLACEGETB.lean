import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREPLACEGETB

/-!
INSTRUCTION: DICTREPLACEGETB

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch/fallback behavior.
   - This file tests `.dictExt (.mutGetB _ _ .replace)`.
   - Non-`.dictExt` instructions are passed through to `next` unmodified.

2. [B2] Stack arity + `n` validation.
   - `checkUnderflow 4` requires `newValueBuilder`, `key`, `dict`, `n`.
   - Underflow, negative `n`, `n > 1023`, and `.nan` for `n` surface `.rangeChk`.

3. [B3] Slice-key acquisition path (`intKey = false`).
   - `VM.popSlice` + `haveBits n` behavior.
   - `n` bits missing in key slice is stored as `none` and later turns into `.cellUnd`.
   - Boundary `n = 0` is valid and reads empty bitstring.

4. [B4] Integer-key acquisition path (`intKey = true`).
   - `VM.popInt` + `dictKeyBits?` is used for signed and unsigned modes.
   - Out-of-range integers trigger `.rangeChk` in `dictKeyBits?` for both signed/unsigned flavors.

5. [B5] Runtime replace semantics.
   - On hit, operation pushes updated dict root, old value as slice, and `-1`.
   - On miss, operation pushes either unchanged root or `.null` and `0`.
   - For `.replace` on empty dict or key mismatch, no new dict root is created (`created = 0`).

6. [B6] Value materialization constraints.
   - `popBuilder` is mandatory.
   - Non-builder at value position triggers `.typeChk`.

7. [B7] Dictionary shape errors.
   - Malformed dictionary payloads propagate `.dictErr` through `dictLookupSetBuilderWithCells`.

8. [B8] Assembler behavior.
   - `.dictExt (.mutGetB _ _ .replace)` is unsupported by CP0 assembler (`.invOpcode`).

9. [B9] Decoder boundaries.
   - `0xf44d`, `0xf44e`, `0xf44f` decode to:
     - `.mutGetB false false .replace`
     - `.mutGetB true false .replace`
     - `.mutGetB true true .replace`.
   - Adjacent opcodes `0xf44c` and `0xf450` are `.invOpcode`.
   - Truncated `0xf4` is `.invOpcode`.

10. [B10] Gas accounting.
   - Base budget uses `computeExactGasBudget`.
   - Exact and exact-minus-one budgets are required.
   - Variable penalty is `created * cellCreateGasPrice` on hit updates where dictionary rebuild occurs.

11. [B11] Decoder/asm/fuzzer overlap.
   - Any decoder/assembler branch not fully covered by oracle tests is covered by fuzz cases.

12. [B12] Fuzzer branch coverage.
   - Fuzzer explicitly emits underflow, arity/type/range/malformed/cell_und paths, valid hits/misses,
     opcode decode cases, and gas exact/exact-minus-one cases.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTREPLACEGETB" }

private def instrSlice : Instr := .dictExt (.mutGetB false false .replace)
private def instrSigned : Instr := .dictExt (.mutGetB true false .replace)
private def instrSignedUnsigned : Instr := .dictExt (.mutGetB true true .replace)

private def rawF44d : Cell := Cell.mkOrdinary (natToBits 0xf44d 16) #[]
private def rawF44e : Cell := Cell.mkOrdinary (natToBits 0xf44e 16) #[]
private def rawF44f : Cell := Cell.mkOrdinary (natToBits 0xf44f 16) #[]
private def rawF44c : Cell := Cell.mkOrdinary (natToBits 0xf44c 16) #[]
private def rawF450 : Cell := Cell.mkOrdinary (natToBits 0xf450 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def valueA : Builder := Builder.empty.storeBits (natToBits 0xA1 8)
private def valueB : Builder := Builder.empty.storeBits (natToBits 0xB2 8)
private def valueC : Builder := Builder.empty.storeBits (natToBits 0xC3 8)
private def valueD : Builder := Builder.empty.storeBits (natToBits 0xD4 8)
private def valueE : Builder := Builder.empty.storeBits (natToBits 0xE5 8)
private def valueHuge : Builder := Builder.empty.storeBits (Array.replicate 1024 false)

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueSliceB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueSliceC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueSliceD : Slice := mkSliceFromBits (natToBits 0xD4 8)

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def key0 : BitString := #[]
private def key4A : BitString := natToBits 0x1 4
private def key4B : BitString := natToBits 0x7 4
private def key4C : BitString := natToBits 0x3 4
private def key4D : BitString := natToBits 0xF 4
private def key8A : BitString := natToBits 0x5A 8
private def key8B : BitString := natToBits 0xC3 8
private def key8C : BitString := natToBits 0xFF 8
private def key1023 : BitString := Array.replicate 1023 true

private def key4ShortSlice : Slice := mkSliceFromBits (natToBits 0x1 1)
private def key4ASlice : Slice := mkSliceFromBits key4A
private def key4BSlice : Slice := mkSliceFromBits key4B
private def key4CSlice : Slice := mkSliceFromBits key4C
private def key4DSlice : Slice := mkSliceFromBits key4D
private def key8ASlice : Slice := mkSliceFromBits key8A
private def key8BSlice : Slice := mkSliceFromBits key8B
private def key8CSlice : Slice := mkSliceFromBits key8C
private def key0Slice : Slice := mkSliceFromBits key0
private def key1023Slice : Slice := mkSliceFromBits key1023

private def mkDictBuilderRoot! (label : String) (pairs : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetBuilderWithCells root k v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root result while building"
      | .error e =>
          panic! s!"{label}: dict build failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"{label}: empty dictionary build"

private def keyBitsFor (label : String) (n : Nat) (unsigned : Bool) (key : Int) : BitString :=
  match dictKeyBits? key n unsigned with
  | some b => b
  | none => panic! s!"{label}: invalid key {key} for n={n}, unsigned={unsigned}"

private def mkDictIntRoot! (label : String) (n : Nat) (unsigned : Bool) (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      let keyBits := keyBitsFor label n unsigned k
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root result while building"
      | .error e =>
          panic! s!"{label}: dict build failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"{label}: empty dictionary build"

private def dictSlice4 : Cell :=
  mkDictBuilderRoot! "dictSlice4" #[
    (key4A, valueA),
    (key4B, valueB),
    (key4C, valueC)
  ]

private def dictSlice4Miss : Cell :=
  mkDictBuilderRoot! "dictSlice4Miss" #[
    (key4D, valueD),
    (key4B, valueA)
  ]

private def dictSlice8 : Cell :=
  mkDictBuilderRoot! "dictSlice8" #[
    (key8A, valueA),
    (key8B, valueB),
    (key8C, valueC)
  ]

private def dictSlice0 : Cell :=
  mkDictBuilderRoot! "dictSlice0" #[(key0, valueA)]

private def dictSigned4 : Cell :=
  mkDictIntRoot! "dictSigned4" 4 false #[
    (-8, valueA),
    (-1, valueB),
    (3, valueC),
    (7, valueD)
  ]

private def dictUnsigned4 : Cell :=
  mkDictIntRoot! "dictUnsigned4" 4 true #[
    (0, valueA),
    (1, valueB),
    (10, valueC),
    (15, valueD)
  ]

private def mkSliceCase
    (value : Builder)
    (key : Slice)
    (dict : Value := .null)
    (n : Int := 4) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

private def mkIntCase
    (value : Builder)
    (key : Int)
    (dict : Value := .null)
    (n : Int := 4) : Array Value :=
  #[.builder value, .int (.num key), dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (instr : Instr := instrSlice)
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
    (instr : Instr)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits} bits)")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure invOpcode")

private def replaceResultRoot
    (dict : Option Cell)
    (key : BitString)
    (value : Builder) : Option Cell :=
  match dictLookupSetBuilderWithCells dict key value .replace with
  | .ok (_, newRoot, _ok, _created, _loaded) =>
      newRoot
  | .error e =>
      panic! s!"DICTREPLACEGETB: replace operation failed while computing expected root ({reprStr e})"

private def replaceCreated
    (dict : Option Cell)
    (key : BitString)
    (value : Builder) : Nat :=
  match dictLookupSetBuilderWithCells dict key value .replace with
  | .ok (_, _old, _ok, created, _loaded) => created
  | .error _ => 0

private def baseGas : Int := computeExactGasBudget instrSlice
private def missGas : Int := baseGas
private def missGasMinusOne : Int := if missGas > 0 then missGas - 1 else 0

private def hitCreated : Nat :=
  replaceCreated (some dictSlice4) key4A valueD

private def hitGas : Int :=
  baseGas + Int.ofNat hitCreated * cellCreateGasPrice
private def hitGasMinusOne : Int :=
  if hitGas > 0 then hitGas - 1 else 0

private def runDICTREPLACEGETBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDICTREPLACEGETBFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (.int (.num 777))) stack

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr suiteId

private def genDICTREPLACEGETBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 59
  let (tag, rng2) := randNat rng1 0 999_999
  if shape < 10 then
    let (idx, rng3) := randNat rng2 0 3
    let c : OracleCase :=
      if idx = 0 then
        mkCase (s!"fuzz/underflow/empty/{tag}") #[]
      else if idx = 1 then
        mkCase (s!"fuzz/underflow/one/{tag}") #[.builder valueA]
      else if idx = 2 then
        mkCase (s!"fuzz/underflow/two/{tag}") (#[.builder valueA, .slice key4ASlice])
      else
        mkCase (s!"fuzz/underflow/three/{tag}") (#[.builder valueA, .slice key4ASlice, .cell dictSlice4])
    (c, rng3)
  else if shape < 18 then
    let (idx, rng3) := randNat rng2 0 7
    let c : OracleCase :=
      if idx = 0 then
        mkCase (s!"fuzz/slice-hit/4/{tag}") (mkSliceCase valueB key4ASlice (.cell dictSlice4) 4)
      else if idx = 1 then
        mkCase (s!"fuzz/slice-hit/8/{tag}") (mkSliceCase valueA key8ASlice (.cell dictSlice8) 8)
      else if idx = 2 then
        mkCase (s!"fuzz/slice-hit/0/{tag}") (mkSliceCase valueC key0Slice (.cell dictSlice0) 0)
      else if idx = 3 then
        mkCase (s!"fuzz/slice-miss/null/{tag}") (mkSliceCase valueA key4BSlice .null 4)
      else if idx = 4 then
        mkCase (s!"fuzz/slice-miss/nonempty/{tag}") (mkSliceCase valueA key4DSlice (.cell dictSlice4Miss) 4)
      else if idx = 5 then
        mkCase (s!"fuzz/slice-miss/1023/{tag}") (mkSliceCase valueB key1023Slice .null 1023)
      else if idx = 6 then
        mkCase (s!"fuzz/slice-0/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 0)
      else
        mkCase (s!"fuzz/slice-short/{tag}") (mkSliceCase valueA key4ShortSlice (.cell dictSlice4) 4)
    (c, rng3)
  else if shape < 26 then
    let (idx, rng3) := randNat rng2 0 5
    let c : OracleCase :=
      if idx = 0 then
        mkCase (s!"fuzz/int-signed-hit/{tag}") (mkIntCase valueA (-8) (.cell dictSigned4) 4) instrSigned
      else if idx = 1 then
        mkCase (s!"fuzz/int-signed-hit-alt/{tag}") (mkIntCase valueB 7 (.cell dictSigned4) 4) instrSigned
      else if idx = 2 then
        mkCase (s!"fuzz/int-signed-miss/{tag}") (mkIntCase valueA 6 (.cell dictSigned4) 4) instrSigned
      else if idx = 3 then
        mkCase (s!"fuzz/int-unsigned-hit/{tag}") (mkIntCase valueC 15 (.cell dictUnsigned4) 4) instrSignedUnsigned
      else if idx = 4 then
        mkCase (s!"fuzz/int-unsigned-miss/{tag}") (mkIntCase valueD 6 (.cell dictUnsigned4) 4) instrSignedUnsigned
      else
        mkCase (s!"fuzz/int-unsigned-null/{tag}") (mkIntCase valueA 15 .null 4) instrSignedUnsigned
    (c, rng3)
  else if shape < 33 then
    let (idx, rng3) := randNat rng2 0 2
    let c : OracleCase :=
      if idx = 0 then
        mkCase (s!"fuzz/range/n-negative/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) (-1))
      else if idx = 1 then
        mkCase (s!"fuzz/range/n-too-large/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 1024)
      else
        mkCase (s!"fuzz/range/n-nan/{tag}") (#[.builder valueA, .slice key4ASlice, .cell dictSlice4, .int .nan])
    (c, rng3)
  else if shape < 40 then
    let (idx, rng3) := randNat rng2 0 6
    let c : OracleCase :=
      if idx = 0 then
        mkCase (s!"fuzz/int/signed-high/{tag}") (mkIntCase valueA 8 (.cell dictSigned4) 4) instrSigned
      else if idx = 1 then
        mkCase (s!"fuzz/int/signed-low/{tag}") (mkIntCase valueA (-9) (.cell dictSigned4) 4) instrSigned
      else if idx = 2 then
        mkCase (s!"fuzz/int/unsigned-high/{tag}") (mkIntCase valueA 16 (.cell dictUnsigned4) 4) instrSignedUnsigned
      else if idx = 3 then
        mkCase (s!"fuzz/int/unsigned-negative/{tag}") (mkIntCase valueA (-1) (.cell dictUnsigned4) 4) instrSignedUnsigned
      else if idx = 4 then
        mkCase (s!"fuzz/type/key-not-int/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSigned4) 4) instrSigned
      else if idx = 5 then
        mkCase (s!"fuzz/type/value-not-builder/{tag}") (#[.int (.num 7), .slice key4ASlice, .cell dictSlice4, intV 4]) instrSlice
      else
        mkCase (s!"fuzz/type/dict-not-cell/{tag}") (mkIntCase valueA 7 (.tuple #[]) 4) instrSigned
    (c, rng3)
  else if shape < 47 then
    let (idx, rng3) := randNat rng2 0 5
    let c : OracleCase :=
      if idx = 0 then
        mkCase (s!"fuzz/malformed-root-slice/{tag}") (mkSliceCase valueA key4ASlice (.cell malformedDict) 4)
      else if idx = 1 then
        mkCase (s!"fuzz/malformed-root-int/{tag}") (mkIntCase valueA 1 (.cell malformedDict) 4) instrSigned
      else if idx = 2 then
        mkCase (s!"fuzz/value/cellov/{tag}") (mkSliceCase valueHuge key4ASlice (.cell dictSlice4) 4)
      else if idx = 3 then
        mkCodeCase (s!"fuzz/decode/f44d/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF44d
      else if idx = 4 then
        mkCodeCase (s!"fuzz/decode/invalid/f44c/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF44c
      else
        mkCodeCase (s!"fuzz/decode/truncated/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF4
    (c, rng3)
  else
    let (idx, rng3) := randNat rng2 0 4
    let c : OracleCase :=
      if idx = 0 then
        mkGasCase (s!"fuzz/gas/miss-exact/{tag}") (mkSliceCase valueA key4ASlice .null 4) instrSlice missGas (oracleGasLimitsExact missGas)
      else if idx = 1 then
        mkGasCase (s!"fuzz/gas/miss-exact-minus-one/{tag}") (mkSliceCase valueA key4ASlice .null 4) instrSlice missGasMinusOne
          (oracleGasLimitsExactMinusOne missGas)
      else if idx = 2 then
        mkGasCase (s!"fuzz/gas/hit-exact/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) instrSlice hitGas (oracleGasLimitsExact hitGas)
      else if idx = 3 then
        mkGasCase (s!"fuzz/gas/hit-exact-minus-one/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) instrSlice hitGasMinusOne
          (oracleGasLimitsExactMinusOne hitGas)
      else
        mkCodeCase (s!"fuzz/decode/invalid/f450/{tag}") (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF450
    (c, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := mkSliceCase valueA key4ASlice (.cell dictSlice4) 4
        let expected := stack ++ #[.int (.num 777)]
        expectOkStack "dispatch/fallback" (runDICTREPLACEGETBFallback stack) expected },
    { name := "unit/asm/reject/slice" -- [B8]
      run := do
        expectAssembleInvOpcode "asm/slice" instrSlice },
    { name := "unit/asm/reject/signed" -- [B8]
      run := do
        expectAssembleInvOpcode "asm/signed" instrSigned },
    { name := "unit/asm/reject/unsigned" -- [B8]
      run := do
        expectAssembleInvOpcode "asm/unsigned" instrSignedUnsigned },
    { name := "unit/decode/valid-f44d" -- [B9]
      run := do
        let _ ← expectDecodeStep "decode/f44d" (Slice.ofCell rawF44d) instrSlice 16
        let _ ← expectDecodeStep "decode/f44e" (Slice.ofCell rawF44e) instrSigned 16
        let _ ← expectDecodeStep "decode/f44f" (Slice.ofCell rawF44f) instrSignedUnsigned 16 },
    { name := "unit/decode/invalid-boundaries" -- [B9]
      run := do
        expectDecodeInvOpcode "decode/f44c" rawF44c
        expectDecodeInvOpcode "decode/f450" rawF450
        expectDecodeInvOpcode "decode/trunc-f4" rawF4 },
    { name := "unit/runtime/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDICTREPLACEGETBDirect instrSlice #[]) .stkUnd },
    { name := "unit/runtime/underflow-three" -- [B2]
      run := do
        expectErr "underflow-three" (runDICTREPLACEGETBDirect instrSlice (#[.builder valueA, .slice key4ASlice, .cell dictSlice4])) .stkUnd },
    { name := "unit/runtime/range-negative" -- [B2]
      run := do
        expectErr "n-negative" (runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueA key4ASlice (.cell dictSlice4) (-1))) .rangeChk },
    { name := "unit/runtime/range-too-large" -- [B2]
      run := do
        expectErr "n-too-large" (runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueA key4ASlice (.cell dictSlice4) 1024)) .rangeChk },
    { name := "unit/runtime/range-nan" -- [B2]
      run := do
        expectErr "n-nan" (runDICTREPLACEGETBDirect instrSlice #[.builder valueA, .slice key4ASlice, .cell dictSlice4, .int .nan]) .rangeChk },
    { name := "unit/runtime/slice-short" -- [B3]
      run := do
        expectErr "slice-short" (runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueA key4ShortSlice (.cell dictSlice4) 4)) .cellUnd },
    { name := "unit/runtime/int-key/signed-out-of-range" -- [B4]
      run := do
        expectErr "int-signed-high" (runDICTREPLACEGETBDirect instrSigned (mkIntCase valueA 8 (.cell dictSigned4) 4))
          .rangeChk
        expectErr "int-signed-low" (runDICTREPLACEGETBDirect instrSigned (mkIntCase valueA (-9) (.cell dictSigned4) 4))
          .rangeChk },
    { name := "unit/runtime/int-key/unsigned-out-of-range" -- [B4]
      run := do
        expectErr "int-unsigned-high" (runDICTREPLACEGETBDirect instrSignedUnsigned (mkIntCase valueA 16 (.cell dictUnsigned4) 4))
          .rangeChk
        expectErr "int-unsigned-neg" (runDICTREPLACEGETBDirect instrSignedUnsigned (mkIntCase valueA (-1) (.cell dictUnsigned4) 4))
          .rangeChk },
    { name := "unit/runtime/type-error/value-not-builder" -- [B6]
      run := do
        expectErr "value-not-builder" (runDICTREPLACEGETBDirect instrSlice (#[.int (.num 7), .slice key4ASlice, .cell dictSlice4, intV 4])) .typeChk },
    { name := "unit/runtime/type-error/key-not-dict" -- [B6]
      run := do
        expectErr "key-not-slice" (runDICTREPLACEGETBDirect instrSlice (#[.builder valueA, .int (.num 7), .cell dictSlice4, intV 4])) .typeChk },
    { name := "unit/runtime/type-error/stack-order-int" -- [B4][B6]
      run := do
        expectErr "key-not-int-for-signed" (runDICTREPLACEGETBDirect instrSigned (mkSliceCase valueA key4ASlice (.cell dictSigned4) 4)) .typeChk
        expectErr "dict-not-cell" (runDICTREPLACEGETBDirect instrSigned (mkIntCase valueA 1 (.tuple #[]) 4)) .typeChk },
    { name := "unit/runtime/type-error/dict-not-cell" -- [B2]
      run := do
        expectErr "dict-not-cell" (runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueA key4ASlice (.tuple #[]) 4)) .typeChk },
    { name := "unit/runtime/malformed-root" -- [B7]
      run := do
        expectErr "malformed-root-slice" (runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueA key4ASlice (.cell malformedDict) 4)) .dictErr
        expectErr "malformed-root-int" (runDICTREPLACEGETBDirect instrSigned (mkIntCase valueA 1 (.cell malformedDict) 4)) .dictErr },
    { name := "unit/runtime/value-too-large" -- [B6]
      run := do
        expectErr "builder-overflow" (runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueHuge key4ASlice (.cell dictSlice4) 4)) .cellOv },
    { name := "unit/runtime/replace-hit/slice" -- [B5]
      run := do
        let got := runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueD key4ASlice (.cell dictSlice4) 4)
        let expectedRoot :=
          match replaceResultRoot (some dictSlice4) key4A valueD with
          | some r => r
          | none => dictSlice4
        let expected :=
          #[.cell expectedRoot, .slice valueSliceA, intV (-1)]
        expectOkStack "replace-hit/slice" got expected },
    { name := "unit/runtime/replace-hit/signed" -- [B5]
      run := do
        let got := runDICTREPLACEGETBDirect instrSigned (mkIntCase valueE (-8) (.cell dictSigned4) 4)
        let expectedRoot :=
          match replaceResultRoot (some dictSigned4) (keyBitsFor "test" 4 false (-8)) valueE with
          | some r => r
          | none => dictSigned4
        let expected :=
          #[.cell expectedRoot, .slice valueSliceA, intV (-1)]
        expectOkStack "replace-hit/signed" got expected },
    { name := "unit/runtime/replace-hit/unsigned" -- [B5]
      run := do
        let got := runDICTREPLACEGETBDirect instrSignedUnsigned (mkIntCase valueC 15 (.cell dictUnsigned4) 4)
        let expectedRoot :=
          match replaceResultRoot (some dictUnsigned4) (keyBitsFor "test" 4 true 15) valueC with
          | some r => r
          | none => dictUnsigned4
        let expected :=
          #[.cell expectedRoot, .slice valueSliceD, intV (-1)]
        expectOkStack "replace-hit/unsigned" got expected },
    { name := "unit/runtime/replace-miss/null" -- [B5]
      run := do
        let got := runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueA key4ASlice .null 4)
        let expected := #[.null, intV 0]
        expectOkStack "replace-miss/null" got expected },
    { name := "unit/runtime/replace-miss/nonempty" -- [B5]
      run := do
        let got := runDICTREPLACEGETBDirect instrSlice (mkSliceCase valueA key4DSlice (.cell dictSlice4Miss) 4)
        let expected := #[.cell dictSlice4Miss, intV 0]
        expectOkStack "replace-miss/nonempty" got expected }
  ]
  oracle := #[
    -- [B3][B5]
    mkCase "oracle/slice/hit/4" (mkSliceCase valueD key4ASlice (.cell dictSlice4) 4),
    -- [B3][B5]
    mkCase "oracle/slice/hit/8" (mkSliceCase valueC key8BSlice (.cell dictSlice8) 8),
    -- [B3][B5]
    mkCase "oracle/slice/hit/0" (mkSliceCase valueA key0Slice (.cell dictSlice0) 0),
    -- [B3][B5]
    mkCase "oracle/slice/miss/null" (mkSliceCase valueA key4BSlice .null 4),
    -- [B3][B5]
    mkCase "oracle/slice/miss/nonempty" (mkSliceCase valueB key4DSlice (.cell dictSlice4Miss) 4),
    -- [B3][B5]
    mkCase "oracle/slice/miss/null-1023" (mkSliceCase valueA key1023Slice .null 1023),
    -- [B3]
    mkCase "oracle/slice/short" (mkSliceCase valueA key4ShortSlice (.cell dictSlice4) 4),

    -- [B4][B5]
    mkCase "oracle/int/signed-hit" (mkIntCase valueA (-8) (.cell dictSigned4) 4) instrSigned,
    -- [B4][B5]
    mkCase "oracle/int/signed-hit-7" (mkIntCase valueB 7 (.cell dictSigned4) 4) instrSigned,
    -- [B4][B5]
    mkCase "oracle/int/signed-miss" (mkIntCase valueC 6 (.cell dictSigned4) 4) instrSigned,
    -- [B4][B5]
    mkCase "oracle/int/signed-null" (mkIntCase valueA 6 .null 4) instrSigned,
    -- [B4][B5]
    mkCase "oracle/int/unsigned-hit" (mkIntCase valueC 15 (.cell dictUnsigned4) 4) instrSignedUnsigned,
    -- [B4][B5]
    mkCase "oracle/int/unsigned-miss" (mkIntCase valueD 3 (.cell dictUnsigned4) 4) instrSignedUnsigned,

    -- [B2]
    mkCase "oracle/underflow/empty" #[],
    -- [B2]
    mkCase "oracle/underflow/one" #[.builder valueA],
    -- [B2]
    mkCase "oracle/underflow/two" (#[.builder valueA, .slice key4ASlice]),
    -- [B2]
    mkCase "oracle/underflow/three" (#[.builder valueA, .slice key4ASlice, .cell dictSlice4]),

    -- [B2]
    mkCase "oracle/range/n-negative" (mkSliceCase valueA key4ASlice (.cell dictSlice4) (-1)),
    -- [B2]
    mkCase "oracle/range/n-too-large" (mkSliceCase valueA key4ASlice (.cell dictSlice4) 1024),
    -- [B2]
    mkCase "oracle/range/n-nan" (#[.builder valueA, .slice key4ASlice, .cell dictSlice4, .int .nan ]),

    -- [B4]
    mkCase "oracle/int/signed/high" (mkIntCase valueA 8 (.cell dictSigned4) 4) instrSigned,
    -- [B4]
    mkCase "oracle/int/signed/low" (mkIntCase valueA (-9) (.cell dictSigned4) 4) instrSigned,
    -- [B4]
    mkCase "oracle/int/unsigned/high" (mkIntCase valueA 16 (.cell dictUnsigned4) 4) instrSignedUnsigned,
    -- [B4]
    mkCase "oracle/int/unsigned/neg" (mkIntCase valueA (-1) (.cell dictUnsigned4) 4) instrSignedUnsigned,

    -- [B6]
    mkCase "oracle/type/value-not-builder" (#[.int (.num 7), .slice key4ASlice, .cell dictSlice4, intV 4]),
    -- [B6]
    mkCase "oracle/type/key-not-int" (mkSliceCase valueA key4ASlice (.cell dictSigned4) 4) instrSigned,
    -- [B6]
    mkCase "oracle/type/key-not-slice" (#[.builder valueA, .int (.num 7), .cell dictSlice4, intV 4]),
    -- [B6]
    mkCase "oracle/type/dict-not-cell" (mkIntCase valueA 7 (.tuple #[]) 4) instrSigned,

    -- [B7]
    mkCase "oracle/malformed-root/slice" (mkSliceCase valueA key4ASlice (.cell malformedDict) 4),
    -- [B7]
    mkCase "oracle/malformed-root/int" (mkIntCase valueA 1 (.cell malformedDict) 4) instrSigned,

    -- [B6]
    mkCase "oracle/builder/overflow" (mkSliceCase valueHuge key4ASlice (.cell dictSlice4) 4),

    -- [B9]
    mkCodeCase "oracle/code/f44d" (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF44d,
    -- [B9]
    mkCodeCase "oracle/code/f44e" (mkIntCase valueA 7 (.cell dictSigned4) 4) rawF44e,
    -- [B9]
    mkCodeCase "oracle/code/f44f" (mkIntCase valueA 15 (.cell dictUnsigned4) 4) rawF44f,
    -- [B9]
    mkCodeCase "oracle/code/f44c" (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF44c,
    -- [B9]
    mkCodeCase "oracle/code/f450" (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF450,
    -- [B9]
    mkCodeCase "oracle/code/trunc-f4" (mkSliceCase valueA key4ASlice (.cell dictSlice4) 4) rawF4,

    -- [B10]
    mkGasCase "oracle/gas/miss-exact" (mkSliceCase valueA key4ASlice .null 4) instrSlice missGas (oracleGasLimitsExact missGas),
    -- [B10]
    mkGasCase "oracle/gas/miss-exact-minus-one" (mkSliceCase valueA key4ASlice .null 4) instrSlice missGasMinusOne
      (oracleGasLimitsExactMinusOne missGas),
    -- [B10][B12]
    mkGasCase "oracle/gas/hit-exact" (mkSliceCase valueD key4ASlice (.cell dictSlice4) 4) instrSlice hitGas (oracleGasLimitsExact hitGas),
    -- [B10]
    mkGasCase "oracle/gas/hit-exact-minus-one" (mkSliceCase valueD key4ASlice (.cell dictSlice4) 4) instrSlice hitGasMinusOne
      (oracleGasLimitsExactMinusOne hitGas)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTREPLACEGETBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREPLACEGETB
