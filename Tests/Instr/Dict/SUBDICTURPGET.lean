import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.SUBDICTURPGET

/-!
INSTRUCTION: SUBDICTURPGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch/path selection:
   - `.dictExt (.subdictGet ...)` is handled by `execInstrDictExt`.
   - Non-`dictExt` instructions must forward to `next` (fallback path).
2. [B2] Stack arity/type precheck:
   - `VM.checkUnderflow 4` rejects stacks with fewer than 4 items.
   - `n` and `k` are popped as naturals with upper bound checks.
    3. [B3] `n` parsing (`popNatUpTo 1023`) and `k` parsing (`popNatUpTo (min 256 n)`):
    - `n = .nan` -> `.rangeChk`, `n < 0`, `n > 1023` -> `.rangeChk`.
    - `k = .nan` -> `.rangeChk`, `k < 0`, `k > min 256 n` -> `.rangeChk`.
   - `k = 0` is valid and keeps prefix length zero.
4. [B4] Operand typing:
   - `dictCell?` accepts `.cell` and `.null`, rejects other non-cell values (`.typeChk`).
   - key must be finite integer (`popIntFinite`), non-int -> `.typeChk`, `NaN` -> `.intOv`.
5. [B5] Unsigned key materialization:
   - `dictKeyBits? idx k true` is used; if it fails, this Lean path maps to `.cellUnd`
     (e.g. key too wide for fixed width, negative key).
6. [B6] Sub-dictionary extraction:
   - `k = 0` returns unchanged dictionary root.
   - mismatched prefix returns `null`.
   - matching prefix with `rp = true` rewrites key-prefix labels and may rebuild the root (`created = 1` when changed).
7. [B7] Error mapping:
   - for this exact opcode (`intKey = true, unsigned = true, rp = true`) `.error .cellUnd` is propagated as `.cellUnd`.
   - malformed dictionary/trie structure propagates `.dictErr` via `dictExtractPrefixSubdictWithCells`.
8. [B8] Assembler behavior:
   - `assembleCp0` rejects all `.dictExt` instructions (`.invOpcode`), including this opcode.
9. [B9] Decoder boundaries:
   - `0xF4B5..0xF4B7` map to `.dictExt (.subdictGet false/true/true/false, true/true/false, true/true/true)` respectively.
   - `0xF4B4` and `0xF4B8` are not valid decode targets and must return `.invOpcode`.
   - 8-bit/15-bit truncations must also error.
10. [B10] Gas:
   - base cost branch from `computeExactGasBudget` must succeed at exact limit and fail at exact-1.
   - changed-prefix success also includes `created * cellCreateGasPrice` surcharge.

TOTAL BRANCHES: 10
-/

private def suiteId : InstrId := { name := "SUBDICTURPGET" }

private def instr : Instr := .dictExt (.subdictGet true true true)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def rawF4B5 : Cell := raw16 0xF4B5
private def rawF4B6 : Cell := raw16 0xF4B6
private def rawF4B7 : Cell := raw16 0xF4B7
private def rawF4B4 : Cell := raw16 0xF4B4
private def rawF4B8 : Cell := raw16 0xF4B8
private def rawF4Trunc8 : Cell := raw8 0xF4
private def rawF4Trunc15 : Cell :=
  Cell.mkOrdinary (natToBits (0xF4B7 >>> 1) 15) #[]

private def fallbackSentinel : Int := 80_901

private def valueA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xA5 8) #[])
private def valueB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x5A 8) #[])
private def valueC : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xCC 8) #[])

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits : BitString :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _, _, _) => root := r
      | .ok (none, _, _, _) => panic! s!"{label}: unexpected none"
      | .error e => panic! s!"{label}: dictSetSliceWithCells failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictRoot4 : Cell :=
  mkDictSetSliceRoot! "SUBDICTURPGET.dictRoot4" 4 #[(5, valueA), (7, valueB), (12, valueC)]

private def dictRoot2ExpectedForK2 : Cell :=
  mkDictSetSliceRoot! "SUBDICTURPGET.dictRoot2ExpectedForK2" 2 #[(1, valueA), (3, valueB)]

private def dictRoot0Single : Cell :=
  mkDictSetSliceRoot! "SUBDICTURPGET.dictRoot0Single" 0 #[(0, valueA)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def baseGasExact : OracleGasLimits := oracleGasLimitsExact baseGas
private def baseGasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne

private def hitCreated : Nat :=
  match dictExtractPrefixSubdictWithCells (some dictRoot4) 4 (natToBits 1 2) 2 true with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def hitGas : Int :=
  baseGas + Int.ofNat hitCreated * cellCreateGasPrice

private def hitGasMinusOne : Int :=
  baseGasMinusOne + Int.ofNat hitCreated * cellCreateGasPrice

private def hitGasExact : OracleGasLimits := oracleGasLimitsExact hitGas
private def hitGasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne hitGasMinusOne

private def runSubdictGetDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runSubdictGetDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (intV fallbackSentinel)) stack

private def expectDecodeOk (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e => throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr actual}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits decoded, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected end of stream, got {reprStr rest}")
      else pure ()

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected {expected}, got decode success {reprStr actual} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := rawF4B7)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[]
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (code : Cell := rawF4B7)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit]
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStack
    (key : Int)
    (dict : Value)
    (n : Int)
    (k : Int) : Array Value :=
  #[intV key, intV k, dict, intV n]

private def genSUBDICTURPGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 32
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/hit/remove-prefix" (mkStack 1 (.cell dictRoot4) 4 2), rng1)
    else if shape = 1 then
      (mkCase "fuzz/hit/zero-prefix" (mkStack 0 (.cell dictRoot4) 4 0), rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/prefix-mismatch" (mkStack 2 (.cell dictRoot4) 4 2), rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null" (mkStack 1 (.null) 4 2), rng1)
    else if shape = 4 then
      (mkCase "fuzz/miss/k0-null" (mkStack 0 (.null) 0 0), rng1)
    else if shape = 5 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 6 then
      (mkCase "fuzz/underflow/one" #[intV 4], rng1)
    else if shape = 7 then
      (mkCase "fuzz/underflow/two" #[intV 4, .cell dictRoot4], rng1)
    else if shape = 8 then
      (mkCase "fuzz/underflow/three" #[intV 4, intV 2, .cell dictRoot4], rng1)
    else if shape = 9 then
      (mkCase "fuzz/nan/n" #[intV 0, intV 4, .cell dictRoot4, .int .nan], rng1)
    else if shape = 10 then
      (mkCase "fuzz/nan/k" #[intV 1, .int .nan, .cell dictRoot4, intV 4], rng1)
    else if shape = 11 then
      (mkCase "fuzz/range/n-negative" (mkStack 0 (.cell dictRoot4) (-1) 1), rng1)
    else if shape = 12 then
      (mkCase "fuzz/range/n-too-large" (mkStack 0 (.cell dictRoot4) 1024 1), rng1)
    else if shape = 13 then
      (mkCase "fuzz/range/k-negative" (mkStack 1 (.cell dictRoot4) 4 (-1)), rng1)
    else if shape = 14 then
      (mkCase "fuzz/range/k-too-large" (mkStack 1 (.cell dictRoot4) 4 257), rng1)
    else if shape = 15 then
      (mkCase "fuzz/key/type-non-int" #[.slice (mkSliceFromBits (natToBits 1 2)), intV 2, .cell dictRoot4, intV 4], rng1)
    else if shape = 16 then
      (mkCase "fuzz/key/intov" (mkStack 16 (.cell dictRoot4) 4 4), rng1)
    else if shape = 17 then
      (mkCase "fuzz/key/int-negative" (mkStack (-1) (.cell dictRoot4) 4 4), rng1)
    else if shape = 18 then
      (mkCase "fuzz/root/type-slice" (mkStack 1 (.slice (mkSliceFromBits (natToBits 0 1))) 4 2), rng1)
    else if shape = 19 then
      (mkCase "fuzz/dict/malformed" (mkStack 1 (.cell malformedDict) 4 2), rng1)
    else if shape = 20 then
      (mkCase "fuzz/decode/f4b5" #[] rawF4B5, rng1)
    else if shape = 21 then
      (mkCase "fuzz/decode/f4b6" #[] rawF4B6, rng1)
    else if shape = 22 then
      (mkCase "fuzz/decode/invalid/below" #[] rawF4B4, rng1)
    else if shape = 23 then
      (mkCase "fuzz/decode/invalid/above" #[] rawF4B8, rng1)
    else if shape = 24 then
      (mkGasCase "fuzz/gas/exact-base" (mkStack 1 (.null) 4 2) baseGas baseGasExact rawF4B7, rng1)
    else if shape = 25 then
      (mkGasCase "fuzz/gas/minus-one-base" (mkStack 1 (.null) 4 2) baseGasMinusOne baseGasExactMinusOne rawF4B7, rng1)
    else if shape = 26 then
      (mkGasCase "fuzz/gas/exact-hit-changed" (mkStack 1 (.cell dictRoot4) 4 2) hitGas hitGasExact rawF4B7, rng1)
    else if shape = 27 then
      (mkGasCase "fuzz/gas/minus-one-hit-changed" (mkStack 1 (.cell dictRoot4) 4 2) hitGasMinusOne hitGasExactMinusOne rawF4B7, rng1)
    else if shape = 28 then
      (mkCase "fuzz/assemble/inv" #[] rawF4B7, rng1)
    else if shape = 29 then
      (mkCase "fuzz/decode/trunc8" #[] rawF4Trunc8, rng1)
    else if shape = 30 then
      (mkCase "fuzz/decode/trunc15" #[] rawF4Trunc15, rng1)
    else
      (mkCase "fuzz/k/type-bad" #[intV 1, .tuple #[], .cell dictRoot4, intV 4], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let expected : Array Value :=
          #[intV 1, intV 2, .cell dictRoot4, intV 4, intV fallbackSentinel]
        match runSubdictGetDispatchFallback (mkStack 1 (.cell dictRoot4) 4 2) with
        | .ok st =>
            if st == expected then
              pure ()
            else
              throw (IO.userError s!"dispatch fallback: expected {reprStr expected}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch fallback failed with {e}") },
    { name := "unit/runtime/underflow/empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runSubdictGetDirect #[]) .stkUnd },
    { name := "unit/runtime/underflow/one" -- [B2]
      run := do
        expectErr "underflow-one" (runSubdictGetDirect #[intV 4]) .stkUnd },
    { name := "unit/runtime/underflow/two" -- [B2]
      run := do
        expectErr "underflow-two" (runSubdictGetDirect #[intV 4, intV 2]) .stkUnd },
    { name := "unit/runtime/underflow/three" -- [B2]
      run := do
        expectErr "underflow-three" (runSubdictGetDirect #[intV 4, intV 2, .cell dictRoot4]) .stkUnd },
    { name := "unit/runtime/range/nan-n" -- [B3]
      run := do
        expectErr "n-nan" (runSubdictGetDirect #[intV 1, intV 2, .cell dictRoot4, .int .nan]) .rangeChk },
    { name := "unit/runtime/range/n-negative" -- [B3]
      run := do
        expectErr "n-negative" (runSubdictGetDirect (mkStack 1 (.cell dictRoot4) (-1) 2)) .rangeChk },
    { name := "unit/runtime/range/n-too-large" -- [B3]
      run := do
        expectErr "n-too-large" (runSubdictGetDirect (mkStack 1 (.cell dictRoot4) 1024 2)) .rangeChk },
    { name := "unit/runtime/range/k-non-int" -- [B3][B4]
      run := do
        expectErr "k-non-int" (runSubdictGetDirect #[intV 1, .tuple #[], .cell dictRoot4, intV 4]) .typeChk },
    { name := "unit/runtime/range/k-negative" -- [B3]
      run := do
        expectErr "k-negative" (runSubdictGetDirect (mkStack 1 (.cell dictRoot4) 4 (-1))) .rangeChk },
    { name := "unit/runtime/range/k-too-large" -- [B3]
      run := do
        expectErr "k-too-large" (runSubdictGetDirect (mkStack 1 (.cell dictRoot4) 4 257)) .rangeChk },
    { name := "unit/runtime/type/root-non-cell" -- [B4]
      run := do
        expectErr "root-non-cell" (runSubdictGetDirect (mkStack 1 (.tuple #[]) 4 2)) .typeChk },
    { name := "unit/runtime/type/key-non-int" -- [B4][B5]
      run := do
        expectErr "key-non-int" (runSubdictGetDirect #[.slice (mkSliceFromBits (natToBits 1 2)), intV 2, .cell dictRoot4, intV 4]) .typeChk },
    { name := "unit/runtime/key/int-nan" -- [B5]
      run := do
        expectErr "key-int-nan" (runSubdictGetDirect #[.int .nan, intV 2, .cell dictRoot4, intV 4]) .intOv },
    { name := "unit/runtime/key/out-of-range-positive" -- [B5]
      run := do
        expectErr "key-out-of-range-positive" (runSubdictGetDirect (mkStack 16 (.cell dictRoot4) 4 4)) .cellUnd },
    { name := "unit/runtime/key/out-of-range-negative" -- [B5]
      run := do
        expectErr "key-out-of-range-negative" (runSubdictGetDirect (mkStack (-1) (.cell dictRoot4) 4 4)) .cellUnd },
    { name := "unit/runtime/execution/miss-null" -- [B6]
      run := do
        expectOkStack "miss-null" (runSubdictGetDirect (mkStack 1 .null 4 2)) #[.null] },
    { name := "unit/runtime/execution/miss-prefix-mismatch" -- [B6]
      run := do
        expectOkStack "miss-mismatch" (runSubdictGetDirect (mkStack 2 (.cell dictRoot4) 4 2)) #[.null] },
    { name := "unit/runtime/execution/hit-k0-unchanged" -- [B6]
      run := do
        expectOkStack "hit-k0" (runSubdictGetDirect (mkStack 0 (.cell dictRoot4) 4 0)) #[.cell dictRoot4] },
    { name := "unit/runtime/execution/hit-prefix-remove" -- [B6]
      run := do
        expectOkStack "hit-prefix-remove"
          (runSubdictGetDirect (mkStack 1 (.cell dictRoot4) 4 2))
          #[.cell dictRoot2ExpectedForK2] },
    { name := "unit/runtime/execution/unaltered-prefix-beyond-key" -- [B6]
      run := do
        expectOkStack "k0-null-root"
          (runSubdictGetDirect (mkStack 0 (.null) 0 0))
          #[.null] },
    { name := "unit/runtime/error/malformed-root" -- [B7]
      run := do
        expectErr "malformed-root" (runSubdictGetDirect (mkStack 1 (.cell malformedDict) 4 2)) .cellUnd },
    { name := "unit/assemble/reject" -- [B8]
      run := do
        expectAssembleErr "assemble-inv" instr .invOpcode },
    { name := "unit/decode/f4b5-chain" -- [B9]
      run := do
        expectDecodeOk "decode/f4b5" rawF4B5 (.dictExt (.subdictGet false false true))
        expectDecodeOk "decode/f4b6" rawF4B6 (.dictExt (.subdictGet true false true))
        expectDecodeOk "decode/f4b7" rawF4B7 (.dictExt (.subdictGet true true true)) },
    { name := "unit/decode/boundaries" -- [B9]
      run := do
        expectDecodeErr "decode/f4b4" rawF4B4 .invOpcode
        expectDecodeErr "decode/f4b8" rawF4B8 .invOpcode
        expectDecodeErr "decode/trunc8" rawF4Trunc8 .invOpcode
        expectDecodeErr "decode/trunc15" rawF4Trunc15 .invOpcode },
  ]
  oracle := #[
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one" #[intV 4],
    mkCase "oracle/underflow/two" #[intV 4, intV 2],
    mkCase "oracle/underflow/three" #[intV 4, intV 2, .cell dictRoot4],
    mkCase "oracle/range/nan" #[intV 1, intV 2, .cell dictRoot4, .int .nan],
    mkCase "oracle/range/n-negative" (mkStack 1 (.cell dictRoot4) (-1) 2),
    mkCase "oracle/range/n-too-large" (mkStack 1 (.cell dictRoot4) 1024 1),
    mkCase "oracle/range/k-negative" (mkStack 1 (.cell dictRoot4) 4 (-1)),
    mkCase "oracle/range/k-too-large" (mkStack 1 (.cell dictRoot4) 4 257),
    mkCase "oracle/range/k-non-int" #[intV 1, .tuple #[], .cell dictRoot4, intV 4],
    mkCase "oracle/type/root-non-cell" (mkStack 1 (.tuple #[]) 4 2),
    mkCase "oracle/type/key-non-int" #[.slice (mkSliceFromBits (natToBits 1 2)), intV 2, .cell dictRoot4, intV 4],
    mkCase "oracle/type/key-nan" #[.int .nan, intV 2, .cell dictRoot4, intV 4],
    mkCase "oracle/key/out-of-range-positive" (mkStack 16 (.cell dictRoot4) 4 4),
    mkCase "oracle/key/out-of-range-negative" (mkStack (-1) (.cell dictRoot4) 4 4),
    mkCase "oracle/runtime/k0" (mkStack 0 (.cell dictRoot4) 4 0),
    mkCase "oracle/runtime/k0-null" (mkStack 0 .null 0 0),
    mkCase "oracle/runtime/hit-remove-prefix" (mkStack 1 (.cell dictRoot4) 4 2),
    mkCase "oracle/runtime/miss-null" (mkStack 1 .null 4 2),
    mkCase "oracle/runtime/miss-prefix" (mkStack 2 (.cell dictRoot4) 4 2),
    mkCase "oracle/runtime/unmodified-root" (mkStack 3 (.cell dictRoot4) 4 0),
    mkCase "oracle/error/malformed-root" (mkStack 1 (.cell malformedDict) 4 2),
    mkCase "oracle/asm/reject" #[] rawF4B7,
    mkCase "oracle/decode/f4b5" #[] rawF4B5,
    mkCase "oracle/decode/f4b6" #[] rawF4B6,
    mkCase "oracle/decode/f4b7" #[] rawF4B7,
    mkCase "oracle/decode/invalid-below" #[] rawF4B4,
    mkCase "oracle/decode/invalid-above" #[] rawF4B8,
    mkCase "oracle/decode/trunc8" #[] rawF4Trunc8,
    mkCase "oracle/decode/trunc15" #[] rawF4Trunc15,
    mkGasCase "oracle/gas/exact-base-null" (mkStack 1 (.cell dictRoot4) 4 2) baseGas baseGasExact,
    mkGasCase "oracle/gas/exact-minus-one-base-null" (mkStack 1 (.cell dictRoot4) 4 2) baseGasMinusOne baseGasExactMinusOne,
    mkGasCase "oracle/gas/exact-hit-changed" (mkStack 1 (.cell dictRoot4) 4 2) hitGas hitGasExact,
    mkGasCase "oracle/gas/exact-minus-one-hit-changed" (mkStack 1 (.cell dictRoot4) 4 2) hitGasMinusOne hitGasExactMinusOne,
    mkGasCase "oracle/gas/exact-hit-k0" (mkStack 0 (.cell dictRoot4) 4 0) baseGas baseGasExact,
    mkGasCase "oracle/gas/exact-minus-one-hit-k0" (mkStack 0 (.cell dictRoot4) 4 0) baseGasMinusOne baseGasExactMinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genSUBDICTURPGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTURPGET
