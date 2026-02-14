import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETNEXT

/-!
INSTRUCTION: DICTUGETNEXT

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDict` must dispatch only when opcode is `.dictGetNear`.
   - Any other opcode falls through via `next`, so fallback behavior is preserved.

2. [B2] Runtime preamble checks and typed stack pops.
   - `checkUnderflow 3` enforces key, dictionary, `n`.
   - `popNatUpTo 256` validates `n` type/range (`n<0` and `n>256` are failures).
   - `popMaybeCell` accepts `.null` and `.cell`; other values fail.
   - `popIntFinite` validates key type and finite values.

3. [B3] Unsigned integer hint conversion vs. fallback path.
   - `dictKeyBits? key n true` success routes to nearest search.
   - Conversion failure for `n`-incompatible keys routes to fallback.
   - For unsigned mode, fallback is only triggered for negative keys (`sgn(key) < 0`), because `cond := (0 ≤ key) != goUp` with `goUp=true`.
   - In this opcode, `goUp=true` and `allowEq=false`.

4. [B4] Nearest search branches for converted hints.
   - Nearest miss pushes only `0`.
   - Nearest hit pushes `(valueSlice, keyInt, -1)` and converts key back via `bitsToNat` (no truncation of unsigned payload).

5. [B5] Fallback nearest/near-max branches for negative out-of-range keys.
   - `dictMinMaxWithCells(...n, false, false)` selects the current largest key.
   - Non-empty dictionary returns that key/value.
   - Empty/null dictionary returns `0`.

6. [B6] Traversal failures.
   - Malformed dictionary structures can fail in nearest path and fallback path via `.dictErr`.

7. [B7] Assembler/decoder behavior.
   - `.dictGetNear` with args4 must satisfy `4 ≤ args4 ≤ 15`; `args4=12` encodes to `0xF47C`.
   - `.dictGetNear 12` decodes from raw word `0xF47C` (and neighbors `0xF474..0xF47F` are in-family).
   - Args outside `[4,15]` are rejected by assembler.
   - Truncated prefixes / invalid families are not decoded.

8. [B8] Gas accounting.
   - No explicit extra `cellCreateGasPrice` branch exists in the int-key success path (Lean matches C++ and neither emits that extra gas charge here).
   - Exact-gas-success and exact-gas-minus-one-failure are still tested for a deterministic miss path.

TOTAL BRANCHES: 8

Each oracle test below is tagged [B#] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTUGETNEXT" }

private def instr : Instr := .dictGetNear 12

private def dispatchSentinel : Int := 10031

private def assembleNoRefCell! (label : String) (code : Array Instr) : Cell :=
  match assembleCp0 code.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assemble failed: {reprStr e}"

private def mkDictSetSliceRootUnsigned! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none =>
            panic! s!"{label}: invalid unsigned key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary input"

private def valueA : Slice := mkSliceFromBits (natToBits 0xA0 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB0 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC0 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD0 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE0 8)

private def dict8A : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict8A" 8 #[(0, valueA), (5, valueB), (128, valueC), (255, valueD)]

private def dict8B : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict8B" 8 #[(1, valueC), (200, valueA)]

private def dict0 : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict0" 0 #[(0, valueE)]

private def dict256 : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict256" 256 #[(0, valueA), (maxInt257, valueB)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def rawF474 : Cell :=
  Cell.mkOrdinary (natToBits 0xF474 16) #[]

private def rawF47C : Cell :=
  Cell.mkOrdinary (natToBits 0xF47C 16) #[]

private def rawF47D : Cell :=
  Cell.mkOrdinary (natToBits 0xF47D 16) #[]

private def rawF47F : Cell :=
  Cell.mkOrdinary (natToBits 0xF47F 16) #[]

private def rawTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def stack3 (key : Int) (dictCell : Value) (n : Int) : Array Value :=
  #[intV key, dictCell, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
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

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetNear instr stack

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetNear .add (VM.push (intV dispatchSentinel)) stack

private def genDICTUGETNEXT (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 30
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow-one" (#[(intV 7)]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow-two" (stack3 7 dict8A 8 |>.take 2), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit-8-0" (stack3 0 dict8A 8), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/hit-8-6" (stack3 6 dict8A 8), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/hit-8-126" (stack3 126 dict8B 8), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/hit-8-254" (stack3 254 dict8A 8), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit-256-0" (stack3 0 dict256 256), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit-256-1" (stack3 1 dict256 256), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit-null-0" (stack3 0 dict0 0), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/miss-8-255" (stack3 255 dict8A 8), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/miss-8-256" (stack3 256 dict8A 8), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss-0-1" (stack3 1 dict0 0), rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/miss-256-overflow" (stack3 (maxInt257 + 1) dict256 256), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/miss-empty-8" (stack3 5 (.null) 8), rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/fallback-neg-8" (stack3 (-1) dict8A 8), rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/fallback-neg-8-hi" (stack3 (-129) dict8B 8), rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/fallback-neg-256" (stack3 (-1) dict256 256), rng1)
    else if shape = 18 then
      (mkCase "fuzz/ok/fallback-neg-0" (stack3 (-1) dict0 0), rng1)
    else if shape = 19 then
      (mkCase "fuzz/ok/fallback-neg-empty-8" (stack3 (-1) (.null) 8), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/n-type" (#[intV 7, dict8A, .cell Cell.empty]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/n-negative" (stack3 7 dict8A (-1)), rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/n-too-large" (stack3 7 dict8A 257), rng1)
    else if shape = 23 then
      (mkCase "fuzz/err/dict-type" (stack3 7 (.tuple #[]) 8), rng1)
    else if shape = 24 then
      (mkCase "fuzz/err/key-type" (#[.slice valueA, dict8A, intV 8]), rng1)
    else if shape = 25 then
      (mkCase "fuzz/err/key-nan" (#[.int .nan, dict8A, intV 8]), rng1)
    else if shape = 26 then
      (mkCase "fuzz/ok/malformed-nearest" (stack3 7 (.cell malformedDict) 8), rng1)
    else if shape = 27 then
      (mkCase "fuzz/ok/malformed-fallback" (stack3 (-1) (.cell malformedDict) 8), rng1)
    else if shape = 28 then
      (mkCaseCode "fuzz/code/raw/f47c" (stack3 7 dict8A 8) rawF47C, rng1)
    else if shape = 29 then
      (mkCaseCode "fuzz/code/raw/trunc" #[] rawTruncated8, rng1)
    else if shape = 30 then
      (mkCase "fuzz/gas/exact" (stack3 7 dict8A 8)
        #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact baseGas), rng1)
    else
      (mkCase "fuzz/gas/exact-minus-one" (stack3 7 dict8A 8)
        #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := stack3 0 dict8A 8
        let expected := stack ++ #[intV dispatchSentinel]
        expectOkStack "dispatch-fallback" (runDispatchFallback stack) expected
    },
    { name := "unit/opcode/assemble/exact" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF47C 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF47C, got bits={c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble failed: {e}")
    },
    { name := "unit/opcode/assemble/reject-oob-args" -- [B7]
      run := do
        match assembleCp0 [.dictGetNear 3] with
        | .ok _ => throw (IO.userError "assemble accepted args=3")
        | .error _ => pure ()
        match assembleCp0 [.dictGetNear 16] with
        | .ok _ => throw (IO.userError "assemble accepted args=16")
        | .error _ => pure ()
    },
    { name := "unit/direct/hit-paths" -- [B4]
      run := do
        expectOkStack "direct/hit-8-0" (runDirect (stack3 0 dict8A 8))
          #[.slice valueB, intV 5, intV (-1)]
        expectOkStack "direct/hit-8-5" (runDirect (stack3 5 dict8A 8))
          #[.slice valueC, intV 128, intV (-1)]
        expectOkStack "direct/hit-256-0" (runDirect (stack3 0 dict256 256))
          #[.slice valueB, intV maxInt257, intV (-1)]
    },
    { name := "unit/direct/miss-paths" -- [B4][B5]
      run := do
        expectOkStack "direct/miss-8-255" (runDirect (stack3 255 dict8A 8)) #[intV 0]
        expectOkStack "direct/miss-8-overflow" (runDirect (stack3 256 dict8A 8)) #[intV 0]
        expectOkStack "direct/miss-8-null" (runDirect (stack3 5 (.null) 8)) #[intV 0]
        expectOkStack "direct/miss-0-1" (runDirect (stack3 1 dict0 0)) #[intV 0]
    },
    { name := "unit/direct/fallback-paths" -- [B5]
      run := do
        expectOkStack "direct/fallback-neg-8" (runDirect (stack3 (-1) dict8A 8))
          #[.slice valueD, intV 255, intV (-1)]
        expectOkStack "direct/fallback-neg-0-empty" (runDirect (stack3 (-1) (.null) 0))
          #[intV 0]
        expectOkStack "direct/fallback-neg-256" (runDirect (stack3 (-7) dict256 256))
          #[.slice valueB, intV maxInt257, intV (-1)]
    },
    { name := "unit/direct/validation-errors" -- [B2][B3][B6]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[intV 7]) .stkUnd
        expectErr "n-negative" (runDirect (stack3 7 dict8A (-1))) .rangeChk
        expectErr "n-type" (runDirect #[intV 7, dict8A, .cell Cell.empty]) .typeChk
        expectErr "n-too-large" (runDirect (stack3 7 dict8A 257)) .rangeChk
        expectErr "dict-type" (runDirect (stack3 7 (.tuple #[]) 8)) .typeChk
        expectErr "key-type" (runDirect #[.null, dict8A, intV 8]) .typeChk
        expectErr "key-nan" (runDirect (#[.int .nan, dict8A, intV 8])) .typeChk
    },
    { name := "unit/direct/malformed-dictionary" -- [B6]
      run := do
        expectErr "malformed-nearest" (runDirect (stack3 7 (.cell malformedDict) 8)) .dictErr
        expectErr "malformed-fallback" (runDirect (stack3 (-1) (.cell malformedDict) 8)) .dictErr
    },
    { name := "unit/decode/neighbors-and-truncated" -- [B7]
      run := do
        let stream : Slice :=
          Slice.ofCell <| Cell.mkOrdinary (rawF474.bits ++ rawF47C.bits ++ rawF47D.bits ++ rawF47F.bits) #[]
        let s1 ← expectDecodeStep "decode/f474" stream (.dictGetNear 4) 16
        let s2 ← expectDecodeStep "decode/f47c" s1 (.dictGetNear 12) 16
        let s3 ← expectDecodeStep "decode/f47d" s2 (.dictGetNear 13) 16
        let s4 ← expectDecodeStep "decode/f47f" s3 (.dictGetNear 15) 16
        if s4.bitsRemaining + s4.refsRemaining ≠ 0 then
          throw (IO.userError "decode chain did not consume full stream")
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated prefix")
    }
  ]
  oracle := #[
    mkCase "ok/hit/8/zero" (stack3 0 dict8A 8), -- [B4]
    mkCase "ok/hit/8/one" (stack3 1 dict8A 8), -- [B4]
    mkCase "ok/hit/8/six" (stack3 6 dict8A 8), -- [B4]
    mkCase "ok/hit/8/126" (stack3 126 dict8B 8), -- [B4]
    mkCase "ok/hit/8/254" (stack3 254 dict8A 8), -- [B4]
    mkCase "ok/hit/256/zero" (stack3 0 dict256 256), -- [B4]
    mkCase "ok/hit/256/one" (stack3 1 dict256 256), -- [B4]
    mkCase "ok/miss/8/255" (stack3 255 dict8A 8), -- [B4]
    mkCase "ok/miss/8/greater-than-255" (stack3 300 dict8A 8), -- [B3][B4]
    mkCase "ok/miss/8/empty" (stack3 5 (.null) 8), -- [B4]
    mkCase "ok/miss/0/one" (stack3 1 dict0 0), -- [B4]
    mkCase "ok/miss/256/overflow" (stack3 (maxInt257 + 1) dict256 256), -- [B3][B4]
    mkCase "ok/fallback/neg/8" (stack3 (-1) dict8A 8), -- [B3][B5]
    mkCase "ok/fallback/neg/8-hi" (stack3 (-128) dict8A 8), -- [B3][B5]
    mkCase "ok/fallback/neg/8-empty" (stack3 (-1) (.null) 8), -- [B5]
    mkCase "ok/fallback/neg/0" (stack3 (-1) dict0 0), -- [B3][B5]
    mkCase "ok/fallback/neg/256" (stack3 (-64) dict256 256), -- [B3][B5]
    mkCase "ok/fallback/neg/256-empty" (stack3 (-64) (.null) 256), -- [B5]
    mkCaseCode "ok/raw/F474" (stack3 7 dict8A 8) rawF474, -- [B7]
    mkCaseCode "ok/code/raw/F47C" (stack3 7 dict8A 8) rawF47C, -- [B7]
    mkCaseCode "ok/code/raw/F47D" (stack3 7 dict8A 8) rawF47D, -- [B7]
    mkCaseCode "ok/code/raw/F47F" (stack3 7 dict8A 8) rawF47F, -- [B7]
    mkCaseCode "err/code/raw/trunc8" #[] rawTruncated8, -- [B7]
    mkCase "err/underflow-empty" #[], -- [B2]
    mkCase "err/underflow-one" (#[intV 7]), -- [B2]
    mkCase "err/underflow-two" (stack3 7 dict8A 8 |>.take 2), -- [B2]
    mkCase "err/n-type" (#[intV 7, dict8A, .tuple #[]]), -- [B3]
    mkCase "err/n-nan" (#[intV 7, dict8A, .int .nan]), -- [B3]
    mkCase "err/n-negative" (stack3 7 dict8A (-1)), -- [B2]
    mkCase "err/n-too-large" (stack3 7 dict8A 257), -- [B2]
    mkCase "err/dict-type" (stack3 7 (.tuple #[]) 8), -- [B2]
    mkCase "err/key-type" (#[.cell Cell.empty, dict8A, intV 8]), -- [B3]
    mkCase "err/key-nan" (#[.int .nan, dict8A, intV 8]), -- [B3]
    mkCase "err/dict-malformed-nearest" (stack3 7 (.cell malformedDict) 8), -- [B6]
    mkCase "err/dict-malformed-fallback" (stack3 (-1) (.cell malformedDict) 8), -- [B6]
    mkCase "gas/exact-base" (stack3 7 dict8A 8)
      #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact baseGas), -- [B8]
    mkCase "gas/exact-minus-one" (stack3 7 dict8A 8)
      #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExactMinusOne baseGasMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTUGETNEXT }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETNEXT
