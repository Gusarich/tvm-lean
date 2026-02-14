import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETNEXTEQ

/-!
INSTRUCTION: DICTUGETNEXTEQ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch:
   - `execInstrDictDictGetNear` only handles `.dictGetNear 13`; all other instructions must fall through to `next`.

2. [B2] Runtime preamble:
   - `checkUnderflow 3` requires key, dictionary, and `n`.
   - `popNatUpTo 256` validates `n` type/range.
   - Dictionary argument accepts `.null` or `.cell`; other tags fail with `typeChk`.
   - Key must be finite int (`popIntFinite`), otherwise `typeChk`.

3. [B3] Integer-key conversion and control split:
   - With args `13`, `allowEq=true`, `goUp=true`, `intKey=true`, `unsigned=true`.
   - `dictKeyBits?` with unsigned mode succeeds for `0 ≤ key < 2^n`.
   - If conversion fails, fallback branch uses `cond := (0 ≤ key) != goUp`.
   - For unsigned + `goUp=true`, negative keys set `cond=true`; positive/large keys set `cond=false`.

4. [B4] Nearest branch for in-range keys:
   - On hit, pushes `(valueSlice, keyInt, -1)`; `keyInt` is decoded via unsigned bit conversion.
   - On miss, pushes single `0`.
   - Traversal errors propagate as `dictErr`.

5. [B5] Fallback branch for negative out-of-range keys:
   - Executes `dictMinMaxWithCells` with `fetchMax := false` and `sgnd := false`.
   - For non-empty dictionaries returns `(valueSlice, keyInt, -1)` where key is the extreme selected by lookup policy.
   - Empty/null dict returns `0`.
   - Traversal errors propagate as `dictErr`.

6. [B6] Error paths:
   - Stack underflow, invalid `n` type/range, malformed dictionary structures, and NaN/type mismatches must fail with expected exceptions.

7. [B7] Assembler/decoder behavior:
   - `.dictGetNear` accepts only `args4 ∈ [4, 15]`.
   - `.dictGetNear 13` assembles to `0xF47D`.
   - Decode for `0xF474..0xF47F` maps to `dictGetNear 4..15`.
   - Truncated/short opcode prefixes must be decode errors.

8. [B8] Gas accounting:
   - No extra `cellCreateGasPrice` path is present in this instruction’s success path.
   - Verify exact-gas success and exact-gas-minus-one failure.

TOTAL BRANCHES: 8

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTUGETNEXTEQ" }

private def instr : Instr := .dictGetNear 13

private def dispatchSentinel : Int := 10039

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
      | .ok (some root1, _ok, _created, _loaded) => root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def valueA : Slice := mkSliceFromBits (natToBits 0xA0 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB0 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC0 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD0 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0xE0 8)
private def valueF : Slice := mkSliceFromBits (natToBits 0xF0 8)

private def dict8A : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict8A" 8 #[
    (0, valueA), (5, valueB), (128, valueC), (255, valueD)
  ]

private def dict8B : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict8B" 8 #[
    (1, valueE), (64, valueF)
  ]

private def dict256 : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict256" 256 #[
    (0, valueA), (maxInt257, valueB)
  ]

private def dict0 : Value :=
  .cell <| mkDictSetSliceRootUnsigned! "dict0" 0 #[(0, valueC)]

private def dictNull : Value := .null

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def rawF47B : Cell := Cell.mkOrdinary (natToBits 0xF47B 16) #[]
private def rawF47C : Cell := Cell.mkOrdinary (natToBits 0xF47C 16) #[]
private def rawF47D : Cell := Cell.mkOrdinary (natToBits 0xF47D 16) #[]
private def rawF47E : Cell := Cell.mkOrdinary (natToBits 0xF47E 16) #[]
private def rawF47F : Cell := Cell.mkOrdinary (natToBits 0xF47F 16) #[]
private def rawF47Trunc8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def exactGas : Int := computeExactGasBudget instr
private def exactGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def mkStack (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[intV key, dict, intV n]

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
  runHandlerDirectWithNext execInstrDictDictGetNear (.add) (VM.push (intV dispatchSentinel)) stack

private def addSuffixToCaseName (name : String) (rng0 : StdGen) : String × StdGen :=
  let (sfx, rng1) := randNat rng0 0 999_999
  (s!"{name}/{sfx}", rng1)

def genDictUGetNextEqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 30
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow/one" (#[intV 7]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow/two" (mkStack 7 dict8A 8 |>.take 2), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit-8-0" (mkStack 0 dict8A 8), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/hit-8-5" (mkStack 5 dict8A 8), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/hit-8-6" (mkStack 6 dict8A 8), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/hit-8-129" (mkStack 129 dict8A 8), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit-8-255" (mkStack 255 dict8A 8), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit-256-0" (mkStack 0 dict256 256), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit-256-max" (mkStack maxInt257 dict256 256), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/hit-0" (mkStack 0 dict0 0), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/miss-8-256" (mkStack 256 dict8A 8), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss-8-300" (mkStack 300 dict8A 8), rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/miss-8-257" (mkStack 257 dict8A 8), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/miss-8-empty" (mkStack 5 dictNull 8), rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/miss-0-1" (mkStack 1 dict0 0), rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/miss-oob-pos-256" (mkStack (maxInt257 + 1) dict256 256), rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/fallback-neg-8" (mkStack (-1) dict8A 8), rng1)
    else if shape = 18 then
      (mkCase "fuzz/ok/fallback-neg-256" (mkStack (-7) dict256 256), rng1)
    else if shape = 19 then
      (mkCase "fuzz/ok/fallback-neg-empty-8" (mkStack (-1) dictNull 8), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/n-type" (#[intV 7, dict8A, .cell Cell.empty]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/n-neg" (mkStack 7 dict8A (-1)), rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/n-over" (mkStack 7 dict8A 257), rng1)
    else if shape = 23 then
      (mkCase "fuzz/err/dict-type" (mkStack 7 (.tuple #[]) 8), rng1)
    else if shape = 24 then
      (mkCase "fuzz/err/key-type" (mkStack 7 (.null) 8 |>.set! 0 (.slice valueA)), rng1)
    else if shape = 25 then
      (mkCase "fuzz/err/key-nan" (mkStack 7 (.null) 8 |>.set! 0 (.int .nan)), rng1)
    else if shape = 26 then
      (mkCase "fuzz/err/malformed-nearest" (mkStack 7 (.cell malformedDict) 8), rng1)
    else if shape = 27 then
      (mkCase "fuzz/err/malformed-minmax" (mkStack (-1) (.cell malformedDict) 8), rng1)
    else if shape = 28 then
      (mkCaseCode "fuzz/code/raw/f47d" (mkStack 7 dict8A 8) rawF47D, rng1)
    else if shape = 29 then
      (mkCaseCode "fuzz/code/raw/trunc" #[] rawF47Trunc8, rng1)
    else if shape = 30 then
      (mkCase
        "fuzz/gas/exact"
        (mkStack 5 dict8A 8)
        (program := #[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        (gasLimits := oracleGasLimitsExact exactGas), rng1)
    else
      (mkCase
        "fuzz/gas/exact-minus-one"
        (mkStack 5 dict8A 8)
        (program := #[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (gasLimits := oracleGasLimitsExactMinusOne exactGasMinusOne), rng1)
  let (name', rng3) := addSuffixToCaseName case0.name rng2
  ({ case0 with name := name' }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := mkStack 7 dict8A 8
        let expected := stack.push (intV dispatchSentinel)
        expectOkStack "dispatch/fallback" (runDispatchFallback stack) expected
    },
    { name := "unit/opcode/assemble-exact" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF47D 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF47D encoding, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTUGETNEXTEQ failed: {e}")
    },
    { name := "unit/opcode/assemble-reject-low" -- [B7]
      run := do
        match assembleCp0 [Instr.dictGetNear 3] with
        | .ok _ =>
            throw (IO.userError "assemble accepted args4=3, expected rangeChk")
        | .error _ =>
            pure ()
    },
    { name := "unit/opcode/assemble-reject-high" -- [B7]
      run := do
        match assembleCp0 [Instr.dictGetNear 16] with
        | .ok _ =>
            throw (IO.userError "assemble accepted args4=16, expected rangeChk")
        | .error _ =>
            pure ()
    },
    { name := "unit/direct/hit-paths" -- [B4]
      run := do
        expectOkStack "direct/hit-8-0" (runDirect (mkStack 0 dict8A 8))
          #[.slice valueA, intV 0, intV (-1)]
        expectOkStack "direct/hit-8-6" (runDirect (mkStack 6 dict8A 8))
          #[.slice valueC, intV 128, intV (-1)]
        expectOkStack "direct/hit-8-128" (runDirect (mkStack 128 dict8A 8))
          #[.slice valueC, intV 128, intV (-1)]
        expectOkStack "direct/hit-8-255" (runDirect (mkStack 255 dict8A 8))
          #[.slice valueD, intV 255, intV (-1)]
        expectOkStack "direct/hit-0" (runDirect (mkStack 0 dict0 0))
          #[.slice valueC, intV 0, intV (-1)]
        expectOkStack "direct/hit-256-max" (runDirect (mkStack maxInt257 dict256 256))
          #[.slice valueB, intV maxInt257, intV (-1)]
    },
    { name := "unit/direct/miss/nearest-path" -- [B4][B7]
      run := do
        expectOkStack "direct/miss-8-overflow" (runDirect (mkStack 300 dict8A 8)) #[intV 0]
        expectOkStack "direct/miss-8-empty" (runDirect (mkStack 5 dictNull 8)) #[intV 0]
        expectOkStack "direct/miss-8-1-0bits" (runDirect (mkStack 1 dict0 0)) #[intV 0]
        expectOkStack "direct/miss-256-overflow" (runDirect (mkStack (maxInt257 + 1) dict256 256)) #[intV 0]
    },
    { name := "unit/direct/fallback-path" -- [B5]
      run := do
        expectOkStack "direct/fallback-neg-8" (runDirect (mkStack (-1) dict8A 8))
          #[.slice valueD, intV 255, intV (-1)]
        expectOkStack "direct/fallback-neg-256" (runDirect (mkStack (-7) dict256 256))
          #[.slice valueB, intV maxInt257, intV (-1)]
        expectOkStack "direct/fallback-neg-empty-8" (runDirect (mkStack (-1) dictNull 8)) #[intV 0]
    },
    { name := "unit/direct/validation-errors" -- [B2][B3][B6]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect (#[intV 7])) .stkUnd
        expectErr "underflow-two" (runDirect (mkStack 7 dict8A 8 |>.take 2)) .stkUnd
        expectErr "n-type" (runDirect (#[intV 7, dict8A, .cell Cell.empty])) .typeChk
        expectErr "n-negative" (runDirect (mkStack 7 dict8A (-1))) .rangeChk
        expectErr "n-too-large" (runDirect (mkStack 7 dict8A 257)) .rangeChk
        expectErr "dict-type" (runDirect (mkStack 7 (.tuple #[]) 8)) .typeChk
        expectErr "key-type" (runDirect (#[.tuple #[], dict8A, intV 8])) .typeChk
        expectErr "key-nan" (runDirect (#[.int .nan, dict8A, intV 8])) .typeChk
    },
    { name := "unit/direct/malformed-dictionary" -- [B6]
      run := do
        expectErr "malformed-nearest" (runDirect (mkStack 7 (.cell malformedDict) 8)) .dictErr
        expectErr "malformed-minmax" (runDirect (mkStack (-1) (.cell malformedDict) 8)) .dictErr
    },
    { name := "unit/decode/neighbors-and-tail" -- [B7]
      run := do
        let s0 : Slice :=
          Slice.ofCell <| Cell.mkOrdinary (rawF47B.bits ++ rawF47C.bits ++ rawF47D.bits ++ rawF47E.bits ++ rawF47F.bits) #[]
        let s1 ← expectDecodeStep "decode/f47b" s0 (.dictGetNear 11) 16
        let s2 ← expectDecodeStep "decode/f47c" s1 (.dictGetNear 12) 16
        let s3 ← expectDecodeStep "decode/f47d" s2 (.dictGetNear 13) 16
        let s4 ← expectDecodeStep "decode/f47e" s3 (.dictGetNear 14) 16
        let s5 ← expectDecodeStep "decode/f47f" s4 (.dictGetNear 15) 16
        if s5.bitsRemaining + s5.refsRemaining != 0 then
          throw (IO.userError "decode chain did not consume full stream")
        match decodeCp0WithBits (Slice.ofCell rawF47Trunc8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated prefix")
    }
  ]
  oracle := #[
    mkCase "ok/hit/8/0" (mkStack 0 dict8A 8), -- [B4]
    mkCase "ok/hit/8/5" (mkStack 5 dict8A 8), -- [B4]
    mkCase "ok/hit/8/6" (mkStack 6 dict8A 8), -- [B4]
    mkCase "ok/hit/8/129" (mkStack 129 dict8A 8), -- [B4]
    mkCase "ok/hit/8/255" (mkStack 255 dict8A 8), -- [B4]
    mkCase "ok/hit/0/0" (mkStack 0 dict0 0), -- [B4]
    mkCase "ok/hit/256/0" (mkStack 0 dict256 256), -- [B4]
    mkCase "ok/hit/256/max" (mkStack maxInt257 dict256 256), -- [B4]
    mkCase "ok/miss/8/256" (mkStack 256 dict8A 8), -- [B4]
    mkCase "ok/miss/8/300" (mkStack 300 dict8A 8), -- [B3][B4]
    mkCase "ok/miss/256/overflow" (mkStack (maxInt257 + 1) dict256 256), -- [B3][B4]
    mkCase "ok/miss/8/empty" (mkStack 12 dictNull 8), -- [B4]
    mkCase "ok/miss/0/one" (mkStack 1 dict0 0), -- [B4]
    mkCase "ok/fallback/neg/8" (mkStack (-1) dict8A 8), -- [B5]
    mkCase "ok/fallback/neg/8-hi" (mkStack (-129) dict8B 8), -- [B5]
    mkCase "ok/fallback/neg/8-empty" (mkStack (-1) dictNull 8), -- [B5]
    mkCase "ok/fallback/neg/256" (mkStack (-7) dict256 256), -- [B5]
    mkCase "ok/fallback/neg/256-empty" (mkStack (-7) dictNull 256), -- [B5]
    mkCaseCode "ok/code/raw-f47c" (mkStack 5 dict8A 8) rawF47C, -- [B7]
    mkCaseCode "ok/code/raw-f47d" (mkStack 6 dict8A 8) rawF47D, -- [B7]
    mkCaseCode "ok/code/raw-f47e" (mkStack 7 dict8B 8) rawF47E, -- [B7]
    mkCaseCode "ok/code/raw-f47f" (mkStack 8 dict8A 8) rawF47F, -- [B7]
    mkCaseCode "err/code/raw/trunc8" #[] rawF47Trunc8, -- [B7]
    mkCase "err/underflow/empty" #[], -- [B2]
    mkCase "err/underflow/one" (#[intV 5]), -- [B2]
    mkCase "err/underflow/two" (mkStack 5 dict8A 8 |>.take 2), -- [B2]
    mkCase "err/n/type" (#[intV 5, dict8A, .tuple #[]]), -- [B3]
    mkCase "err/n/nan" (#[intV 5, dict8A, .int .nan]), -- [B3]
    mkCase "err/n/negative" (mkStack 5 dict8A (-1)), -- [B2]
    mkCase "err/n/too-large" (mkStack 5 dict8A 257), -- [B2]
    mkCase "err/dict/type" (mkStack 5 (.tuple #[]) 8), -- [B2]
    mkCase "err/key/type" (mkStack 5 dict8A 8 |>.set! 0 (.slice valueA)), -- [B3]
    mkCase "err/key/nan" (mkStack 5 dict8A 8 |>.set! 0 (.int .nan)), -- [B3]
    mkCase "err/dict-malformed-nearest" (mkStack 0 (.cell malformedDict) 8), -- [B6]
    mkCase "err/dict-malformed-minmax" (mkStack (-1) (.cell malformedDict) 8), -- [B6]
    mkCase "gas/exact" (mkStack 5 dict8A 8)
      #[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExact exactGas), -- [B8]
    mkCase "gas/exact-minus-one" (mkStack 5 dict8A 8)
      #[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr]
      (oracleGasLimitsExactMinusOne exactGasMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictUGetNextEqFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETNEXTEQ
