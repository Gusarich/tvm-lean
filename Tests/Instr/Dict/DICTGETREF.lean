import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTGETREF

/-!
INSTRUCTION: DICTGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `.dictGet` instructions are handled by `execInstrDictDictGet`; non-matching instructions
     pass through via `next`.

2. [B2] Stack arity check.
   - `checkUnderflow 3` must run before any typed/numeric validation.

3. [B3] `n` parsing and width validation.
   - `popNatUpTo 1023` accepts only integer values in `[0, 1023]`.
   - `NaN`, negative, and >1023 reject with range-type errors via `popNatUpTo`.

4. [B4] Dictionary argument parsing.
   - `popMaybeCell` accepts `.null` or `.cell`.
   - Other types produce `.typeChk`.

5. [B5] Slice-key validation (`intKey = false`).
   - Key must be a slice.
   - If fewer than `n` bits available, `.cellUnd`.
   - `n = 0` reads an empty key and can match an empty-key entry.

6. [B6] Lookup outcome.
   - Missing root or lookup miss pushes `0`.
   - Hit pushes found value reference and `-1`, preserving prefix stack values.

7. [B7] By-ref return validation.
   - By-ref hit is valid only when value slice has `bitsRemaining = 0`, `refsRemaining = 1`.
   - Any other layout throws `.dictErr`.

8. [B8] Dictionary structure errors.
   - Malformed dictionary structures throw `.dictErr`.

9. [B9] Assembler behavior.
   - `.dictGet false false true` assembles to `0xF40B`.
   - `.dictGet false true true` is rejected as `.invOpcode`.

10. [B10] Decoder behavior.
   - `0xF40A..0xF40F` decode as `.dictGet` family.
   - `0xF409`, `0xF410`, and truncated `0xF4` are `.invOpcode`.

11. [B11] Gas accounting.
   - Fixed-cost branches only; exact and exact-minus-one checks cover success/failure boundary.

TOTAL BRANCHES: 11
-/

private def suiteId : InstrId :=
  { name := "DICTGETREF" }

private def instr : Instr :=
  .dictGet false false true

private def instrInvalid : Instr :=
  .dictGet false true true

private def rawF40A : Cell := Cell.mkOrdinary (natToBits 0xF40A 16) #[]
private def rawF40B : Cell := Cell.mkOrdinary (natToBits 0xF40B 16) #[]
private def rawGapLow : Cell := Cell.mkOrdinary (natToBits 0xF409 16) #[]
private def rawGapHigh : Cell := Cell.mkOrdinary (natToBits 0xF410 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def markerA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def markerB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def markerC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def markerD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def byRefValueA : Cell := Cell.mkOrdinary #[] #[markerA]
private def byRefValueB : Cell := Cell.mkOrdinary #[] #[markerB]
private def byRefValueC : Cell := Cell.mkOrdinary #[] #[markerC]
private def byRefValueD : Cell := Cell.mkOrdinary #[] #[markerD]

private def badValueBits : Cell :=
  Cell.mkOrdinary (natToBits 0xF0 8) #[]

private def badValueRefs : Cell :=
  Cell.mkOrdinary #[] #[markerA, markerB]

private def signedKeyBits (label : String) (k : Int) (n : Nat) : BitString :=
  match dictKeyBits? k n false with
  | some bits => bits
  | none => panic! s!"{label}: invalid signed key ({k}) for n={n}"

private def mkDictSetRefRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits := signedKeyBits label k n
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k}, n={n})"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed ({k}, n={n}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def mkDictSetSliceRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits := signedKeyBits label k n
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k}, n={n})"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed ({k}, n={n}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def dictTypeValue : Value :=
  .tuple #[]

private def dictSigned8 : Cell :=
  mkDictSetRefRoot! "DICTGETREF::dictSigned8" 8 #[(5, byRefValueA), (-1, byRefValueB), (127, byRefValueC)]

private def dictSigned1 : Cell :=
  mkDictSetRefRoot! "DICTGETREF::dictSigned1" 1 #[(0, byRefValueD)]

private def dictSigned0 : Cell :=
  mkDictSetRefRoot! "DICTGETREF::dictSigned0" 0 #[(0, byRefValueD)]

private def dictBadValueBits : Cell :=
  mkDictSetSliceRoot! "DICTGETREF::dictBadValueBits" 8 #[
    (6, Slice.ofCell badValueBits)
  ]

private def dictBadValueRefs : Cell :=
  mkDictSetSliceRoot! "DICTGETREF::dictBadValueRefs" 8 #[
    (7, Slice.ofCell badValueRefs)
  ]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b10 2) #[]

private def exactGas : Int :=
  computeExactGasBudget instr

private def exactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

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

private def mkCodeCase
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def stackSliceKey (keyBits : BitString) (dictValue : Value) (n : Int) : Array Value :=
  #[.slice (mkSliceFromBits keyBits), dictValue, intV n]

private def runDispatchFallback : Array Value → Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGet instr (VM.push (intV 909))

private def runDirect : Array Value → Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGet instr

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (decoded, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {decoded}")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def genDICTGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase (s!"fuzz/miss/null/{tag}") (stackSliceKey (signedKeyBits "fuzz/miss/null" 5 8) .null 8), rng2)
    else if shape = 1 then
      (mkCase (s!"fuzz/miss/null-n0/{tag}") (stackSliceKey (signedKeyBits "fuzz/miss/null-n0" 0 0) .null 0), rng2)
    else if shape = 2 then
      (mkCase (s!"fuzz/miss/wide-null/{tag}") (stackSliceKey (signedKeyBits "fuzz/miss/wide-null" 1 1) .null 257), rng2)
    else if shape = 3 then
      (mkCase (s!"fuzz/miss/narrow/{tag}") (stackSliceKey (signedKeyBits "fuzz/miss/narrow" 0 1) (.cell dictSigned1) 1), rng2)
    else if shape = 4 then
      (mkCase (s!"fuzz/miss/not-found/{tag}") (stackSliceKey (signedKeyBits "fuzz/miss/not-found" 11 8) (.cell dictSigned8) 8), rng2)
    else if shape = 5 then
      (mkCase (s!"fuzz/hit/5/{tag}") (stackSliceKey (signedKeyBits "fuzz/hit/5" 5 8) (.cell dictSigned8) 8), rng2)
    else if shape = 6 then
      (mkCase (s!"fuzz/hit/-1/{tag}") (stackSliceKey (signedKeyBits "fuzz/hit/-1" (-1) 8) (.cell dictSigned8) 8), rng2)
    else if shape = 7 then
      (mkCase (s!"fuzz/hit/127/{tag}") (stackSliceKey (signedKeyBits "fuzz/hit/127" 127 8) (.cell dictSigned8) 8), rng2)
    else if shape = 8 then
      (mkCase (s!"fuzz/hit/n0/{tag}") (stackSliceKey #[] (.cell dictSigned0) 0), rng2)
    else if shape = 9 then
      (mkCase (s!"fuzz/hit/n1/{tag}") (stackSliceKey #[] (.cell dictSigned1) 1), rng2)
    else if shape = 10 then
      (mkCase (s!"fuzz/hit/prefix/{tag}") (#[intV 909, .slice (mkSliceFromBits (signedKeyBits "fuzz/hit/prefix" 5 8)), .cell dictSigned8, intV 8]), rng2)
    else if shape = 11 then
      (mkCase (s!"fuzz/err/key-null/{tag}") (#[.null, .cell dictSigned8, intV 8]), rng2)
    else if shape = 12 then
      (mkCase (s!"fuzz/err/key-cell/{tag}") (#[.cell Cell.empty, .cell dictSigned8, intV 8]), rng2)
    else if shape = 13 then
      (mkCase (s!"fuzz/err/key-int/{tag}") (#[.int (.num 11), .cell dictSigned8, intV 8]), rng2)
    else if shape = 14 then
      (mkCase (s!"fuzz/err/key-builder/{tag}") (#[.builder Builder.empty, .cell dictSigned8, intV 8]), rng2)
    else if shape = 15 then
      (mkCase (s!"fuzz/err/dict-type/{tag}") (#[.slice (mkSliceFromBits (signedKeyBits "fuzz/err/dict-type" 5 8)), dictTypeValue, intV 8], rng2)
    else if shape = 16 then
      (mkCase (s!"fuzz/err/n-null/{tag}") (#[.slice (mkSliceFromBits (signedKeyBits "fuzz/err/n-null" 5 8)), .cell dictSigned8, .null], rng2)
    else if shape = 17 then
      (mkCase (s!"fuzz/err/n-builder/{tag}") (#[.slice (mkSliceFromBits (signedKeyBits "fuzz/err/n-builder" 5 8)), .cell dictSigned8, .builder Builder.empty], rng2)
    else if shape = 18 then
      (mkCase (s!"fuzz/err/n-nan/{tag}") (#[.slice (mkSliceFromBits (signedKeyBits "fuzz/err/n-nan" 5 8)), .cell dictSigned8, .int .nan], rng2)
    else if shape = 19 then
      (mkCase (s!"fuzz/err/n-negative/{tag}") (#[.slice (mkSliceFromBits (signedKeyBits "fuzz/err/n-negative" 5 8)), .cell dictSigned8, intV (-1)], rng2)
    else if shape = 20 then
      (mkCase (s!"fuzz/err/n-too-large/{tag}") (#[.slice (mkSliceFromBits (signedKeyBits "fuzz/err/n-too-large" 5 8)), .cell dictSigned8, intV 1024], rng2)
    else if shape = 21 then
      (mkCase (s!"fuzz/err/key-too-short/{tag}") (#[.slice (mkSliceFromBits (natToBits 5 4)), .cell dictSigned8, intV 8]), rng2)
    else if shape = 22 then
      (mkCase (s!"fuzz/err/bad-value-bits/{tag}") (stackSliceKey (signedKeyBits "fuzz/err/bad-value-bits" 6 8) (.cell dictBadValueBits) 8), rng2)
    else if shape = 23 then
      (mkCase (s!"fuzz/err/bad-value-refs/{tag}") (stackSliceKey (signedKeyBits "fuzz/err/bad-value-refs" 7 8) (.cell dictBadValueRefs) 8), rng2)
    else if shape = 24 then
      (mkCase (s!"fuzz/err/malformed-dict/{tag}") (stackSliceKey (signedKeyBits "fuzz/err/malformed-dict" 5 8) (.cell malformedDict) 8), rng2)
    else if shape = 25 then
      (mkCase (s!"fuzz/underflow/empty/{tag}") #[], rng2)
    else if shape = 26 then
      (mkCase (s!"fuzz/underflow/one/{tag}") #[.cell dictSigned8], rng2)
    else if shape = 27 then
      (mkCase (s!"fuzz/underflow/two/{tag}") (#[.slice (mkSliceFromBits (natToBits 5 8)), .cell dictSigned8]), rng2)
    else if shape = 28 then
      (mkCase (s!"fuzz/gas/exact/{tag}")
        (stackSliceKey (signedKeyBits "fuzz/gas/exact" 5 8) (.cell dictSigned8) 8)
        (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact exactGas), rng2)
    else
      (mkCase (s!"fuzz/gas/exact-minus-one/{tag}")
        (stackSliceKey (signedKeyBits "fuzz/gas/exact-minus-one" 5 8) (.cell dictSigned8) 8)
        (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne exactGasMinusOne), rng2)
  ({ case0 with name := case0.name }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st : Except Excno (Array Value) := runDispatchFallback #[]
        expectOkStack "dispatch/fallback" st (#[intV 909]) },
    { name := "unit/decode/valid-f40a" -- [B10]
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xF40A 16)
        let _ ← expectDecodeStep "decode/f40a" s (.dictGet false false false) 16
        pure () },
    { name := "unit/decode/valid-f40b" -- [B10]
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xF40B 16)
        let _ ← expectDecodeStep "decode/f40b" s instr 16
        pure () },
    { name := "unit/decode/invalid-boundaries" -- [B10]
      run := do
        expectDecodeInvOpcode "decode/f409" 0xF409
        expectDecodeInvOpcode "decode/f410" 0xF410
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated expected failure") },
    { name := "unit/asm/encode" -- [B9]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF40B 16 then
              pure ()
            else
              throw (IO.userError s!"expected bits 0xF40B, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"expected assembly success, got {e}") },
    { name := "unit/asm/encode/reject-invalid-flags" -- [B9]
      run := do
        match assembleCp0 [instrInvalid] with
        | .ok _ =>
            throw (IO.userError "expected invOpcode, got success")
        | .error e =>
            if e != .invOpcode then
              throw (IO.userError s!"expected invOpcode, got {e}")
            else
              pure () },
    { name := "unit/runtime/hit-miss" -- [B6][B7]
      run := do
        expectOkStack "miss/null" (runDirect (stackSliceKey (signedKeyBits "unit/miss/null" 5 8) .null 8))
          (#[intV 0])
        expectOkStack "hit/key-5" (runDirect (stackSliceKey (signedKeyBits "unit/hit/key-5" 5 8) (.cell dictSigned8) 8))
          (#[.cell byRefValueA, intV (-1)])
        expectOkStack "hit/key-neg1" (runDirect (stackSliceKey (signedKeyBits "unit/hit/key-neg1" (-1) 8) (.cell dictSigned8) 8))
          (#[.cell byRefValueB, intV (-1)])
        expectOkStack "hit/prefix-preserved"
          (runDirect (#[intV 777, .slice (mkSliceFromBits (signedKeyBits "unit/hit/prefix-preserved" 5 8)), .cell dictSigned8, intV 8]))
          (#[intV 777, .cell byRefValueA, intV (-1)]) },
    { name := "unit/runtime/errors" -- [B3][B4][B5][B7][B8]
      run := do
        expectErr "key-too-short" (runDirect (#[.slice (mkSliceFromBits (natToBits 5 4)), .cell dictSigned8, intV 8])) .cellUnd
        expectErr "bad-value-bits" (runDirect (stackSliceKey (signedKeyBits "unit/err/bad-value-bits" 6 8) (.cell dictBadValueBits) 8)) .dictErr
        expectErr "bad-value-refs" (runDirect (stackSliceKey (signedKeyBits "unit/err/bad-value-refs" 7 8) (.cell dictBadValueRefs) 8)) .dictErr
        expectErr "malformed-dict" (runDirect (stackSliceKey (signedKeyBits "unit/err/malformed-dict" 5 8) (.cell malformedDict) 8)) .dictErr
        expectErr "n-negative" (runDirect (#[.slice (mkSliceFromBits (signedKeyBits "unit/err/n-negative" 5 8)), .cell dictSigned8, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDirect (#[.slice (mkSliceFromBits (signedKeyBits "unit/err/n-too-large" 5 8)), .cell dictSigned8, intV 1024]) .rangeChk
        expectErr "n-nan" (runDirect (#[.slice (mkSliceFromBits (signedKeyBits "unit/err/n-nan" 5 8)), .cell dictSigned8, .int .nan]) .rangeChk
        expectErr "key-non-slice" (runDirect (stackSliceKey (signedKeyBits "unit/err/key-non-slice" 5 8) (.cell dictSigned8) 8)) .typeChk
        expectErr "dict-non-cell" (runDirect (#[.slice (mkSliceFromBits (signedKeyBits "unit/err/dict-non-cell" 5 8)), dictTypeValue, intV 8]) .typeChk
        expectErr "underflow-empty" (runDirect #[]) .stkUnd }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow-empty" #[],
    mkCase "oracle/underflow-one" #[.cell dictSigned8],
    mkCase "oracle/underflow-two" (#[.slice (mkSliceFromBits (signedKeyBits "oracle/underflow-two" 5 8)), .cell dictSigned8]),

    -- [B3]
    mkCase "oracle/err/n-null" (#[.slice (mkSliceFromBits (signedKeyBits "oracle/err/n-null" 5 8)), .cell dictSigned8, .null),
    mkCase "oracle/err/n-builder" (#[.slice (mkSliceFromBits (signedKeyBits "oracle/err/n-builder" 5 8)), .cell dictSigned8, .builder Builder.empty]),
    mkCase "oracle/err/n-nan" (#[.slice (mkSliceFromBits (signedKeyBits "oracle/err/n-nan" 5 8)), .cell dictSigned8, .int .nan]),
    mkCase "oracle/err/n-negative" (#[.slice (mkSliceFromBits (signedKeyBits "oracle/err/n-negative" 5 8)), .cell dictSigned8, intV (-1)]),
    mkCase "oracle/err/n-too-large" (#[.slice (mkSliceFromBits (signedKeyBits "oracle/err/n-too-large" 5 8)), .cell dictSigned8, intV 1024]),

    -- [B4][B5]
    mkCase "oracle/err/key-null" (#[.null, .cell dictSigned8, intV 8]),
    mkCase "oracle/err/key-cell" (#[.cell Cell.empty, .cell dictSigned8, intV 8]),
    mkCase "oracle/err/key-int" (#[.int (.num 11), .cell dictSigned8, intV 8]),
    mkCase "oracle/err/key-builder" (#[.builder Builder.empty, .cell dictSigned8, intV 8]),
    mkCase "oracle/err/dict-type" (#[.slice (mkSliceFromBits (signedKeyBits "oracle/err/dict-type" 5 8)), dictTypeValue, intV 8),
    mkCase "oracle/err/key-too-short" (#[.slice (mkSliceFromBits (natToBits 5 4)), .cell dictSigned8, intV 8]),

    -- [B6]
    mkCase "oracle/miss/null" (stackSliceKey (signedKeyBits "oracle/miss/null" 5 8) .null 8),
    mkCase "oracle/miss/wide-null" (stackSliceKey (signedKeyBits "oracle/miss/wide-null" 1 1) .null 257),
    mkCase "oracle/miss/key-not-found" (stackSliceKey (signedKeyBits "oracle/miss/not-found" 11 8) (.cell dictSigned8) 8),
    mkCase "oracle/miss/narrow-key-miss" (stackSliceKey (signedKeyBits "oracle/miss/narrow-key-miss" 0 1) (.cell dictSigned8) 1),
    mkCase "oracle/hit/5" (stackSliceKey (signedKeyBits "oracle/hit/5" 5 8) (.cell dictSigned8) 8),
    mkCase "oracle/hit/-1" (stackSliceKey (signedKeyBits "oracle/hit/-1" (-1) 8) (.cell dictSigned8) 8),
    mkCase "oracle/hit/127" (stackSliceKey (signedKeyBits "oracle/hit/127" 127 8) (.cell dictSigned8) 8),
    mkCase "oracle/hit/n0" (stackSliceKey #[] (.cell dictSigned0) 0),
    mkCase "oracle/hit/n1" (stackSliceKey #[] (.cell dictSigned1) 1),
    mkCase "oracle/hit/prefix-preserved" (#[intV 42, .slice (mkSliceFromBits (signedKeyBits "oracle/hit/prefix-preserved" 5 8)), .cell dictSigned8, intV 8]),

    -- [B7]
    mkCase "oracle/err/bad-value-bits" (stackSliceKey (signedKeyBits "oracle/err/bad-value-bits" 6 8) (.cell dictBadValueBits) 8),
    mkCase "oracle/err/bad-value-refs" (stackSliceKey (signedKeyBits "oracle/err/bad-value-refs" 7 8) (.cell dictBadValueRefs) 8),

    -- [B8]
    mkCase "oracle/err/malformed-dict" (stackSliceKey (signedKeyBits "oracle/err/malformed-dict" 5 8) (.cell malformedDict) 8),

    -- [B9][B10]
    mkCodeCase "oracle/code/f40a" #[] rawF40A,
    mkCodeCase "oracle/code/f40b" #[] rawF40B,
    mkCodeCase "oracle/code/f409-fail" #[] rawGapLow,
    mkCodeCase "oracle/code/f410-fail" #[] rawGapHigh,

    -- [B11]
    mkCase "oracle/gas/exact-hit"
      (stackSliceKey (signedKeyBits "oracle/gas/exact-hit" 5 8) (.cell dictSigned8) 8)
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact exactGas),
    mkCase "oracle/gas/exact-minus-one-miss"
      (stackSliceKey (signedKeyBits "oracle/gas/exact-minus-one-miss" 5 8) .null 8)
      (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne exactGasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTGETREF
