import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTIMAXREF

/-!
INSTRUCTION: DICTIMAXREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path:
   `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`; unrelated instructions must flow to `next`.

2. [B2] Runtime preamble / underflow checks:
   `checkUnderflow 2` requires dictionary and width.
   `popNatUpTo 257` validates width for the signed int-key path (`maxN=257`).

3. [B3] Missing/miss path:
   Empty or non-matching dictionary returns `0` and no key/value.

4. [B4] Hit path:
   Valid hit with byRef mode (`args5=13`, odd) pushes:
   value as `.cell`, signed key as `Int`, then success flag `-1`.

5. [B5] Dictionary shape errors on value lookup:
   For byRef mode, found value must have `bits=0` and `refs=1`.
   Any other shape yields `.dictErr`.

6. [B6] Runtime width/type range behavior:
   `n = -1`, `NaN`, `>257` produce `.rangeChk`.
   Non-cell dictionary roots produce `.typeChk`.
   Root type mismatches and malformed roots produce errors from dictionary helpers.

7. [B7] Assembler encoding constraints:
   `.dictGetMinMax 13` is valid and encodes to `0xF48D`.
   Unsupported args (e.g. `9`) are `.invOpcode`.
   `args5 > 31` is `.rangeChk`.

8. [B8] Decoder behavior:
   Family range `0xF48A..0xF48F` decodes to `.dictGetMinMax` with args `10..15`.
   `0xF48B` and `0xF48E` are neighbors of this variant, and `0xF489` / truncated bytes are invalid.

9. [B9] Gas accounting:
   This is base-cost-only for this opcode variant (`DICTI{MAX,MIN}REF`, remove flag unset).
   Exact exact-gas must succeed.
   Exact-1 must fail for out-of-gas.

TOTAL BRANCHES: 9

Each oracle test below is tagged with one or more [Bn] IDs.
-/

private def dictIMaxRefId : InstrId :=
  { name := "DICTIMAXREF" }

private def dictIMaxRefInstr : Instr :=
  .dictGetMinMax 13

private def dictIMaxRefExactGas : Int :=
  computeExactGasBudget dictIMaxRefInstr

private def dictIMaxRefExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictIMaxRefInstr

private def dictIMaxRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictIMaxRefExactGas

private def dictIMaxRefGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictIMaxRefExactGasMinusOne

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def dispatchSentinel : Int :=
  12_013

private def mkDictRefRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid key={k}, n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected no-root after insert"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary input"

private def mkDictSliceRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid key={k}, n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected no-root after insert"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary input"

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def dictNull : Value := .null

private def dictSingleRef0 : Cell :=
  mkDictRefRoot! "dictSingleRef0" 0 #[(0, valueA)]

private def dictSingleRef8 : Cell :=
  mkDictRefRoot! "dictSingleRef8" 8 #[(5, valueA)]

private def dictSingleNeg8 : Cell :=
  mkDictRefRoot! "dictSingleNeg8" 8 #[( -1, valueC)]

private def dictTwoRef8 : Cell :=
  mkDictRefRoot! "dictTwoRef8" 8 #[(5, valueA), (-1, valueB)]

private def dictThreeRef8 : Cell :=
  mkDictRefRoot! "dictThreeRef8" 8 #[(5, valueA), (9, valueB), (-12, valueC)]

private def dictSingleRef257 : Cell :=
  mkDictRefRoot! "dictSingleRef257" 257 #[(0, valueA)]

private def dictTwoRef257 : Cell :=
  mkDictRefRoot! "dictTwoRef257" 257 #[(minInt257, valueA), (maxInt257, valueB)]

private def dictSliceSingle8 : Cell :=
  mkDictSliceRoot! "dictSliceSingle8" 8 #[(7, Slice.ofCell (Cell.mkOrdinary (natToBits 0xF0 8) #[]))]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b1 1) #[]

private def rawOpcodeF489 : Cell := raw16 0xF489
private def rawOpcodeF48A : Cell := raw16 0xF48A
private def rawOpcodeF48B : Cell := raw16 0xF48B
private def rawOpcodeF48C : Cell := raw16 0xF48C
private def rawOpcodeF48D : Cell := raw16 0xF48D
private def rawOpcodeF48E : Cell := raw16 0xF48E
private def rawOpcodeF48F : Cell := raw16 0xF48F
private def rawOpcodeF490 : Cell := raw16 0xF490
private def rawOpcodeF4 : Cell := raw8 0xF4

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictIMaxRefInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIMaxRefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIMaxRefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIMaxRefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV dispatchSentinel)) stack

private def runDictIMaxRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictIMaxRefInstr stack

private def expectDecodeOk
    (label : String)
    (cell : Cell)
    (expected : Instr)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected exact decode, got {rest.bitsRemaining} bits/{rest.refsRemaining} refs")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {instr}/{bits}")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def genDictIMaxRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/257" #[dictNull, intV 257], rng1)
    else if shape = 3 then
      (mkCase "fuzz/hit/single/ref8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/two/ref8" #[.cell dictTwoRef8, intV 8], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/three/ref8" #[.cell dictThreeRef8, intV 8], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/single/ref257" #[.cell dictSingleRef257, intV 257], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/two/ref257" #[.cell dictTwoRef257, intV 257], rng1)
    else if shape = 8 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 9 then
      (mkCase "fuzz/underflow/one" #[intV 8], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/root-tuple" #[.tuple #[], intV 8], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/root-cont" #[.cont (.quit 0), intV 8], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/n-negative" #[.cell dictSingleRef8, intV (-1)], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/n-too-large" #[.cell dictSingleRef8, intV 258], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/n-nan"
        #[.cell dictSingleRef8]
        #[.pushInt .nan, dictIMaxRefInstr], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/byref-shape" #[.cell dictSliceSingle8, intV 8], rng1)
    else if shape = 17 then
      (mkCase "fuzz/gas/exact" #[dictNull, intV 8]
        (#[.pushInt (.num dictIMaxRefExactGas), .tonEnvOp .setGasLimit, dictIMaxRefInstr])
        dictIMaxRefGasExact, rng1)
    else if shape = 18 then
      (mkCase "fuzz/gas/exact-minus-one" #[dictNull, intV 8]
        (#[.pushInt (.num dictIMaxRefExactGasMinusOne), .tonEnvOp .setGasLimit, dictIMaxRefInstr])
        dictIMaxRefGasExactMinusOne, rng1)
    else
      (mkRawCase "fuzz/raw/f48d" #[.cell dictSingleRef8, intV 8] rawOpcodeF48D, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr dictIMaxRefId

def suite : InstrSuite where
  id := dictIMaxRefId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "fallback"
          (runDictIMaxRefDispatchFallback #[.cell dictSingleRef8, intV 8])
          #[.cell dictSingleRef8, intV 8, intV dispatchSentinel] },
    { name := "unit/miss/null/0" -- [B2][B3]
      run := do
        expectOkStack "miss-null/0" (runDictIMaxRefDirect #[dictNull, intV 0]) #[intV 0] },
    { name := "unit/miss/null/8" -- [B2][B3]
      run := do
        expectOkStack "miss-null/8" (runDictIMaxRefDirect #[dictNull, intV 8]) #[intV 0] },
    { name := "unit/miss/null/257" -- [B2][B3]
      run := do
        expectOkStack "miss-null/257" (runDictIMaxRefDirect #[dictNull, intV 257]) #[intV 0] },
    { name := "unit/hit/single-ref8" -- [B4]
      run := do
        expectOkStack "hit-single-ref8"
          (runDictIMaxRefDirect #[.cell dictSingleRef8, intV 8])
          #[.cell valueA, intV 5, intV (-1)] },
    { name := "unit/hit/single-neg-ref8" -- [B4][B6]
      run := do
        expectOkStack "hit-single-neg-ref8"
          (runDictIMaxRefDirect #[.cell dictSingleNeg8, intV 8])
          #[.cell valueC, intV (-1), intV (-1)] },
    { name := "unit/hit/two-ref8" -- [B4]
      run := do
        expectOkStack "hit-two-ref8"
          (runDictIMaxRefDirect #[.cell dictTwoRef8, intV 8])
          #[.cell valueA, intV 5, intV (-1)] },
    { name := "unit/hit/three-ref8" -- [B4]
      run := do
        expectOkStack "hit-three-ref8"
          (runDictIMaxRefDirect #[.cell dictThreeRef8, intV 8])
          #[.cell valueB, intV 9, intV (-1)] },
    { name := "unit/hit/single-ref257" -- [B4][B6]
      run := do
        expectOkStack "hit-single-ref257"
          (runDictIMaxRefDirect #[.cell dictSingleRef257, intV 257])
          #[.cell valueA, intV 0, intV (-1)] },
    { name := "unit/hit/two-ref257" -- [B4][B6]
      run := do
        expectOkStack "hit-two-ref257"
          (runDictIMaxRefDirect #[.cell dictTwoRef257, intV 257])
          #[.cell valueB, intV maxInt257, intV (-1)] },
    { name := "unit/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictIMaxRefDirect #[]) .stkUnd },
    { name := "unit/underflow-one" -- [B2]
      run := do
        expectErr "underflow-one" (runDictIMaxRefDirect #[intV 8]) .stkUnd },
    { name := "unit/err/n-nan" -- [B6]
      run := do
        expectErr "n-nan" (runDictIMaxRefDirect #[dictNull, .int .nan]) .rangeChk },
    { name := "unit/err/n-negative" -- [B6]
      run := do
        expectErr "n-negative" (runDictIMaxRefDirect #[dictNull, intV (-1)]) .rangeChk },
    { name := "unit/err/n-too-large" -- [B6]
      run := do
        expectErr "n-too-large" (runDictIMaxRefDirect #[dictNull, intV 9999]) .rangeChk },
    { name := "unit/err/root-type-tuple" -- [B6]
      run := do
        expectErr "root-type" (runDictIMaxRefDirect #[.tuple #[], intV 8]) .typeChk },
    { name := "unit/err/root-type-cont" -- [B6]
      run := do
        expectErr "root-type" (runDictIMaxRefDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/err/byref-shape" -- [B5]
      run := do
        expectErr "byref-shape" (runDictIMaxRefDirect #[.cell dictSliceSingle8, intV 8]) .dictErr },
    { name := "unit/asm/encode-valid" -- [B7]
      run := do
        match assembleCp0 [dictIMaxRefInstr] with
        | .ok c =>
            if c.bits = natToBits 0xF48D 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF48D, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"expected assemble success, got {e}") },
    { name := "unit/asm/reject-gap" -- [B7]
      run := expectAssembleErr "asm-reject-gap" (.dictGetMinMax 9) .invOpcode },
    { name := "unit/asm/reject-range" -- [B7]
      run := expectAssembleErr "asm-reject-range" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/decode/chain" -- [B8]
      run := do
        expectDecodeOk "decode-f48c" rawOpcodeF48C (.dictGetMinMax 12)
        expectDecodeOk "decode-f48d" rawOpcodeF48D (.dictGetMinMax 13)
        expectDecodeOk "decode-f48e" rawOpcodeF48E (.dictGetMinMax 14)
        expectDecodeOk "decode-f48f" rawOpcodeF48F (.dictGetMinMax 15)
        expectDecodeOk "decode-f48a" rawOpcodeF48A (.dictGetMinMax 10)
        expectDecodeOk "decode-f48b" rawOpcodeF48B (.dictGetMinMax 11) },
    { name := "unit/decode/errors" -- [B8]
      run := do
        expectDecodeErr "decode-invalid" rawOpcodeF489 .invOpcode
        expectDecodeErr "decode-invalid2" rawOpcodeF490 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode },
  ]
  oracle := #[
    -- [B3][B6]
    mkCase "oracle/miss/null/0" #[dictNull, intV 0],
    mkCase "oracle/miss/null/8" #[dictNull, intV 8],
    mkCase "oracle/miss/null/16" #[dictNull, intV 16],
    mkCase "oracle/miss/null/257" #[dictNull, intV 257],
    -- [B4][B6]
    mkCase "oracle/hit/single/ref8" #[.cell dictSingleRef8, intV 8],
    mkCase "oracle/hit/single/neg/ref8" #[.cell dictSingleNeg8, intV 8],
    mkCase "oracle/hit/two/ref8" #[.cell dictTwoRef8, intV 8],
    mkCase "oracle/hit/three/ref8" #[.cell dictThreeRef8, intV 8],
    mkCase "oracle/hit/single/ref0" #[.cell dictSingleRef0, intV 0],
    mkCase "oracle/hit/single/ref257" #[.cell dictSingleRef257, intV 257],
    mkCase "oracle/hit/two/ref257" #[.cell dictTwoRef257, intV 257],
    -- [B2]
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one" #[intV 8],
    -- [B6]
    mkCase "oracle/err/root-type-tuple" #[.tuple #[], intV 8],
    mkCase "oracle/err/root-type-cont" #[.cont (.quit 0), intV 8],
    mkCase "oracle/err/n-nan"
      #[.cell dictSingleRef8]
      #[.pushInt .nan, dictIMaxRefInstr],
    mkCase "oracle/err/n-negative" #[.cell dictSingleRef8, intV (-1)],
    mkCase "oracle/err/n-too-large" #[.cell dictSingleRef8, intV 9999],
    mkCase "oracle/err/n-too-large-edge" #[.cell dictSingleRef8, intV 258],
    mkCase "oracle/err/malformed-root" #[.cell malformedDict, intV 8],
    mkCase "oracle/err/byref-shape" #[.cell dictSliceSingle8, intV 8],
    -- [B7]
    mkCase "oracle/asm-encode-13" #[dictNull, intV 8] #[dictIMaxRefInstr],
    -- [B8]
    mkRawCase "oracle/raw/f48a" #[.cell dictSingleRef8, intV 8] rawOpcodeF48A,
    mkRawCase "oracle/raw/f48b" #[.cell dictSingleRef8, intV 8] rawOpcodeF48B,
    mkRawCase "oracle/raw/f48c" #[.cell dictSingleRef8, intV 8] rawOpcodeF48C,
    mkRawCase "oracle/raw/f48d" #[.cell dictSingleRef8, intV 8] rawOpcodeF48D,
    mkRawCase "oracle/raw/f48e" #[.cell dictSingleRef8, intV 8] rawOpcodeF48E,
    mkRawCase "oracle/raw/f48f" #[.cell dictSingleRef8, intV 8] rawOpcodeF48F,
    mkRawCase "oracle/raw/f489" #[] rawOpcodeF489,
    mkRawCase "oracle/raw/f4" #[] rawOpcodeF4,
    -- [B9]
    mkCase "oracle/gas/exact-null" #[dictNull, intV 8]
      (#[.pushInt (.num dictIMaxRefExactGas), .tonEnvOp .setGasLimit, dictIMaxRefInstr])
      dictIMaxRefGasExact,
    mkCase "oracle/gas/exact-minus-one-null" #[dictNull, intV 8]
      (#[.pushInt (.num dictIMaxRefExactGasMinusOne), .tonEnvOp .setGasLimit, dictIMaxRefInstr])
      dictIMaxRefGasExactMinusOne,
    mkRawCase "oracle/raw/f490" #[] rawOpcodeF490
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictIMaxRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIMAXREF
