import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREMMAXREF

/-!
INSTRUCTION: DICTUREMMAXREF

BRANCH ANALYSIS (Lean + C++ reference):

1. [B1] Dispatch branch.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`;
     all other opcodes must route to `next`.

2. [B2] Runtime preamble.
   - `VM.checkUnderflow 2` must reject short stacks.
   - `n` is validated with `popNatUpTo 257`.

3. [B3] Dictionary-pop and lookup path.
   - `VM.popMaybeCell` accepts `null` (empty dict) and cell values.
   - Non-cell dictionarys raise `typeChk`.
   - Missing key case pushes dictionary root (or `null`) and `0`.

4. [B4] Hit/remove path.
   - For remove opcodes, `dictDeleteWithCells` runs and can rebuild a non-empty root.
   - Single-element dictionary removes to `null`.
   - Dict-rebuild operations can consume cell-create gas.

5. [B5] By-ref value shape.
   - `DICTUREMMAXREF` requires value representation `bits=0, refs=1`;
     otherwise `.dictErr`.

6. [B6] Unsigned key reconstruction.
   - `unsigned=true`, `intKey=true` uses natural decoding for keys.

7. [B7] Assembler behavior.
   - `.dictGetMinMax 31` assembles to `0xF49F`.
   - In-range gap/bad encoding combinations reject with `.invOpcode`/`.rangeChk`.

8. [B8] Decoder behavior.
   - `0xF49F` decodes to `.dictGetMinMax 31`.
   - Neighbor opcodes decode to neighboring args.
   - Truncated/invalid encodings fail.

9. [B9] Gas accounting.
   - Base gas + remove-branch rebuild penalty `created * cellCreateGasPrice` are enforced.
   - Exact-minus-one gas failure is observed.

TOTAL BRANCHES: 9

Each oracle case below is tagged [Bn] to branch IDs.
-/

private def suiteId : InstrId :=
  { name := "DICTUREMMAXREF" }

private def instr : Instr :=
  .dictGetMinMax 31

private def maxKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n true false with
  | .ok (some (_, keyBits), _) => some keyBits
  | _ => none

private def dictDeleteCreated (root : Cell) (n : Nat) : Nat :=
  match maxKeyBits root n with
  | some keyBits =>
      match dictDeleteWithCells (some root) keyBits with
      | .ok (_, _, created, _) => created
      | .error _ => 0
  | none => 0

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def payloadA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def payloadB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def payloadC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def valueA : Cell := Cell.mkOrdinary #[] #[payloadA]
private def valueB : Cell := Cell.mkOrdinary #[] #[payloadB]
private def valueC : Cell := Cell.mkOrdinary #[] #[payloadC]
private def badValueSlice : Slice := mkSliceFromBits (natToBits 0xF0 8)

private def dictNull : Value := .null
private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]
private def dictSingleRef8Alt : Cell :=
  mkDictSetRefRoot! "dictSingleRef8Alt" 8 #[(13, valueB)]
private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[(13, valueB), (5, valueA)]
private def dictTwoRef8AfterMax : Cell :=
  mkDictSetRefRoot! "dictTwoRef8AfterMax" 8 #[(5, valueA)]
private def dictThreeRef8 : Cell :=
  mkDictSetRefRoot! "dictThreeRef8" 8 #[(0, valueA), (5, valueB), (200, valueC)]
private def dictSingleRef257 : Cell :=
  mkDictSetRefRoot! "dictSingleRef257" 257 #[(0, valueA)]
private def dictSingleRef257Min : Cell :=
  mkDictSetRefRoot! "dictSingleRef257Min" 257 #[(1, valueA)]
private def dictSingleRef257Max : Cell :=
  mkDictSetRefRoot! "dictSingleRef257Max" 257 #[(2, valueB)]
private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(7, badValueSlice)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def twoRef8Created : Nat := dictDeleteCreated dictTwoRef8 8
private def twoRef8Penalty : Int := Int.ofNat twoRef8Created * cellCreateGasPrice
private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def removeTwoRef8Gas : Int := baseGas + twoRef8Penalty
private def removeTwoRef8GasMinusOne : Int :=
  if removeTwoRef8Gas > 0 then removeTwoRef8Gas - 1 else 0

private def rawOpcodeF49C : Cell := Cell.mkOrdinary (natToBits 0xF49C 16) #[]
private def rawOpcodeF49D : Cell := Cell.mkOrdinary (natToBits 0xF49D 16) #[]
private def rawOpcodeF49E : Cell := Cell.mkOrdinary (natToBits 0xF49E 16) #[]
private def rawOpcodeF49F : Cell := Cell.mkOrdinary (natToBits 0xF49F 16) #[]
private def rawOpcodeF498 : Cell := Cell.mkOrdinary (natToBits 0xF498 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

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

private def expectDecodeOk (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decode did not consume full code cell")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {instr}/{bits}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV 909)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

def genDictIremMaxRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/miss/null/257" #[dictNull, intV 257], rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit/single8" #[ .cell dictSingleRef8, intV 8], rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/miss/single8-width-mismatch" #[ .cell dictSingleRef8, intV 5], rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/hit/single8-alt" #[ .cell dictSingleRef8Alt, intV 8], rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/hit/two8" #[ .cell dictTwoRef8, intV 8], rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit/three8" #[ .cell dictThreeRef8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit/257" #[ .cell dictSingleRef257, intV 257], rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit/257-min" #[ .cell dictSingleRef257Min, intV 257], rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/hit/257-max" #[ .cell dictSingleRef257Max, intV 257], rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/miss/non-empty/0" #[ .cell dictSingleRef8, intV 0], rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss/non-empty/mismatch-width" #[ .cell dictSingleRef257, intV 4], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/type-top" #[.cell valueA, intV 8], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/dict-not-cell" #[.cont (.quit 0), intV 8], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/nan" #[ .cell dictSingleRef8, .int .nan], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/n-negative" #[ .cell dictSingleRef8, intV (-1)], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/n-large" #[ .cell dictSingleRef8, intV 258], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/malformed-dict" #[ .cell malformedDict, intV 8], rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/bad-ref-value" #[ .cell dictSliceSingle8, intV 8], rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/base-exact-miss" #[dictNull, intV 8]
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/base-exact-minus-one-miss" #[dictNull, intV 8]
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/remove-two8-exact" #[.cell dictTwoRef8, intV 8]
        (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact removeTwoRef8Gas), rng1)
    else
      (mkCase "fuzz/gas/remove-two8-exact-minus-one" #[.cell dictTwoRef8, intV 8]
        (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne removeTwoRef8GasMinusOne), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

/--
There are 30+ manually curated oracle entries covering dispatch/runtime/decoder/gas branches.
-/
def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "dispatch-fallback"
          (runDispatchFallback #[intV 1, intV 2])
          #[intV 1, intV 2, intV 909] },
    { name := "unit/asm/assemble-ok" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF49F 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF49F bits, got {reprStr c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTUREMMAXREF failed: {reprStr e}") },
    { name := "unit/asm/assemble-reject-gap-and-range" -- [B7]
      run := do
        expectAssembleErr "gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "out-of-range" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/decode/self-and-neighbors" -- [B8]
      run := do
        expectDecodeOk "decode/self" rawOpcodeF49F (.dictGetMinMax 31)
        expectDecodeOk "decode/prev" rawOpcodeF49E (.dictGetMinMax 30)
        expectDecodeOk "decode/prevprev" rawOpcodeF49D (.dictGetMinMax 29) },
    { name := "unit/decode/invalid" -- [B8]
      run := do
        expectDecodeErr "decode/gap" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode/truncated-8" rawTruncated8 .invOpcode },
    { name := "unit/exec/miss-null" -- [B3][B4]
      run := do
        expectOkStack "miss-null-8" (runDirect #[dictNull, intV 8]) #[dictNull, intV 0]
        expectOkStack "miss-null-0" (runDirect #[dictNull, intV 0]) #[dictNull, intV 0] },
    { name := "unit/exec/hit-single8-max-remove-empty" -- [B4][B5][B6]
      run := do
        expectOkStack "hit-single8"
          (runDirect #[ .cell dictSingleRef8, intV 8])
          #[.null, .cell valueA, intV 5, intV (-1)] },
    { name := "unit/exec/hit-single8-alt-key13" -- [B6]
      run := do
        expectOkStack "hit-single8-alt"
          (runDirect #[ .cell dictSingleRef8Alt, intV 8])
          #[.null, .cell valueB, intV 13, intV (-1)] },
    { name := "unit/exec/hit-two8-root-move" -- [B4][B5][B6]
      run := do
        expectOkStack "hit-two8"
          (runDirect #[ .cell dictTwoRef8, intV 8])
          #[.cell dictTwoRef8AfterMax, .cell valueA, intV 5, intV (-1)] },
    { name := "unit/exec/miss-non-empty-width-mismatch" -- [B4]
      run := do
        expectOkStack "miss-non-empty-0-width"
          (runDirect #[ .cell dictSingleRef8, intV 0])
          #[.cell dictSingleRef8, intV 0] },
    { name := "unit/exec/hit-257-boundary-max" -- [B6][B3]
      run := do
        expectOkStack "hit-257-max"
          (runDirect #[ .cell dictSingleRef257Max, intV 257])
          #[.null, .cell valueB, intV 2, intV (-1)] },
    { name := "unit/exec/hit-257-boundary-min" -- [B6][B3]
      run := do
        expectOkStack "hit-257-min"
          (runDirect #[ .cell dictSingleRef257Min, intV 257])
          #[.null, .cell valueA, intV 1, intV (-1)] },
    { name := "unit/exec/byref-shape-invalid" -- [B6][B5]
      run := do
        expectErr "bad-ref-shape" (runDirect #[ .cell dictSliceSingle8, intV 8]) .dictErr },
    { name := "unit/exec/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/n-errors" -- [B2][B3]
      run := do
        expectErr "n-nan" (runDirect #[dictNull, .int .nan]) .rangeChk
        expectErr "n-negative" (runDirect #[dictNull, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDirect #[dictNull, intV 258]) .rangeChk },
    { name := "unit/exec/type-errors" -- [B2]
      run := do
        expectErr "dict-top-not-cell" (runDirect #[.cell valueA, intV 8]) .typeChk
        expectErr "dict-not-cell" (runDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/exec/malformed-dict" -- [B4][B5]
      run := do
        expectErr "malformed-dict" (runDirect #[.cell malformedDict, intV 8]) .cellUnd
    }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0],
    mkCase "oracle/miss/null/8" #[dictNull, intV 8],
    mkCase "oracle/miss/null/257" #[dictNull, intV 257],
    mkCase "oracle/miss/non-empty/0" #[.cell dictSingleRef8, intV 0],
    mkCase "oracle/miss/non-empty/4" #[.cell dictThreeRef8, intV 4],
    mkCase "oracle/hit/single8" #[.cell dictSingleRef8, intV 8],
    mkCase "oracle/miss/single8-width-mismatch" #[.cell dictSingleRef8, intV 5],
    mkCase "oracle/hit/single8-alt" #[.cell dictSingleRef8Alt, intV 8],
    mkCase "oracle/hit/two8" #[.cell dictTwoRef8, intV 8],
    mkCase "oracle/hit/three8" #[.cell dictThreeRef8, intV 8],
    mkCase "oracle/hit/257" #[.cell dictSingleRef257, intV 257],
    mkCase "oracle/hit/257-min" #[.cell dictSingleRef257Min, intV 257],
    mkCase "oracle/hit/257-max" #[.cell dictSingleRef257Max, intV 257],
    mkCase "oracle/hit/bad-ref-value" #[.cell dictSliceSingle8, intV 8],
    mkCase "oracle/err/underflow-empty" (#[] : Array Value),
    mkCase "oracle/err/underflow-one" #[dictNull],
    mkCase "oracle/err/underflow-two" #[dictNull, intV 8],
    mkCase "oracle/err/type-top-int" #[.cell valueA, intV 8],
    mkCase "oracle/err/type-top-cont" #[.cont (.quit 0), intV 8],
    mkCase "oracle/err/nan" #[.cell dictSingleRef8, .int .nan],
    mkCase "oracle/err/n-negative" #[.cell dictSingleRef8, intV (-1)],
    mkCase "oracle/err/n-too-large" #[.cell dictSingleRef8, intV 258],
    mkCase "oracle/err/n-way-overflow" #[.cell dictSingleRef8, intV 300],
    mkCase "oracle/err/malformed-dict" #[.cell malformedDict, intV 8],
    mkCase "gas/exact-miss" #[dictNull, intV 8]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas),
    mkCase "gas/exact-minus-one-miss" #[dictNull, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne),
    mkCase "gas/remove-two8" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwoRef8Gas),
    mkCase "gas/remove-two8-minus-one" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwoRef8GasMinusOne),
    mkCodeCase "code/raw/f49d" #[] rawOpcodeF49D,
    mkCodeCase "code/raw/f49c" #[] rawOpcodeF49C,
    mkCodeCase "code/raw/f49e" #[] rawOpcodeF49E,
    mkCodeCase "code/raw/f49f" #[] rawOpcodeF49F,
    mkCodeCase "code/gap/f498" #[] rawOpcodeF498,
    mkCodeCase "code/truncated8" #[] rawTruncated8
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictIremMaxRefFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREMMAXREF
