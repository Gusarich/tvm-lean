import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREMMINREF

/-!
INSTRUCTION: DICTREMMINREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`.

2. [B2] Preamble validation.
   - `checkUnderflow` requires 2 stack items.
   - `popNatUpTo` uses max key width 1023 for non-integer dictionaries.

3. [B3] Dictionary root/type behavior.
   - `.null` and `.cell` roots are accepted via `popMaybeCell`.
   - Non-cell roots (tuple/cont/slice/etc.) are `.typeChk`.

4. [B4] Miss path.
   - Empty dict or non-match case pushes the original root (or `.null`) and flag `0`.

5. [B5] Hit path + unsigned key output.
   - `fetchMax=false`, `invertFirst=true` means smallest key in normal unsigned order.
   - `intKey=false`, so the returned key is emitted as a fresh slice.

6. [B6] Remove path.
   - `remove=true` calls delete on hit.
   - Single-element dict becomes `.null`; multi-element returns the rebuilt root.
   - Delete can add `created * cellCreateGasPrice` gas.

7. [B7] By-ref output shape check.
   - For hit-by-ref, the value must satisfy `bitsRemaining=0` and `refsRemaining=1`.
   - Any mismatch raises `.dictErr`.

8. [B8] Assembler constraints.
   - `.dictGetMinMax 19` encodes to `0xF493`.
   - Valid args for this opcode family are `18..23`; other in-range values cause `.invOpcode`.
   - Args > 31 cause `.rangeChk`.

9. [B9] Decoder behavior.
   - `0xF492..0xF497` decode to `.dictGetMinMax 18..23`.
   - `0xF491`, `0xF498`, and truncated forms are `.invOpcode`.

10. [B10] Gas accounting.
    - Exact base gas should succeed.
    - Exact gas minus one should fail.
    - Hit path additionally consumes `cellCreateGasPrice` for key-slice creation.

TOTAL BRANCHES: 10

Each oracle test below is tagged with one or more [Bn].
-/

private def suiteId : InstrId :=
  { name := "DICTREMMINREF" }

private def instr : Instr :=
  .dictGetMinMax 19

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def dispatchSentinel : Int := 12_345

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}): {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def badValueSlice : Slice := mkSliceFromBits (natToBits 0xF0 8)

private def dictNull : Value := .null

private def dictSingleRef0 : Cell :=
  mkDictSetRefRoot! "dictSingleRef0" 0 #[(0, valueA)]
private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]
private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[(5, valueA), (200, valueB)]
private def dictThreeRef8 : Cell :=
  mkDictSetRefRoot! "dictThreeRef8" 8 #[(5, valueA), (13, valueB), (240, valueC)]
private def dictSingleRef257 : Cell :=
  mkDictSetRefRoot! "dictSingleRef257" 257 #[(0, valueA)]
private def dictSingleRef1023 : Cell :=
  mkDictSetRefRoot! "dictSingleRef1023" 1023 #[(0, valueA)]

private def dictTwoRef8AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwoRef8AfterMin" 8 #[(200, valueB)]
private def dictThreeRef8AfterMin : Cell :=
  mkDictSetRefRoot! "dictThreeRef8AfterMin" 8 #[(13, valueB), (240, valueC)]

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(5, badValueSlice)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b111 3) #[]

private def minKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n false false with
  | .ok (some (_val, keyBits), _) => some keyBits
  | _ => none

private def dictDeleteCreated (root : Cell) (n : Nat) : Nat :=
  match minKeyBits root n with
  | some keyBits =>
      match dictDeleteWithCells (some root) keyBits with
      | .ok (_old, _root, created, _loaded) => created
      | .error _ => 0
  | none => 0

private def twoRef8Created : Nat := dictDeleteCreated dictTwoRef8 8
private def threeRef8Created : Nat := dictDeleteCreated dictThreeRef8 8

private def rawOpcodeF492 : Cell := raw16 0xF492
private def rawOpcodeF493 : Cell := raw16 0xF493
private def rawOpcodeF494 : Cell := raw16 0xF494
private def rawOpcodeF495 : Cell := raw16 0xF495
private def rawOpcodeF496 : Cell := raw16 0xF496
private def rawOpcodeF497 : Cell := raw16 0xF497
private def rawOpcodeF491 : Cell := raw16 0xF491
private def rawOpcodeF498 : Cell := raw16 0xF498
private def rawOpcodeF4 : Cell := raw8 0xF4

private def keySlice0 : Slice := mkSliceFromBits (natToBits 0 0)
private def keySlice5_8 : Slice := mkSliceFromBits (natToBits 5 8)
private def keySlice13_8 : Slice := mkSliceFromBits (natToBits 13 8)
private def keySlice200_8 : Slice := mkSliceFromBits (natToBits 200 8)
private def keySlice240_8 : Slice := mkSliceFromBits (natToBits 240 8)
private def keySlice0_257 : Slice := mkSliceFromBits (natToBits 0 257)
private def keySlice0_1023 : Slice := mkSliceFromBits (natToBits 0 1023)

private def exactGas : Int := computeExactGasBudget instr
private def exactGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def hitGas : Int := exactGas + cellCreateGasPrice
private def hitGasMinusOne : Int := if hitGas > 0 then hitGas - 1 else 0
private def removeTwoRef8Gas : Int :=
  hitGas + Int.ofNat twoRef8Created * cellCreateGasPrice
private def removeThreeRef8Gas : Int :=
  hitGas + Int.ofNat threeRef8Created * cellCreateGasPrice
private def removeTwoRef8GasMinusOne : Int :=
  if removeTwoRef8Gas > 0 then removeTwoRef8Gas - 1 else 0
private def removeThreeRef8GasMinusOne : Int :=
  if removeThreeRef8Gas > 0 then removeThreeRef8Gas - 1 else 0

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

private def mkRawCase
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

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV dispatchSentinel)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected exact decode")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")

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

private def genDICTREMMINREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/n0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/n1" #[dictNull, intV 1], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/n8" #[dictNull, intV 8], rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/n16" #[dictNull, intV 16], rng1)
    else if shape = 4 then
      (mkCase "fuzz/miss/null/n257" #[dictNull, intV 257], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/single0" #[.cell dictSingleRef0, intV 0], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/single8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/two8" #[.cell dictTwoRef8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/three8" #[.cell dictThreeRef8, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/hit/single257" #[.cell dictSingleRef257, intV 257], rng1)
    else if shape = 10 then
      (mkCase "fuzz/hit/single1023" #[.cell dictSingleRef1023, intV 1023], rng1)
    else if shape = 11 then
      (mkCase "fuzz/miss/width-mismatch" #[.cell dictSingleRef8, intV 16], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/underflow-one" #[dictNull], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/nan" #[dictNull, .int .nan], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/negative-n" #[dictNull, intV (-1)], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/too-large-n" #[dictNull, intV 2048], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-top" #[.tuple #[], intV 8], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/byref-shape" #[.cell dictSliceSingle8, intV 8], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng1)
    else if shape = 20 then
      (mkCase "fuzz/gas/exact-miss" #[dictNull, intV 8]
        (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact exactGas), rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/minus-one-miss" #[dictNull, intV 8]
        (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne exactGasMinusOne), rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/hit-exact" #[dictNull, intV 8]
        (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact hitGas), rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/hit-minus-one" #[.cell dictTwoRef8, intV 8]
        (#[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne hitGasMinusOne), rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/remove-two8-exact" #[.cell dictTwoRef8, intV 8]
        (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact removeTwoRef8Gas), rng1)
    else if shape = 25 then
      (mkCase "fuzz/gas/remove-two8-minus-one" #[.cell dictTwoRef8, intV 8]
        (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne removeTwoRef8GasMinusOne), rng1)
    else if shape = 26 then
      (mkCase "fuzz/gas/remove-three8-exact" #[.cell dictThreeRef8, intV 8]
        (#[.pushInt (.num removeThreeRef8Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact removeThreeRef8Gas), rng1)
    else if shape = 27 then
      (mkCase "fuzz/gas/remove-three8-minus-one" #[.cell dictThreeRef8, intV 8]
        (#[.pushInt (.num removeThreeRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne removeThreeRef8GasMinusOne), rng1)
    else if shape = 28 then
      (mkCase "fuzz/code/f495" #[dictNull, intV 8] (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact exactGas), rng1)
    else
      (mkRawCase "fuzz/code/raw/f493" #[dictNull, intV 8] rawOpcodeF493, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDispatchFallback #[intV 1, intV 2] with
        | .ok st =>
            if st == #[intV 1, intV 2, intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"dispatch fallback failed: expected {reprStr #[intV 1, intV 2, intV dispatchSentinel]}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch fallback failed: {e}") },
    { name := "unit/asm/encode" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF493 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF493 bits, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTREMMINREF failed: {reprStr e}") },
    { name := "unit/asm/reject" -- [B8]
      run := do
        expectAssembleErr "gap-in-family" (.dictGetMinMax 17) .invOpcode
        expectAssembleErr "gap-before-family" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "oob" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/decode/family" -- [B9]
      run := do
        expectDecodeOk "decode/f492" rawOpcodeF492 (.dictGetMinMax 18)
        expectDecodeOk "decode/f493" rawOpcodeF493 (.dictGetMinMax 19)
        expectDecodeOk "decode/f494" rawOpcodeF494 (.dictGetMinMax 20)
        expectDecodeOk "decode/f495" rawOpcodeF495 (.dictGetMinMax 21)
        expectDecodeOk "decode/f496" rawOpcodeF496 (.dictGetMinMax 22)
        expectDecodeOk "decode/f497" rawOpcodeF497 (.dictGetMinMax 23)
        expectDecodeErr "decode/gap-before" rawOpcodeF491 .invOpcode
        expectDecodeErr "decode/gap-after" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode/truncated" rawOpcodeF4 .invOpcode },
    { name := "unit/exec/miss/null" -- [B4]
      run := do
        expectOkStack "miss-null-0" (runDirect #[dictNull, intV 0]) #[dictNull, intV 0]
        expectOkStack "miss-null-1023" (runDirect #[dictNull, intV 1023]) #[dictNull, intV 0] },
    { name := "unit/exec/hit/single0" -- [B5][B7][B6]
      run := do
      expectOkStack "single0"
        (runDirect #[.cell dictSingleRef0, intV 0])
          #[.null, .cell valueA, .slice keySlice0, intV (-1)] },
    { name := "unit/exec/hit/single8" -- [B5][B7][B6]
      run := do
        expectOkStack "single8"
          (runDirect #[.cell dictSingleRef8, intV 8])
          #[.null, .cell valueA, .slice keySlice5_8, intV (-1)] },
    { name := "unit/exec/hit/two8" -- [B5][B6]
      run := do
        expectOkStack "two8"
          (runDirect #[.cell dictTwoRef8, intV 8])
          #[.cell dictTwoRef8AfterMin, .cell valueB, .slice keySlice200_8, intV (-1)] },
    { name := "unit/exec/hit/three8" -- [B5][B6]
      run := do
        expectOkStack "three8"
          (runDirect #[.cell dictThreeRef8, intV 8])
          #[.cell dictThreeRef8AfterMin, .cell valueB, .slice keySlice13_8, intV (-1)] },
    { name := "unit/exec/hit/single1023" -- [B5]
      run := do
        expectOkStack "single1023"
          (runDirect #[.cell dictSingleRef1023, intV 1023])
          #[.null, .cell valueA, .slice keySlice0_1023, intV (-1)] },
    { name := "unit/exec/miss/width-mismatch" -- [B4]
      run := do
        expectOkStack "width-mismatch"
          (runDirect #[.cell dictSingleRef8, intV 16])
          #[.cell dictSingleRef8, intV 0] },
    { name := "unit/exec/err/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/err/n" -- [B2][B3]
      run := do
        expectErr "n-nan" (runDirect #[dictNull, .int .nan]) .rangeChk
        expectErr "n-negative" (runDirect #[dictNull, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDirect #[dictNull, intV 1024]) .rangeChk },
    { name := "unit/exec/err/type" -- [B3]
      run := do
        expectErr "root-tuple" (runDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/exec/err/byref-shape" -- [B7]
      run := do
        expectErr "bad-byref-shape" (runDirect #[.cell dictSliceSingle8, intV 8]) .dictErr
        expectErr "malformed-root" (runDirect #[.cell malformedDict, intV 8]) .cellUnd }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0], -- [B4]
    mkCase "oracle/miss/null/1" #[dictNull, intV 1], -- [B4]
    mkCase "oracle/miss/null/8" #[dictNull, intV 8], -- [B4]
    mkCase "oracle/miss/null/16" #[dictNull, intV 16], -- [B4]
    mkCase "oracle/miss/null/257" #[dictNull, intV 257], -- [B4]
    mkCase "oracle/miss/null/1023" #[dictNull, intV 1023], -- [B4]
    mkCase "oracle/miss/width-mismatch" #[.cell dictSingleRef8, intV 16], -- [B4]
    mkCase "oracle/miss/have-dict-non-empty-0" #[.cell dictSingleRef8, intV 0], -- [B4]
    mkCase "oracle/hit/single0" #[.cell dictSingleRef0, intV 0], -- [B5][B7]
    mkCase "oracle/hit/single8" #[.cell dictSingleRef8, intV 8], -- [B5][B6][B7]
    mkCase "oracle/hit/two8" #[.cell dictTwoRef8, intV 8], -- [B5][B6]
    mkCase "oracle/hit/three8" #[.cell dictThreeRef8, intV 8], -- [B5][B6]
    mkCase "oracle/hit/single257" #[.cell dictSingleRef257, intV 257], -- [B5]
    mkCase "oracle/hit/single1023" #[.cell dictSingleRef1023, intV 1023], -- [B5]
    mkCase "oracle/err/underflow-empty" #[], -- [B2]
    mkCase "oracle/err/underflow-one" #[dictNull], -- [B2]
    mkCase "oracle/err/type-root-tuple" #[.tuple #[], intV 8], -- [B3]
    mkCase "oracle/err/type-root-cont" #[.cont (.quit 0), intV 8], -- [B3]
    mkCase "oracle/err/nan" #[dictNull, .int .nan], -- [B2]
    mkCase "oracle/err/n-negative" #[dictNull, intV (-1)], -- [B2]
    mkCase "oracle/err/n-too-large" #[dictNull, intV 1024], -- [B2]
    mkCase "oracle/err/n-over" #[dictNull, intV 3000], -- [B2]
    mkCase "oracle/err/byref-bad-shape" #[.cell dictSliceSingle8, intV 8], -- [B7]
    mkCase "oracle/err/malformed-root" #[.cell malformedDict, intV 8], -- [B3]
    mkCase "gas/base-exact-miss" #[dictNull, intV 8]
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact exactGas), -- [B10]
    mkCase "gas/base-exact-minus-one-miss" #[dictNull, intV 8]
      (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne exactGasMinusOne), -- [B10]
    mkCase "gas/hit-exact" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGas), -- [B10]
    mkCase "gas/hit-minus-one" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitGasMinusOne), -- [B10]
    mkCase "gas/remove-two8-exact" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwoRef8Gas), -- [B6][B10]
    mkCase "gas/remove-two8-minus-one" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwoRef8GasMinusOne), -- [B6][B10]
    mkCase "gas/remove-three8-exact" #[.cell dictThreeRef8, intV 8]
      (#[.pushInt (.num removeThreeRef8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeThreeRef8Gas), -- [B6][B10]
    mkCase "gas/remove-three8-minus-one" #[.cell dictThreeRef8, intV 8]
      (#[.pushInt (.num removeThreeRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeThreeRef8GasMinusOne), -- [B6][B10]
    mkRawCase "code/f492" #[] rawOpcodeF492, -- [B9]
    mkRawCase "code/f493" #[] rawOpcodeF493, -- [B9]
    mkRawCase "code/f494" #[] rawOpcodeF494, -- [B9]
    mkRawCase "code/f495" #[] rawOpcodeF495, -- [B9]
    mkRawCase "code/f496" #[] rawOpcodeF496, -- [B9]
    mkRawCase "code/f497" #[] rawOpcodeF497, -- [B9]
    mkRawCase "code/f493-default-stack" #[dictNull, intV 8] rawOpcodeF493, -- [B9]
    mkRawCase "code/f491-gap" #[] rawOpcodeF491, -- [B9]
    mkRawCase "code/f498-gap" #[] rawOpcodeF498, -- [B9]
    mkRawCase "code/truncated" #[] rawOpcodeF4
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTREMMINREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREMMINREF
