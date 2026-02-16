import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREMMINREF

/-!
INSTRUCTION: DICTUREMMINREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`.
   - Any other opcode must follow `next` without side effects.

2. [B2] Runtime preamble validation.
   - `VM.checkUnderflow 2` requires two stack values `(dict, n)`.
   - `popNatUpTo 256` rejects non-integer, negative, and >256 `n` values.

3. [B3] Dictionary root extraction/type checks.
   - `VM.popMaybeCell` accepts `null` and `.cell`.
   - Non-cell root values (`.slice`, `.cont`, etc.) are `.typeChk`.

4. [B4] Miss/empty-root behavior.
   - `null` root always misses and returns pushed root `null` (because remove mode is enabled).
   - Non-empty roots can also miss when `n` does not match key width.
   - On miss, no delete attempt is made; old root is returned unchanged.

5. [B5] Hit path semantics for unsigned min.
   - For `DICTUREMMINREF` (`args = 23`, fetchMin + byRef + unsigned int + intKey + remove),
     signed/unsigned order is `unsigned` (`bits_to_nat`) and minimum is selected by this order.
   - Hit result returns updated root, minimum value reference, minimum key as non-negative `Int`, then `-1`.

6. [B6] Delete/reshape branch.
   - `dictDeleteWithCells` runs on hit and may mutate root.
   - Single-item dict becomes `null`; multi-item dict remains a (possibly changed) cell.
   - `created > 0` contributes variable gas penalty.

7. [B7] By-ref payload shape validation.
   - Return payload must be a reference-cell-only slice (`bitsRemaining = 0`, `refsRemaining = 1`).
   - All other payload shapes raise `.dictErr`.

8. [B8] Assembler encoding/validation.
   - `.dictGetMinMax 23` assembles exactly to `0xF497`.
   - In-family gaps (`17`, `24`, etc.) are `.invOpcode`.
   - `args > 31` is `.rangeChk`.

9. [B9] Decoder behavior.
   - `0xF497` decodes to `.dictGetMinMax 23`.
   - Neighbor opcodes `0xF495`/`0xF496` decode to adjacent variants in same group.
   - Boundary/gap bytes (`0xF491`, `0xF498`) and truncated bytes decode to `.invOpcode`.

10. [B10] Gas accounting.
    - Base compute budget succeeds for base path.
    - `exact-1` fails by gas.
    - Remove path can additionally fail with `created * cellCreateGasPrice`.

    TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTUREMMINREF" }

private def instr : Instr :=
  .dictGetMinMax 23

private def minKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n false false with
  | .ok (some (_, keyBits), _) => some keyBits
  | _ => none

private def dictDeleteCreated (root : Cell) (n : Nat) : Nat :=
  match minKeyBits root n with
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
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: empty root after insertion ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict after construction"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: empty root after insertion ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict after construction"

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def badValueSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xF0 8) #[])

private def maxU256 : Int :=
  Int.ofNat ((1 <<< 256) - 1)

private def dictNull : Value := .null

private def dictSingleRef0 : Cell :=
  mkDictSetRefRoot! "dictSingleRef0" 0 #[(0, valueA)]

private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]

private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[(5, valueA), (7, valueB)]

private def dictThreeRef8 : Cell :=
  mkDictSetRefRoot! "dictThreeRef8" 8 #[(3, valueA), (8, valueB), (200, valueC)]

private def dictSingleRef256 : Cell :=
  mkDictSetRefRoot! "dictSingleRef256" 256 #[(0, valueB)]

private def dictSingleRef256Max : Cell :=
  mkDictSetRefRoot! "dictSingleRef256Max" 256 #[(maxU256, valueA)]

private def dictTwoRef256 : Cell :=
  mkDictSetRefRoot! "dictTwoRef256" 256 #[(5, valueA), (maxU256, valueC)]

private def dictTwoRef8AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwoRef8AfterMin" 8 #[(7, valueB)]

private def dictThreeRef8AfterMin : Cell :=
  mkDictSetRefRoot! "dictThreeRef8AfterMin" 8 #[(8, valueB), (200, valueC)]

private def dictTwoRef256AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwoRef256AfterMin" 256 #[(maxU256, valueC)]

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(5, badValueSlice)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0b0 1) #[]

private def twoRef8Created : Nat :=
  dictDeleteCreated dictTwoRef8 8

private def twoRef256Created : Nat :=
  dictDeleteCreated dictTwoRef256 256

private def exactGas : Int :=
  computeExactGasBudget instr

private def exactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def removeTwoRef8Gas : Int :=
  exactGas + Int.ofNat twoRef8Created * cellCreateGasPrice

private def removeTwoRef8GasMinusOne : Int :=
  if removeTwoRef8Gas > 0 then removeTwoRef8Gas - 1 else 0

private def removeTwoRef256Gas : Int :=
  exactGas + Int.ofNat twoRef256Created * cellCreateGasPrice

private def removeTwoRef256GasMinusOne : Int :=
  if removeTwoRef256Gas > 0 then removeTwoRef256Gas - 1 else 0

private def rawOpcodeF495 : Cell := Cell.mkOrdinary (natToBits 0xF495 16) #[]
private def rawOpcodeF496 : Cell := Cell.mkOrdinary (natToBits 0xF496 16) #[]
private def rawOpcodeF497 : Cell := Cell.mkOrdinary (natToBits 0xF497 16) #[]
private def rawOpcodeF491 : Cell := Cell.mkOrdinary (natToBits 0xF491 16) #[]
private def rawOpcodeF498 : Cell := Cell.mkOrdinary (natToBits 0xF498 16) #[]
private def rawOpcodeF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def dispatchSentinel : Int := 909_909

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV dispatchSentinel)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

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

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, _) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
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

private def genDICTUREMMINREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/16" #[dictNull, intV 16], rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/256" #[dictNull, intV 256], rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/single/0" #[.cell dictSingleRef0, intV 0], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/single/8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/single/256" #[.cell dictSingleRef256, intV 256], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/two/8" #[.cell dictTwoRef8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/three/8" #[.cell dictThreeRef8, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/hit/two/256" #[.cell dictTwoRef256, intV 256], rng1)
    else if shape = 10 then
      (mkCase "fuzz/miss/width-mismatch" #[.cell dictSingleRef8, intV 16], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/underflow-one" #[dictNull], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/nan" #[dictNull, .int .nan], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/n-negative" #[.cell dictSingleRef8, intV (-1)], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/n-too-large" #[.cell dictSingleRef8, intV 257], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-top-slice" #[.cell dictSingleRef8, .slice badValueSlice], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-top-cont" #[.cell dictSingleRef8, .cont (.quit 0)], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/malformed-byref" #[.cell dictSliceSingle8, intV 8], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng1)
    else if shape = 20 then
      (mkCase "fuzz/gas/exact-base" #[dictNull, intV 8]
        (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/exact-minus-one" #[dictNull, intV 8]
        (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/remove/two8" #[.cell dictTwoRef8, intV 8]
        (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/remove/two8-minus-one" #[.cell dictTwoRef8, intV 8]
        (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/remove/two256" #[.cell dictTwoRef256, intV 256]
        (#[.pushInt (.num removeTwoRef256Gas), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 25 then
      (mkCase "fuzz/gas/remove/two256-minus-one" #[.cell dictTwoRef256, intV 256]
        (#[.pushInt (.num removeTwoRef256GasMinusOne), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 26 then
      (mkCodeCase "fuzz/code/raw/f495" #[] rawOpcodeF495, rng1)
    else if shape = 27 then
      (mkCodeCase "fuzz/code/raw/f496" #[] rawOpcodeF496, rng1)
    else if shape = 28 then
      (mkCodeCase "fuzz/code/raw/f497" #[] rawOpcodeF497, rng1)
    else
      (mkCodeCase "fuzz/code/raw/truncated8" #[] rawOpcodeF4, rng1)
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
              throw (IO.userError s!"fallback expected stack unchanged with sentinel, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"fallback execution failed: {e}") },
    { name := "unit/opcode/assemble/exact" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF497 16 then
              pure ()
            else
              throw (IO.userError s!"expected opcode 0xF497 bits, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTUREMMINREF failed: {reprStr e}") },
    { name := "unit/opcode/assemble/reject-gap1" -- [B8]
      run := expectAssembleErr "assemble-gap1" (.dictGetMinMax 17) .invOpcode },
    { name := "unit/opcode/assemble/reject-gap2" -- [B8]
      run := expectAssembleErr "assemble-gap2" (.dictGetMinMax 24) .invOpcode },
    { name := "unit/opcode/assemble/reject-oob" -- [B8]
      run := expectAssembleErr "assemble-oob" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/decode/branches" -- [B9]
      run := do
        expectDecodeOk "decode-self" rawOpcodeF497 (.dictGetMinMax 23)
        expectDecodeOk "decode-prev" rawOpcodeF496 (.dictGetMinMax 22)
        expectDecodeOk "decode-prevprev" rawOpcodeF495 (.dictGetMinMax 21)
        expectDecodeErr "decode-gap-before" rawOpcodeF491 .invOpcode
        expectDecodeErr "decode-gap-after" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode-truncated8" rawOpcodeF4 .invOpcode },
    { name := "unit/exec/success/miss/null/0" -- [B4]
      run := do
        expectOkStack "miss-null-0" (runDirect #[dictNull, intV 0]) #[.null, intV 0] },
    { name := "unit/exec/success/miss/null/256" -- [B4]
      run := do
        expectOkStack "miss-null-256" (runDirect #[dictNull, intV 256]) #[.null, intV 0] },
    { name := "unit/exec/success/hit/single/ref0" -- [B5][B6][B7]
      run := do
        expectOkStack "hit-single0"
          (runDirect #[.cell dictSingleRef0, intV 0])
          #[.null, .cell valueA, intV 0, intV (-1)] },
    { name := "unit/exec/success/hit/single8" -- [B5][B6][B7]
      run := do
        expectOkStack "hit-single8"
          (runDirect #[.cell dictSingleRef8, intV 8])
          #[.null, .cell valueA, intV 5, intV (-1)] },
    { name := "unit/exec/success/hit/two8-remove-min" -- [B5][B6]
      run := do
        expectOkStack "hit-two8"
          (runDirect #[.cell dictTwoRef8, intV 8])
          #[.cell dictTwoRef8AfterMin, .cell valueA, intV 5, intV (-1)] },
    { name := "unit/exec/success/hit/three8-remove-min" -- [B5][B6]
      run := do
        expectOkStack "hit-three8"
          (runDirect #[.cell dictThreeRef8, intV 8])
          #[.cell dictThreeRef8AfterMin, .cell valueA, intV 3, intV (-1)] },
    { name := "unit/exec/success/hit/single256" -- [B5][B6]
      run := do
        expectOkStack "hit-single256"
          (runDirect #[.cell dictSingleRef256, intV 256])
          #[.null, .cell valueB, intV 0, intV (-1)] },
    { name := "unit/exec/success/hit/two256-remove-min" -- [B5][B6]
      run := do
        expectOkStack "hit-two256"
          (runDirect #[.cell dictTwoRef256, intV 256])
          #[.cell dictTwoRef256AfterMin, .cell valueA, intV 5, intV (-1)] },
    { name := "unit/exec/err/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd },
    { name := "unit/exec/err/underflow-one" -- [B2]
      run := do
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/err/nan" -- [B2]
      run := do
        expectErr "nan" (runDirect #[dictNull, .int .nan]) .rangeChk },
    { name := "unit/exec/err/n-negative" -- [B2]
      run := do
        expectErr "negative-n" (runDirect #[dictNull, intV (-1)]) .rangeChk },
    { name := "unit/exec/err/n-too-large" -- [B2]
      run := do
        expectErr "too-large-n" (runDirect #[dictNull, intV 257]) .rangeChk },
    { name := "unit/exec/err/type-root-slice" -- [B3]
      run := do
        expectErr "root-slice" (runDirect #[.slice badValueSlice, intV 8]) .typeChk },
    { name := "unit/exec/err/type-root-cont" -- [B3]
      run := do
        expectErr "root-cont" (runDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/exec/err/invalid-byref-shape" -- [B7]
      run := do
        expectErr "not-ref-value" (runDirect #[.cell dictSliceSingle8, intV 8]) .dictErr },
    { name := "unit/exec/err/malformed-root" -- [B4]
      run := do
        expectErr "malformed-root" (runDirect #[.cell malformedDict, intV 8]) .cellUnd },
    { name := "unit/exec/mismatch-width-miss" -- [B4]
      run := do
        expectErr "width-mismatch" (runDirect #[.cell dictSingleRef8, intV 16]) .cellUnd }
  ]
  oracle := #[
    mkCase "ok/miss/null/0" #[dictNull, intV 0], -- [B4]
    mkCase "ok/miss/null/8" #[dictNull, intV 8], -- [B4]
    mkCase "ok/miss/null/16" #[dictNull, intV 16], -- [B4]
    mkCase "ok/miss/null/256" #[dictNull, intV 256], -- [B4]
    mkCase "ok/miss/width-mismatch" #[.cell dictSingleRef8, intV 16], -- [B4]
    mkCase "ok/hit/single0" #[.cell dictSingleRef0, intV 0], -- [B5][B6][B7]
    mkCase "ok/hit/single8" #[.cell dictSingleRef8, intV 8], -- [B5][B6][B7]
    mkCase "ok/hit/two8" #[.cell dictTwoRef8, intV 8], -- [B5][B6][B7]
    mkCase "ok/hit/three8" #[.cell dictThreeRef8, intV 8], -- [B5][B6]
    mkCase "ok/hit/single256" #[.cell dictSingleRef256, intV 256], -- [B5][B6][B7]
    mkCase "ok/hit/two256" #[.cell dictTwoRef256, intV 256], -- [B5][B6][B7]
    mkCase "ok/hit/single256-max" #[.cell dictSingleRef256Max, intV 256], -- [B5][B6]
    mkCodeCase "ok/code/raw/f495" #[] rawOpcodeF495, -- [B9]
    mkCodeCase "ok/code/raw/f496" #[] rawOpcodeF496, -- [B9]
    mkCodeCase "ok/code/raw/f497" #[] rawOpcodeF497, -- [B9]
    mkCodeCase "ok/code/raw/gap-before" #[] rawOpcodeF491, -- [B9]
    mkCodeCase "ok/code/raw/gap-after" #[] rawOpcodeF498, -- [B9]
    mkCodeCase "ok/code/raw/truncated8" #[] rawOpcodeF4, -- [B9]
    mkCase "err/underflow/empty" #[], -- [B2]
    mkCase "err/underflow/one-item" #[dictNull], -- [B2]
    mkCase "err/type-top-nan" #[dictNull, .int .nan], -- [B2]
    mkCase "err/type-top-slice" #[.cell dictSingleRef8, .slice badValueSlice], -- [B2]
    mkCase "err/type-top-cont" #[.cell dictSingleRef8, .cont (.quit 0)], -- [B3]
    mkCase "err/n-negative" #[.cell dictSingleRef8, intV (-1)], -- [B2]
    mkCase "err/n-overflow257" #[.cell dictSingleRef8, intV 257], -- [B2]
    mkCase "err/n-overflow-large" #[.cell dictSingleRef8, intV 1024], -- [B2]
    mkCase "err/byref-not-cell-payload" #[.cell dictSliceSingle8, intV 8], -- [B7]
    mkCase "err/root-malformed" #[.cell malformedDict, intV 8], -- [B3]
    mkCase "err/gas/exact-minus-one-miss" #[dictNull, intV 8]
      (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact exactGasMinusOne), -- [B10]
    mkCase "gas/exact/base-miss" #[dictNull, intV 8]
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact exactGas), -- [B10]
    mkCase "gas/remove/two-ref8-exact" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact removeTwoRef8Gas), -- [B6][B10]
    mkCase "gas/remove/two-ref8-minus-one" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact removeTwoRef8GasMinusOne), -- [B6][B10]
    mkCase "gas/remove/two-ref256-exact" #[.cell dictTwoRef256, intV 256]
      (#[.pushInt (.num removeTwoRef256Gas), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact removeTwoRef256Gas), -- [B6][B10]
    mkCase "gas/remove/two-ref256-minus-one" #[.cell dictTwoRef256, intV 256]
      (#[.pushInt (.num removeTwoRef256GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact removeTwoRef256GasMinusOne), -- [B6][B10]
    mkCase "ok/program/trim-stack" #[.cell dictTwoRef8, intV 8] #[instr, .pushInt (.num 777)] -- [B1]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUREMMINREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREMMINREF
