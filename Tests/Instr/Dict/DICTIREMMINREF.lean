import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREMMINREF

/-!
INSTRUCTION: DICTIREMMINREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`; all other opcodes should delegate to
     `next`.

2. [B2] Runtime preamble validation.
   - `checkUnderflow` requires two stack items (`dict`, `n`).
   - `popNatUpTo 257` rejects NaN, negative, and >257.

3. [B3] Dictionary root decoding.
   - `VM.popMaybeCell` accepts `null` as empty dict and `.cell c` as an optional root.
   - Non-cell top-of-stack values are `.typeChk`.

4. [B4] Empty/missing-key behavior.
   - Empty dict (`null`) always reports miss (`0`) and preserves/returns `null` for the old dict.
   - Non-empty dict can also be miss for width/key-mismatch and returns original root plus `0`.

5. [B5] Hit behavior for signed int keys (min path).
   - `fetchMax = false`, `invertFirst = true`; returns minimum key in signed order.
   - `intKey` outputs reconstructed signed integer (`bitsToIntSignedTwos`).

6. [B6] Remove-path behavior (`remove = true`).
   - On hit, delete is attempted via `dictDeleteWithCells`.
   - On miss no delete occurs.
   - New dict root is pushed (`null` if empty after delete).

7. [B7] By-ref output shape requirement.
   - `byRef = true` requires payload slice with zero remaining bits and one reference.
   - Any other payload shape raises `.dictErr`.

8. [B8] Assembler encoding/validation categories.
   - `.dictGetMinMax 21` must assemble.
   - Gaps in argument space (`1`, `9`, `17`, etc.) are `.invOpcode`.
   - Args >31 is `.rangeChk`.

9. [B9] Decoder behavior.
   - `0xF495` decodes to `.dictGetMinMax 21`.
   - Neighbors `0xF494` and `0xF496`/`0xF497` decode in the same family.
   - Gaps (`0xF491`, `0xF498`) and truncated bytes must fail as `.invOpcode`.

10. [B10] Gas accounting.
    - Exact base gas should succeed.
    - Exact gas minus one should fail by gas exhaustion.
    - Remove-mode path may add `cellCreateGasPrice * created` penalties from `dictDeleteWithCells`.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTIREMMINREF" }

private def instr : Instr :=
  .dictGetMinMax 21

private def minKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n false true with
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
        match dictKeyBits? k n false with
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
        match dictKeyBits? k n false with
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

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC 8) #[]
private def badValueSlice : Slice := mkSliceFromBits (natToBits 0xF0 8)

private def dictNull : Value := .null
private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]
private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[( -1, valueA), (5, valueB)]
private def dictThreeRef8 : Cell :=
  mkDictSetRefRoot! "dictThreeRef8" 8 #[( -1, valueA), (5, valueB), (7, valueC)]
private def dictSingleRef257 : Cell :=
  mkDictSetRefRoot! "dictSingleRef257" 257 #[(0, valueA)]
private def dictTwoRef257 : Cell :=
  mkDictSetRefRoot! "dictTwoRef257" 257 #[(minInt257, valueA), (0, valueB)]
private def dictSingleRef257Min : Cell :=
  mkDictSetRefRoot! "dictSingleRef257Min" 257 #[(minInt257, valueA)]
private def dictTwoRef8AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwoRef8AfterMin" 8 #[(5, valueB)]
private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[( -1, badValueSlice)]
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def twoRef8Created : Nat := dictDeleteCreated dictTwoRef8 8
private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def removeTwoRef8Gas : Int := baseGas + Int.ofNat twoRef8Created * cellCreateGasPrice
private def removeTwoRef8GasMinusOne : Int := if removeTwoRef8Gas > 0 then removeTwoRef8Gas - 1 else 0

private def rawOpcodeF495 : Cell := Cell.mkOrdinary (natToBits 0xF495 16) #[]
private def rawOpcodeF494 : Cell := Cell.mkOrdinary (natToBits 0xF494 16) #[]
private def rawOpcodeF496 : Cell := Cell.mkOrdinary (natToBits 0xF496 16) #[]
private def rawOpcodeF497 : Cell := Cell.mkOrdinary (natToBits 0xF497 16) #[]
private def rawOpcodeF491 : Cell := Cell.mkOrdinary (natToBits 0xF491 16) #[]
private def rawOpcodeF498 : Cell := Cell.mkOrdinary (natToBits 0xF498 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV 909)) stack

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
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got error {e}")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got success {instr}/{bits}")

def genDictIremMinRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/miss/null/n0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/miss/null/n8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/miss/null/n16" #[dictNull, intV 16], rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/miss/null/n256" #[dictNull, intV 256], rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/miss/null/n257" #[dictNull, intV 257], rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/hit/single8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/hit/two8" #[.cell dictTwoRef8, intV 8], rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit/three8" #[.cell dictThreeRef8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit/single257" #[.cell dictSingleRef257, intV 257], rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit/two257" #[.cell dictTwoRef257, intV 257], rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/miss/width16-in-8-key" #[.cell dictSingleRef8, intV 16], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/underflow-empty" (#[]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/underflow-one" #[dictNull], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/nan" #[dictNull, .int .nan], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/negative-n" #[.cell dictSingleRef8, intV (-1)], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/too-large-n" #[.cell dictSingleRef8, intV 258], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-top" #[.slice badValueSlice, intV 8], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/malformed-byref" #[.cell dictSliceSingle8, intV 8], rng1)
    else if shape = 18 then
      (mkCase "fuzz/gas/exact/min" #[dictNull, intV 8]
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]), rng1)
    else if shape = 19 then
      (mkCase "fuzz/gas/minus-one/miss" #[dictNull, intV 8]
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]), rng1)
    else
      (mkCodeCase "fuzz/gas/raw" #[.cell dictTwoRef8, intV 8] rawOpcodeF495, rng1)
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
            if st == #[intV 1, intV 2, intV 909] then
              pure ()
            else
              throw (IO.userError s!"fallback failed: expected {reprStr #[intV 1, intV 2, intV 909]}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"fallback failed: {e}") },
    { name := "unit/opcode/assemble/exact" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF495 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF495 bits, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTIREMMINREF failed: {reprStr e}") },
    { name := "unit/opcode/assemble/reject-gaps" -- [B8]
      run := do
        match assembleCp0 [(.dictGetMinMax 1)] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted args=1 (gap)")
        | .error _ => pure () },
    { name := "unit/opcode/assemble/reject-oob" -- [B8]
      run := do
        match assembleCp0 [(.dictGetMinMax 33)] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted args=33")
        | .error _ => pure () },
    { name := "unit/decode/branches" -- [B9]
      run := do
        expectDecodeOk "decode/self" rawOpcodeF495 (.dictGetMinMax 21)
        expectDecodeOk "decode/prev" rawOpcodeF494 (.dictGetMinMax 20)
        expectDecodeOk "decode/next" rawOpcodeF496 (.dictGetMinMax 22)
        expectDecodeOk "decode/nextnext" rawOpcodeF497 (.dictGetMinMax 23)
        expectDecodeErr "decode-gap-before-family" rawOpcodeF491 .invOpcode
        expectDecodeErr "decode-gap-inside-family" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode-truncated8" rawTruncated8 .invOpcode },
    { name := "unit/exec/success/miss-null/0" -- [B4]
      run := do
        expectOkStack "miss-null-0" (runDirect #[.null, intV 0]) #[intV 0, .null] },
    { name := "unit/exec/success/miss-null/257" -- [B4]
      run := do
        expectOkStack "miss-null-257" (runDirect #[.null, intV 257]) #[intV 0, .null] },
    { name := "unit/exec/success/hit/single-ref8" -- [B5][B6][B7]
      run := do
        expectOkStack "single-ref8"
          (runDirect #[.cell dictSingleRef8, intV 8])
          #[.null, .cell valueA, intV 5, intV (-1)] },
    { name := "unit/exec/success/hit/two-ref8-remains" -- [B6][B8][B5]
      run := do
        expectOkStack "two-ref8"
          (runDirect #[.cell dictTwoRef8, intV 8])
          #[.cell dictTwoRef8AfterMin, .cell valueA, intV (-1), intV (-1)] },
    { name := "unit/exec/success/hit/single-ref257" -- [B5][B7]
      run := do
        expectOkStack "single-ref257"
          (runDirect #[.cell dictSingleRef257, intV 257])
          #[.null, .cell valueA, intV 0, intV (-1)] },
    { name := "unit/exec/err/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[.cell dictSingleRef8]) .stkUnd },
    { name := "unit/exec/err/n-invalid" -- [B2]
      run := do
        expectErr "nan" (runDirect #[.null, .int .nan]) .rangeChk
        expectErr "negative" (runDirect #[.null, intV (-1)]) .rangeChk
        expectErr "too-large" (runDirect #[.null, intV 3000]) .rangeChk },
    { name := "unit/exec/err/type" -- [B3]
      run := do
        expectErr "top-not-cell" (runDirect #[.slice badValueSlice, intV 8]) .typeChk
        expectErr "top-not-cell-or-null" (runDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/exec/err/dict-err-byref" -- [B7]
      run := do
        expectErr "not-ref-val" (runDirect #[.cell dictSliceSingle8, intV 8]) .dictErr
        expectErr "malformed-root" (runDirect #[.cell malformedDict, intV 8]) .cellUnd },
    { name := "unit/exec/mismatch-width-miss" -- [B4][B5]
      run := do
        expectOkStack "width-mismatch"
          (runDirect #[.cell dictSingleRef8, intV 16])
          #[.cell dictSingleRef8, intV 0] }
  ]
  oracle := #[
    mkCase "ok/miss/null/0" #[dictNull, intV 0], -- [B4]
    mkCase "ok/miss/null/8" #[dictNull, intV 8], -- [B4]
    mkCase "ok/miss/null/16" #[dictNull, intV 16], -- [B4]
    mkCase "ok/miss/null/256" #[dictNull, intV 256], -- [B4]
    mkCase "ok/miss/null/257" #[dictNull, intV 257], -- [B4]
    mkCase "ok/miss/width-mismatch" #[.cell dictSingleRef8, intV 16], -- [B4][B5]
    mkCase "ok/hit/single8" #[.cell dictSingleRef8, intV 8], -- [B5][B6][B7]
    mkCase "ok/hit/two8" #[.cell dictTwoRef8, intV 8], -- [B5][B6][B7]
    mkCase "ok/hit/three8" #[.cell dictThreeRef8, intV 8], -- [B5][B7]
    mkCase "ok/hit/single257" #[.cell dictSingleRef257, intV 257], -- [B5][B7]
    mkCase "ok/hit/two257-min" #[.cell dictTwoRef257, intV 257], -- [B5][B7]
    mkCase "ok/hit/min257" #[.cell dictSingleRef257Min, intV 257], -- [B5][B7]
    mkCodeCase "ok/code/raw/f494" #[dictNull, intV 8] rawOpcodeF494, -- [B9]
    mkCodeCase "ok/code/raw/f495" #[dictNull, intV 8] rawOpcodeF495, -- [B9]
    mkCodeCase "ok/code/raw/f496" #[dictNull, intV 8] rawOpcodeF496, -- [B9]
    mkCodeCase "ok/code/raw/f497" #[dictNull, intV 8] rawOpcodeF497, -- [B9]
    mkCodeCase "ok/code/raw/f491" #[dictNull, intV 8] rawOpcodeF491, -- [B9]
    mkCodeCase "ok/code/raw/f498" #[dictNull, intV 8] rawOpcodeF498, -- [B9]
    mkCodeCase "ok/code/raw/truncated8" #[] rawTruncated8, -- [B9]
    mkCase "err/underflow/empty" #[], -- [B2]
    mkCase "err/underflow/one-item" #[dictNull], -- [B2]
    mkCase "err/type-top-int" #[.int .nan, intV 8], -- [B2]
    mkCase "err/type-top-slice" #[.slice badValueSlice, intV 8], -- [B2]
    mkCase "err/type-top-cont" #[.cont (.quit 0), intV 8], -- [B2]
    mkCase "err/n-neg" #[.cell dictSingleRef8, intV (-1)], -- [B3]
    mkCase "err/n-too-large" #[.cell dictSingleRef8, intV 300], -- [B3]
    mkCase "err/n-max-plus" #[.cell dictSingleRef8, intV 258], -- [B3]
    mkCase "err/nan" #[.cell dictSingleRef8, .int .nan], -- [B3]
    mkCase "err/root-malformed" #[.cell malformedDict, intV 8], -- [B4]
    mkCase "err/byref-not-cell-payload" #[.cell dictSliceSingle8, intV 8], -- [B7]
    mkCase "err/gas/exact-minus-one-miss" #[dictNull, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact baseGasMinusOne), -- [B10]
    mkCase "gas/exact/base-miss" #[dictNull, intV 8]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact baseGas), -- [B10]
    mkCase "gas/remove/two-ref8-exact" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact removeTwoRef8Gas), -- [B6][B10]
    mkCase "gas/remove/two-ref8-minus-one" #[.cell dictTwoRef8, intV 8]
      (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact removeTwoRef8GasMinusOne), -- [B6][B10]
    mkCase "ok/program/trim-stack" #[.cell dictTwoRef8, intV 8] #[instr, .pushInt (.num 777)],
    mkCodeCase "err/program/truncated8" #[] rawTruncated8
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictIremMinRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREMMINREF
