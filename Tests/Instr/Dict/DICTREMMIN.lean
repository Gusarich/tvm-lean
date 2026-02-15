import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREMMIN

/-!
INSTRUCTION: DICTREMMIN

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Runtime dispatch path.
   `execInstrDictDictGetMinMax` handles `.dictGetMinMax`; all other instructions
   defer to `next`.

2. [B2] Runtime preamble.
   `VM.checkUnderflow 2` requires a dictionary and width `n`.
   `VM.popNatUpTo 1023` rejects `.nan`, negative, and out-of-range values.

3. [B3] Dictionary root handling.
   `popMaybeCell` accepts `null` and `.cell`, rejects other top types.

4. [B4] Empty/miss behavior.
   Empty/`null` dicts and non-matching keys return `[dictRoot-or-null, 0]`.

5. [B5] Hit path semantics (by-ref disabled / non-int key).
   For `DICTREMMIN` (`args5 = 18`) `byRef=false`, `intKey=false`, `fetchMax=false`,
   `remove=true`, `unsigned=false`.
   Hit returns `(root', valueSlice, keySlice, -1)` where `valueSlice` is the stored
   dictionary value as a VM slice and key is the reconstructed `n`-bit key slice.

6. [B6] Signed ordering behavior.
   `unsigned=false` means signed traversal order in `dictMinMaxWithCells`, so negative
   signed labels (e.g. key `-1` at `n=8`) can compare before positive ones.

7. [B7] Remove/delete branch.
   On hit with `remove=true`, `dictDeleteWithCells` is invoked.
   Single-element dictionaries return `null`; non-empty dictionaries return updated
   dictionary roots. Delete can add `created * cellCreateGasPrice` gas cost.

8. [B8] Assembler encoding.
   `.dictGetMinMax 18` must encode to `0xF492`.
   In-family gaps (`17`, `24`) are `.invOpcode`, out-of-range (`33`) is `.rangeChk`.

9. [B9] Decoder behavior.
   `0xF492..0xF497` decode to `.dictGetMinMax 18..23`.
   `0xF491`, `0xF498`, and truncated opcodes are `.invOpcode`.

10. [B10] Gas accounting.
    Base exact gas should succeed on miss and exact-minus-one should fail.
    Hit adds one `cellCreateGasPrice` for key-slice creation.
    Hit+delete paths also add `created * cellCreateGasPrice`.

TOTAL BRANCHES: 10
-/

private def suiteId : InstrId :=
  { name := "DICTREMMIN" }

private def instr : Instr :=
  .dictGetMinMax 18

private def fallbackSentinel : Int := 909

private def maxKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n false false with
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

private def dictSingle0N0 : Cell :=
  mkDictSetRefRoot! "dictSingle0N0" 0 #[(0, valueA)]
private def dictSingle8 : Cell :=
  mkDictSetRefRoot! "dictSingle8" 8 #[(7, valueA)]
private def dictSingle8Alt : Cell :=
  mkDictSetRefRoot! "dictSingle8Alt" 8 #[(13, valueB)]
private def dictTwo8 : Cell :=
  mkDictSetRefRoot! "dictTwo8" 8 #[(7, valueA), (13, valueB)]
private def dictTwo8AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwo8AfterMin" 8 #[(13, valueB)]
private def dictThree8 : Cell :=
  mkDictSetRefRoot! "dictThree8" 8 #[(1, valueA), (7, valueB), (13, valueC)]
private def dictThree8AfterMin : Cell :=
  mkDictSetRefRoot! "dictThree8AfterMin" 8 #[(7, valueB), (13, valueC)]
private def dictSigned8 : Cell :=
  mkDictSetRefRoot! "dictSigned8" 8 #[( -1, valueA), (1, valueB)]
private def dictSigned8AfterMin : Cell :=
  mkDictSetRefRoot! "dictSigned8AfterMin" 8 #[(-1, valueA)]

private def dictSingle1023 : Cell :=
  mkDictSetRefRoot! "dictSingle1023" 1023 #[(0, valueA)]
private def dictTwo1023 : Cell :=
  mkDictSetRefRoot! "dictTwo1023" 1023 #[(0, valueA), (1, valueB)]
private def dictTwo1023AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwo1023AfterMin" 1023 #[(1, valueB)]

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(7, badValueSlice)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def keySlice (n k : Nat) : Slice :=
  Slice.ofCell <| Cell.mkOrdinary (natToBits k n) #[]

private def two8Created : Nat := dictDeleteCreated dictTwo8 8
private def three8Created : Nat := dictDeleteCreated dictThree8 8
private def two1023Created : Nat := dictDeleteCreated dictTwo1023 1023
private def signed8Created : Nat := dictDeleteCreated dictSigned8 8
private def two8Penalty : Int := Int.ofNat two8Created * cellCreateGasPrice
private def three8Penalty : Int := Int.ofNat three8Created * cellCreateGasPrice
private def two1023Penalty : Int := Int.ofNat two1023Created * cellCreateGasPrice
private def signed8Penalty : Int := Int.ofNat signed8Created * cellCreateGasPrice

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def hitGas : Int := baseGas + cellCreateGasPrice
private def hitGasMinusOne : Int := if hitGas > 0 then hitGas - 1 else 0
private def removeTwo8Gas : Int := hitGas + two8Penalty
private def removeTwo8GasMinusOne : Int := if removeTwo8Gas > 0 then removeTwo8Gas - 1 else 0
private def removeThree8Gas : Int := hitGas + three8Penalty
private def removeThree8GasMinusOne : Int := if removeThree8Gas > 0 then removeThree8Gas - 1 else 0
private def removeTwo1023Gas : Int := hitGas + two1023Penalty
private def removeTwo1023GasMinusOne : Int := if removeTwo1023Gas > 0 then removeTwo1023Gas - 1 else 0
private def removeSigned8Gas : Int := hitGas + signed8Penalty
private def removeSigned8GasMinusOne : Int := if removeSigned8Gas > 0 then removeSigned8Gas - 1 else 0

private def raw16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]
private def raw8 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 8) #[]

private def rawOpcodeF492 : Cell := raw16 0xF492
private def rawOpcodeF493 : Cell := raw16 0xF493
private def rawOpcodeF494 : Cell := raw16 0xF494
private def rawOpcodeF495 : Cell := raw16 0xF495
private def rawOpcodeF496 : Cell := raw16 0xF496
private def rawOpcodeF497 : Cell := raw16 0xF497
private def rawOpcodeF491 : Cell := raw16 0xF491
private def rawOpcodeF498 : Cell := raw16 0xF498
private def rawOpcodeF4 : Cell := raw8 0xF4

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

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV fallbackSentinel)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

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

private def sliceRemBits (s : Slice) : BitString :=
  s.cell.bits.extract s.bitPos s.cell.bits.size

-- DICT* ops can return dictionary values as a "direct" slice over the value cell,
-- or as a wrapper slice whose next ref points at the value cell (bits consumed).
private def expectSliceRepresentsCell
    (label : String)
    (s : Slice)
    (expected : Cell) : IO Unit := do
  let remBits := sliceRemBits s
  if s.refsRemaining = 0 then
    if remBits != expected.bits then
      throw (IO.userError s!"{label}: expected value bits {reprStr expected.bits}, got {reprStr remBits}")
  else if s.bitsRemaining = 0 && s.refsRemaining ≥ 1 then
    let r := s.cell.refs.get! s.refPos
    if r != expected then
      throw (IO.userError s!"{label}: expected value ref {reprStr expected}, got {reprStr r}")
  else
    throw (IO.userError s!"{label}: unexpected value slice shape {reprStr s}")

private def expectHitShape
    (label : String)
    (result : Except Excno (Array Value))
    (expectedRoot : Value)
    (keyBits : Nat)
    (expectedValue : Cell) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok #[root, .slice value, .slice key, .int (.num flag)] =>
      if root != expectedRoot then
        throw (IO.userError s!"{label}: expected root {reprStr expectedRoot}, got {reprStr root}")
      else if flag != (-1 : Int) then
        throw (IO.userError s!"{label}: expected -1 flag, got {flag}")
      else if key.bitsRemaining != keyBits then
        throw (IO.userError s!"{label}: expected key width {keyBits}, got {key.bitsRemaining}")
      else
        expectSliceRepresentsCell label value expectedValue
  | .ok st =>
      throw (IO.userError s!"{label}: expected [root,slice,slice,-1], got {reprStr st}")

-- NOTE: `runDispatchFallback` and `runDirect` use `runHandlerDirectWithNext` /
-- `runHandlerDirect` from `Tests.Harness.Gen.Arith`.

private def genDictRemMinFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/16" #[dictNull, intV 16], rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/1023" #[dictNull, intV 1023], rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/single8" #[.cell dictSingle8, intV 8], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/single8-alt" #[.cell dictSingle8Alt, intV 8], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/signed8" #[.cell dictSigned8, intV 8], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/two8" #[.cell dictTwo8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/three8" #[.cell dictThree8, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/hit/single1023" #[.cell dictSingle1023, intV 1023], rng1)
    else if shape = 10 then
      (mkCase "fuzz/hit/two1023" #[.cell dictTwo1023, intV 1023], rng1)
    else if shape = 11 then
      (mkCase "fuzz/miss/width-mismatch-16" #[.cell dictSingle8, intV 16], rng1)
    else if shape = 12 then
      (mkCodeCase "fuzz/err/code/f492" #[.cell dictSingle8, intV 8] rawOpcodeF492, rng1)
    else if shape = 13 then
      (mkCodeCase "fuzz/err/code/gap491" #[.cell dictSingle8, intV 8] rawOpcodeF491, rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/underflow-one" #[dictNull], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-top-int" #[.cell dictSingle8, .int .nan], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-negative-n" #[.cell dictSingle8, intV (-1)], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/type-too-large-n" #[.cell dictSingle8, intV 1024], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/root-non-cell" #[.tuple #[], intV 8], rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/root-malformed" #[.cell malformedDict, intV 8], rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/exact" #[dictNull, intV 8]
        #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/exact-minus-one" #[dictNull, intV 8]
        #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/remove-two8" #[.cell dictTwo8, intV 8]
        #[.pushInt (.num removeTwo8Gas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact removeTwo8Gas), rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/remove-two8-oog" #[.cell dictTwo8, intV 8]
        #[.pushInt (.num removeTwo8GasMinusOne), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExactMinusOne removeTwo8GasMinusOne), rng1)
    else if shape = 25 then
      (mkCase "fuzz/gas/remove-three8" #[.cell dictThree8, intV 8]
        #[.pushInt (.num removeThree8Gas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact removeThree8Gas), rng1)
    else if shape = 26 then
      (mkCase "fuzz/gas/remove-two1023" #[.cell dictTwo1023, intV 1023]
        #[.pushInt (.num removeTwo1023Gas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact removeTwo1023Gas), rng1)
    else if shape = 27 then
      (mkCase "fuzz/gas/remove-signed8" #[.cell dictSigned8, intV 8]
        #[.pushInt (.num removeSigned8Gas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact removeSigned8Gas), rng1)
    else if shape = 28 then
      (mkCase "fuzz/gas/remove-signed8-oog" #[.cell dictSigned8, intV 8]
        #[.pushInt (.num removeSigned8GasMinusOne), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExactMinusOne removeSigned8GasMinusOne), rng1)
    else if shape = 29 then
      (mkCodeCase "fuzz/code/f493" #[.cell dictSingle8, intV 8] rawOpcodeF493, rng1)
    else if shape = 30 then
      (mkCase "fuzz/gas/hit-exact" #[.cell dictSingle8, intV 8]
        #[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact hitGas), rng1)
    else if shape = 31 then
      (mkCodeCase "fuzz/code/gap498" #[.cell dictSingle8, intV 8] rawOpcodeF498, rng1)
    else
      (mkCodeCase "fuzz/code/truncated8" #[] rawOpcodeF4, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback"
          (runDispatchFallback #[intV 1, intV 2])
          #[intV 1, intV 2, intV fallbackSentinel] },
    { name := "unit/asm/assemble/valid" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF492 16 then
              throw (IO.userError s!"expected 0xF492 bits, got {reprStr c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTREMMIN failed: {reprStr e}") },
    { name := "unit/asm/assemble/gaps" -- [B8]
      run := do
        expectAssembleErr "assemble-gap-17" (.dictGetMinMax 17) .invOpcode
        expectAssembleErr "assemble-gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "assemble-range" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/decode/branches" -- [B9]
      run := do
        let s0 : Slice :=
          Slice.ofCell
            (Cell.mkOrdinary
              (rawOpcodeF492.bits ++
                rawOpcodeF493.bits ++
                rawOpcodeF494.bits ++
                rawOpcodeF495.bits ++
                rawOpcodeF496.bits ++
                rawOpcodeF497.bits) #[])
        let s1 ← expectDecodeStep "decode/f492" s0 (.dictGetMinMax 18) 16
        let s2 ← expectDecodeStep "decode/f493" s1 (.dictGetMinMax 19) 16
        let s3 ← expectDecodeStep "decode/f494" s2 (.dictGetMinMax 20) 16
        let s4 ← expectDecodeStep "decode/f495" s3 (.dictGetMinMax 21) 16
        let s5 ← expectDecodeStep "decode/f496" s4 (.dictGetMinMax 22) 16
        let s6 ← expectDecodeStep "decode/f497" s5 (.dictGetMinMax 23) 16
        if s6.bitsRemaining + s6.refsRemaining != 0 then
          throw (IO.userError "decode did not consume full stream") },
    { name := "unit/decode/invalid" -- [B9]
      run := do
        expectDecodeErr "decode-gap-before" rawOpcodeF491 .invOpcode
        expectDecodeErr "decode-gap-after" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode },
    { name := "unit/exec/miss-null" -- [B4]
      run := do
        expectOkStack "miss/null-0" (runDirect #[dictNull, intV 0]) #[dictNull, intV 0]
        expectOkStack "miss/null-1023" (runDirect #[dictNull, intV 1023]) #[dictNull, intV 0] },
    { name := "unit/exec/hit/single" -- [B5]
      run := do
        expectHitShape "single-0" (runDirect #[.cell dictSingle0N0, intV 0]) .null 0 valueA
        expectHitShape "single-8" (runDirect #[.cell dictSingle8, intV 8]) .null 8 valueA
        expectHitShape "single-1023" (runDirect #[.cell dictSingle1023, intV 1023]) .null 1023 valueA },
    { name := "unit/exec/hit/multi" -- [B6][B7]
      run := do
        expectHitShape "two8-remove-root" (runDirect #[.cell dictTwo8, intV 8]) (.cell dictTwo8AfterMin) 8 valueA
        expectHitShape "three8-remove-root" (runDirect #[.cell dictThree8, intV 8]) (.cell dictThree8AfterMin) 8 valueA
        expectHitShape "signed8-remove-root" (runDirect #[.cell dictSigned8, intV 8]) (.cell dictSigned8AfterMin) 8 valueB },
    { name := "unit/exec/marshal-slice-value" -- [B5]
      run := do
        expectHitShape "slice-value" (runDirect #[.cell dictSliceSingle8, intV 8]) .null 8 badValueSlice.cell },
    { name := "unit/exec/width-mismatch" -- [B4]
      run := do
        expectErr "width-mismatch-16" (runDirect #[.cell dictSingle8, intV 16]) .cellUnd },
    { name := "unit/exec/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "n-nan" (runDirect #[dictNull, .int .nan]) .rangeChk
        expectErr "n-negative" (runDirect #[dictNull, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDirect #[dictNull, intV 1024]) .rangeChk },
    { name := "unit/exec/type-errors" -- [B3]
      run := do
        expectErr "root-top-int" (runDirect #[.cell valueA, intV 8]) .dictErr
        expectErr "root-tuple" (runDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/exec/malformed-root" -- [B3]
      run := do
        expectErr "malformed-root" (runDirect #[.cell malformedDict, intV 8]) .cellUnd },
    { name := "unit/exec/malformed-gap-code" -- [B9]
      run := do
        expectOkStack "invalid-gap-opcode"
          (runHandlerDirect execInstrDictDictGetMinMax (.dictGetMinMax 17) #[.cell dictSingle8, intV 8])
          #[.null, .cell valueA, .slice (keySlice 8 7), intV (-1)] },
    { name := "unit/gas/exact-miss" -- [B10]
      run := do
        expectOkStack "base" (runDirect #[dictNull, intV 8])
          #[dictNull, intV 0] }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0],
    mkCase "oracle/miss/null/8" #[dictNull, intV 8],
    mkCase "oracle/miss/null/16" #[dictNull, intV 16],
    mkCase "oracle/miss/null/1023" #[dictNull, intV 1023],
    mkCase "oracle/hit/single0" #[.cell dictSingle0N0, intV 0],
    mkCase "oracle/hit/single8" #[.cell dictSingle8, intV 8],
    mkCase "oracle/hit/alt8" #[.cell dictSingle8Alt, intV 8],
    mkCase "oracle/hit/signed8" #[.cell dictSigned8, intV 8],
    mkCase "oracle/hit/two8" #[.cell dictTwo8, intV 8],
    mkCase "oracle/hit/three8" #[.cell dictThree8, intV 8],
    mkCase "oracle/hit/two1023" #[.cell dictTwo1023, intV 1023],
    mkCase "oracle/miss/mismatch-16" #[.cell dictSingle8, intV 16],
    mkCase "oracle/miss/type-root-non-cell" #[.tuple #[], intV 8],
    mkCase "oracle/miss/type-root-cont" #[.cont (.quit 0), intV 8],
    mkCase "oracle/miss/root-malformed" #[.cell malformedDict, intV 8],
    mkCase "oracle/miss/type-nan" #[.null, .int .nan],
    mkCase "oracle/miss/type-negative" #[.null, intV (-1)],
    mkCase "oracle/miss/type-too-large" #[.null, intV 1024],
    mkCodeCase "oracle/code/f492" #[.cell dictSingle8, intV 8] rawOpcodeF492,
    mkCodeCase "oracle/code/f493" #[.cell dictSingle8, intV 8] rawOpcodeF493,
    mkCodeCase "oracle/code/f494" #[.cell dictSingle8, intV 8] rawOpcodeF494,
    mkCodeCase "oracle/code/f495" #[.cell dictSingle8, intV 8] rawOpcodeF495,
    mkCodeCase "oracle/code/f496" #[.cell dictSingle8, intV 8] rawOpcodeF496,
    mkCodeCase "oracle/code/f497" #[.cell dictSingle8, intV 8] rawOpcodeF497,
    mkCodeCase "oracle/code/gap491" #[.cell dictSingle8, intV 8] rawOpcodeF491,
    mkCodeCase "oracle/code/gap498" #[.cell dictSingle8, intV 8] rawOpcodeF498,
    mkCodeCase "oracle/code/truncated8" #[] rawOpcodeF4,
    mkCase "oracle/gas/base" #[dictNull, intV 8]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas),
    mkCase "oracle/gas/base-minus-one" #[dictNull, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne),
    mkCase "oracle/gas/hit" #[.cell dictSingle8, intV 8]
      (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGas),
    mkCase "oracle/gas/hit-minus-one" #[.cell dictSingle8, intV 8]
      (#[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitGasMinusOne),
    mkCase "oracle/gas/remove-two8" #[.cell dictTwo8, intV 8]
      (#[.pushInt (.num removeTwo8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwo8Gas),
    mkCase "oracle/gas/remove-two8-oog" #[.cell dictTwo8, intV 8]
      (#[.pushInt (.num removeTwo8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwo8GasMinusOne),
    mkCase "oracle/gas/remove-three8" #[.cell dictThree8, intV 8]
      (#[.pushInt (.num removeThree8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeThree8Gas),
    mkCase "oracle/gas/remove-three8-oog" #[.cell dictThree8, intV 8]
      (#[.pushInt (.num removeThree8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeThree8GasMinusOne),
    mkCase "oracle/gas/remove-two1023" #[.cell dictTwo1023, intV 1023]
      (#[.pushInt (.num removeTwo1023Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwo1023Gas),
    mkCase "oracle/gas/remove-two1023-oog" #[.cell dictTwo1023, intV 1023]
      (#[.pushInt (.num removeTwo1023GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwo1023GasMinusOne),
    mkCase "oracle/gas/remove-signed8" #[.cell dictSigned8, intV 8]
      (#[.pushInt (.num removeSigned8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeSigned8Gas),
    mkCase "oracle/gas/remove-signed8-oog" #[.cell dictSigned8, intV 8]
      (#[.pushInt (.num removeSigned8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeSigned8GasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictRemMinFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREMMIN
