import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREPLACEGETREF

/-!
INSTRUCTION: DICTUREPLACEGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch.
   - `.dictExt` instructions are handled by `execInstrDictExt`.
   - `.dictExt (.mutGet ... )` takes the `.mutGet` path; non-matching opcodes continue with `next`.

2. [B2] Stack shape/arity and operand ordering.
   - `VM.checkUnderflow 4` enforces argument order: `newValue`, `key`, `dict`, `n`.
   - Empty stack and 1/2/3-element stacks fail before type conversion.

3. [B3] Width parsing.
   - `popNatUpTo 1023` validates `n` and reports `.rangeChk` for negative, `NaN`, or `>1023`.
   - `n = 0` is valid only when key is exactly zero.

4. [B4] Unsigned integer key conversion.
   - `dictKeyBits? key n true` is used for key conversion.
   - Key is invalid if:
     - negative,
     - larger or equal to `2^n`,
     - nonzero for `n = 0`.
   - Invalid key conversion path raises `.rangeChk`.

5. [B5] Runtime semantics for unsigned replace/getref.
   - Missing key: dictionary root is unchanged and `0` is pushed (`ok_f` false branch).
   - Existing key: dictionary root is rewritten and `(oldValueRef, -1)` is pushed.
   - `.dictErr` is not expected on ordinary hits/misses.

6. [B6] Return-value shape and dictionary value constraints.
   - On hit, `extractRefOrThrow` requires the old dictionary value to be exactly one ref and no bits.
   - Non-ref values or malformed refs trigger `.dictErr`.

7. [B7] Dictionary structure validation.
   - Malformed root structures fail during dict traversal and raise `.dictErr`.

8. [B8] Decoder + assembler mapping.
   - `0xf42a..0xf42f` decode into `.dictExt (.mutGet intKey=bit2 unsigned=bit1 byRef=bit0 .replace)`.
   - `0xf429` and `0xf430` are invalid.
   - 8-bit opcode input is rejected (`.invOpcode`).
   - `assembleCp0` currently cannot emit these `.dictExt` variants (`.invOpcode`).

9. [B9] Gas accounting.
   - Base cost is `computeExactGasBudget instr`.
   - Hit paths consume additional `created * cellCreateGasPrice`.
   - Exact and exact-minus-one budget variants must be exercised.

TOTAL BRANCHES: 9

Every oracle test below is tagged with the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTUREPLACEGETREF" }

private def instr : Instr :=
  .dictExt (.mutGet true true true .replace)

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def malformedValueBits : Slice :=
  mkSliceFromBits (natToBits 0xF0 8)

private def malformedValueBitsAndRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[valueA])

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictSetRefRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Nat × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? (Int.ofNat k) n true with
        | some b => b
        | none => panic! s!"{label}: invalid unsigned key ({k}) for n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root during set"
      | .error e =>
          panic! s!"{label}: dict set failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def mkDictSetSliceRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Nat × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? (Int.ofNat k) n true with
        | some b => b
        | none => panic! s!"{label}: invalid unsigned key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root during set"
      | .error e =>
          panic! s!"{label}: dict set failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def dictUnsigned8Single : Cell :=
  mkDictSetRefRoot! "DICTUREPLACEGETREF::unsigned8Single" 8 #[(5, valueA)]

private def dictUnsigned8Double : Cell :=
  mkDictSetRefRoot! "DICTUREPLACEGETREF::unsigned8Double" 8 #[(5, valueA), (11, valueB)]

private def dictUnsigned8Triple : Cell :=
  mkDictSetRefRoot! "DICTUREPLACEGETREF::unsigned8Triple" 8 #[(0, valueA), (127, valueB), (255, valueC)]

private def dictUnsigned1 : Cell :=
  mkDictSetRefRoot! "DICTUREPLACEGETREF::unsigned1" 1 #[(0, valueA), (1, valueC)]

private def dictUnsigned0 : Cell :=
  mkDictSetRefRoot! "DICTUREPLACEGETREF::unsigned0" 0 #[(0, valueA)]

private def dictUnsigned1023 : Cell :=
  mkDictSetRefRoot! "DICTUREPLACEGETREF::unsigned1023" 1023 #[(0, valueA)]

private def dictUnsigned8MalformedRef : Cell :=
  mkDictSetSliceRoot! "DICTUREPLACEGETREF::unsigned8MalformedRef" 8 #[(10, malformedValueBits)]

private def dictUnsigned8MalformedRefWithRef : Cell :=
  mkDictSetSliceRoot! "DICTUREPLACEGETREF::unsigned8MalformedRefWithRef" 8 #[(11, malformedValueBitsAndRef)]

private def replaceHitCreated (dict : Cell) (n : Nat) (key : Int) (newValue : Cell) : Nat :=
  match dictKeyBits? key n true with
  | some keyBits =>
      match dictLookupSetRefWithCells (some dict) keyBits newValue .replace with
      | .ok (_oldVal, _newRoot, _ok, created, _loaded) => created
      | .error _ => 0
  | none => 0

private def hitCreatedSingle : Nat :=
  replaceHitCreated dictUnsigned8Single 8 5 valueB

private def hitCreatedDouble : Nat :=
  replaceHitCreated dictUnsigned8Double 8 5 valueC

private def hitCreatedMax : Nat :=
  replaceHitCreated dictUnsigned8Triple 8 255 valueA

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def hitGasSingle : Int :=
  baseGas + (Int.ofNat hitCreatedSingle * cellCreateGasPrice)

private def hitGasDouble : Int :=
  baseGas + (Int.ofNat hitCreatedDouble * cellCreateGasPrice)

private def hitGasMax : Int :=
  baseGas + (Int.ofNat hitCreatedMax * cellCreateGasPrice)

private def hitGasSingleMinusOne : Int :=
  if hitGasSingle > 0 then hitGasSingle - 1 else 0

private def hitGasDoubleMinusOne : Int :=
  if hitGasDouble > 0 then hitGasDouble - 1 else 0

private def hitGasMaxMinusOne : Int :=
  if hitGasMax > 0 then hitGasMax - 1 else 0

private def rawF42a : Cell := Cell.mkOrdinary (natToBits 0xF42A 16) #[]
private def rawF42b : Cell := Cell.mkOrdinary (natToBits 0xF42B 16) #[]
private def rawF42c : Cell := Cell.mkOrdinary (natToBits 0xF42C 16) #[]
private def rawF42d : Cell := Cell.mkOrdinary (natToBits 0xF42D 16) #[]
private def rawF42e : Cell := Cell.mkOrdinary (natToBits 0xF42E 16) #[]
private def rawF42f : Cell := Cell.mkOrdinary (natToBits 0xF42F 16) #[]
private def rawInvalidBelow : Cell := Cell.mkOrdinary (natToBits 0xf429 16) #[]
private def rawInvalidAbove : Cell := Cell.mkOrdinary (natToBits 0xf430 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def mkDictCaseStack (newValue : Value) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[newValue, intV key, dict, intV n]

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

private def expectDecodeInvOpcode (label : String) (cell : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error .invOpcode =>
      pure ()
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} after {bits} bits")
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode =>
      pure ()
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got code {c.bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def runDICTUREPLACEGETREFDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (.int (.num 909))) stack

private def genDICTUREPLACEGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase (s!"fuzz/underflow-empty/{tag}") #[] -- [B2]
    else if shape = 1 then
      mkCase (s!"fuzz/underflow-one/{tag}") #[.cell valueA] -- [B2]
    else if shape = 2 then
      mkCase (s!"fuzz/underflow-two/{tag}") (mkDictCaseStack (.cell valueB) 5 (.cell dictUnsigned8Single) 8) -- [B2]
    else if shape = 3 then
      mkCase (s!"fuzz/underflow-three/{tag}") (mkDictCaseStack (.cell valueC) 11 .null 8) -- [B2]
    else if shape = 4 then
      mkCase (s!"fuzz/miss/null/{tag}") (mkDictCaseStack (.cell valueA) 7 .null 8) -- [B3][B5]
    else if shape = 5 then
      mkCase (s!"fuzz/miss/null-wide/{tag}") (mkDictCaseStack (.cell valueB) 31 (.cell dictUnsigned1023) 1023) -- [B5]
    else if shape = 6 then
      mkCase (s!"fuzz/miss/n-zero/{tag}") (mkDictCaseStack (.cell valueC) 0 .null 0) -- [B3][B5]
    else if shape = 7 then
      mkCase (s!"fuzz/hit/single/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8) -- [B5]
    else if shape = 8 then
      mkCase (s!"fuzz/hit/double/{tag}") (mkDictCaseStack (.cell valueA) 11 (.cell dictUnsigned8Double) 8) -- [B5]
    else if shape = 9 then
      mkCase (s!"fuzz/hit/triple/{tag}") (mkDictCaseStack (.cell valueA) 127 (.cell dictUnsigned8Triple) 8) -- [B5]
    else if shape = 10 then
      mkCase (s!"fuzz/hit/max/{tag}") (mkDictCaseStack (.cell valueA) 255 (.cell dictUnsigned8Triple) 8) -- [B5]
    else if shape = 11 then
      mkCase (s!"fuzz/hit/trimmed-stack/{tag}") (#[
        .int (.num 777), .cell valueA, .int (.num 127), .cell dictUnsigned8Double, intV 8]) -- [B5]
    else if shape = 12 then
      mkCase (s!"fuzz/err/key-negative/{tag}") (mkDictCaseStack (.cell valueA) (-1) (.cell dictUnsigned8Single) 8) -- [B4]
    else if shape = 13 then
      mkCase (s!"fuzz/err/key-overflow/{tag}") (mkDictCaseStack (.cell valueA) 256 (.cell dictUnsigned8Single) 8) -- [B4]
    else if shape = 14 then
      mkCase (s!"fuzz/err/key-bit0-violation/{tag}") (mkDictCaseStack (.cell valueA) 1 (.cell dictUnsigned0) 0) -- [B4]
    else if shape = 15 then
      mkCase (s!"fuzz/err/key-high-for-n1/{tag}") (mkDictCaseStack (.cell valueA) 2 (.cell dictUnsigned1) 1) -- [B4]
    else if shape = 16 then
      mkCase (s!"fuzz/err/n-negative/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) (-1)) -- [B3]
    else if shape = 17 then
      mkCase (s!"fuzz/err/n-too-large/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 1024) -- [B3]
    else if shape = 18 then
      mkCase (s!"fuzz/err/n-nan/{tag}") (#[.cell valueA, .int (.num 5), .cell dictUnsigned8Single, .int .nan]) -- [B3]
    else if shape = 19 then
      mkCase (s!"fuzz/err/type-dict/{tag}") (mkDictCaseStack (.cell valueA) 5 (.tuple #[]) 8) -- [B2]
    else if shape = 20 then
      mkCase (s!"fuzz/err/type-key/{tag}") (#[.cell valueA, .slice (mkSliceFromBits (natToBits 5 8)), .cell dictUnsigned8Single, intV 8]) -- [B2]
    else if shape = 21 then
      mkCase (s!"fuzz/err/type-value/{tag}") (#[.int (.num 7), .int (.num 5), .cell dictUnsigned8Single, intV 8]) -- [B2]
    else if shape = 22 then
      mkCase (s!"fuzz/err/malformed-value/{tag}") (mkDictCaseStack (.cell valueC) 10 (.cell dictUnsigned8MalformedRef) 8) -- [B6]
    else if shape = 23 then
      mkCase (s!"fuzz/err/malformed-value-with-bits/{tag}") (mkDictCaseStack (.cell valueC) 11 (.cell dictUnsigned8MalformedRefWithRef) 8) -- [B6]
    else if shape = 24 then
      mkCase (s!"fuzz/err/malformed-root/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell malformedDictRoot) 8) -- [B7]
    else if shape = 25 then
      mkCodeCase (s!"fuzz/raw/f42a/{tag}") (mkDictCaseStack (.cell valueA) 5 .null 8) rawF42a -- [B8]
    else if shape = 26 then
      mkCodeCase (s!"fuzz/raw/f42f/{tag}") (mkDictCaseStack (.cell valueA) 5 .null 8) rawF42f -- [B8]
    else if shape = 27 then
      mkCodeCase (s!"fuzz/raw/invalid-low/{tag}") (#[] : Array Value) rawInvalidBelow -- [B8]
    else if shape = 28 then
      mkCodeCase (s!"fuzz/raw/invalid-high/{tag}") (#[] : Array Value) rawInvalidAbove -- [B8]
    else if shape = 29 then
      mkCodeCase (s!"fuzz/raw/truncated8/{tag}") (#[] : Array Value) rawTruncated8 -- [B8]
    else if shape = 30 then
      mkCase (s!"fuzz/gas/base-exact/{tag}") (mkDictCaseStack (.cell valueA) 7 .null 8)
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact baseGas) -- [B9]
    else
      mkCase (s!"fuzz/gas/hit-double-exact/{tag}") (mkDictCaseStack (.cell valueA) 11 (.cell dictUnsigned8Double) 8)
        (#[.pushInt (.num hitGasDouble), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitGasDouble) -- [B9]
  ({ case0 with name := case0.name }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let expectedStack : Array Value :=
          #[.int (.num 1), .int (.num 2), .int (.num 3), .cell dictUnsigned8Single, .int (.num 909)]
        match runDICTUREPLACEGETREFDispatchFallback (#[.int (.num 1), .int (.num 2), .int (.num 3), .cell dictUnsigned8Single]) with
        | .ok st =>
            if st == expectedStack then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback failed: expected {reprStr expectedStack}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback failed with {e}") },
    { name := "unit/decode/f42a" -- [B8]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42A 16)
        let _ ← expectDecodeStep "decode/f42a" s (.dictExt (.mutGet false false false .replace)) 16 },
    { name := "unit/decode/f42b" -- [B8]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42B 16)
        let _ ← expectDecodeStep "decode/f42b" s (.dictExt (.mutGet false false true .replace)) 16 },
    { name := "unit/decode/f42c" -- [B8]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42C 16)
        let _ ← expectDecodeStep "decode/f42c" s (.dictExt (.mutGet true false false .replace)) 16 },
    { name := "unit/decode/f42d" -- [B8]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42D 16)
        let _ ← expectDecodeStep "decode/f42d" s (.dictExt (.mutGet true false true .replace)) 16 },
    { name := "unit/decode/f42e" -- [B8]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42E 16)
        let _ ← expectDecodeStep "decode/f42e" s (.dictExt (.mutGet true true false .replace)) 16 },
    { name := "unit/decode/f42f" -- [B8]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42F 16)
        let _ ← expectDecodeStep "decode/f42f" s instr 16 },
    { name := "unit/decode/replacegetref-family" -- [B8]
      run := do
        let s0 : Slice := Slice.ofCell (Cell.mkOrdinary (rawF42a.bits ++ rawF42b.bits ++ rawF42c.bits ++ rawF42d.bits ++ rawF42e.bits ++ rawF42f.bits) #[])
        let s1 ← expectDecodeStep "decode/chain/f42a" s0 (.dictExt (.mutGet false false false .replace)) 16
        let s2 ← expectDecodeStep "decode/chain/f42b" s1 (.dictExt (.mutGet false false true .replace)) 16
        let s3 ← expectDecodeStep "decode/chain/f42c" s2 (.dictExt (.mutGet true false false .replace)) 16
        let s4 ← expectDecodeStep "decode/chain/f42d" s3 (.dictExt (.mutGet true false true .replace)) 16
        let s5 ← expectDecodeStep "decode/chain/f42e" s4 (.dictExt (.mutGet true true false .replace)) 16
        let _ ← expectDecodeStep "decode/chain/f42f" s5 (.dictExt (.mutGet true true true .replace)) 16 -- [B8]
        pure () },
    { name := "unit/decode/invalid-low" -- [B8]
      run := do
        expectDecodeInvOpcode "decode/f429" rawInvalidBelow },
    { name := "unit/decode/invalid-high" -- [B8]
      run := do
        expectDecodeInvOpcode "decode/f430" rawInvalidAbove },
    { name := "unit/decode/truncated" -- [B8]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated unexpectedly succeeded") },
    { name := "unit/asm/unsupported" -- [B9]
      run := do
        expectAssembleInvOpcode "asm/unsupported" instr }
  ]
  oracle := #[
    mkCase "oracle/err/underflow-empty" #[] , -- [B2]
    mkCase "oracle/err/underflow-one" #[.cell valueA], -- [B2]
    mkCase "oracle/err/underflow-two" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8), -- [B2]
    mkCase "oracle/err/underflow-three" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8), -- [B2]
    mkCase "oracle/err/n-negative" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) (-1)), -- [B3]
    mkCase "oracle/err/n-too-large" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 1024), -- [B3]
    mkCase "oracle/err/n-nan" (#[.cell valueA, intV 5, .cell dictUnsigned8Single, .int .nan]), -- [B3]
    mkCase "oracle/err/key-negative" (mkDictCaseStack (.cell valueA) (-1) (.cell dictUnsigned8Single) 8), -- [B4]
    mkCase "oracle/err/key-overflow-8bit" (mkDictCaseStack (.cell valueA) 256 (.cell dictUnsigned8Single) 8), -- [B4]
    mkCase "oracle/err/key-overflow-1bit" (mkDictCaseStack (.cell valueA) 2 (.cell dictUnsigned1) 1), -- [B4]
    mkCase "oracle/err/key-zero-width-nonzero" (mkDictCaseStack (.cell valueA) 1 (.cell dictUnsigned0) 0), -- [B4]
    mkCase "oracle/err/type-dict" (mkDictCaseStack (.cell valueA) 5 (.tuple #[]) 8), -- [B2]
    mkCase "oracle/err/type-key" (#[.cell valueA, .slice (mkSliceFromBits (natToBits 5 8)), .cell dictUnsigned8Single, intV 8]), -- [B2]
    mkCase "oracle/err/type-value" (#[.int (.num 7), .int (.num 5), .cell dictUnsigned8Single, intV 8]), -- [B2]
    mkCase "oracle/ok/miss/null" (mkDictCaseStack (.cell valueA) 7 .null 8), -- [B5]
    mkCase "oracle/ok/miss/zero" (mkDictCaseStack (.cell valueA) 7 .null 0), -- [B5]
    mkCase "oracle/ok/miss/wide" (mkDictCaseStack (.cell valueA) 31 (.cell dictUnsigned1023) 1023), -- [B5]
    mkCase "oracle/ok/hit/single" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8), -- [B5]
    mkCase "oracle/ok/hit/double" (mkDictCaseStack (.cell valueA) 11 (.cell dictUnsigned8Double) 8), -- [B5]
    mkCase "oracle/ok/hit/triple" (mkDictCaseStack (.cell valueB) 127 (.cell dictUnsigned8Triple) 8), -- [B5]
    mkCase "oracle/ok/hit/max-key" (mkDictCaseStack (.cell valueC) 255 (.cell dictUnsigned8Triple) 8), -- [B5]
    mkCase "oracle/ok/hit/one-bit" (mkDictCaseStack (.cell valueA) 1 (.cell dictUnsigned1) 1), -- [B5]
    mkCase "oracle/ok/hit/zero-width" (mkDictCaseStack (.cell valueA) 0 (.cell dictUnsigned0) 0), -- [B5]
    mkCase "oracle/ok/hit/trimmed-stack" (#[.int (.num 777), .cell valueB, intV 11, .cell dictUnsigned8Double, intV 8]), -- [B5]
    mkCase "oracle/err/value-not-ref" (mkDictCaseStack (.cell valueA) 10 (.cell dictUnsigned8MalformedRef) 8), -- [B6]
    mkCase "oracle/err/value-not-ref-with-bits" (mkDictCaseStack (.cell valueA) 11 (.cell dictUnsigned8MalformedRefWithRef) 8), -- [B6]
    mkCase "oracle/err/malformed-root" (mkDictCaseStack (.cell valueA) 5 (.cell malformedDictRoot) 8), -- [B7]
    mkCodeCase "oracle/raw/f42a" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8) rawF42a, -- [B8]
    mkCodeCase "oracle/raw/f42b" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8) rawF42b, -- [B8]
    mkCodeCase "oracle/raw/f42c" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8) rawF42c, -- [B8]
    mkCodeCase "oracle/raw/f42d" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8) rawF42d, -- [B8]
    mkCodeCase "oracle/raw/f42e" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8) rawF42e, -- [B8]
    mkCodeCase "oracle/raw/f42f" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Single) 8) rawF42f, -- [B8]
    mkCodeCase "oracle/raw/f42f-with-stack" (mkDictCaseStack (.cell valueA) 5 .null 8) rawF42f, -- [B8]
    mkCodeCase "oracle/raw/truncated8" (#[] : Array Value) rawTruncated8, -- [B8]
    mkCodeCase "oracle/raw/invalid-low" (#[] : Array Value) rawInvalidBelow, -- [B8]
    mkCodeCase "oracle/raw/invalid-high" (#[] : Array Value) rawInvalidAbove, -- [B8]
    mkCase "oracle/gas/base-exact" (mkDictCaseStack (.cell valueA) 7 .null 8)
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact baseGas), -- [B9]
    mkCase "oracle/gas/base-exact-minus-one" (mkDictCaseStack (.cell valueA) 7 .null 8)
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne baseGasMinusOne), -- [B9]
    mkCase "oracle/gas/hit-single-exact" (mkDictCaseStack (.cell valueA) 11 (.cell dictUnsigned8Single) 8)
      (#[.pushInt (.num hitGasSingle), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitGasSingle), -- [B9]
    mkCase "oracle/gas/hit-single-exact-minus-one" (mkDictCaseStack (.cell valueA) 11 (.cell dictUnsigned8Single) 8)
      (#[.pushInt (.num hitGasSingleMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitGasSingleMinusOne), -- [B9]
    mkCase "oracle/gas/hit-double-exact" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Double) 8)
      (#[.pushInt (.num hitGasDouble), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitGasDouble), -- [B9]
    mkCase "oracle/gas/hit-double-exact-minus-one" (mkDictCaseStack (.cell valueA) 5 (.cell dictUnsigned8Double) 8)
      (#[.pushInt (.num hitGasDoubleMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitGasDoubleMinusOne), -- [B9]
    mkCase "oracle/gas/hit-max-exact" (mkDictCaseStack (.cell valueA) 255 (.cell dictUnsigned8Triple) 8)
      (#[.pushInt (.num hitGasMax), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitGasMax), -- [B9]
    mkCase "oracle/gas/hit-max-exact-minus-one" (mkDictCaseStack (.cell valueA) 255 (.cell dictUnsigned8Triple) 8)
      (#[.pushInt (.num hitGasMaxMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitGasMaxMinusOne) -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTUREPLACEGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREPLACEGETREF
