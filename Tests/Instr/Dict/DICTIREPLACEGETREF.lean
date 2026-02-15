import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREPLACEGETREF

/-!
INSTRUCTION: DICTIREPLACEGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch.
   - `.dictExt` instructions are handled in `execInstrDictExt`.
   - `.dictExt (.mutGet ... )` routes to `mutGet`; all other opcodes keep executing `next`.

2. [B2] Stack arity + primitive type ordering.
   - `checkUnderflow 4` is mandatory before popping arguments.
   - For `DICTIREPLACEGETREF`: pops `n`, `dict`, `key`, `newValueRef` in that order.
   - Underflow, `n` range/type, dictionary type, key type, and value type errors must all occur along this order.

3. [B3] `n` and integer key validation.
   - `popNatUpTo 1023` validates `n`: negative/`NaN`/>1023 are `.rangeChk`.
   - `intKey` is fixed to `true`, `unsigned` to `false`, so signed-key bounds apply.
   - Invalid signed key for width raises `.rangeChk`.
   - `n = 0` allows only key `0`.

4. [B4] Runtime semantics for replace/getref.
   - Replace-miss: dictionary unchanged and `0` is pushed.
   - Replace-hit: dictionary is rebuilt and new root plus old value (`cell`) plus `-1` is pushed.
   - No `.dictErr` is thrown for normal leaf replacements.

5. [B5] Value shape check for by-ref return.
   - On hit, returned old value must be exactly one reference and no remaining bits.
   - Any `Slice` payload or `slice+refs` payload triggers `.dictErr`.

6. [B6] Dictionary integrity/structure errors.
   - Malformed dict nodes (label/constructor violations) throw `.dictErr`.

7. [B7] Decoder mapping for opcode family.
   - `0xf42a..0xf42f` decode to `.dictExt (.mutGet intKey=…, unsigned=…, byRef=…, .replace)`.
   - `0xf429` and `0xf430` must fail as `invOpcode`.
   - Truncated 8-bit input must fail to decode.

8. [B8] Assembler behavior.
   - `.dictExt` in this family is supported by the assembler.
   - `assembleCp0` must round-trip via decoder for `instr`.

9. [B9] Gas accounting.
   - Base gas is `computeExactGasBudget instr`.
   - Hit paths add `created * cellCreateGasPrice`.
   - Exact-budget and exact-minus-one budget cases must be exercised.

TOTAL BRANCHES: 9

Every oracle test below is tagged with the branch family it targets.
-/

private def suiteId : InstrId :=
  { name := "DICTIREPLACEGETREF" }

private def instr : Instr :=
  .dictExt (.mutGet true false true .replace)

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC 8) #[]

private def malformedValueBits : Slice :=
  mkSliceFromBits (natToBits 0xF0 8)

private def malformedValueBitsAndRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[valueA])

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictSetRefRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid signed key ({k}, n={n})"
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
    (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid signed key ({k}, n={n})"
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

private def dictSigned8Single : Cell :=
  mkDictSetRefRoot! "DICTIREPLACEGETREF::dictSigned8Single" 8 #[(5, valueA)]

private def dictSigned8Double : Cell :=
  mkDictSetRefRoot! "DICTIREPLACEGETREF::dictSigned8Double" 8 #[(5, valueA), (-1, valueB)]

private def dictSigned8Triple : Cell :=
  mkDictSetRefRoot! "DICTIREPLACEGETREF::dictSigned8Triple" 8 #[(5, valueA), (-1, valueB), (1, valueC)]

private def dictSigned8Three : Cell :=
  mkDictSetRefRoot! "DICTIREPLACEGETREF::dictSigned8Three" 8 #[(0, valueA), (4, valueB), (127, valueC)]

private def dictSigned0 : Cell :=
  mkDictSetRefRoot! "DICTIREPLACEGETREF::dictSigned0" 0 #[(0, valueA)]

private def dictSigned257 : Cell :=
  mkDictSetRefRoot! "DICTIREPLACEGETREF::dictSigned257" 257 #[(0, valueA)]

private def dictSigned8MalformedRef : Cell :=
  mkDictSetSliceRoot! "DICTIREPLACEGETREF::dictSigned8MalformedRef" 8 #[(10, malformedValueBits)]

private def dictSigned8MalformedRefWithRef : Cell :=
  mkDictSetSliceRoot! "DICTIREPLACEGETREF::dictSigned8MalformedRefWithRef" 8 #[(11, malformedValueBitsAndRef)]

private def replaceHitCreated (dict : Cell) (n : Nat) (key : Int) (newValue : Cell) : Nat :=
  match dictKeyBits? key n false with
  | some keyBits =>
      match dictLookupSetRefWithCells (some dict) keyBits newValue .replace with
      | .ok (_oldValue, _newRoot, _ok, created, _loaded) => created
      | .error _ => 0
  | none => 0

private def hitCreatedSingle : Nat :=
  replaceHitCreated dictSigned8Single 8 5 valueB

private def hitCreatedDouble : Nat :=
  replaceHitCreated dictSigned8Double 8 5 valueB

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def hitGasSingle : Int :=
  baseGas + (Int.ofNat hitCreatedSingle * cellCreateGasPrice)

private def hitGasDouble : Int :=
  baseGas + (Int.ofNat hitCreatedDouble * cellCreateGasPrice)

private def hitGasSingleMinusOne : Int :=
  if hitGasSingle > 0 then hitGasSingle - 1 else 0

private def hitGasDoubleMinusOne : Int :=
  if hitGasDouble > 0 then hitGasDouble - 1 else 0

private def rawF42a : Cell := Cell.mkOrdinary (natToBits 0xF42A 16) #[]
private def rawF42b : Cell := Cell.mkOrdinary (natToBits 0xF42B 16) #[]
private def rawF42c : Cell := Cell.mkOrdinary (natToBits 0xF42C 16) #[]
private def rawF42d : Cell := Cell.mkOrdinary (natToBits 0xF42D 16) #[]
private def rawF42e : Cell := Cell.mkOrdinary (natToBits 0xF42E 16) #[]
private def rawF42f : Cell := Cell.mkOrdinary (natToBits 0xF42F 16) #[]
private def rawInvalidBelow : Cell := Cell.mkOrdinary (natToBits 0xF429 16) #[]
private def rawInvalidAbove : Cell := Cell.mkOrdinary (natToBits 0xF430 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

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

private def expectAssembleOk16 (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok c => do
      let rest ← expectDecodeStep label (Slice.ofCell c) i 16
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected no trailing bits")
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")

private def runDICTIREPLACEGETREFDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (.int (.num 909))) stack

private def genDICTIREPLACEGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase (s!"fuzz/miss/null/{tag}") (mkDictCaseStack (.cell valueA) 7 .null 8) -- [B4][B9]
    else if shape = 1 then
      mkCase (s!"fuzz/miss/wide-null/{tag}") (mkDictCaseStack (.cell valueA) 3 .null 257) -- [B4][B9]
    else if shape = 2 then
      mkCase (s!"fuzz/miss/n0/{tag}") (mkDictCaseStack (.cell valueA) 1 .null 0) -- [B3][B4]
    else if shape = 3 then
      mkCase (s!"fuzz/hit/single/{tag}") (mkDictCaseStack (.cell valueB) 5 (.cell dictSigned8Single) 8) -- [B4][B5]
    else if shape = 4 then
      mkCase (s!"fuzz/hit/double/{tag}") (mkDictCaseStack (.cell valueA) (-1) (.cell dictSigned8Double) 8) -- [B4][B5]
    else if shape = 5 then
      mkCase (s!"fuzz/hit/triple/{tag}") (mkDictCaseStack (.cell valueC) 1 (.cell dictSigned8Three) 8) -- [B4][B5]
    else if shape = 6 then
      mkCase (s!"fuzz/hit/trimmed-stack/{tag}")
        (#[.int (.num 777), .cell valueB, intV 5, .cell dictSigned8Double, intV 8]) -- [B4][B5]
    else if shape = 7 then
      mkCase (s!"fuzz/err/n-neg/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) (-1)) -- [B3]
    else if shape = 8 then
      mkCase (s!"fuzz/err/n-too-large/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 1024) -- [B3]
    else if shape = 9 then
      mkCase (s!"fuzz/err/n-nan/{tag}") (#[.cell valueA, intV 5, .cell dictSigned8Single, .int .nan]) -- [B3]
    else if shape = 10 then
      mkCase (s!"fuzz/err/key-range-high/{tag}") (mkDictCaseStack (.cell valueA) 16 (.cell dictSigned8Single) 4) -- [B3]
    else if shape = 11 then
      mkCase (s!"fuzz/err/key-range-low/{tag}") (mkDictCaseStack (.cell valueA) (-9) (.cell dictSigned8Single) 4) -- [B3]
    else if shape = 12 then
      mkCase (s!"fuzz/err/key-range-n0/{tag}") (mkDictCaseStack (.cell valueA) 1 (.cell dictSigned0) 0) -- [B3]
    else if shape = 13 then
      mkCase (s!"fuzz/err/type-dict/{tag}") (mkDictCaseStack (.cell valueA) 5 (.tuple #[]) 8) -- [B2]
    else if shape = 14 then
      mkCodeCase (s!"fuzz/raw/f42d/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8) rawF42d -- [B7]
    else if shape = 15 then
      mkCase (s!"fuzz/err/type-key/{tag}") (#[.cell valueA, .slice malformedValueBits, .cell dictSigned8Single, intV 8]) -- [B2]
    else if shape = 16 then
      mkCase (s!"fuzz/err/type-value/{tag}") (#[.int (.num 7), intV 5, .cell dictSigned8Single, intV 8]) -- [B2]
    else if shape = 17 then
      mkCase (s!"fuzz/err/malformed-value/{tag}") (mkDictCaseStack (.cell valueB) 10 (.cell dictSigned8MalformedRef) 8) -- [B5]
    else if shape = 18 then
      mkCase (s!"fuzz/err/malformed-value-ref/{tag}") (mkDictCaseStack (.cell valueB) 11 (.cell dictSigned8MalformedRefWithRef) 8) -- [B5]
    else if shape = 19 then
      mkCase (s!"fuzz/err/malformed-root/{tag}") (mkDictCaseStack (.cell valueA) 5 (.cell malformedDictRoot) 8) -- [B6]
    else if shape = 20 then
      mkCase (s!"fuzz/gas/base/{tag}") (mkDictCaseStack (.cell valueA) 7 .null 8)
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact baseGas) -- [B9]
    else if shape = 21 then
      mkCase (s!"fuzz/gas/hit-single/{tag}") (mkDictCaseStack (.cell valueB) 5 (.cell dictSigned8Single) 8)
        (#[.pushInt (.num hitGasSingle), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitGasSingle) -- [B9]
    else if shape = 22 then
      mkCodeCase (s!"fuzz/err/decode-below/{tag}") (mkDictCaseStack (.cell valueA) 5 .null 8) rawInvalidBelow -- [B7]
    else
      mkCodeCase (s!"fuzz/err/decode-above/{tag}") (mkDictCaseStack (.cell valueA) 5 .null 8) rawInvalidAbove -- [B7]
  ({ case0 with name := case0.name }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDICTIREPLACEGETREFDispatchFallback (#[intV 1, intV 2, intV 3, .cell dictSigned8Single]) with
        | .ok st =>
            if st == #[intV 1, intV 2, intV 3, .cell dictSigned8Single, intV 909] then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback failed: expected {reprStr #[intV 1, intV 2, intV 3, .cell dictSigned8Single, intV 909]}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback failed with {e}") },
    { name := "unit/decode/f42a" -- [B7]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42A 16)
        let _ ← expectDecodeStep "decode/f42a" s (.dictExt (.mutGet false false false .replace)) 16 },
    { name := "unit/decode/f42b" -- [B7]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42B 16)
        let _ ← expectDecodeStep "decode/f42b" s (.dictExt (.mutGet false false true .replace)) 16 },
    { name := "unit/decode/f42d" -- [B7]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42D 16)
        let _ ← expectDecodeStep "decode/f42d" s instr 16 },
    { name := "unit/decode/f42f" -- [B7]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42F 16)
        let _ ← expectDecodeStep "decode/f42f" s (.dictExt (.mutGet true true true .replace)) 16 },
    { name := "unit/decode/chain/replacegetref-family" -- [B7]
      run := do
        let s0 := Slice.ofCell (Cell.mkOrdinary (rawF42a.bits ++ rawF42b.bits ++ rawF42c.bits ++ rawF42d.bits ++ rawF42e.bits ++ rawF42f.bits) #[])
        let s1 ← expectDecodeStep "decode/chain/f42a" s0 (.dictExt (.mutGet false false false .replace)) 16
        let s2 ← expectDecodeStep "decode/chain/f42b" s1 (.dictExt (.mutGet false false true .replace)) 16
        let s3 ← expectDecodeStep "decode/chain/f42c" s2 (.dictExt (.mutGet true false false .replace)) 16
        let s4 ← expectDecodeStep "decode/chain/f42d" s3 instr 16
        let s5 ← expectDecodeStep "decode/chain/f42e" s4 (.dictExt (.mutGet true true false .replace)) 16
        let _ ← expectDecodeStep "decode/chain/f42f" s5 (.dictExt (.mutGet true true true .replace)) 16
        pure () },
    { name := "unit/decode/invalid-low" -- [B7]
      run := do
        expectDecodeInvOpcode "decode/f429" rawInvalidBelow },
    { name := "unit/decode/invalid-high" -- [B7]
      run := do
        expectDecodeInvOpcode "decode/f430" rawInvalidAbove },
    { name := "unit/decode/truncated" -- [B7]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated unexpectedly succeeded") },
    { name := "unit/asm/encodes" -- [B8]
      run := do
        expectAssembleOk16 "asm/encode" instr }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/err/underflow-empty" #[],
    -- [B2]
    mkCase "oracle/err/underflow-one" (#[.cell valueA]),
    -- [B2]
    mkCase "oracle/err/underflow-two" (#[.cell valueA, intV 5, .cell dictSigned8Single, intV 8]),
    -- [B2]
    mkCase "oracle/err/underflow-three" (#[.cell valueA, intV 5, .cell dictSigned8Single]),
    -- [B3]
    mkCase "oracle/err/n-negative" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) (-1)),
    -- [B3]
    mkCase "oracle/err/n-too-large" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 1024),
    -- [B3]
    mkCase "oracle/err/n-nan" (#[.cell valueA, intV 5, .cell dictSigned8Single, .int .nan]),
    -- [B3]
    mkCase "oracle/err/key-range-positive" (mkDictCaseStack (.cell valueA) 16 (.cell dictSigned8Single) 4),
    -- [B3]
    mkCase "oracle/err/key-range-negative" (mkDictCaseStack (.cell valueA) (-9) (.cell dictSigned8Single) 4),
    -- [B3]
    mkCase "oracle/err/key-range-nonzero-n0" (mkDictCaseStack (.cell valueA) 1 (.cell dictSigned0) 0),
    -- [B2][B2]
    mkCase "oracle/err/type-dict" (mkDictCaseStack (.cell valueA) 5 (.tuple #[]) 8),
    -- [B2]
    mkCase "oracle/err/type-key" (#[.cell valueA, .slice malformedValueBits, .cell dictSigned8Single, intV 8]),
    -- [B2]
    mkCase "oracle/err/type-value" (#[.int (.num 7), intV 5, .cell dictSigned8Single, intV 8]),

    -- [B4]
    mkCase "oracle/ok/miss/null" (mkDictCaseStack (.cell valueA) 5 .null 8),
    -- [B4]
    mkCase "oracle/ok/miss/null-wide" (mkDictCaseStack (.cell valueA) 5 .null 257),
    -- [B4]
    mkCase "oracle/ok/miss/zwidth" (mkDictCaseStack (.cell valueA) 1 .null 0),
    -- [B4]
    mkCase "oracle/ok/hit/single" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8),
    -- [B4]
    mkCase "oracle/ok/hit/double" (mkDictCaseStack (.cell valueB) (-1) (.cell dictSigned8Double) 8),
    -- [B4]
    mkCase "oracle/ok/hit/triple" (mkDictCaseStack (.cell valueC) 1 (.cell dictSigned8Triple) 8),
    -- [B4]
    mkCase "oracle/ok/hit/zero-width" (mkDictCaseStack (.cell valueA) 0 (.cell dictSigned0) 0),
    -- [B4]
    mkCase "oracle/ok/hit/program-trimmed-stack"
      (#[.int (.num 777), .cell valueB, intV 5, .cell dictSigned8Double, intV 8]),

    -- [B5]
    mkCase "oracle/err/value-not-ref" (mkDictCaseStack (.cell valueA) 10 (.cell dictSigned8MalformedRef) 8),
    -- [B5]
    mkCase "oracle/err/value-not-ref-with-bits" (mkDictCaseStack (.cell valueA) 11 (.cell dictSigned8MalformedRefWithRef) 8),

    -- [B6]
    mkCase "oracle/err/malformed-root" (mkDictCaseStack (.cell valueA) 5 (.cell malformedDictRoot) 8),

    -- [B7]
    mkCodeCase "oracle/raw/f42a" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8) rawF42a,
    -- [B7]
    mkCodeCase "oracle/raw/f42b" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8) rawF42b,
    -- [B7]
    mkCodeCase "oracle/raw/f42c" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8) rawF42c,
    -- [B7]
    mkCodeCase "oracle/raw/f42d" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8) rawF42d,
    -- [B7]
    mkCodeCase "oracle/raw/f42e" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8) rawF42e,
    -- [B7]
    mkCodeCase "oracle/raw/f42f" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Single) 8) rawF42f,
    -- [B7]
    mkCodeCase "oracle/raw/truncated8" (#[] : Array Value) rawTruncated8,
    -- [B7]
    mkCodeCase "oracle/raw/invalid-low" (#[] : Array Value) rawInvalidBelow,
    -- [B7]
    mkCodeCase "oracle/raw/invalid-high" (#[] : Array Value) rawInvalidAbove,

    -- [B9]
    mkCase "oracle/gas/base-exact" (mkDictCaseStack (.cell valueA) 7 .null 8)
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas),
    -- [B9]
    mkCase "oracle/gas/base-exact-minus-one" (mkDictCaseStack (.cell valueA) 7 .null 8)
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGas),
    -- [B9]
    mkCase "oracle/gas/hit-single-exact" (mkDictCaseStack (.cell valueB) 5 (.cell dictSigned8Single) 8)
      (#[.pushInt (.num hitGasSingle), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGasSingle),
    -- [B9]
    mkCase "oracle/gas/hit-single-exact-minus-one" (mkDictCaseStack (.cell valueB) 5 (.cell dictSigned8Single) 8)
      (#[.pushInt (.num hitGasSingleMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitGasSingle),
    -- [B9]
    mkCase "oracle/gas/hit-double-exact" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Double) 8)
      (#[.pushInt (.num hitGasDouble), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGasDouble),
    -- [B9]
    mkCase "oracle/gas/hit-double-exact-minus-one" (mkDictCaseStack (.cell valueA) 5 (.cell dictSigned8Double) 8)
      (#[.pushInt (.num hitGasDoubleMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitGasDouble)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTIREPLACEGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACEGETREF
