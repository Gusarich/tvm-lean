import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREPLACEGETREF

/-!
INSTRUCTION: DICTREPLACEGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `.dictExt` instructions are handled by `execInstrDictExt`.
   - `.dictExt (.mutGet ... )` is the active branch for `DICTREPLACEGETREF`.
   - Non-matching instructions continue with `next`.

2. [B2] Stack arity and ordering.
   - `checkUnderflow 4` ensures `(newValueRef, key, dict, n)` are popped in this order.
   - Any missing argument at these positions yields `.stackUnderflow` before type checks.

3. [B3] Width parsing.
   - `popNatUpTo 1023` enforces `n` range and numeric sanity.
   - Negative, `NaN`, and values `> 1023` raise `.rangeChk`.

4. [B4] Slice-key extraction.
   - Slice key mode requires `n` bits from the key slice.
   - If the key has fewer than `n` bits, `.cellUnd` is thrown.

5. [B5] Operand-type checks.
   - `newValueRef` must be a cell.
   - `dict` can be `null` or a dictionary-like cell; wrong types are `.typeChk`.

6. [B6] Runtime semantics of replace/getref.
   - Missing key: dictionary is unchanged and `0` is pushed.
   - Hit: dictionary is updated and `(oldRef, -1)` is pushed.

7. [B7] Returned old-value payload validation for by-ref mode.
   - Returned old value must be exactly one reference and zero bits.
   - Payloads with extra bits and/or wrong ref shape raise `.dictErr`.

8. [B8] Dictionary traversal errors.
   - Malformed dictionary cells raise `.dictErr` after `registerLoaded` of traversed cells.

9. [B9] Decoder mapping.
   - `0xf42a..0xf42f` decode to `.dictExt (.mutGet intKey=<bit2> unsigned=<bit1> byRef=<bit0> .replace)`.
   - `0xf429` and `0xf430` are invalid.
   - Truncated 8-bit input is invalid.

10. [B10] Assembler behavior.
    - `.dictExt` instructions in this family are encodable by the CP0 assembler.

11. [B11] Gas accounting.
    - Base gas is `computeExactGasBudget instr`.
    - Hit paths may add `created * cellCreateGasPrice`.
    - Exact and exact-minus-one limits are required for miss and hit flows.

TOTAL BRANCHES: 11

Each oracle test below is tagged with the branch family it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTREPLACEGETREF" }

private def instr : Instr :=
  .dictExt (.mutGet false false true .replace)

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA0 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB0 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC0 8) #[]

private def malformedValueBits : Slice :=
  mkSliceFromBits (natToBits 0xF0 8)

private def malformedValueBitsAndRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[valueA])

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def key8 (k : Nat) : BitString :=
  natToBits k 8

private def key2560 (k : Nat) : BitString :=
  natToBits k 257

private def mkDictSetRefRoot!
    (label : String)
    (n : Nat)
    (entries : Array (Nat × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits := if n = 257 then key2560 k else natToBits k n
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
      let keyBits := if n = 257 then key2560 k else natToBits k n
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

private def dict8Single : Cell :=
  mkDictSetRefRoot! "DICTREPLACEGETREF::dict8Single" 8 #[(5, valueA)]

private def dict8Double : Cell :=
  mkDictSetRefRoot! "DICTREPLACEGETREF::dict8Double" 8 #[(5, valueA), (11, valueB)]

private def dict8Triple : Cell :=
  mkDictSetRefRoot! "DICTREPLACEGETREF::dict8Triple" 8 #[(5, valueA), (11, valueB), (3, valueC)]

private def dict8Zero : Cell :=
  mkDictSetRefRoot! "DICTREPLACEGETREF::dict8Zero" 8 #[(0, valueA)]

private def dict8Wide : Cell :=
  mkDictSetRefRoot! "DICTREPLACEGETREF::dict8Wide" 257 #[(0, valueA)]

private def dictMalformedRefValue : Cell :=
  mkDictSetSliceRoot! "DICTREPLACEGETREF::dictMalformedRefValue" 8 #[(10, malformedValueBits)]

private def dictMalformedRefValueWithBits : Cell :=
  mkDictSetSliceRoot! "DICTREPLACEGETREF::dictMalformedRefValueWithBits" 8 #[(11, malformedValueBitsAndRef)]

private def replaceCreated (dict : Cell) (n : Nat) (k : Nat) (newValue : Cell) : Nat :=
  match dictLookupSetRefWithCells (some dict) (if n = 257 then key2560 k else natToBits k n) newValue .replace with
  | .ok (_old, _newRoot, _ok, created, _loaded) => created
  | .error _ => 0

private def hitCreatedSingle : Nat :=
  replaceCreated dict8Single 8 5 valueB

private def hitCreatedDouble : Nat :=
  replaceCreated dict8Double 8 5 valueC

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

private def rawF42a : Cell :=
  Cell.mkOrdinary (natToBits (0xf42a) 16) #[]

private def rawF42b : Cell :=
  Cell.mkOrdinary (natToBits (0xf42b) 16) #[]

private def rawF42c : Cell :=
  Cell.mkOrdinary (natToBits (0xf42c) 16) #[]

private def rawF42d : Cell :=
  Cell.mkOrdinary (natToBits (0xf42d) 16) #[]

private def rawF42e : Cell :=
  Cell.mkOrdinary (natToBits (0xf42e) 16) #[]

private def rawF42f : Cell :=
  Cell.mkOrdinary (natToBits (0xf42f) 16) #[]

private def rawInvalidBelow : Cell :=
  Cell.mkOrdinary (natToBits 0xf429 16) #[]

private def rawInvalidAbove : Cell :=
  Cell.mkOrdinary (natToBits 0xf430 16) #[]

private def rawTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def mkDictCaseStack (newValue : Value) (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[newValue, .slice key, dict, intV n]

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

private def expectAssembleOk16 (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assembly success, got {e}")
  | .ok code =>
      match decodeCp0WithBits (Slice.ofCell code) with
      | .error e =>
          throw (IO.userError s!"{label}: expected decode success, got {e}")
      | .ok (decoded, bits, rest) =>
          if decoded != i then
            throw (IO.userError s!"{label}: expected {reprStr i}, got {reprStr decoded}")
          else if bits != 16 then
            throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
          else if rest.bitsRemaining + rest.refsRemaining != 0 then
            throw (IO.userError s!"{label}: expected end-of-stream decode")

private def runDICTREPLACEGETREFDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt (.dictGet false false false) (VM.push (.int (.num 909))) stack

private def genDICTREPLACEGETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 35
  let (tag, rng2) := randNat rng1 0 999_999
  let key5 : Slice := mkSliceFromBits (key8 5)
  let key7 : Slice := mkSliceFromBits (key8 7)
  let key3 : Slice := mkSliceFromBits (key8 3)
  let key11 : Slice := mkSliceFromBits (key8 11)
  let key10 : Slice := mkSliceFromBits (key8 10)
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase (s!"fuzz/underflow-empty/{tag}") #[] -- [B2]
    else if shape = 1 then
      mkCase (s!"fuzz/underflow-one/{tag}") #[(.cell valueA)] -- [B2]
    else if shape = 2 then
      mkCase (s!"fuzz/underflow-two/{tag}") (mkDictCaseStack (.cell valueA) key5 .null 8) -- [B2]
    else if shape = 3 then
      mkCase (s!"fuzz/underflow-three/{tag}") (mkDictCaseStack (.cell valueA) key5 (.cell dict8Single) 8) -- [B2]
    else if shape = 4 then
      mkCase (s!"fuzz/miss/null/{tag}") (mkDictCaseStack (.cell valueA) key7 .null 8) -- [B4][B6]
    else if shape = 5 then
      mkCase (s!"fuzz/miss/null-wide/{tag}") (mkDictCaseStack (.cell valueB) key7 (.cell dict8Wide) 257) -- [B4][B6]
    else if shape = 6 then
      mkCase (s!"fuzz/miss/zwidth/{tag}") (mkDictCaseStack (.cell valueA) (mkSliceFromBits #[]) (.cell dict8Zero) 0) -- [B3][B6]
    else if shape = 7 then
      mkCase (s!"fuzz/hit/single/{tag}") (mkDictCaseStack (.cell valueC) key5 (.cell dict8Single) 8) -- [B6][B7]
    else if shape = 8 then
      mkCase (s!"fuzz/hit/double/{tag}") (mkDictCaseStack (.cell valueA) key11 (.cell dict8Double) 8) -- [B6][B7]
    else if shape = 9 then
      mkCase (s!"fuzz/hit/triple/{tag}") (mkDictCaseStack (.cell valueC) key3 (.cell dict8Triple) 8) -- [B6][B7]
    else if shape = 10 then
      mkCase (s!"fuzz/hit/trimmed-stack/{tag}")
        (#[.int (.num 777), .cell valueA, .slice key11, .cell dict8Double, intV 8]) -- [B6][B7]
    else if shape = 11 then
      mkCase (s!"fuzz/err/key-short/{tag}") (mkDictCaseStack (.cell valueA) (mkSliceFromBits (natToBits 5 3)) (.cell dict8Single) 8) -- [B4]
    else if shape = 12 then
      mkCase (s!"fuzz/err/n-neg/{tag}") (mkDictCaseStack (.cell valueA) key5 (.cell dict8Single) (-1)) -- [B3]
    else if shape = 13 then
      mkCase (s!"fuzz/err/n-too-large/{tag}") (mkDictCaseStack (.cell valueA) key5 (.cell dict8Single) 1024) -- [B3]
    else if shape = 14 then
      mkCase (s!"fuzz/err/n-nan/{tag}") (#[.cell valueA, .slice key5, .cell dict8Single, .int .nan]) -- [B3]
    else if shape = 15 then
      mkCase (s!"fuzz/err/type-dict/{tag}") (mkDictCaseStack (.cell valueA) key5 (.tuple #[]) 8) -- [B5]
    else if shape = 16 then
      mkCase (s!"fuzz/err/type-key/{tag}") (#[.cell valueA, .int (.num 5), .cell dict8Single, intV 8]) -- [B5]
    else if shape = 17 then
      mkCase (s!"fuzz/err/type-value/{tag}") (#[.int (.num 7), .slice key5, .cell dict8Single, intV 8]) -- [B5]
    else if shape = 18 then
      mkCase (s!"fuzz/err/malformed-value/{tag}") (mkDictCaseStack (.cell valueA) key10 (.cell dictMalformedRefValue) 8) -- [B7]
    else if shape = 19 then
      mkCase (s!"fuzz/err/malformed-value-bits/{tag}") (mkDictCaseStack (.cell valueB) key11 (.cell dictMalformedRefValueWithBits) 8) -- [B7]
    else if shape = 20 then
      mkCase (s!"fuzz/err/malformed-root/{tag}") (mkDictCaseStack (.cell valueA) key5 (.cell malformedDictRoot) 8) -- [B8]
    else if shape = 21 then
      mkCodeCase (s!"fuzz/raw/f42a/{tag}") (#[] : Array Value) rawF42a -- [B9]
    else if shape = 22 then
      mkCodeCase (s!"fuzz/raw/f42b/{tag}") (#[] : Array Value) rawF42b -- [B9]
    else if shape = 23 then
      mkCodeCase (s!"fuzz/raw/f42c/{tag}") (#[] : Array Value) rawF42c -- [B9]
    else if shape = 24 then
      mkCodeCase (s!"fuzz/raw/f42d/{tag}") (#[] : Array Value) rawF42d -- [B9]
    else if shape = 25 then
      mkCodeCase (s!"fuzz/raw/f42e/{tag}") (#[] : Array Value) rawF42e -- [B9]
    else if shape = 26 then
      mkCodeCase (s!"fuzz/raw/f42f/{tag}") (#[] : Array Value) rawF42f -- [B9]
    else if shape = 27 then
      mkCodeCase (s!"fuzz/raw/invalid-low/{tag}") (#[] : Array Value) rawInvalidBelow -- [B9]
    else if shape = 28 then
      mkCodeCase (s!"fuzz/raw/invalid-high/{tag}") (#[] : Array Value) rawInvalidAbove -- [B9]
    else if shape = 29 then
      mkCodeCase (s!"fuzz/raw/truncated8/{tag}") (#[] : Array Value) rawTruncated8 -- [B9]
    else if shape = 30 then
      mkCase (s!"fuzz/gas/base/{tag}") (mkDictCaseStack (.cell valueA) key7 .null 8)
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact baseGas) -- [B11]
    else if shape = 31 then
      mkCase (s!"fuzz/gas/base-minus-one/{tag}") (mkDictCaseStack (.cell valueA) key7 .null 8)
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne baseGasMinusOne) -- [B11]
    else if shape = 32 then
      mkCase (s!"fuzz/gas/hit-single/{tag}") (mkDictCaseStack (.cell valueB) key5 (.cell dict8Single) 8)
        (#[.pushInt (.num hitGasSingle), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitGasSingle) -- [B11]
    else if shape = 33 then
      mkCase (s!"fuzz/gas/hit-single-minus-one/{tag}") (mkDictCaseStack (.cell valueB) key5 (.cell dict8Single) 8)
        (#[.pushInt (.num hitGasSingleMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitGasSingleMinusOne) -- [B11]
    else if shape = 34 then
      mkCase (s!"fuzz/gas/hit-double/{tag}") (mkDictCaseStack (.cell valueA) key11 (.cell dict8Double) 8)
        (#[.pushInt (.num hitGasDouble), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitGasDouble) -- [B11]
    else
      mkCase (s!"fuzz/gas/hit-double-minus-one/{tag}") (mkDictCaseStack (.cell valueA) key11 (.cell dict8Double) 8)
        (#[.pushInt (.num hitGasDoubleMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitGasDoubleMinusOne) -- [B11]
  ({ case0 with name := case0.name }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let expectedStack : Array Value :=
          #[.int (.num 1), .int (.num 2), .int (.num 3), .cell dict8Single, .int (.num 909)]
        match runDICTREPLACEGETREFDispatchFallback (#[.int (.num 1), .int (.num 2), .int (.num 3), .cell dict8Single]) with
        | .ok st =>
            if st == expectedStack then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback failed: expected {reprStr expectedStack}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback failed with {e}") },
    { name := "unit/decode/f42a" -- [B9]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42A 16)
        let _ ← expectDecodeStep "decode/f42a" s (.dictExt (.mutGet false false false .replace)) 16 },
    { name := "unit/decode/f42b" -- [B9]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42B 16)
        let _ ← expectDecodeStep "decode/f42b" s (.dictExt (.mutGet false false true .replace)) 16 },
    { name := "unit/decode/f42c" -- [B9]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42C 16)
        let _ ← expectDecodeStep "decode/f42c" s (.dictExt (.mutGet true false false .replace)) 16 },
    { name := "unit/decode/f42d" -- [B9]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42D 16)
        let _ ← expectDecodeStep "decode/f42d" s (.dictExt (.mutGet true false true .replace)) 16 },
    { name := "unit/decode/f42e" -- [B9]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42E 16)
        let _ ← expectDecodeStep "decode/f42e" s (.dictExt (.mutGet true true false .replace)) 16 },
    { name := "unit/decode/f42f" -- [B9]
      run := do
        let s := mkSliceFromBits (natToBits 0xF42F 16)
        let _ ← expectDecodeStep "decode/f42f" s (.dictExt (.mutGet true true true .replace)) 16 },
    { name := "unit/decode/replacegetref-family" -- [B9]
      run := do
        let s0 : Slice := Slice.ofCell (Cell.mkOrdinary (rawF42a.bits ++ rawF42b.bits ++ rawF42c.bits ++ rawF42d.bits ++ rawF42e.bits ++ rawF42f.bits) #[])
        let s1 ← expectDecodeStep "decode/chain/f42a" s0 (.dictExt (.mutGet false false false .replace)) 16
        let s2 ← expectDecodeStep "decode/chain/f42b" s1 (.dictExt (.mutGet false false true .replace)) 16
        let s3 ← expectDecodeStep "decode/chain/f42c" s2 (.dictExt (.mutGet true false false .replace)) 16
        let s4 ← expectDecodeStep "decode/chain/f42d" s3 (.dictExt (.mutGet true false true .replace)) 16
        let s5 ← expectDecodeStep "decode/chain/f42e" s4 (.dictExt (.mutGet true true false .replace)) 16
        let _ ← expectDecodeStep "decode/chain/f42f" s5 (.dictExt (.mutGet true true true .replace)) 16
        pure () },
    { name := "unit/decode/invalid-low" -- [B9]
      run := do
        expectDecodeInvOpcode "decode/f429" rawInvalidBelow },
    { name := "unit/decode/invalid-high" -- [B9]
      run := do
        expectDecodeInvOpcode "decode/f430" rawInvalidAbove },
    { name := "unit/decode/truncated" -- [B9]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated unexpectedly succeeded") },
    { name := "unit/asm/encodes" -- [B10]
      run := do
        expectAssembleOk16 "asm/encodes" instr }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/err/underflow-empty" #[],
    -- [B2]
    mkCase "oracle/err/underflow-one" #[.cell valueA],
    -- [B2]
    mkCase "oracle/err/underflow-two" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 5)) .null 8),
    -- [B2]
    mkCase "oracle/err/underflow-three" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 5)) (.cell dict8Single) 8),
    -- [B3]
    mkCase "oracle/err/n-negative" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 5)) (.cell dict8Single) (-1)),
    -- [B3]
    mkCase "oracle/err/n-too-large" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 5)) (.cell dict8Single) 1024),
    -- [B3]
    mkCase "oracle/err/n-nan" (#[.cell valueA, .slice (mkSliceFromBits (key8 5)), .cell dict8Single, .int .nan]),
    -- [B4]
    mkCase "oracle/err/key-short" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (natToBits 5 3)) (.cell dict8Single) 8),
    -- [B4][B6]
    mkCase "oracle/ok/miss/null" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 7)) .null 8),
    -- [B4][B6]
    mkCase "oracle/ok/miss/wide-null" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 7)) (.null) 257),
    -- [B4][B6]
    mkCase "oracle/ok/miss/zero-width" (mkDictCaseStack (.cell valueA) (mkSliceFromBits #[]) (.cell dict8Zero) 0),
    -- [B5]
    mkCase "oracle/err/type-dict" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 7)) (.tuple #[]) 8),
    -- [B5]
    mkCase "oracle/err/type-key" (#[.cell valueA, .int (.num 5), .cell dict8Single, intV 8]),
    -- [B5]
    mkCase "oracle/err/type-value" (#[.int (.num 7), .slice (mkSliceFromBits (key8 5)), .cell dict8Single, intV 8]),
    -- [B6]
    mkCase "oracle/ok/hit/single" (mkDictCaseStack (.cell valueB) (mkSliceFromBits (key8 5)) (.cell dict8Single) 8),
    -- [B6]
    mkCase "oracle/ok/hit/double" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 11)) (.cell dict8Double) 8),
    -- [B6]
    mkCase "oracle/ok/hit/triple" (mkDictCaseStack (.cell valueC) (mkSliceFromBits (key8 3)) (.cell dict8Triple) 8),
    -- [B6]
    mkCase "oracle/ok/trimmed-stack"
      (#[.int (.num 777), .cell valueA, .slice (mkSliceFromBits (key8 5)), .cell dict8Double, intV 8]),
    -- [B7]
    mkCase "oracle/err/value-not-ref" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 10)) (.cell dictMalformedRefValue) 8),
    -- [B7]
    mkCase "oracle/err/value-not-ref-with-bits" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 11)) (.cell dictMalformedRefValueWithBits) 8),
    -- [B8]
    mkCase "oracle/err/malformed-root" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 5)) (.cell malformedDictRoot) 8),
    -- [B9]
    mkCodeCase "oracle/raw/f42a" (#[] : Array Value) rawF42a,
    -- [B9]
    mkCodeCase "oracle/raw/f42b" (#[] : Array Value) rawF42b,
    -- [B9]
    mkCodeCase "oracle/raw/f42c" (#[] : Array Value) rawF42c,
    -- [B9]
    mkCodeCase "oracle/raw/f42d" (#[] : Array Value) rawF42d,
    -- [B9]
    mkCodeCase "oracle/raw/f42e" (#[] : Array Value) rawF42e,
    -- [B9]
    mkCodeCase "oracle/raw/f42f" (#[] : Array Value) rawF42f,
    -- [B9]
    mkCodeCase "oracle/raw/truncated8" (#[] : Array Value) rawTruncated8,
    -- [B9]
    mkCodeCase "oracle/raw/invalid-low" (#[] : Array Value) rawInvalidBelow,
    -- [B9]
    mkCodeCase "oracle/raw/invalid-high" (#[] : Array Value) rawInvalidAbove,
    -- [B11]
    mkCase "oracle/gas/base-exact" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 7)) .null 8)
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas),
    -- [B11]
    mkCase "oracle/gas/base-exact-minus-one" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 7)) .null 8)
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne),
    -- [B11]
    mkCase "oracle/gas/hit-single-exact" (mkDictCaseStack (.cell valueB) (mkSliceFromBits (key8 5)) (.cell dict8Single) 8)
      (#[.pushInt (.num hitGasSingle), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGasSingle),
    -- [B11]
    mkCase "oracle/gas/hit-single-exact-minus-one" (mkDictCaseStack (.cell valueB) (mkSliceFromBits (key8 5)) (.cell dict8Single) 8)
      (#[.pushInt (.num hitGasSingleMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitGasSingleMinusOne),
    -- [B11]
    mkCase "oracle/gas/hit-double-exact" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 11)) (.cell dict8Double) 8)
      (#[.pushInt (.num hitGasDouble), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGasDouble),
    -- [B11]
    mkCase "oracle/gas/hit-double-exact-minus-one" (mkDictCaseStack (.cell valueA) (mkSliceFromBits (key8 11)) (.cell dict8Double) 8)
      (#[.pushInt (.num hitGasDoubleMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitGasDoubleMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTREPLACEGETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREPLACEGETREF
