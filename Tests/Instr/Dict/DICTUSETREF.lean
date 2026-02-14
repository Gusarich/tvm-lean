import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUSETREF

/-!
INSTRUCTION: DICTUSETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictDictSet` handles only `.dictSet` constructors.
   - Non-`dictSet` instructions must execute `next` with stack unchanged.

2. [B2] Runtime arity and stack-order checks.
   - `checkUnderflow 4` is required before any pops.
   - Operand order is `newValue`, `key`, `root`, `n` from stack top.
   - Wrong arity with 0..3 items produces `.stkUnd`.

3. [B3] Width (`n`) parsing and boundary checks.
   - `popNatUpTo 1023` accepts values `0..1023`.
   - Negative, NaN and `>1023` values produce `.rangeChk`.

4. [B4] Unsigned integer key conversion.
   - `dictKeyBits?` is invoked with `unsigned = true`.
   - `n = 0` accepts only `key = 0`.
   - Any key outside `[0, 2^n-1]` raises `.rangeChk`.

5. [B5] Value and root argument type checks.
   - Root is checked by `popMaybeCell` (`.null` or `.cell` only).
   - Value is required to be a `.cell` in `byRef` form.
   - Wrong key type (`.slice`) raises `.typeChk` in `popInt`.

6. [B6] Runtime insert (miss) semantics.
   - On absent key, dictionary is created/extended and returned as `.cell`.
   - Example: `null` root with any valid key inserts into empty dictionary.

7. [B7] Runtime replace (hit) semantics.
   - Existing key value is replaced and new root is pushed.
   - Example: same key on non-empty dictionary updates the existing entry.

8. [B8] Structural/malformed dictionary behavior.
   - Malformed dictionary payload can throw `.dictErr` from dictionary helpers.
   - Error path is exercised through `.setRef` helper failure.

9. [B9] Boundary width behavior.
   - `n = 0` is supported.
   - High-width dictionaries (e.g. `n = 1023`) are supported for valid key `0`.

10. [B10] Assembler constraints.
   - `.dictSet true true true .set` is valid and encodes as `0xF417`.
   - `.dictSet false true true .set` is invalid and must encode as `.invOpcode`.

11. [B11] Decoder behavior and opcode boundaries.
   - `0xF412..0xF417` is the DICT*SET family.
   - `0xF417` decodes to `.dictSet true true true .set`.
   - `0xF418` and `0xF411` must decode as `.invOpcode`.
   - Truncated opcodes such as `0xF4` (8 bits) must decode as `.invOpcode`.

12. [B12] Gas accounting.
   - Base gas is `computeExactGasBudget instr`.
   - Execution adds `created * cellCreateGasPrice`.
   - Exact-gas and exact-gas-minus-one cases are validated for hit and miss paths.

TOTAL BRANCHES: 12

Every oracle test is tagged with one or more `[Bn]` references above.
-/

private def suiteId : InstrId :=
  { name := "DICTUSETREF" }

private def instr : Instr :=
  .dictSet true true true .set

private def dispatchSentinel : Int :=
  13_021

private def raw16 (v : Nat) : Cell :=
  Cell.mkOrdinary (natToBits v 16) #[]

private def rawF412 : Cell := raw16 0xF412
private def rawF413 : Cell := raw16 0xF413
private def rawF414 : Cell := raw16 0xF414
private def rawF415 : Cell := raw16 0xF415
private def rawF416 : Cell := raw16 0xF416
private def rawF417 : Cell := raw16 0xF417
private def rawF411 : Cell := raw16 0xF411
private def rawF418 : Cell := raw16 0xF418
private def rawF4 : Cell := raw16 0xF4

private def rawSetFamily : Cell :=
  Cell.mkOrdinary
    (rawF412.bits ++ rawF413.bits ++ rawF414.bits ++ rawF415.bits ++ rawF416.bits ++ rawF417.bits)
    #[]

private def valueCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xA1 8) #[]

private def valueCellB : Cell :=
  Cell.mkOrdinary (natToBits 0xB2 8) #[]

private def valueCellC : Cell :=
  Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def valueCellD : Cell :=
  Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def valueCellE : Cell :=
  Cell.mkOrdinary (natToBits 0xE5 8) #[]

private def valueSliceA : Slice :=
  mkSliceFromBits (natToBits 0x12 8)

private def valueBitsOnly : Slice :=
  mkSliceFromBits (natToBits 0x42 8)

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 0b111 3) #[]

private def keyBitsFor (idx : Int) (n : Nat) : BitString :=
  match dictKeyBits? idx n true with
  | some b => b
  | none => panic! s!"DICTUSETREF: invalid unsigned key (key={idx}, n={n})"

private def mkDictSetRefUIntRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetRefWithCells root (keyBitsFor k n) v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected none root"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictUInt8Single : Cell :=
  mkDictSetRefUIntRoot! "dictUInt8Single" 8 #[(5, valueCellA)]

private def dictUInt8SingleRepl : Cell :=
  mkDictSetRefUIntRoot! "dictUInt8SingleRepl" 8 #[(5, valueCellB)]

private def dictUInt8Double : Cell :=
  mkDictSetRefUIntRoot! "dictUInt8Double" 8 #[(5, valueCellA), (200, valueCellC)]

private def dictUInt8DoubleRepl : Cell :=
  mkDictSetRefUIntRoot! "dictUInt8DoubleRepl" 8 #[(5, valueCellA), (200, valueCellD)]

private def dictUInt8Triple : Cell :=
  mkDictSetRefUIntRoot! "dictUInt8Triple" 8 #[(5, valueCellA), (6, valueCellB), (255, valueCellC)]

private def dictUInt8TripleRepl : Cell :=
  mkDictSetRefUIntRoot! "dictUInt8TripleRepl" 8 #[(5, valueCellD), (6, valueCellE), (255, valueCellB)]

private def dictUInt8SingleInsert7 : Cell :=
  mkDictSetRefUIntRoot! "dictUInt8SingleInsert7" 8 #[(5, valueCellA), (7, valueCellD)]

private def dictUInt0Single : Cell :=
  mkDictSetRefUIntRoot! "dictUInt0Single" 0 #[(0, valueCellA)]

private def dictUInt0SingleRepl : Cell :=
  mkDictSetRefUIntRoot! "dictUInt0SingleRepl" 0 #[(0, valueCellB)]

private def dictUInt1Single : Cell :=
  mkDictSetRefUIntRoot! "dictUInt1Single" 1 #[(0, valueCellA)]

private def dictUInt1SingleRepl : Cell :=
  mkDictSetRefUIntRoot! "dictUInt1SingleRepl" 1 #[(0, valueCellB)]

private def dictUInt1023Single : Cell :=
  mkDictSetRefUIntRoot! "dictUInt1023Single" 1023 #[(0, valueCellC)]

private def createdFor (dictCell? : Option Cell) (n : Nat) (key : Int) (newValue : Cell) : Nat :=
  match dictSetRefWithCells dictCell? (keyBitsFor key n) newValue .set with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error e => panic! s!"DICTUSETREF: dictSetRefWithCells failed ({reprStr e})"

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  if baseGas > 0 then baseGas - 1 else 0

private def hitSingleCreated : Nat :=
  createdFor (some dictUInt8Single) 8 5 valueCellB

private def hitDoubleCreated : Nat :=
  createdFor (some dictUInt8Double) 8 200 valueCellD

private def hitTripleCreated : Nat :=
  createdFor (some dictUInt8Triple) 8 255 valueCellE

private def hitZeroCreated : Nat :=
  createdFor (some dictUInt0Single) 0 0 valueCellB

private def hitOneCreated : Nat :=
  createdFor (some dictUInt1Single) 1 0 valueCellC

private def missNullCreated : Nat :=
  createdFor none 8 5 valueCellA

private def missNonEmptyCreated : Nat :=
  createdFor (some dictUInt8Single) 8 7 valueCellB

private def hitSingleGas : Int :=
  baseGas + (Int.ofNat hitSingleCreated * cellCreateGasPrice)

private def hitDoubleGas : Int :=
  baseGas + (Int.ofNat hitDoubleCreated * cellCreateGasPrice)

private def hitTripleGas : Int :=
  baseGas + (Int.ofNat hitTripleCreated * cellCreateGasPrice)

private def hitZeroGas : Int :=
  baseGas + (Int.ofNat hitZeroCreated * cellCreateGasPrice)

private def hitOneGas : Int :=
  baseGas + (Int.ofNat hitOneCreated * cellCreateGasPrice)

private def missNullGas : Int :=
  baseGas + (Int.ofNat missNullCreated * cellCreateGasPrice)

private def missNonEmptyGas : Int :=
  baseGas + (Int.ofNat missNonEmptyCreated * cellCreateGasPrice)

private def hitSingleGasMinusOne : Int :=
  if hitSingleGas > 0 then hitSingleGas - 1 else 0

private def hitZeroGasMinusOne : Int :=
  if hitZeroGas > 0 then hitZeroGas - 1 else 0

private def missNullGasMinusOne : Int :=
  if missNullGas > 0 then missNullGas - 1 else 0

private def missNonEmptyGasMinusOne : Int :=
  if missNonEmptyGas > 0 then missNonEmptyGas - 1 else 0

private def mkCaseStack (newValue : Cell) (key : Int) (dict : Value) (n : Int := 8) : Array Value :=
  #[.cell newValue, intV key, dict, intV n]

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

private def expectDecodeStep (label : String) (code : Slice) (expected : Instr) : IO Slice := do
  match decodeCp0WithBits code with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {instr}")
      if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected code fully consumed")
      pure rest

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {instr} ({bits})")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok c =>
      throw (IO.userError s!"{label}: expected .invOpcode, got bits {c.bits}")

private def runDICTUSETREFDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def runDICTUSETREFDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def genDICTUSETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 38
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/underflow/one" #[.cell valueCellA], rng1)
    else if shape = 2 then
      (mkCase "fuzz/underflow/two" #[.cell valueCellA, .int (.num 5)], rng1)
    else if shape = 3 then
      (mkCase "fuzz/underflow/three" #[.cell valueCellA, .int (.num 5), .cell dictUInt8Single], rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/n-negative" (mkCaseStack valueCellA 5 (.cell dictUInt8Single) (-1)), rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/n-too-large" (mkCaseStack valueCellA 5 (.cell dictUInt8Single) 1024), rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/n-nan" #[.cell valueCellA, .int (.num 5), .cell dictUInt8Single, .int .nan], rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/key-range-high" (mkCaseStack valueCellA 256 (.cell dictUInt8Single) 8), rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/key-range-neg" (mkCaseStack valueCellA (-1) (.cell dictUInt8Single) 8), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/key-nonzero-n0" (mkCaseStack valueCellA 1 (.cell dictUInt0Single) 0), rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/type-root" (mkCaseStack valueCellA 5 (.tuple #[]) 8), rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/type-key" (#[.cell valueCellA, .slice valueSliceA, .cell dictUInt8Single, intV 8]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-value" (#[.slice valueBitsOnly, .int (.num 5), .cell dictUInt8Single, intV 8]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/hit-single" (mkCaseStack valueCellB 5 (.cell dictUInt8Single) 8), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/hit-double" (mkCaseStack valueCellD 200 (.cell dictUInt8Double) 8), rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/hit-triple" (mkCaseStack valueCellA 255 (.cell dictUInt8Triple) 8), rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/hit-zero" (mkCaseStack valueCellC 0 (.cell dictUInt0Single) 0), rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/hit-one" (mkCaseStack valueCellE 0 (.cell dictUInt1Single) 1), rng1)
    else if shape = 18 then
      (mkCase "fuzz/ok/miss-null" (mkCaseStack valueCellA 5 .null 8), rng1)
    else if shape = 19 then
      (mkCase "fuzz/ok/miss-non-empty" (mkCaseStack valueCellC 7 (.cell dictUInt8Single) 8), rng1)
    else if shape = 20 then
      (mkCase "fuzz/ok/miss-wide" (mkCaseStack valueCellB 0 (.cell dictUInt1023Single) 1023), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/malformed-root" (mkCaseStack valueCellA 5 (.cell malformedDictRoot) 8), rng1)
    else if shape = 22 then
      (mkCodeCase "fuzz/raw/f412" #[.slice valueBitsOnly, .slice valueBitsOnly, .null, intV 8] rawF412, rng1)
    else if shape = 23 then
      (mkCodeCase "fuzz/raw/f413" #[.cell valueCellA, .slice valueBitsOnly, .null, intV 8] rawF413, rng1)
    else if shape = 24 then
      (mkCodeCase "fuzz/raw/f414" (mkCaseStack valueCellA 5 (.null) 8) rawF414, rng1)
    else if shape = 25 then
      (mkCodeCase "fuzz/raw/f415" (mkCaseStack valueCellB 5 (.null) 8) rawF415, rng1)
    else if shape = 26 then
      (mkCodeCase "fuzz/raw/f416" #[.slice valueBitsOnly, .int (.num 5), .null, intV 8] rawF416, rng1)
    else if shape = 27 then
      (mkCodeCase "fuzz/raw/f417" (mkCaseStack valueCellC 5 (.null) 8) rawF417, rng1)
    else if shape = 28 then
      (mkCodeCase "fuzz/raw/f411" #[] rawF411, rng1)
    else if shape = 29 then
      (mkCodeCase "fuzz/raw/f418" #[] rawF418, rng1)
    else if shape = 30 then
      (mkCodeCase "fuzz/raw/truncated" #[] rawF4, rng1)
    else if shape = 31 then
      (mkCase
        "fuzz/gas/hit-exact"
        (mkCaseStack valueCellD 5 (.cell dictUInt8Single) 8)
        (#[.pushInt (.num hitSingleGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact hitSingleGas),
       rng1)
    else if shape = 32 then
      (mkCase
        "fuzz/gas/hit-minus-one"
        (mkCaseStack valueCellD 5 (.cell dictUInt8Single) 8)
        (#[.pushInt (.num hitSingleGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne hitSingleGasMinusOne),
       rng1)
    else if shape = 33 then
      (mkCase
        "fuzz/gas/miss-exact"
        (mkCaseStack valueCellB 5 .null 8)
        (#[.pushInt (.num missNullGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact missNullGas),
       rng1)
    else if shape = 34 then
      (mkCase
        "fuzz/gas/miss-minus-one"
        (mkCaseStack valueCellB 5 .null 8)
        (#[.pushInt (.num missNullGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne missNullGasMinusOne),
       rng1)
    else if shape = 35 then
      (mkCase
        "fuzz/gas/miss-non-empty-exact"
        (mkCaseStack valueCellA 7 (.cell dictUInt8Single) 8)
        (#[.pushInt (.num missNonEmptyGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact missNonEmptyGas),
       rng1)
    else
      (mkCase
        "fuzz/gas/miss-non-empty-minus-one"
        (mkCaseStack valueCellA 7 (.cell dictUInt8Single) 8)
        (#[.pushInt (.num missNonEmptyGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne missNonEmptyGasMinusOne),
       rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  let case1 : OracleCase := { case0 with name := s!"{case0.name}/{tag}" }
  (case1, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDICTUSETREFDispatchFallback (mkCaseStack valueCellA 5 (.cell dictUInt8Single) 8) with
        | .ok st =>
            if st == #[.cell valueCellA, intV 5, .cell dictUInt8Single, intV 8, intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback: expected original stack + sentinel, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback: unexpected {e}") },
    { name := "unit/encoding/target" -- [B10]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != rawF417.bits then
              throw (IO.userError "encoding expected 0xF417")
        | .error e =>
            throw (IO.userError s!"encoding failed: {e}")
        expectAssembleInvOpcode "encoding/invalid-unsigned-nonint" (.dictSet false true true .set) },
    { name := "unit/decoder/family-boundaries" -- [B11]
      run := do
        let s0 : Slice := Slice.ofCell rawSetFamily
        let s1 ← expectDecodeStep "decode/f412" s0 (.dictSet false false false .set)
        let s2 ← expectDecodeStep "decode/f413" s1 (.dictSet false false true .set)
        let s3 ← expectDecodeStep "decode/f414" s2 (.dictSet true false false .set)
        let s4 ← expectDecodeStep "decode/f415" s3 (.dictSet true false true .set)
        let s5 ← expectDecodeStep "decode/f416" s4 (.dictSet true true false .set)
        let _ ← expectDecodeStep "decode/f417" s5 (.dictSet true true true .set)
        expectDecodeInvOpcode "decode/f411" rawF411
        expectDecodeInvOpcode "decode/f418" rawF418
        expectDecodeInvOpcode "decode/truncated" rawF4 },
    { name := "unit/runtime/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDICTUSETREFDirect #[]) .stkUnd
        expectErr "underflow-one" (runDICTUSETREFDirect #[.cell valueCellA]) .stkUnd
        expectErr "underflow-two" (runDICTUSETREFDirect #[.cell valueCellA, .int (.num 5)]) .stkUnd
        expectErr "underflow-three" (runDICTUSETREFDirect #[.cell valueCellA, .int (.num 5), .cell dictUInt8Single]) .stkUnd },
    { name := "unit/runtime/n-and-type" -- [B3][B5]
      run := do
        expectErr "n-negative" (runDICTUSETREFDirect (mkCaseStack valueCellA 5 (.cell dictUInt8Single) (-1))) .rangeChk
        expectErr "n-too-large" (runDICTUSETREFDirect (mkCaseStack valueCellA 5 (.cell dictUInt8Single) 1024)) .rangeChk
        expectErr "n-nan" (runDICTUSETREFDirect #[.cell valueCellA, .int (.num 5), .cell dictUInt8Single, .int .nan]) .rangeChk
        expectErr "type-root" (runDICTUSETREFDirect (mkCaseStack valueCellA 5 (.tuple #[]) 8)) .typeChk
        expectErr "type-key" (runDICTUSETREFDirect #[.cell valueCellA, .slice valueBitsOnly, .cell dictUInt8Single, intV 8]) .typeChk
        expectErr "type-value" (runDICTUSETREFDirect (#[.slice valueBitsOnly, .int (.num 5), .cell dictUInt8Single, intV 8])) .typeChk },
    { name := "unit/runtime/key-boundary" -- [B4][B9]
      run := do
        expectErr "key-nonzero-at-n0" (runDICTUSETREFDirect (mkCaseStack valueCellA 1 (.cell dictUInt0Single) 0)) .rangeChk
        expectErr "key-range-high" (runDICTUSETREFDirect (mkCaseStack valueCellA 256 (.cell dictUInt8Single) 8)) .rangeChk
        expectErr "key-range-negative" (runDICTUSETREFDirect (mkCaseStack valueCellA (-1) (.cell dictUInt8Single) 8)) .rangeChk
        expectOkStack "ok-zero-width-hit"
          (runDICTUSETREFDirect (mkCaseStack valueCellB 0 (.cell dictUInt0Single) 0))
          #[.cell dictUInt0SingleRepl]
        expectOkStack "ok-wide-width-hit"
          (runDICTUSETREFDirect (mkCaseStack valueCellD 0 (.cell dictUInt1023Single) 1023))
          #[.cell dictUInt1023Single] },
    { name := "unit/runtime/semantics-ok" -- [B6][B7]
      run := do
        expectOkStack "ok-miss-null"
          (runDICTUSETREFDirect (mkCaseStack valueCellA 5 .null 8))
          #[.cell dictUInt8Single]
        expectOkStack "ok-hit-single"
          (runDICTUSETREFDirect (mkCaseStack valueCellB 5 (.cell dictUInt8Single) 8))
          #[.cell dictUInt8SingleRepl]
        expectOkStack "ok-hit-double"
          (runDICTUSETREFDirect (mkCaseStack valueCellD 200 (.cell dictUInt8Double) 8))
          #[.cell dictUInt8DoubleRepl]
        expectOkStack "ok-hit-triple"
          (runDICTUSETREFDirect (mkCaseStack valueCellA 6 (.cell dictUInt8Triple) 8))
          #[.cell dictUInt8TripleRepl]
        expectOkStack "ok-miss-non-empty"
          (runDICTUSETREFDirect (mkCaseStack valueCellC 7 (.cell dictUInt8Single) 8))
          #[.cell dictUInt8SingleInsert7] },
    { name := "unit/runtime/structural-error" -- [B8]
      run := do
        expectErr "malformed-root" (runDICTUSETREFDirect (mkCaseStack valueCellA 5 (.cell malformedDictRoot) 8)) .dictErr },
    { name := "unit/gas/hit-exact-minus-one" -- [B12]
      run := do
        expectErr
          "gas-minus-one-hit"
          (runDICTUSETREFDirect (mkCaseStack valueCellA 5 (.cell dictUInt8Single) 8))
          .outOfGas },
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow-empty" #[],
    mkCase "oracle/underflow-one" #[.cell valueCellA],
    mkCase "oracle/underflow-two" #[.cell valueCellA, .int (.num 7)],
    mkCase "oracle/underflow-three" #[.cell valueCellA, .int (.num 7), .cell dictUInt8Single],
    -- [B3]
    mkCase "oracle/err/n-negative" (mkCaseStack valueCellA 5 (.cell dictUInt8Single) (-1)),
    mkCase "oracle/err/n-too-large" (mkCaseStack valueCellA 5 (.cell dictUInt8Single) 1024),
    mkCase "oracle/err/n-nan" #[.cell valueCellA, .int (.num 5), .cell dictUInt8Single, .int .nan],
    -- [B4]
    mkCase "oracle/err/key-range-high" (mkCaseStack valueCellA 256 (.cell dictUInt8Single) 8),
    mkCase "oracle/err/key-range-negative" (mkCaseStack valueCellA (-1) (.cell dictUInt8Single) 8),
    mkCase "oracle/err/key-nonzero-n0" (mkCaseStack valueCellA 1 (.cell dictUInt0Single) 0),
    mkCase "oracle/ok/wide-key-zero" (mkCaseStack valueCellD 0 (.cell dictUInt1023Single) 1023),
    -- [B5]
    mkCase "oracle/err/type-root" (mkCaseStack valueCellA 5 (.tuple #[]) 8),
    mkCase "oracle/err/type-key" #[.cell valueCellA, .slice valueSliceA, .cell dictUInt8Single, intV 8],
    mkCase "oracle/err/type-value" #[.slice valueBitsOnly, .int (.num 5), .cell dictUInt8Single, intV 8],
    -- [B6] miss path
    mkCase "oracle/ok/miss-null" (mkCaseStack valueCellA 5 .null 8),
    mkCase "oracle/ok/miss-non-empty" (mkCaseStack valueCellC 7 (.cell dictUInt8Single) 8),
    mkCase "oracle/ok/miss-wide" (mkCaseStack valueCellB 0 .null 1023),
    -- [B7] hit path
    mkCase "oracle/ok/hit-single" (mkCaseStack valueCellB 5 (.cell dictUInt8Single) 8),
    mkCase "oracle/ok/hit-double" (mkCaseStack valueCellA 200 (.cell dictUInt8Double) 8),
    mkCase "oracle/ok/hit-triple" (mkCaseStack valueCellA 6 (.cell dictUInt8Triple) 8),
    mkCase "oracle/ok/hit-zero" (mkCaseStack valueCellC 0 (.cell dictUInt0Single) 0),
    mkCase "oracle/ok/hit-one" (mkCaseStack valueCellE 0 (.cell dictUInt1Single) 1),
    -- [B8]
    mkCase "oracle/err/malformed-root" (mkCaseStack valueCellA 5 (.cell malformedDictRoot) 8),
    -- [B9]
    mkCodeCase "oracle/raw/f412" #[.slice valueBitsOnly, .slice valueBitsOnly, .null, intV 8] rawF412,
    mkCodeCase "oracle/raw/f413" #[.cell valueCellA, .slice valueBitsOnly, .null, intV 8] rawF413,
    mkCodeCase "oracle/raw/f414" #[.slice valueBitsOnly, .int (.num 5), .null, intV 8] rawF414,
    mkCodeCase "oracle/raw/f415" (mkCaseStack valueCellC 5 (.null) 8) rawF415,
    mkCodeCase "oracle/raw/f416" #[.slice valueBitsOnly, .int (.num 5), .null, intV 8] rawF416,
    mkCodeCase "oracle/raw/f417" (mkCaseStack valueCellB 5 (.null) 8) rawF417,
    mkCodeCase "oracle/raw/f411" #[] rawF411,
    mkCodeCase "oracle/raw/f418" #[] rawF418,
    mkCodeCase "oracle/raw/truncated" #[] rawF4,
    -- [B10]
    mkCase "oracle/gas/hit-exact" (mkCaseStack valueCellB 5 (.cell dictUInt8Single) 8)
      (#[.pushInt (.num hitSingleGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitSingleGas),
    mkCase "oracle/gas/hit-minus-one" (mkCaseStack valueCellB 5 (.cell dictUInt8Single) 8)
      (#[.pushInt (.num hitSingleGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitSingleGasMinusOne),
    mkCase "oracle/gas/miss-null-exact" (mkCaseStack valueCellB 5 .null 8)
      (#[.pushInt (.num missNullGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact missNullGas),
    mkCase "oracle/gas/miss-null-minus-one" (mkCaseStack valueCellB 5 .null 8)
      (#[.pushInt (.num missNullGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne missNullGasMinusOne),
    mkCase "oracle/gas/miss-non-empty-exact" (mkCaseStack valueCellC 7 (.cell dictUInt8Single) 8)
      (#[.pushInt (.num missNonEmptyGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact missNonEmptyGas),
    mkCase "oracle/gas/miss-non-empty-minus-one" (mkCaseStack valueCellC 7 (.cell dictUInt8Single) 8)
      (#[.pushInt (.num missNonEmptyGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne missNonEmptyGasMinusOne),
    mkCase "oracle/gas/hit-double-exact" (mkCaseStack valueCellE 255 (.cell dictUInt8Double) 8)
      (#[.pushInt (.num hitDoubleGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitDoubleGas),
    mkCase "oracle/gas/hit-zero-exact" (mkCaseStack valueCellE 0 (.cell dictUInt0Single) 0)
      (#[.pushInt (.num hitZeroGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitZeroGas),
    mkCase "oracle/gas/hit-zero-minus-one" (mkCaseStack valueCellE 0 (.cell dictUInt0Single) 0)
      (#[.pushInt (.num hitZeroGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitZeroGasMinusOne),
    mkCase "oracle/gas/hit-one-exact" (mkCaseStack valueCellB 0 (.cell dictUInt1Single) 1)
      (#[.pushInt (.num hitOneGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitOneGas)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTUSETREFFuzzCase } ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSETREF
