import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTISETREF

/-!
INSTRUCTION: DICTISETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictDictSet` handles only `.dictSet`; all other opcodes execute `next`.

2. [B2] Runtime preamble and stack/arity/type sequencing.
   - `checkUnderflow 4` runs first.
   - Operand pop order for execution: `n`, `dict`, `key`, `newValueRef`.
   - `newValueRef` is enforced as `.cell` by `popCell`.

3. [B3] `n` validation.
   - `popNatUpTo 1023` rejects `.nan`, negative values, and `n > 1023` with `.rangeChk`.

4. [B4] Signed integer key conversion.
   - Signed key conversion uses `dictKeyBits?` with `unsigned = false`.
   - `n = 0` accepts only key `0`.
   - Any other key outside signed range for the given width yields `.rangeChk`.

5. [B5] Dict-set core behavior.
   - `.set` mode replaces existing entries when key exists, inserts when absent.
   - No old payload is returned for `DICTISETREF`; result stack contains only updated root (or `.null`).
   - On `.set`, `!ok` raises `.fatal`.

6. [B6] Malformed roots and type errors.
   - Non-`cell`/non-`null` dictionary root => `.typeChk`.
   - Malformed dictionary structure may yield `.dictErr`.

7. [B7] Assembler/decoder behavior.
   - Signed-by-ref form encodes to `0xF415`.
   - `0xF412..0xF417` are the `DICT*SET` family in this range.
   - `.dictSet false true true .set` is invalid (`unsigned` only for int-key forms).
   - Decoder rejects `0xF411` and `0xF418`; truncated inputs must decode as `.invOpcode`.

8. [B8] Gas accounting.
   - Base gas is `computeExactGasBudget instr`.
   - Actual run gas adds `created * cellCreateGasPrice`.
   - Exact-gas and exact-minus-one branch checks apply to hit and miss paths.

9. [B9] Boundary width behavior.
   - `n = 0` is supported and has zero-bit key extraction.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn].
Any branch not covered by oracle tests is covered by fuzz.
-/

private def suiteId : InstrId :=
  { name := "DICTISETREF" }

private def instr : Instr :=
  .dictSet true false true .set

private def dispatchSentinel : Int :=
  13021

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
  Cell.mkOrdinary (natToBits 0xB1 8) #[]

private def valueCellC : Cell :=
  Cell.mkOrdinary (natToBits 0xC1 8) #[]

private def valueCellD : Cell :=
  Cell.mkOrdinary (natToBits 0xD1 8) #[]

private def valueSliceA : Slice :=
  mkSliceFromBits (natToBits 0x12 8)

private def valueBitsOnly : Slice :=
  mkSliceFromBits (natToBits 0x42 8)

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 0b111 3) #[]

private def keyBitsFor (idx : Int) (n : Nat) : BitString :=
  match dictKeyBits? idx n false with
  | some b => b
  | none => panic! s!"DICTISETREF: invalid signed key (key={idx}, n={n})"

private def mkDictSetRefIntRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
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

private def dictSigned8Single : Cell :=
  mkDictSetRefIntRoot! "dictSigned8Single" 8 #[(5, valueCellA)]

private def dictSigned8SingleRepl : Cell :=
  mkDictSetRefIntRoot! "dictSigned8SingleRepl" 8 #[(5, valueCellB)]

private def dictSigned8Double : Cell :=
  mkDictSetRefIntRoot! "dictSigned8Double" 8 #[(5, valueCellA), (-1, valueCellC)]

private def dictSigned8DoubleRepl : Cell :=
  mkDictSetRefIntRoot! "dictSigned8DoubleRepl" 8 #[(5, valueCellB), (-1, valueCellC)]

private def dictSigned8Triple : Cell :=
  mkDictSetRefIntRoot! "dictSigned8Triple" 8 #[(5, valueCellA), (-1, valueCellC), (1, valueCellD)]

private def dictSigned8TripleRepl : Cell :=
  mkDictSetRefIntRoot! "dictSigned8TripleRepl" 8 #[(5, valueCellA), (-1, valueCellB), (1, valueCellA)]

private def dictSigned8NullInsert : Cell :=
  mkDictSetRefIntRoot! "dictSigned8NullInsert" 8 #[(5, valueCellA)]

private def dictSigned8SingleInsert7 : Cell :=
  mkDictSetRefIntRoot! "dictSigned8SingleInsert7" 8 #[(5, valueCellA), (7, valueCellB)]

private def dictSigned0Single : Cell :=
  mkDictSetRefIntRoot! "dictSigned0Single" 0 #[(0, valueCellA)]

private def dictSigned0SingleRepl : Cell :=
  mkDictSetRefIntRoot! "dictSigned0SingleRepl" 0 #[(0, valueCellB)]

private def dictSigned1023Single : Cell :=
  mkDictSetRefIntRoot! "dictSigned1023Single" 1023 #[(0, valueCellC)]

private def createdFor (dictCell? : Option Cell) (n : Nat) (key : Int) (newValue : Cell) : Nat :=
  match dictSetRefWithCells dictCell? (keyBitsFor key n) newValue .set with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error e => panic! s!"DICTISETREF: dictSetRefWithCells failed ({reprStr e})"

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  if baseGas > 0 then baseGas - 1 else 0

private def hitSingleCreated : Nat :=
  createdFor (some dictSigned8Single) 8 5 valueCellB

private def hitDoubleCreated : Nat :=
  createdFor (some dictSigned8Double) 8 (-1) valueCellB

private def hitTripleCreated : Nat :=
  createdFor (some dictSigned8Triple) 8 1 valueCellA

private def hitZeroCreated : Nat :=
  createdFor (some dictSigned0Single) 0 0 valueCellB

private def missNullCreated : Nat :=
  createdFor none 8 5 valueCellA

private def missNonEmptyCreated : Nat :=
  createdFor (some dictSigned8Single) 8 7 valueCellB

private def hitSingleGas : Int :=
  baseGas + (Int.ofNat hitSingleCreated * cellCreateGasPrice)

private def hitDoubleGas : Int :=
  baseGas + (Int.ofNat hitDoubleCreated * cellCreateGasPrice)

private def hitTripleGas : Int :=
  baseGas + (Int.ofNat hitTripleCreated * cellCreateGasPrice)

private def hitZeroGas : Int :=
  baseGas + (Int.ofNat hitZeroCreated * cellCreateGasPrice)

private def missNullGas : Int :=
  baseGas + (Int.ofNat missNullCreated * cellCreateGasPrice)

private def missNonEmptyGas : Int :=
  baseGas + (Int.ofNat missNonEmptyCreated * cellCreateGasPrice)

private def hitSingleGasMinusOne : Int :=
  if hitSingleGas > 0 then hitSingleGas - 1 else 0

private def missNullGasMinusOne : Int :=
  if missNullGas > 0 then missNullGas - 1 else 0

private def mkDictCaseStack (newValue : Cell) (key : Int) (dict : Value) (n : Int := 8) : Array Value :=
  #[.cell newValue, .int (.num key), dict, .int (.num n)]

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
        throw (IO.userError s!"{label}: expected consumed bits")
      pure rest

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {instr}/{bits}")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok c =>
      throw (IO.userError s!"{label}: expected .invOpcode, got bits {c.bits}")

private def runDICTISETREFDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def runDICTISETREFDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def genDICTISETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 33
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/underflow/one" #[.cell valueCellA], rng1)
    else if shape = 2 then
      (mkCase "fuzz/underflow/two" #[.cell valueCellA, .int (.num 5)], rng1)
    else if shape = 3 then
      (mkCase "fuzz/underflow/three" #[.cell valueCellA, .int (.num 5), .cell dictSigned8Single], rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/n-negative" (mkDictCaseStack valueCellA 5 (.cell dictSigned8Single) (-1)), rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/n-too-large" (mkDictCaseStack valueCellA 5 (.cell dictSigned8Single) 1024), rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/n-nan" #[.cell valueCellA, .int (.num 5), .cell dictSigned8Single, .int .nan], rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/key-range-high" (mkDictCaseStack valueCellA 16 (.cell dictSigned8Single) 4), rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/key-range-low" (mkDictCaseStack valueCellA (-9) (.cell dictSigned8Single) 4), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/key-range-nonzero-n0" (mkDictCaseStack valueCellA 1 (.cell dictSigned0Single) 0), rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/type-root" (mkDictCaseStack valueCellA 5 (.tuple #[]) 8), rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/type-key" (#[(.cell valueCellA), .slice valueSliceA, .cell dictSigned8Single, intV 8]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-value" #[.slice valueBitsOnly, .int (.num 5), .cell dictSigned8Single, intV 8], rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/hit-single" (mkDictCaseStack valueCellB 5 (.cell dictSigned8Single) 8), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/hit-double" (mkDictCaseStack valueCellA 5 (.cell dictSigned8Double) 8), rng1)
    else if shape = 15 then
      (mkCase "fuzz/ok/hit-triple" (mkDictCaseStack valueCellD 1 (.cell dictSigned8Triple) 8), rng1)
    else if shape = 16 then
      (mkCase "fuzz/ok/hit-zero" (mkDictCaseStack valueCellC 0 (.cell dictSigned0Single) 0), rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/miss-null" (mkDictCaseStack valueCellB 5 .null 8), rng1)
    else if shape = 18 then
      (mkCase "fuzz/ok/miss-non-empty" (mkDictCaseStack valueCellC 7 (.cell dictSigned8Single) 8), rng1)
    else if shape = 19 then
      (mkCase "fuzz/ok/miss-zero-width" (mkDictCaseStack valueCellD 0 (.cell dictSigned0Single) 0), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/malformed-root" (mkDictCaseStack valueCellA 5 (.cell malformedDictRoot) 8), rng1)
    else if shape = 21 then
      (mkCodeCase "fuzz/raw/f412" (mkDictCaseStack valueCellA 5 (.null) 8) rawF412, rng1)
    else if shape = 22 then
      (mkCodeCase "fuzz/raw/f413" (#[.cell valueCellA, .slice valueBitsOnly, .null, intV 8]) rawF413, rng1)
    else if shape = 23 then
      (mkCodeCase "fuzz/raw/f414" (#[.slice valueBitsOnly, .slice valueBitsOnly, .null, intV 8]) rawF414, rng1)
    else if shape = 24 then
      (mkCodeCase "fuzz/raw/f415" (mkDictCaseStack valueCellA 5 (.null) 8) rawF415, rng1)
    else if shape = 25 then
      (mkCodeCase "fuzz/raw/f416" (#[.slice valueBitsOnly, .slice valueBitsOnly, .null, intV 8]) rawF416, rng1)
    else if shape = 26 then
      (mkCodeCase "fuzz/raw/f417" (#[.cell valueCellA, .slice valueBitsOnly, .null, intV 8]) rawF417, rng1)
    else if shape = 27 then
      (mkCodeCase "fuzz/raw/f411" #[] rawF411, rng1)
    else if shape = 28 then
      (mkCodeCase "fuzz/raw/f418" #[] rawF418, rng1)
    else if shape = 29 then
      (mkCodeCase "fuzz/raw/truncated" #[] rawF4, rng1)
    else if shape = 30 then
      (mkCase
        "fuzz/gas/hit-exact"
        (mkDictCaseStack valueCellB 5 (.cell dictSigned8Single) 8)
        (#[.pushInt (.num hitSingleGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact hitSingleGas),
       rng1)
    else if shape = 31 then
      (mkCase
        "fuzz/gas/hit-minus-one"
        (mkDictCaseStack valueCellB 5 (.cell dictSigned8Single) 8)
        (#[.pushInt (.num hitSingleGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne hitSingleGasMinusOne),
       rng1)
    else if shape = 32 then
      (mkCase
        "fuzz/gas/miss-exact"
        (mkDictCaseStack valueCellB 5 .null 8)
        (#[.pushInt (.num missNullGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact missNullGas),
       rng1)
    else
      (mkCase
        "fuzz/gas/miss-minus-one"
        (mkDictCaseStack valueCellB 5 .null 8)
        (#[.pushInt (.num missNullGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne missNullGasMinusOne), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  let case1 := { case0 with name := s!"{case0.name}/{tag}" }
  (case1, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDICTISETREFDispatchFallback (mkDictCaseStack valueCellA 5 (.cell dictSigned8Single) 8) with
        | .ok st =>
            if st == #[.cell valueCellA, .int (.num 5), .cell dictSigned8Single, intV 8, .int (.num dispatchSentinel)] then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback: expected stack unchanged + sentinel, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback: unexpected {e}") }
    ,
    { name := "unit/encoding/diсtisetref" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != rawF415.bits then
              throw (IO.userError "encoding expected 0xF415")
        | .error e =>
            throw (IO.userError s!"encoding failed: {e}")
        expectAssembleInvOpcode "encoding/invalid-unsiged-nonint" (.dictSet false true true .set)
        match assembleCp0 [(.dictSet true true true .set)] with
        | .ok c =>
            if c.bits != rawF417.bits then
              throw (IO.userError "encoding for 0xF417 incorrect")
        | .error e =>
            throw (IO.userError s!"encoding/unsigned-ref failed: {e}") }
    ,
    { name := "unit/decoder/chain-and-boundaries" -- [B7]
      run := do
        let s0 : Slice := Slice.ofCell rawSetFamily
        let s1 ← expectDecodeStep "decode/f412" s0 (.dictSet false false false .set)
        let s2 ← expectDecodeStep "decode/f413" s1 (.dictSet false false true .set)
        let s3 ← expectDecodeStep "decode/f414" s2 (.dictSet true false false .set)
        let s4 ← expectDecodeStep "decode/f415" s3 (.dictSet true false true .set)
        let _ ← expectDecodeStep "decode/f416" s4 (.dictSet true true false .set)
        let _ ← expectDecodeStep "decode/f417" s4 (.dictSet true true true .set)
        expectDecodeInvOpcode "decode/underflow-low" rawF411
        expectDecodeInvOpcode "decode/over" rawF418
        expectDecodeInvOpcode "decode/truncated" rawF4 }
    ,
    { name := "unit/runtime/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDICTISETREFDirect #[]) .stkUnd
        expectErr "underflow-one" (runDICTISETREFDirect #[.cell valueCellA]) .stkUnd
        expectErr "underflow-two" (runDICTISETREFDirect #[.cell valueCellA, .int (.num 5)]) .stkUnd
        expectErr "underflow-three" (runDICTISETREFDirect #[.cell valueCellA, .int (.num 5), .cell dictSigned8Single]) .stkUnd }
    ,
    { name := "unit/runtime/n-and-type" -- [B3][B4][B5]
      run := do
        expectErr "n-negative" (runDICTISETREFDirect (mkDictCaseStack valueCellA 5 (.cell dictSigned8Single) (-1))) .rangeChk
        expectErr "n-too-large" (runDICTISETREFDirect (mkDictCaseStack valueCellA 5 (.cell dictSigned8Single) 1024)) .rangeChk
        expectErr "n-nan" (runDICTISETREFDirect #[.cell valueCellA, .int (.num 5), .cell dictSigned8Single, .int .nan]) .rangeChk
        expectErr "type-root" (runDICTISETREFDirect (mkDictCaseStack valueCellA 5 (.tuple #[]) 8)) .typeChk
        expectErr "type-key" (runDICTISETREFDirect #[.cell valueCellA, .slice valueSliceA, .cell dictSigned8Single, intV 8]) .typeChk
        expectErr "type-value" (runDICTISETREFDirect (#[(.slice valueBitsOnly), .int (.num 5), .cell dictSigned8Single, intV 8])) .typeChk }
    ,
    { name := "unit/runtime/key-boundary" -- [B4][B9]
      run := do
        expectErr "key-non-zero-at-n0" (runDICTISETREFDirect (mkDictCaseStack valueCellA 1 (.cell dictSigned0Single) 0)) .rangeChk
        expectErr "key-range-high" (runDICTISETREFDirect (mkDictCaseStack valueCellA 8 (.cell dictSigned8Single) 4)) .rangeChk
        expectErr "key-range-low" (runDICTISETREFDirect (mkDictCaseStack valueCellA (-9) (.cell dictSigned8Single) 4)) .rangeChk
        expectOkStack "ok-zero-width-hit"
          (runDICTISETREFDirect (mkDictCaseStack valueCellB 0 (.cell dictSigned0Single) 0))
          #[.cell dictSigned0SingleRepl] }
    ,
    { name := "unit/runtime/semantics-ok" -- [B5]
      run := do
        expectOkStack "ok-miss-null"
          (runDICTISETREFDirect (mkDictCaseStack valueCellA 5 .null 8))
          #[.cell dictSigned8NullInsert]
        expectOkStack "ok-hit-single"
          (runDICTISETREFDirect (mkDictCaseStack valueCellB 5 (.cell dictSigned8Single) 8))
          #[.cell dictSigned8SingleRepl]
        expectOkStack "ok-hit-double"
          (runDICTISETREFDirect (mkDictCaseStack valueCellC (-1) (.cell dictSigned8Double) 8))
          #[.cell dictSigned8DoubleRepl]
        expectOkStack "ok-hit-triple"
          (runDICTISETREFDirect (mkDictCaseStack valueCellA 1 (.cell dictSigned8Triple) 8))
          #[.cell dictSigned8TripleRepl]
        expectOkStack "ok-miss-non-empty"
          (runDICTISETREFDirect (mkDictCaseStack valueCellB 7 (.cell dictSigned8Single) 8))
          #[.cell dictSigned8SingleInsert7] }
    ,
    { name := "unit/runtime/structural-error" -- [B6]
      run := do
        expectErr "malformed-root" (runDICTISETREFDirect (mkDictCaseStack valueCellA 5 (.cell malformedDictRoot) 8)) .dictErr }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow-empty" #[]
    ,
    mkCase "oracle/underflow-one" #[.cell valueCellA]
    ,
    mkCase "oracle/underflow-two" #[.cell valueCellA, .int (.num 7)]
    ,
    mkCase "oracle/underflow-three" #[.cell valueCellA, .int (.num 7), .cell dictSigned8Single]
    ,
    -- [B3]
    mkCase "oracle/err/n-negative" (mkDictCaseStack valueCellA 5 (.cell dictSigned8Single) (-1))
    ,
    mkCase "oracle/err/n-too-large" (mkDictCaseStack valueCellA 5 (.cell dictSigned8Single) 1024)
    ,
    mkCase "oracle/err/n-nan" #[.cell valueCellA, .int (.num 5), .cell dictSigned8Single, .int .nan]
    ,
    -- [B4]
    mkCase "oracle/err/key-high" (mkDictCaseStack valueCellA 8 (.cell dictSigned8Single) 4)
    ,
    mkCase "oracle/err/key-low" (mkDictCaseStack valueCellA (-9) (.cell dictSigned8Single) 4)
    ,
    mkCase "oracle/err/key-nonzero-n0" (mkDictCaseStack valueCellA 1 (.cell dictSigned0Single) 0)
    ,
    -- [B5]
    mkCase "oracle/err/type-key" #[.cell valueCellA, .slice valueSliceA, .cell dictSigned8Single, intV 8]
    ,
    mkCase "oracle/err/type-value" #[.slice valueBitsOnly, .int (.num 5), .cell dictSigned8Single, intV 8]
    ,
    mkCase "oracle/err/type-root" (mkDictCaseStack valueCellA 5 (.tuple #[]) 8)
    ,
    -- [B6]
    mkCase "oracle/ok/miss-null" (mkDictCaseStack valueCellA 5 .null 8)
    ,
    mkCase "oracle/ok/miss-non-empty" (mkDictCaseStack valueCellB 7 (.cell dictSigned8Single) 8)
    ,
    mkCase "oracle/ok/hit-single" (mkDictCaseStack valueCellB 5 (.cell dictSigned8Single) 8)
    ,
    mkCase "oracle/ok/hit-double" (mkDictCaseStack valueCellC (-1) (.cell dictSigned8Double) 8)
    ,
    mkCase "oracle/ok/hit-triple" (mkDictCaseStack valueCellA 1 (.cell dictSigned8Triple) 8)
    ,
    mkCase "oracle/ok/hit-zero" (mkDictCaseStack valueCellC 0 (.cell dictSigned0Single) 0)
    ,
    mkCase "oracle/ok/miss-zero" (mkDictCaseStack valueCellD 0 .null 0)
    ,
    mkCase "oracle/ok/wide-n" (mkDictCaseStack valueCellB 0 (.cell dictSigned1023Single) 1023)
    ,
    -- [B6] malformed
    mkCase "oracle/err/malformed-root" (mkDictCaseStack valueCellA 5 (.cell malformedDictRoot) 8)
    ,
    -- [B7]
    mkCodeCase "oracle/raw/f412" (#[.cell valueCellA, .slice valueBitsOnly, .null, intV 8]) rawF412
    ,
    mkCodeCase "oracle/raw/f413" (#[.cell valueCellA, .slice valueBitsOnly, .null, intV 8]) rawF413
    ,
    mkCodeCase "oracle/raw/f414" (#[.slice valueSliceA, .slice valueBitsOnly, .null, intV 8]) rawF414
    ,
    mkCodeCase "oracle/raw/f415" (#[.cell valueCellA, .int (.num 5), .null, intV 8]) rawF415
    ,
    mkCodeCase "oracle/raw/f416" (#[.slice valueSliceA, .slice valueBitsOnly, .null, intV 8]) rawF416
    ,
    mkCodeCase "oracle/raw/f417" (#[.cell valueCellA, .slice valueBitsOnly, .null, intV 8]) rawF417
    ,
    mkCodeCase "oracle/raw/f411" #[] rawF411
    ,
    mkCodeCase "oracle/raw/f418" #[] rawF418
    ,
    mkCodeCase "oracle/raw/truncated" #[] rawF4
    ,
    -- [B8]
    mkCase
      "oracle/gas/hit-single-exact"
      (mkDictCaseStack valueCellB 5 (.cell dictSigned8Single) 8)
      (#[.pushInt (.num hitSingleGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitSingleGas)
    ,
    mkCase
      "oracle/gas/hit-single-minus-one"
      (mkDictCaseStack valueCellB 5 (.cell dictSigned8Single) 8)
      (#[.pushInt (.num hitSingleGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitSingleGasMinusOne)
    ,
    mkCase
      "oracle/gas/miss-null-exact"
      (mkDictCaseStack valueCellA 5 .null 8)
      (#[.pushInt (.num missNullGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact missNullGas)
    ,
    mkCase
      "oracle/gas/miss-null-minus-one"
      (mkDictCaseStack valueCellA 5 .null 8)
      (#[.pushInt (.num missNullGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne missNullGasMinusOne)
    ,
    mkCase
      "oracle/gas/miss-non-empty-exact"
      (mkDictCaseStack valueCellB 7 (.cell dictSigned8Single) 8)
      (#[.pushInt (.num missNonEmptyGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact missNonEmptyGas)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTISETREFFuzzCase } ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTISETREF
