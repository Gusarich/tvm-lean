import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTSETREF

/--!
INSTRUCTION: DICTSETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `.dictSet` instructions are executed by `execInstrDictDictSet`.
   - Non-`dictSet` opcode paths must take fallback (`next`) unchanged.

2. [B2] Arity and stack layout branch.
   - `checkUnderflow 4` is required.
   - Stack order is `newValue`, `key`, `dict`, `n` (top item is popped first).
   - Less than 4 items must fail with `.stkUnd`.

3. [B3] Width argument branch.
   - `n` is constrained by `popNatUpTo 1023`.
   - Negative, `.nan`, and `>1023` widths fail with `.rangeChk`.

4. [B4] Signed key conversion branch (`intKey=true`, `unsigned=false`).
   - Key conversion is `dictKeyBits? key n false`.
   - For `n = 0`, only key `0` is valid.
   - For `n > 0`, keys outside `[-2^(n-1), 2^(n-1)-1]` fail with `.rangeChk`.

5. [B5] By-ref value branch.
   - `.dictSet ... byRef` requires `.cell` value.
   - Non-cell value fails with `.typeChk`.

6. [B6] Dictionary-set set-mode branch.
   - In `.set` mode, `dictSetRefWithCells` is executed and may push created root updates.
   - On success, only the updated dictionary root is pushed, without boolean status.
   - Valid miss and hit paths are tested.

7. [B7] Root-structure error branch.
   - A malformed dictionary can raise `.dictErr` via `dictSetRefWithCells`.

8. [B8] Assembler branch.
   - `.dictSet true false true .set` encodes to `0xf415`.
   - `.dictSet false true true .set` and invalid unsigned combinations must be `.invOpcode`.
   - `.dictSet true true true .set` encodes to `0xf417`.

9. [B9] Decoder boundaries branch.
   - `0xf414..0xf417` are valid DICTSETREF-anchored forms at width-dependent `dictSet` modes.
   - `0xf411` and `0xf418` are `.invOpcode`.
   - Truncated `0xf4` (8-bit) is `.invOpcode`.

10. [B10] Gas accounting branch.
   - Base cost is `computeExactGasBudget instr`.
   - Miss/insertion branch pays `cellCreateGasPrice * created` surcharge.
   - `exact` should succeed and `exactMinusOne` should fail.

11. [B11] Width boundaries branch.
   - `n=0` and `n=1023` are allowed by preamble; conversion and key constraints still apply.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branches it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTSETREF" }

private def instr : Instr :=
  .dictSet true false true .set

private def dispatchSentinel : Int :=
  13021

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC 8) #[]
private def valueD : Cell := Cell.mkOrdinary (natToBits 0xD 8) #[]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b111 3) #[]
private def badSliceValue : Slice := mkSliceFromBits (natToBits 0xEE 8)

private def mkBits (k : Int) (n : Nat) : BitString :=
  match dictKeyBits? k n false with
  | some bits => bits
  | none => panic! s!"DICTSETREF key conversion failed for key={k}, n={n}"

private def mkDictSetRefRootWithWidth! (label : String) (width : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits : BitString := mkBits k width
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: no dictionary root built"

private def mkDictSetRefRoot! (label : String) (entries : Array (Int × Cell)) : Cell :=
  mkDictSetRefRootWithWidth! label 8 entries

private def dict8Single0 : Cell :=
  mkDictSetRefRoot! "dict/8/single/0" #[(0, valueA)]

private def dict8Single127 : Cell :=
  mkDictSetRefRoot! "dict/8/single/127" #[(127, valueB)]

private def dict8Pair : Cell :=
  mkDictSetRefRoot! "dict/8/pair" #[(0, valueA), (127, valueC)]

private def dict8Fork : Cell :=
  mkDictSetRefRoot! "dict/8/fork" #[(6, valueA), (7, valueB)]

private def dict8Shared : Cell :=
  mkDictSetRefRoot! "dict/8/shared" #[(4, valueC), (5, valueD)]

private def dict0Single : Cell :=
  mkDictSetRefRoot! "dict/0/single" #[(0, valueA)]

private def dict1023Single : Cell :=
  mkDictSetRefRootWithWidth! "dict/1023/single" 1023 #[(0, valueA)]

private def hitCreated : Nat :=
  match dictSetRefWithCells (some dict8Single0) (mkBits 0 8) valueB .set with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def missCreated8 : Nat :=
  match dictSetRefWithCells none (mkBits 1 8) valueC .set with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def missCreated1023 : Nat :=
  match dictSetRefWithCells none (mkBits 0 1023) valueD .set with
  | .ok (_newRoot?, _ok, created, _loaded) => created
  | .error _ => 0

private def minusOneOrZero (g : Int) : Int :=
  if g > 0 then g - 1 else 0

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := minusOneOrZero baseGas

private def hitGas : Int := baseGas + (Int.ofNat hitCreated * cellCreateGasPrice)
private def hitGasMinusOne : Int := minusOneOrZero hitGas
private def missGas8 : Int := baseGas + (Int.ofNat missCreated8 * cellCreateGasPrice)
private def missGas8MinusOne : Int := minusOneOrZero missGas8
private def missGas1023 : Int := baseGas + (Int.ofNat missCreated1023 * cellCreateGasPrice)
private def missGas1023MinusOne : Int := minusOneOrZero missGas1023

private def rawF411 : Cell := Cell.mkOrdinary (natToBits 0xf411 16) #[]
private def rawF412 : Cell := Cell.mkOrdinary (natToBits 0xf412 16) #[]
private def rawF413 : Cell := Cell.mkOrdinary (natToBits 0xf413 16) #[]
private def rawF414 : Cell := Cell.mkOrdinary (natToBits 0xf414 16) #[]
private def rawF415 : Cell := Cell.mkOrdinary (natToBits 0xf415 16) #[]
private def rawF416 : Cell := Cell.mkOrdinary (natToBits 0xf416 16) #[]
private def rawF417 : Cell := Cell.mkOrdinary (natToBits 0xf417 16) #[]
private def rawF418 : Cell := Cell.mkOrdinary (natToBits 0xf418 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]
private def rawChain : Cell :=
  Cell.mkOrdinary
    (rawF412.bits ++ rawF413.bits ++ rawF414.bits ++ rawF415.bits ++ rawF416.bits ++ rawF417.bits)
    #[]

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

private def runDICTSETREFDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def runDICTSETREFDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits opcode 16) #[])) with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (i, _, _) => throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr i}")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected .invOpcode, got success")

private def genDICTSETREFFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 34
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/underflow/one" #[.int (.num 8)], rng1)
    else if shape = 2 then
      (mkCase "fuzz/underflow/two" #[.int (.num 8), .null], rng1)
    else if shape = 3 then
      (mkCase "fuzz/underflow/three" #[.cell valueA, .int (.num 8), .null], rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/miss/null8" #[.cell valueA, .int (.num 1), .null, .int (.num 8)], rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss/null16" #[.cell valueB, .int (.num 42), .null, .int (.num 16)], rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/miss/null1023" #[.cell valueC, .int (.num 0), .null, .int (.num 1023)], rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit/single" #[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)], rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit/single127" #[.cell valueD, .int (.num 127), .cell dict8Single127, .int (.num 8)], rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit/pair-first" #[.cell valueA, .int (.num 0), .cell dict8Pair, .int (.num 8)], rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/hit/pair-second" #[.cell valueC, .int (.num 127), .cell dict8Pair, .int (.num 8)], rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/hit/zero-width" #[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 0)], rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/hit/1023" #[.cell valueD, .int (.num 0), .cell dict1023Single, .int (.num 1023)], rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/n/negative" #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num (-1))], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/n/nan" #[.cell valueA, .int (.num 8), .cell dict8Single0, .int .nan], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/n/too-large" #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 1024)], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-key" #[.cell valueA, .slice badSliceValue, .cell dict8Single0, .int (.num 8)], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-dict" #[.cell valueA, .int (.num 8), .tuple #[], .int (.num 8)], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/type-value" #[.slice badSliceValue, .int (.num 8), .cell dict8Single0, .int (.num 8)], rng1)
    else if shape = 19 then
      (mkCodeCase "fuzz/err/key-high" (#[.cell valueA, .int (.num 128), .cell dict8Single0, .int (.num 8)]) rawF415, rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/key-low" #[.cell valueA, .int (.num (-129)), .cell dict8Single0, .int (.num 8)], rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/key/nonzero-width-zero" #[.cell valueA, .int (.num 1), .cell dict0Single, .int (.num 0)], rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/malformed-root" #[.cell valueA, .int (.num 8), .cell malformedDict, .int (.num 8)], rng1)
    else if shape = 23 then
      (mkCodeCase "fuzz/decode/f414" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF414, rng1)
    else if shape = 24 then
      (mkCodeCase "fuzz/decode/f415" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF415, rng1)
    else if shape = 25 then
      (mkCodeCase "fuzz/decode/f416" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF416, rng1)
    else if shape = 26 then
      (mkCodeCase "fuzz/decode/f417" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF417, rng1)
    else if shape = 27 then
      (mkCodeCase "fuzz/decode/f412" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF412, rng1)
    else if shape = 28 then
      (mkCodeCase "fuzz/decode/f413" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF413, rng1)
    else if shape = 29 then
      (mkCodeCase "fuzz/decode/f411-inv" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF411, rng1)
    else if shape = 30 then
      (mkCodeCase "fuzz/decode/f418-inv" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF418, rng1)
    else if shape = 31 then
      (mkCodeCase "fuzz/decode/truncated" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF4, rng1)
    else if shape = 32 then
      (mkCase "fuzz/gas/hit-exact"
        (#[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 0)] )
        (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact hitGas), rng1)
    else if shape = 33 then
      (mkCase "fuzz/gas/hit-exact-minus-one"
        (#[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 0)] )
        (#[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne hitGasMinusOne), rng1)
    else if shape = 34 then
      (mkCase "fuzz/gas/miss-exact"
        (#[.cell valueA, .int (.num 1), .null, .int (.num 8)] )
        (#[.pushInt (.num missGas8), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact missGas8), rng1)
    else
      (mkCodeCase "fuzz/default" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF415, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def expectedHitSingle0 : Cell :=
  mkDictSetRefRoot! "tmp-hit-s0" #[(0, valueB)]

private def expectedHitPair : Cell :=
  mkDictSetRefRoot! "tmp-hit-pair" #[(0, valueA), (127, valueD)]

private def expectedMiss8 : Cell :=
  mkDictSetRefRoot! "tmp-miss8" #[(1, valueC)]

private def expectedMiss1023 : Cell :=
  mkDictSetRefRoot! "tmp-miss1023" #[(0, valueA)]

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st ←
          match runDICTSETREFDispatchFallback #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)] with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"fallback failed: {e}")
        if st == #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8), .int (.num dispatchSentinel)] then
          pure ()
        else
          throw (IO.userError s!"fallback failed: expected unchanged stack with sentinel") }
    ,
    { name := "unit/asm/encode/ref" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits == natToBits 0xf415 16 then
              pure ()
            else
              throw (IO.userError s!"unit/asm/encode/ref: expected 0xf415, got {reprStr c.bits}")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/ref: {e}") }
    ,
    { name := "unit/asm/invalid-non-int" -- [B8]
      run := do
        expectAssembleInvOpcode "unit/asm/invalid-non-int" (.dictSet false true true .set) }
    ,
    { name := "unit/asm/encode/valid-unsigned" -- [B8]
      run := do
        match assembleCp0 [.dictSet true true true .set] with
        | .ok c =>
            if c.bits == natToBits 0xf417 16 then
              pure ()
            else
              throw (IO.userError s!"unit/asm/invalid-unsigned: unexpected bits {c.bits}")
        | .error e =>
            throw (IO.userError s!"unit/asm/invalid-unsigned: {e}") }
    ,
    { name := "unit/decode/valid" -- [B9]
      run := do
        let s414 : Slice := Slice.ofCell rawF414
        let _ ← expectDecodeStep "decode/f414" s414 (.dictSet true false false .set) 16
        let s415 : Slice := Slice.ofCell rawF415
        let _ ← expectDecodeStep "decode/f415" s415 (.dictSet true false true .set) 16
        let s416 : Slice := Slice.ofCell rawF416
        let _ ← expectDecodeStep "decode/f416" s416 (.dictSet true true false .set) 16
        let s417 : Slice := Slice.ofCell rawF417
        let _ ← expectDecodeStep "decode/f417" s417 (.dictSet true true true .set) 16
        pure () }
    ,
    { name := "unit/decode/adjacent-and-boundaries" -- [B9]
      run := do
        let chain : Slice := Slice.ofCell rawChain
        let _ ← expectDecodeStep "decode/f412" chain (.dictSet false false false .set) 16
        let _ ← expectDecodeStep "decode/f413" chain (.dictSet false false true .set) 16
        let _ ← expectDecodeStep "decode/f414" chain (.dictSet true false false .set) 16
        let _ ← expectDecodeStep "decode/f415" chain (.dictSet true false true .set) 16
        let _ ← expectDecodeStep "decode/f416" chain (.dictSet true true false .set) 16
        let _ ← expectDecodeStep "decode/f417" chain (.dictSet true true true .set) 16
        expectDecodeInvOpcode "decode/f411" 0xf411
        expectDecodeInvOpcode "decode/f418" 0xf418
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated: expected invOpcode, got {e}")
        | .ok (i, _, _) => throw (IO.userError s!"decode/truncated: expected invOpcode, got {reprStr i}") }
    ,
    { name := "unit/direct/ok-miss" -- [B6]
      run := do
        expectOkStack "direct/ok-miss"
          (runDICTSETREFDirect #[.cell valueC, .int (.num 1), .null, .int (.num 8)])
          #[.cell expectedMiss8] }
    ,
    { name := "unit/direct/ok-hit" -- [B6]
      run := do
        expectOkStack "direct/ok-hit"
          (runDICTSETREFDirect #[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)])
          #[.cell expectedHitSingle0] }
    ,
    { name := "unit/direct/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDICTSETREFDirect #[]) .stkUnd
        expectErr "underflow-one" (runDICTSETREFDirect #[.cell valueA]) .stkUnd
        expectErr "underflow-two" (runDICTSETREFDirect #[.int (.num 8), .cell valueA]) .stkUnd
        expectErr "underflow-three" (runDICTSETREFDirect #[.cell valueA, .int (.num 8), .null]) .stkUnd }
    ,
    { name := "unit/errors" -- [B3] [B4] [B5] [B7]
      run := do
        expectErr "n-negative" (runDICTSETREFDirect #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num (-1))]) .rangeChk
        expectErr "n-too-large" (runDICTSETREFDirect #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 1024)]) .rangeChk
        expectErr "n-nan" (runDICTSETREFDirect #[.cell valueA, .int (.num 8), .cell dict8Single0, .int .nan]) .rangeChk
        expectErr "key-type" (runDICTSETREFDirect #[.cell valueA, .slice badSliceValue, .cell dict8Single0, .int (.num 8)]) .typeChk
        expectErr "value-type" (runDICTSETREFDirect #[.slice badSliceValue, .int (.num 8), .cell dict8Single0, .int (.num 8)]) .typeChk
        expectErr "dict-type" (runDICTSETREFDirect #[.cell valueA, .int (.num 8), .tuple #[], .int (.num 8)]) .typeChk
        expectErr "key-high" (runDICTSETREFDirect #[.cell valueA, .int (.num 128), .cell dict8Single0, .int (.num 8)]) .rangeChk
        expectErr "key-low" (runDICTSETREFDirect #[.cell valueA, .int (.num (-129)), .cell dict8Single0, .int (.num 8)]) .rangeChk
        expectErr "zero-width-non-zero-key" (runDICTSETREFDirect #[.cell valueA, .int (.num 1), .cell dict0Single, .int (.num 0)]) .rangeChk
        expectErr "malformed-root" (runDICTSETREFDirect #[.cell valueA, .int (.num 8), .cell malformedDict, .int (.num 8)]) .dictErr }
    ,
    { name := "unit/gas-check" -- [B10]
      run := do
        if baseGas > 0 then
          pure ()
        else
          throw (IO.userError "baseGas must be positive")
    }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow/empty" #[] ,
    mkCase "oracle/underflow/one" #[.int (.num 8)] ,
    mkCase "oracle/underflow/two" #[.int (.num 8), .cell valueA] ,
    mkCase "oracle/underflow/three" #[.cell valueA, .int (.num 8), .null] ,
    -- [B3]
    mkCase "oracle/err/n-negative" #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num (-1))] ,
    mkCase "oracle/err/n-nan" #[.cell valueA, .int (.num 8), .cell dict8Single0, .int .nan] ,
    mkCase "oracle/err/n-too-large" #[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 1024)] ,
    -- [B4]
    mkCase "oracle/err/key-type" #[.cell valueA, .slice badSliceValue, .cell dict8Single0, .int (.num 8)] ,
    mkCase "oracle/err/key-out-of-range-high" #[.cell valueA, .int (.num 128), .cell dict8Single0, .int (.num 8)] ,
    mkCase "oracle/err/key-out-of-range-low" #[.cell valueA, .int (.num (-129)), .cell dict8Single0, .int (.num 8)] ,
    mkCase "oracle/err/zero-width-key" #[.cell valueA, .int (.num 1), .cell dict0Single, .int (.num 0)] ,
    -- [B5]
    mkCase "oracle/ok/miss-null8" #[.cell valueA, .int (.num 1), .null, .int (.num 8)] ,
    mkCase "oracle/ok/miss-null1023" #[.cell valueA, .int (.num 0), .null, .int (.num 1023)] ,
    mkCase "oracle/ok/hit-single0" #[.cell valueB, .int (.num 0), .cell dict8Single0, .int (.num 8)] ,
    mkCase "oracle/ok/hit-single127" #[.cell valueC, .int (.num 127), .cell dict8Single127, .int (.num 8)] ,
    mkCase "oracle/ok/hit-pair0" #[.cell valueA, .int (.num 0), .cell dict8Pair, .int (.num 8)] ,
    mkCase "oracle/ok/hit-pair127" #[.cell valueD, .int (.num 127), .cell dict8Pair, .int (.num 8)] ,
    mkCase "oracle/ok/hit-fork-a" #[.cell valueA, .int (.num 6), .cell dict8Fork, .int (.num 8)] ,
    mkCase "oracle/ok/hit-shared-prefix" #[.cell valueD, .int (.num 4), .cell dict8Shared, .int (.num 8)] ,
    mkCase "oracle/ok/hit-0-width" #[.cell valueB, .int (.num 0), .cell dict0Single, .int (.num 0)] ,
    mkCase "oracle/ok/hit-1023" #[.cell valueD, .int (.num 0), .cell dict1023Single, .int (.num 1023)] ,
    -- [B5]/[B7]
    mkCase "oracle/err/value-type" #[.slice badSliceValue, .int (.num 8), .cell dict8Single0, .int (.num 8)] ,
    mkCase "oracle/err/dict-type" #[.cell valueA, .int (.num 8), .tuple #[], .int (.num 8)] ,
    mkCase "oracle/err/malformed-root" #[.cell valueA, .int (.num 8), .cell malformedDict, .int (.num 8)] ,
    -- [B9]
    mkCodeCase "oracle/code/f414" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF414 ,
    mkCodeCase "oracle/code/f415" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF415 ,
    mkCodeCase "oracle/code/f416" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF416 ,
    mkCodeCase "oracle/code/f417" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF417 ,
    mkCodeCase "oracle/code/f412" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF412 ,
    mkCodeCase "oracle/code/f413" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF413 ,
    mkCodeCase "oracle/code/f411-inv" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF411 ,
    mkCodeCase "oracle/code/f418-inv" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF418 ,
    mkCodeCase "oracle/code/truncated" (#[.cell valueA, .int (.num 8), .cell dict8Single0, .int (.num 8)]) rawF4 ,
    -- [B10]
    mkCase "oracle/gas/hit" #[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 0)]
      (#[.pushInt (.num hitGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitGas) ,
    mkCase "oracle/gas/hit-minus-one" #[.cell valueA, .int (.num 0), .cell dict0Single, .int (.num 0)]
      (#[.pushInt (.num hitGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitGasMinusOne) ,
    mkCase "oracle/gas/miss8" #[.cell valueA, .int (.num 1), .null, .int (.num 8)]
      (#[.pushInt (.num missGas8), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact missGas8) ,
    mkCase "oracle/gas/miss8-minus-one" #[.cell valueA, .int (.num 1), .null, .int (.num 8)]
      (#[.pushInt (.num missGas8MinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne missGas8MinusOne) ,
    mkCase "oracle/gas/miss1023" #[.cell valueA, .int (.num 0), .null, .int (.num 1023)]
      (#[.pushInt (.num missGas1023), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact missGas1023) ,
    mkCase "oracle/gas/miss1023-minus-one" #[.cell valueA, .int (.num 0), .null, .int (.num 1023)]
      (#[.pushInt (.num missGas1023MinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne missGas1023MinusOne) ,
    mkCase "oracle/gas/base" #[.cell valueA, .int (.num 127), .cell dict8Single127, .int (.num 8)]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas) ,
    mkCase "oracle/gas/base-minus-one" #[.cell valueA, .int (.num 127), .cell dict8Single127, .int (.num 8)]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTSETREFFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTSETREF
