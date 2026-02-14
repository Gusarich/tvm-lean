import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUADD

/-!
INSTRUCTION: DICTUADD

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictDictSet` handles `.dictSet` instructions and calls `next` for any other
     instruction.

2. [B2] Stack preconditions.
   - The handler requires 4 operands and immediately throws `.stkUnd` on underflow.
   - `n` is then parsed with `popNatUpTo 1023`; non-int / NaN / negative / >1023 are `.rangeChk`.

3. [B3] Dictionary root and key parsing.
   - Root is parsed with `popMaybeCell`; non-cell values raise `.typeChk`.
   - Signed/unsigned key conversion is performed via integer path because `intKey = true`.
   - `dictKeyBits?` in unsigned mode rejects key underflow/overflow and non-finite/int keys.
   - For `n = 0`, only key `0` is valid; any other value triggers `.rangeChk`.

4. [B4] Value parsing.
   - Value must be a slice for `byRef = false`; non-slice values raise `.typeChk`.

5. [B5] Dictionary add semantics.
   - Missing key path inserts and returns `-1` with new root.
   - Existing key path keeps root and returns `0`.

6. [B6] Dictionary shape failures.
   - Malformed dictionary roots must raise `.dictErr`.

7. [B7] Assembler encoding.
   - `.dictSet true true false .add` has exact opcode `0xF436`.
   - `.dictSet false true false .add` is rejected (`.invOpcode`) because `unsigned`
     is only meaningful when `intKey = true`.

8. [B8] Decoder boundaries.
   - `0xF432..0xF437` decode across the DICT*ADD family.
   - `0xF431`, `0xF438`, and truncated encodings must decode as `.invOpcode`.

9. [B9] Gas accounting.
   - Base cost uses `computeExactGasBudget`.
   - Missing-key inserts charge `created * cellCreateGasPrice` in addition to base.
   - `exact` budget succeeds and `exact-1` fails for both hit and miss branches.

TOTAL BRANCHES: 9
-/

private def suiteId : InstrId :=
  { name := "DICTUADD" }

private def instr : Instr :=
  .dictSet true true false .add

private def dispatchSentinel : Int := 42_007

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1011 4) #[]

private def valueA : Slice := mkSliceFromBits (natToBits 0xA1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xB2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xD4 8)
private def nonSliceValue : Cell := Cell.mkOrdinary (natToBits 0xAB 8) #[]

private def rawF431 : Cell := Cell.mkOrdinary (natToBits 0xF431 16) #[]
private def rawF432 : Cell := Cell.mkOrdinary (natToBits 0xF432 16) #[]
private def rawF433 : Cell := Cell.mkOrdinary (natToBits 0xF433 16) #[]
private def rawF434 : Cell := Cell.mkOrdinary (natToBits 0xF434 16) #[]
private def rawF435 : Cell := Cell.mkOrdinary (natToBits 0xF435 16) #[]
private def rawF436 : Cell := Cell.mkOrdinary (natToBits 0xF436 16) #[]
private def rawF437 : Cell := Cell.mkOrdinary (natToBits 0xF437 16) #[]
private def rawF438 : Cell := Cell.mkOrdinary (natToBits 0xF438 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def rawFamilyChain : Cell :=
  Cell.mkOrdinary (rawF432.bits ++ rawF433.bits ++ rawF434.bits ++ rawF435.bits ++ rawF436.bits ++ rawF437.bits) #[]

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
      | .ok (some r, _, _, _) =>
          root := r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root for ({k}, n={n})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary input"

private def expectedAddResult (label : String) (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Array Value :=
  let keyBits :=
    match dictKeyBits? key n true with
    | some bits => bits
    | none => panic! s!"{label}: invalid key ({key}) for n={n}"
  match dictSetSliceWithCells root keyBits value .add with
  | .ok (root?, ok, _, _) =>
      let rootValue : Value :=
        match root? with
        | some c => .cell c
        | none => .null
      #[(rootValue), intV (if ok then -1 else 0)]
  | .error e =>
      panic! s!"{label}: expected add branch but got {reprStr e}"

private def dictCreatedOnAdd (root : Option Cell) (n : Nat) (key : Int) (value : Slice) : Nat :=
  let keyBits :=
    match dictKeyBits? key n true with
    | some bits => bits
    | none => panic! s!"dictCreatedOnAdd: invalid key ({key}) for n={n}"
  match dictSetSliceWithCells root keyBits value .add with
  | .ok (_, _, created, _) => created
  | .error e => panic! s!"dictCreatedOnAdd failed: {reprStr e}"

private def dictZero : Cell := mkDictSetSliceRoot! "dict/u/zero" 0 #[(0, valueA)]
private def dictU8Single : Cell := mkDictSetSliceRoot! "dict/u/8/single" 8 #[(5, valueA)]
private def dictU8Pair : Cell := mkDictSetSliceRoot! "dict/u/8/pair" 8 #[(5, valueA), (200, valueB)]
private def dictU8Triple : Cell := mkDictSetSliceRoot! "dict/u/8/triple" 8 #[(5, valueA), (13, valueB), (200, valueC)]
private def dictU8Deep : Cell := mkDictSetSliceRoot! "dict/u/8/deep" 8 #[(5, valueA), (13, valueB), (200, valueC), (77, valueD)]
private def dictU257Single : Cell := mkDictSetSliceRoot! "dict/u/257/single" 257 #[(0, valueA)]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def insertEmpty8Gas : Int :=
  baseGas + Int.ofNat (dictCreatedOnAdd none 8 11 valueC) * cellCreateGasPrice
private def insertSingle8Gas : Int :=
  baseGas + Int.ofNat (dictCreatedOnAdd (some dictU8Single) 8 11 valueD) * cellCreateGasPrice
private def insertTriple8Gas : Int :=
  baseGas + Int.ofNat (dictCreatedOnAdd (some dictU8Triple) 8 11 valueB) * cellCreateGasPrice

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

private def runDictUAddDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def runDictUAddDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} with {bits} bits")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode, got success")

private def genDictUAddFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow/empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow/one" #[intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow/two" #[intV 8, .null], rng1)
    else if shape = 3 then
      (mkCase "fuzz/err/underflow/three" #[.slice valueA, intV 7, .cell dictU8Single], rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/type/dict-root" #[.slice valueA, intV 7, .tuple #[], intV 8], rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/type/key" #[.slice valueA, .null, .cell dictU8Single, intV 8], rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/type/value" #[.cell nonSliceValue, intV 7, .cell dictU8Single, intV 8], rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/nan-key" #[.slice valueA, .int .nan, .cell dictU8Single, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/neg-key" #[.slice valueA, intV (-1), .null, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/too-large-key" #[.slice valueA, intV 256, .null, intV 8], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/n-too-large" #[.slice valueA, intV 7, .null, intV 1024], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/n-neg" #[.slice valueA, intV 7, .null, intV (-1)], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/n-nan" #[.slice valueA, intV 7, .null, .int .nan], rng1)
    else if shape = 13 then
      (mkCodeCase "fuzz/err/decode-f431" #[] rawF431, rng1)
    else if shape = 14 then
      (mkCodeCase "fuzz/err/decode-f438" #[] rawF438, rng1)
    else if shape = 15 then
      (mkCodeCase "fuzz/err/decode-truncated8" #[] rawTruncated8, rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/malformed-root" #[.slice valueA, intV 7, .cell malformedDict, intV 8], rng1)
    else if shape = 17 then
      (mkCase "fuzz/ok/insert-null/8" #[.slice valueA, intV 77, .null, intV 8], rng1)
    else if shape = 18 then
      (mkCase "fuzz/ok/insert-null/0" #[.slice valueB, intV 0, .null, intV 0], rng1)
    else if shape = 19 then
      (mkCase "fuzz/ok/insert-null/257" #[.slice valueC, intV 0, .null, intV 257], rng1)
    else if shape = 20 then
      (mkCase "fuzz/ok/miss-pair" #[.slice valueD, intV 77, .cell dictU8Single, intV 8], rng1)
    else if shape = 21 then
      (mkCase "fuzz/ok/hit" #[.slice valueB, intV 5, .cell dictU8Single, intV 8], rng1)
    else if shape = 22 then
      (mkCodeCase "fuzz/ok/raw-f436" #[.slice valueA, intV 7, .null, intV 8] rawF436, rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/exact-hit" #[.slice valueC, intV 5, .cell dictU8Single, intV 8]
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/exact-minus-one-hit" #[.slice valueC, intV 5, .cell dictU8Single, intV 8]
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else if shape = 25 then
      (mkCase "fuzz/gas/exact-insert-empty" #[.slice valueD, intV 11, .null, intV 8]
        (#[.pushInt (.num insertEmpty8Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact insertEmpty8Gas), rng1)
    else if shape = 26 then
      (mkCase "fuzz/gas/exact-minus-one-insert-empty" #[.slice valueD, intV 11, .null, intV 8]
        (#[.pushInt (.num (insertEmpty8Gas - 1)), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne (insertEmpty8Gas - 1)), rng1)
    else if shape = 27 then
      (mkCase "fuzz/gas/exact-insert-single" #[.slice valueA, intV 11, .cell dictU8Single, intV 8]
        (#[.pushInt (.num insertSingle8Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact insertSingle8Gas), rng1)
    else if shape = 28 then
      (mkCase "fuzz/gas/exact-minus-one-insert-single" #[.slice valueA, intV 11, .cell dictU8Single, intV 8]
        (#[.pushInt (.num (insertSingle8Gas - 1)), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne (insertSingle8Gas - 1)), rng1)
    else if shape = 29 then
      (mkCase "fuzz/gas/exact-insert-triple" #[.slice valueB, intV 11, .cell dictU8Triple, intV 8]
        (#[.pushInt (.num insertTriple8Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact insertTriple8Gas), rng1)
    else if shape = 30 then
      (mkCase "fuzz/gas/exact-minus-one-insert-triple" #[.slice valueB, intV 11, .cell dictU8Triple, intV 8]
        (#[.pushInt (.num (insertTriple8Gas - 1)), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne (insertTriple8Gas - 1)), rng1)
    else
      (mkCase "fuzz/ok/insert-zero-key" #[.slice valueD, intV 0, .null, intV 0], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let expected : Array Value :=
          (#[] : Array Value) ++ [ .slice valueA, intV 5, .cell dictU8Single, intV 8, intV dispatchSentinel ]
        expectOkStack
          "dispatch/fallback"
          (runDictUAddDispatchFallback #[.slice valueA, intV 5, .cell dictU8Single, intV 8])
          expected },
    { name := "unit/encoding/valid" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF436 16 then
              pure ()
            else
              throw (IO.userError s!"unit/encoding/valid: unexpected bits {c.bits}")
        | .error e =>
            throw (IO.userError s!"unit/encoding/valid: expected success, got {e}") },
    { name := "unit/encoding/invalid-non-int-key" -- [B7]
      run := do
        expectAssembleInvOpcode "unit/encoding/invalid-non-int-key" (.dictSet false true false .add) },
    { name := "unit/decoder/chain" -- [B8]
      run := do
        let s : Slice := Slice.ofCell rawFamilyChain
        let s1 ← expectDecodeStep "unit/decoder/f432" s (.dictSet false false false .add) 16
        let s2 ← expectDecodeStep "unit/decoder/f433" s1 (.dictSet false false true .add) 16
        let s3 ← expectDecodeStep "unit/decoder/f434" s2 (.dictSet true false false .add) 16
        let s4 ← expectDecodeStep "unit/decoder/f435" s3 (.dictSet true false true .add) 16
        let s5 ← expectDecodeStep "unit/decoder/f436" s4 (.dictSet true true false .add) 16
        let _ ← expectDecodeStep "unit/decoder/f437" s5 (.dictSet true true true .add) 16
        pure () },
    { name := "unit/decoder/invalid-and-truncated" -- [B8]
      run := do
        expectDecodeInvOpcode "unit/decoder/f431" rawF431
        expectDecodeInvOpcode "unit/decoder/f438" rawF438
        expectDecodeInvOpcode "unit/decoder/truncated" rawTruncated8 },
    { name := "unit/runtime/insert-and-hit" -- [B2] [B3] [B4] [B5]
      run := do
        expectOkStack "unit/runtime/insert-empty"
          (runDictUAddDirect #[.slice valueB, intV 11, .null, intV 8])
          (expectedAddResult "unit/runtime/insert-empty" none 8 11 valueB)
        expectOkStack "unit/runtime/insert-single-key"
          (runDictUAddDirect #[.slice valueC, intV 11, .cell dictU8Single, intV 8])
          (expectedAddResult "unit/runtime/insert-single-key" (some dictU8Single) 8 11 valueC)
        expectOkStack "unit/runtime/hit"
          (runDictUAddDirect #[.slice valueD, intV 5, .cell dictU8Single, intV 8])
          (expectedAddResult "unit/runtime/hit" (some dictU8Single) 8 5 valueD)
        expectOkStack "unit/runtime/hit-n0"
          (runDictUAddDirect #[.slice valueA, intV 0, .cell dictZero, intV 0])
          (expectedAddResult "unit/runtime/hit-n0" (some dictZero) 0 0 valueA) },
    { name := "unit/runtime/underflow-type-range" -- [B2] [B3] [B4] [B5] [B6]
      run := do
        expectErr "unit/runtime/underflow-empty" (runDictUAddDirect #[]) .stkUnd
        expectErr "unit/runtime/underflow-one" (runDictUAddDirect #[.slice valueA]) .stkUnd
        expectErr "unit/runtime/underflow-two" (runDictUAddDirect #[.slice valueA, intV 1]) .stkUnd
        expectErr "unit/runtime/underflow-three" (runDictUAddDirect #[.slice valueA, intV 1, .cell dictU8Single]) .stkUnd
        expectErr "unit/runtime/type-dict-root" (runDictUAddDirect #[.slice valueA, intV 7, .tuple #[], intV 8]) .typeChk
        expectErr "unit/runtime/type-key" (runDictUAddDirect #[.slice valueA, .null, .cell dictU8Single, intV 8]) .typeChk
        expectErr "unit/runtime/type-value" (runDictUAddDirect #[.cell nonSliceValue, intV 7, .cell dictU8Single, intV 8]) .typeChk
        expectErr "unit/runtime/range-n-negative" (runDictUAddDirect #[.slice valueA, intV 7, .null, intV (-1)]) .rangeChk
        expectErr "unit/runtime/range-n-too-large" (runDictUAddDirect #[.slice valueA, intV 7, .null, intV 1024]) .rangeChk
        expectErr "unit/runtime/range-key-negative" (runDictUAddDirect #[.slice valueA, intV (-1), .null, intV 8]) .rangeChk
        expectErr "unit/runtime/range-key-too-large" (runDictUAddDirect #[.slice valueA, intV 256, .null, intV 8]) .rangeChk
        expectErr "unit/runtime/range-key-nan" (runDictUAddDirect #[.slice valueA, .int .nan, .null, intV 8]) .rangeChk },
    { name := "unit/runtime/malformed-root" -- [B6]
      run := do
        expectErr "unit/runtime/malformed-root" (runDictUAddDirect #[.slice valueA, intV 0, .cell malformedDict, intV 8]) .dictErr }
  ]
  oracle := #[
    mkCase "oracle/ok/insert/null/8" #[.slice valueA, intV 11, .null, intV 8], -- [B5]
    mkCase "oracle/ok/insert/null/4" #[.slice valueB, intV 11, .null, intV 4], -- [B5]
    mkCase "oracle/ok/insert/null/0" #[.slice valueC, intV 0, .null, intV 0], -- [B3][B5]
    mkCase "oracle/ok/insert/null/257" #[.slice valueD, intV 0, .null, intV 257], -- [B3][B5]
    mkCase "oracle/ok/insert-into-single" #[.slice valueC, intV 11, .cell dictU8Single, intV 8], -- [B5]
    mkCase "oracle/ok/insert-into-pair" #[.slice valueD, intV 77, .cell dictU8Pair, intV 8], -- [B5]
    mkCase "oracle/ok/insert-into-deep" #[.slice valueA, intV 2, .cell dictU8Deep, intV 8], -- [B5]
    mkCase "oracle/ok/hit" #[.slice valueA, intV 5, .cell dictU8Single, intV 8], -- [B5]
    mkCase "oracle/ok/hit/n0" #[.slice valueB, intV 0, .cell dictZero, intV 0], -- [B3][B5]
    mkCase "oracle/ok/hit/deep" #[.slice valueC, intV 200, .cell dictU8Deep, intV 8], -- [B5]
    mkCodeCase "oracle/decode/valid/f436" #[.slice valueA, intV 7, .null, intV 8] rawF436, -- [B8]
    mkCase "oracle/err/underflow-empty" #[], -- [B2]
    mkCase "oracle/err/underflow-one" #[.slice valueA], -- [B2]
    mkCase "oracle/err/underflow-two" #[.slice valueA, intV 7], -- [B2]
    mkCase "oracle/err/underflow-three" #[.slice valueA, intV 7, .null], -- [B2]
    mkCase "oracle/err/type/dict-root" #[.slice valueA, intV 7, .tuple #[], intV 8], -- [B3][B6]
    mkCase "oracle/err/type/key" #[.slice valueA, .null, .cell dictU8Single, intV 8], -- [B3]
    mkCase "oracle/err/type/value" #[.cell nonSliceValue, intV 7, .cell dictU8Single, intV 8], -- [B4]
    mkCase "oracle/err/range/n-negative" #[.slice valueA, intV 7, .null, intV (-1)], -- [B2]
    mkCase "oracle/err/range/n-too-large" #[.slice valueA, intV 7, .null, intV 1024], -- [B2]
    mkCase "oracle/err/range/n-nan" #[.slice valueA, intV 7, .null, .int .nan], -- [B2]
    mkCase "oracle/err/range/key-negative" #[.slice valueA, intV (-1), .null, intV 8], -- [B3]
    mkCase "oracle/err/range/key-too-large" #[.slice valueA, intV 256, .null, intV 8], -- [B3]
    mkCase "oracle/err/range/key-nan" #[.slice valueA, .int .nan, .null, intV 8], -- [B3]
    mkCase "oracle/err/range/key-nonzero-zero-width" #[.slice valueA, intV 1, .null, intV 0], -- [B3]
    mkCase "oracle/err/malformed-root" #[.slice valueA, intV 0, .cell malformedDict, intV 8], -- [B6]
    mkCodeCase "oracle/decode/f431" #[] rawF431, -- [B8]
    mkCodeCase "oracle/decode/f438" #[] rawF438, -- [B8]
    mkCodeCase "oracle/decode/truncated" #[] rawTruncated8, -- [B8]
    mkCase "oracle/gas/exact-hit" #[.slice valueB, intV 5, .cell dictU8Single, intV 8]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas), -- [B9]
    mkCase "oracle/gas/exact-minus-one-hit" #[.slice valueB, intV 5, .cell dictU8Single, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne), -- [B9]
    mkCase "oracle/gas/exact-insert-empty" #[.slice valueC, intV 11, .null, intV 8]
      (#[.pushInt (.num insertEmpty8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact insertEmpty8Gas), -- [B8][B9]
    mkCase "oracle/gas/exact-minus-one-insert-empty" #[.slice valueC, intV 11, .null, intV 8]
      (#[.pushInt (.num (insertEmpty8Gas - 1)), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne (insertEmpty8Gas - 1)), -- [B9]
    mkCase "oracle/gas/exact-insert-single" #[.slice valueD, intV 77, .cell dictU8Single, intV 8]
      (#[.pushInt (.num insertSingle8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact insertSingle8Gas), -- [B9]
    mkCase "oracle/gas/exact-minus-one-insert-single" #[.slice valueD, intV 77, .cell dictU8Single, intV 8]
      (#[.pushInt (.num (insertSingle8Gas - 1)), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne (insertSingle8Gas - 1)), -- [B9]
    mkCase "oracle/gas/exact-insert-triple" #[.slice valueA, intV 11, .cell dictU8Triple, intV 8]
      (#[.pushInt (.num insertTriple8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact insertTriple8Gas), -- [B9]
    mkCase "oracle/gas/exact-minus-one-insert-triple" #[.slice valueA, intV 11, .cell dictU8Triple, intV 8]
      (#[.pushInt (.num (insertTriple8Gas - 1)), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne (insertTriple8Gas - 1)) -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictUAddFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUADD
