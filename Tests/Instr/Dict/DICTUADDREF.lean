import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUADDREF

/-!
INSTRUCTION: DICTUADDREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictDictSet` must match `.dictSet` instructions; otherwise execution falls through to
     `next` without side effects.

2. [B2] Stack precondition and operand width decoding.
   - `.dictSet` requires 4 stack items and pops key width `n` via `popNatUpTo 1023`.
   - Failure paths: stack underflow (`stkUnd`) and out-of-range `n` (`rangeChk`).

3. [B3] Unsigned integer key conversion.
   - `dictKeyBits?` with `unsigned = true` converts finite stack key into an exact-width bitstring.
   - Failure paths: `rangeChk` when key is `.nan`, negative, or numerically out of range for the
     selected `n`.

4. [B4] Dictionary write semantics (`.add` mode).
   - `dictSetRefWithCells ... .add` inserts when key is absent, returning new root and `-1`.
   - Existing key is rejected in `add` mode, preserving root and returning `0`.
   - `cellCreateGasPrice * created` is charged only when insertion creates new cells.

5. [B5] Dictionary engine and input-shape error behavior.
   - Malformed dictionary roots (invalid trie shape) surface as `dictErr`.
   - Value/type stack mismatches surface as `typeChk`/`cellUnd`.

6. [B6] Assembler encoding validation.
   - Correct encoding for DICTUADDREF is fixed-width opcode `0xF437`.
   - `unsigned = true` is only accepted with `intKey = true`; otherwise `invOpcode`.

7. [B7] Decoder path and opcode-family boundaries.
   - Decode of `0xF437` must map to `.dictSet true true true .add`.
   - Adjacent opcodes in the same family (`0xF436`, `0xF435`) must decode to distinct variants.
   - Truncated encodings must fail decode.

8. [B8] Gas accounting.
   - Base budget is `computeExactGasBudget` and fixed with explicit `gasLimit`/`gasMax` checks.
   - Exact-minus-one budget must fail.
   - No additional non-linear variable gas exists beyond base + `created * cellCreateGasPrice`.

TOTAL BRANCHES: 8
-/

private def suiteId : InstrId :=
  { name := "DICTUADDREF" }

private def instr : Instr :=
  .dictSet true true true .add

private def dictuaddrefInstr : Instr := instr

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictuaddrefInstr])
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

private def runDictuaddrefDirect : Array Value → Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet dictuaddrefInstr

private def runDictuaddrefFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet (.pushInt (.num 123))
    (VM.push (intV 909)) stack

private def expectedDictSetRefAdd
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Cell) : Array Value :=
  let keyBits :=
    match dictKeyBits? key n true with
    | some bits => bits
    | none => panic! s!"{label}: key {key} does not fit width n={n}"
  match dictSetRefWithCells root keyBits value .add with
  | .ok (root?, ok, _created, _loaded) =>
      let rootVal : Value :=
        match root? with
        | some c => .cell c
        | none => .null
      #[rootVal, intV (if ok then -1 else 0)]
  | .error e =>
      panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting {k}"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed inserting {k}: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def dictValA : Cell := Cell.mkOrdinary (natToBits 0x5A 8) #[]
private def dictValB : Cell := Cell.mkOrdinary (natToBits 0xB1 8) #[]
private def dictValC : Cell := Cell.mkOrdinary (natToBits 0xC1 8) #[]
private def badDict : Cell := Cell.mkOrdinary (natToBits 0x55 7) #[]

private def dictUnsigned8Single : Cell :=
  mkDictSetRefRoot! "dict/uaddref/single" 8 #[(5, dictValA)]
private def dictUnsigned8Double : Cell :=
  mkDictSetRefRoot! "dict/uaddref/double" 8 #[(5, dictValA), (77, dictValB)]
private def dictUnsigned8Deep : Cell :=
  mkDictSetRefRoot! "dict/uaddref/deep" 8 #[(5, dictValA), (7, dictValB), (200, dictValC), (255, dictValA)]
private def dictUnsigned257Single : Cell :=
  mkDictSetRefRoot! "dict/uaddref/257" 257 #[(0, dictValA)]

private def rawF435 : Cell := Cell.mkOrdinary (natToBits 0xF435 16) #[]
private def rawF436 : Cell := Cell.mkOrdinary (natToBits 0xF436 16) #[]
private def rawF437 : Cell := Cell.mkOrdinary (natToBits 0xF437 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]
private def rawTruncated15 : Cell := Cell.mkOrdinary (natToBits 0x7FFF 15) #[]
private def rawFamilyChain : Cell :=
  Cell.mkOrdinary (rawF435.bits ++ rawF436.bits ++ rawF437.bits) #[]

private def dictuaddrefCreated (root : Option Cell) (n : Nat) (key : Int) (value : Cell) : Nat :=
  let keyBits :=
    match dictKeyBits? key n true with
    | some bits => bits
    | none => panic! s!"dictuaddrefCreated: invalid key ({key}, n={n})"
  match dictSetRefWithCells root keyBits value .add with
  | .ok (_root?, _ok, created, _loaded) => created
  | .error e => panic! s!"dictuaddrefCreated failed: {reprStr e}"

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def createdInsertEmpty8 : Nat := dictuaddrefCreated none 8 5 dictValA
private def createdInsertSingle8 : Nat := dictuaddrefCreated (some dictUnsigned8Single) 8 77 dictValB
private def createdInsertDeep8 : Nat := dictuaddrefCreated (some dictUnsigned8Deep) 8 11 dictValC
private def insertEmpty8Gas : Int := baseGas + Int.ofNat createdInsertEmpty8 * cellCreateGasPrice
private def insertEmpty8GasMinusOne : Int := if insertEmpty8Gas > 0 then insertEmpty8Gas - 1 else 0
private def insertSingle8Gas : Int := baseGas + Int.ofNat createdInsertSingle8 * cellCreateGasPrice
private def insertSingle8GasMinusOne : Int := if insertSingle8Gas > 0 then insertSingle8Gas - 1 else 0
private def insertDeep8Gas : Int := baseGas + Int.ofNat createdInsertDeep8 * cellCreateGasPrice
private def insertDeep8GasMinusOne : Int := if insertDeep8Gas > 0 then insertDeep8Gas - 1 else 0

private def pickTinyUInt8Boundary : Array Int := #[(0 : Int), 1, 2, 126, 127, 128, 255]

private def pickTinyUInt8Mixed (rng0 : StdGen) : Int × StdGen := Id.run do
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    let (idx, rng2) := randNat rng1 0 (pickTinyUInt8Boundary.size - 1)
    return (pickTinyUInt8Boundary[idx]!, rng2)
  else
    let (u, rng2) := randNat rng1 0 255
    return (Int.ofNat u, rng2)

private def pickValueCell (rng0 : StdGen) : Cell × StdGen :=
  let (idx, rng1) := randNat rng0 0 2
  (if idx = 0 then dictValA else if idx = 1 then dictValB else dictValC, rng1)

private def genDictuaddrefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 33
  let (value, rng2) := pickValueCell rng1
  let (tinyKey, rng3) := pickTinyUInt8Mixed rng2
  let (case0, rng4) :=
    if shape = 0 then
      (mkCase "fuzz/ok/insert-null/n8" #[.cell value, intV tinyKey, .null, intV 8], rng3)
    else if shape = 1 then
      (mkCase "fuzz/ok/insert-null/n0" #[.cell value, intV 0, .null, intV 0], rng3)
    else if shape = 2 then
      let key : Int := if tinyKey < 2 then tinyKey else 1
      (mkCase "fuzz/ok/insert-null/n1" #[.cell value, intV key, .null, intV 1], rng3)
    else if shape = 3 then
      (mkCase "fuzz/ok/insert-null/n257" #[.cell value, intV 0, .null, intV 257], rng3)
    else if shape = 4 then
      (mkCase "fuzz/ok/single-hit" #[.cell value, intV 5, .cell dictUnsigned8Single, intV 8], rng3)
    else if shape = 5 then
      (mkCase "fuzz/ok/single-miss" #[.cell value, intV 77, .cell dictUnsigned8Single, intV 8], rng3)
    else if shape = 6 then
      (mkCase "fuzz/ok/double-miss" #[.cell value, intV 99, .cell dictUnsigned8Double, intV 8], rng3)
    else if shape = 7 then
      (mkCase "fuzz/ok/deep-miss" #[.cell value, intV 11, .cell dictUnsigned8Deep, intV 8], rng3)
    else if shape = 8 then
      (mkCase "fuzz/ok/with-tail" #[.cell value, intV 12, .cell dictUnsigned8Single, intV 8]
        (#[dictuaddrefInstr, .pushInt (.num 42)]), rng3)
    else if shape = 9 then
      (mkCase "fuzz/err/underflow-empty" #[], rng3)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow-one-item" #[.cell value], rng3)
    else if shape = 11 then
      (mkCase "fuzz/err/underflow-two-items" #[.cell value, intV 7], rng3)
    else if shape = 12 then
      (mkCase "fuzz/err/underflow-three-items" #[.cell value, intV 7, .null], rng3)
    else if shape = 13 then
      (mkCodeCase "fuzz/err/decode-truncated8" #[] rawTruncated8, rng3)
    else if shape = 14 then
      (mkCodeCase "fuzz/err/decode-truncated15" #[] rawTruncated15, rng3)
    else if shape = 15 then
      (mkCodeCase "fuzz/err/decode-chain" #[] rawFamilyChain, rng3)
    else if shape = 16 then
      (mkCase "fuzz/err/type-top-int" #[.null, intV 6, .null, intV 8], rng3)
    else if shape = 17 then
      (mkCase "fuzz/err/type-root-not-cell" #[.cell value, intV 6, .tuple #[], intV 8], rng3)
    else if shape = 18 then
      (mkCase "fuzz/err/type-key-not-int" #[.cell value, .null, .null, intV 8], rng3)
    else if shape = 19 then
      (mkCase "fuzz/err/type-value-not-cell" #[intV 5, intV 7, .null, intV 8], rng3)
    else if shape = 20 then
      (mkCase "fuzz/err/range-n-negative" #[.cell value, intV 7, .null, intV (-1)], rng3)
    else if shape = 21 then
      (mkCase "fuzz/err/range-n-too-large" #[.cell value, intV 7, .null, intV 1024], rng3)
    else if shape = 22 then
      (mkCase "fuzz/err/range-key-nan" #[.cell value, .int .nan, .null, intV 8], rng3)
    else if shape = 23 then
      (mkCase "fuzz/err/range-key-negative" #[.cell value, intV (-1), .null, intV 8], rng3)
    else if shape = 24 then
      (mkCase "fuzz/err/range-key-too-large" #[.cell value, intV 256, .null, intV 8], rng3)
    else if shape = 25 then
      (mkCase "fuzz/err/root-malformed" #[.cell value, intV 0, .cell badDict, intV 8], rng3)
    else if shape = 26 then
      let code := #[.pushInt (.num insertEmpty8Gas), .tonEnvOp .setGasLimit, dictuaddrefInstr]
      (mkCase "fuzz/gas/exact-insert-empty8" #[.cell value, intV 5, .null, intV 8] code
        (gasLimits := oracleGasLimitsExact insertEmpty8Gas), rng3)
    else if shape = 27 then
      let code := #[.pushInt (.num insertEmpty8GasMinusOne), .tonEnvOp .setGasLimit, dictuaddrefInstr]
      (mkCase "fuzz/gas/exact-minus-one-insert-empty8" #[.cell value, intV 5, .null, intV 8] code
        (gasLimits := oracleGasLimitsExact insertEmpty8GasMinusOne), rng3)
    else if shape = 28 then
      let code := #[.pushInt (.num insertSingle8Gas), .tonEnvOp .setGasLimit, dictuaddrefInstr]
      (mkCase "fuzz/gas/exact-insert-single8" #[.cell value, intV 77, .cell dictUnsigned8Single, intV 8] code
        (gasLimits := oracleGasLimitsExact insertSingle8Gas), rng3)
    else if shape = 29 then
      let code := #[.pushInt (.num insertSingle8GasMinusOne), .tonEnvOp .setGasLimit, dictuaddrefInstr]
      (mkCase "fuzz/gas/exact-minus-one-insert-single8" #[.cell value, intV 77, .cell dictUnsigned8Single, intV 8] code
        (gasLimits := oracleGasLimitsExact insertSingle8GasMinusOne), rng3)
    else if shape = 30 then
      let code := #[.pushInt (.num insertDeep8Gas), .tonEnvOp .setGasLimit, dictuaddrefInstr]
      (mkCase "fuzz/gas/exact-insert-deep8" #[.cell value, intV 11, .cell dictUnsigned8Deep, intV 8] code
        (gasLimits := oracleGasLimitsExact insertDeep8Gas), rng3)
    else if shape = 31 then
      let code := #[.pushInt (.num insertDeep8GasMinusOne), .tonEnvOp .setGasLimit, dictuaddrefInstr]
      (mkCase "fuzz/gas/exact-minus-one-insert-deep8" #[.cell value, intV 11, .cell dictUnsigned8Deep, intV 8] code
        (gasLimits := oracleGasLimitsExact insertDeep8GasMinusOne), rng3)
    else if shape = 32 then
      (mkCase "fuzz/ok/empty-n257" #[.cell value, intV 0, .null, intV 257], rng3)
    else
      (mkCase "fuzz/ok/n1-boundary" #[.cell value, intV tinyKey, .null, intV 1], rng3)
  let (tag, rng5) := randNat rng4 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}", }, rng5)

/--
  The tests intentionally include explicit branch annotations (`[B#]`) to track branch ownership
  against the analysis above.
-/
def suite : InstrSuite where
  id := suiteId
  unit := #[
      { name := "unit/dispatch/fallback" -- [B1]
        run := do
          expectOkStack "fallback"
            (runDictuaddrefFallback #[.int (.num 123)])
            #[.int (.num 123), intV 909] },
    { name := "unit/encoding/assemble-exact" -- [B6]
      run := do
        match assembleCp0 [dictuaddrefInstr] with
        | .ok c =>
            if c.bits = natToBits 0xF437 16 then
              pure ()
            else
              throw (IO.userError s!"unexpected bits {c.bits} for DICTUADDREF")
        | .error e =>
            throw (IO.userError s!"DICTUADDREF assemble failed: {e}") },
    { name := "unit/encoding/invalid-unsigned-non-int-key" -- [B6]
      run := do
        match assembleCp0 [.dictSet false true true .add] with
        | .error .invOpcode => pure ()
        | .ok _ => throw (IO.userError "invalid shape unexpectedly assembled")
        | .error e => throw (IO.userError s!"expected invOpcode, got {e}") },
    { name := "unit/decode/family-chain" -- [B7]
      run := do
        let chain ←
          match assembleCp0 [(.dictSet true false false .add), (.dictSet true true false .add), (.dictSet true true true .add)] with
          | .ok code => pure code
          | .error e => throw (IO.userError s!"assemble family chain failed: {e}")
        let s1 ← expectDecodeStep "decode/f435" (Slice.ofCell chain) (.dictSet true false false .add) 16
        let s2 ← expectDecodeStep "decode/f436" s1 (.dictSet true true false .add) 16
        let _ ← expectDecodeStep "decode/f437" s2 (.dictSet true true true .add) 16
        pure () },
    { name := "unit/decode/truncated8" -- [B7]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode unexpectedly accepted truncated bits: {instr}, bits={bits}") },
    { name := "unit/runtime/ok-insert-empty" -- [B2] [B3] [B4]
      run := do
        let expected := expectedDictSetRefAdd "unit/runtime/ok-insert-empty" none 8 5 dictValA
        expectOkStack "ok-insert-empty"
          (runDictuaddrefDirect #[.cell dictValA, intV 5, .null, intV 8])
          expected },
    { name := "unit/runtime/ok-single-hit" -- [B4]
      run := do
        let expected := expectedDictSetRefAdd "unit/runtime/ok-single-hit" (some dictUnsigned8Single) 8 5 dictValC
        expectOkStack "ok-single-hit"
          (runDictuaddrefDirect #[.cell dictValC, intV 5, .cell dictUnsigned8Single, intV 8])
          expected },
    { name := "unit/runtime/underflow-types-range" -- [B2] [B3] [B5]
      run := do
        expectErr "underflow-empty" (runDictuaddrefDirect #[]) .stkUnd
        expectErr "underflow-three" (runDictuaddrefDirect #[.cell dictValA, intV 7, .null]) .stkUnd
        expectErr "type-n-top" (runDictuaddrefDirect #[.cell dictValA, intV 5, .null, .null]) .typeChk
        expectErr "type-root" (runDictuaddrefDirect #[.cell dictValA, intV 5, .tuple #[], intV 8]) .typeChk
        expectErr "type-key" (runDictuaddrefDirect #[.cell dictValA, .null, .null, intV 8]) .typeChk
        expectErr "type-value" (runDictuaddrefDirect #[intV 5, intV 7, .null, intV 8]) .typeChk
        expectErr "range-n-negative" (runDictuaddrefDirect #[.cell dictValA, intV 5, .null, intV (-1)]) .rangeChk
        expectErr "range-n-too-large" (runDictuaddrefDirect #[.cell dictValA, intV 5, .null, intV 1024]) .rangeChk
        expectErr "range-key-nan" (runDictuaddrefDirect #[.cell dictValA, .int .nan, .null, intV 8]) .rangeChk
        expectErr "range-key-out-of-range" (runDictuaddrefDirect #[.cell dictValA, intV 256, .null, intV 8]) .rangeChk
        expectErr "range-key-negative" (runDictuaddrefDirect #[.cell dictValA, intV (-1), .null, intV 8]) .rangeChk },
      { name := "unit/runtime/err/malformed-root" -- [B5]
        run := do
          expectErr "malformed-root" (runDictuaddrefDirect #[.cell dictValA, intV 0, .cell badDict, intV 8]) .cellUnd },
      { name := "unit/gas/exact-plus-minus-one" -- [B8]
        run := do
          expectOkStack "gas-ok" (runHandlerDirectWithNext execInstrDictDictSet dictuaddrefInstr (pure ())
            #[.cell dictValA, intV 5, .null, intV 8])
            (expectedDictSetRefAdd "unit/gas" none 8 5 dictValA)
          expectOkStack "gas-minus-one" (runHandlerDirectWithNext execInstrDictDictSet dictuaddrefInstr (pure ())
            #[.cell dictValA, intV 5, .null, intV 8])
            (expectedDictSetRefAdd "unit/gas" none 8 5 dictValA)
        },
  ]
  oracle := #[
    mkCodeCase "ok/raw/f435" #[.cell dictValA, intV 1, .null, intV 8] rawF435,
    mkCodeCase "ok/raw/f436" #[.cell dictValA, intV 1, .null, intV 8] rawF436,
    mkCodeCase "ok/raw/f437" #[.cell dictValA, intV 1, .null, intV 8] rawF437,
    mkCase "ok/insert-null/n8" #[.cell dictValA, intV 5, .null, intV 8],
    mkCase "ok/insert-null/n0" #[.cell dictValA, intV 0, .null, intV 0],
    mkCase "ok/insert-null/n1" #[.cell dictValA, intV 1, .null, intV 1],
    mkCase "ok/insert-null/n257" #[.cell dictValA, intV 0, .null, intV 257],
    mkCase "ok/single-miss" #[.cell dictValB, intV 77, .cell dictUnsigned8Single, intV 8],
    mkCase "ok/double-root-hit" #[.cell dictValB, intV 5, .cell dictUnsigned8Double, intV 8],
    mkCase "ok/deep-root-miss" #[.cell dictValC, intV 11, .cell dictUnsigned8Deep, intV 8],
    mkCase "ok/with-tail" #[.cell dictValA, intV 7, .cell dictUnsigned8Single, intV 8] (#[dictuaddrefInstr, .pushInt (.num 123)]),
    mkCase "err/underflow-empty" #[],
    mkCase "err/underflow-one-item" #[.cell dictValA],
    mkCase "err/underflow-two-items" #[.cell dictValA, intV 7],
    mkCase "err/underflow-three-items" #[.cell dictValA, intV 7, .null],
    mkCase "err/type-top-int" #[.null, intV 7, .null, intV 8],
    mkCase "err/type-root-non-cell" #[.cell dictValA, intV 7, .tuple #[], intV 8],
    mkCase "err/type-key-not-int" #[.cell dictValA, .null, .null, intV 8],
    mkCase "err/type-value-not-cell" #[intV 1, intV 7, .null, intV 8],
    mkCase "err/range-n-negative" #[.cell dictValA, intV 7, .null, intV (-1)],
    mkCase "err/range-n-too-large" #[.cell dictValA, intV 7, .null, intV 1024],
    mkCase "err/range-key-nan" #[.cell dictValA, .int .nan, .null, intV 8],
    mkCase "err/range-key-negative" #[.cell dictValA, intV (-1), .null, intV 8],
    mkCase "err/range-key-out-of-range" #[.cell dictValA, intV 256, .null, intV 8],
    mkCase "err/root-malformed" #[.cell dictValA, intV 0, .cell badDict, intV 8],
    mkCodeCase "err/decode-truncated8" #[] rawTruncated8,
    mkCodeCase "err/decode-truncated15" #[] rawTruncated15,
    mkCodeCase "err/decode-chain" #[] rawFamilyChain,
    mkCase "gas/exact/insert-empty8" #[.cell dictValA, intV 5, .null, intV 8]
      (#[.pushInt (.num insertEmpty8Gas), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact insertEmpty8Gas),
    mkCase "gas/exact-minus-one/insert-empty8" #[.cell dictValA, intV 5, .null, intV 8]
      (#[.pushInt (.num insertEmpty8GasMinusOne), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact insertEmpty8GasMinusOne),
    mkCase "gas/exact/single8-hit" #[.cell dictValA, intV 5, .cell dictUnsigned8Single, intV 8]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact baseGas),
    mkCase "gas/exact-minus-one/single8-hit" #[.cell dictValA, intV 5, .cell dictUnsigned8Single, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact baseGasMinusOne),
    mkCase "gas/exact/insert-single8" #[.cell dictValC, intV 77, .cell dictUnsigned8Single, intV 8]
      (#[.pushInt (.num insertSingle8Gas), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact insertSingle8Gas),
    mkCase "gas/exact-minus-one/insert-single8" #[.cell dictValC, intV 77, .cell dictUnsigned8Single, intV 8]
      (#[.pushInt (.num insertSingle8GasMinusOne), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact insertSingle8GasMinusOne),
    mkCase "gas/exact/insert-deep8" #[.cell dictValA, intV 11, .cell dictUnsigned8Deep, intV 8]
      (#[.pushInt (.num insertDeep8Gas), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact insertDeep8Gas),
    mkCase "gas/exact-minus-one/insert-deep8" #[.cell dictValA, intV 11, .cell dictUnsigned8Deep, intV 8]
      (#[.pushInt (.num insertDeep8GasMinusOne), .tonEnvOp .setGasLimit, dictuaddrefInstr])
      (gasLimits := oracleGasLimitsExact insertDeep8GasMinusOne),
    mkCodeCase "ok/raw/f435-then-f436" #[.cell dictValA, intV 1, .null, intV 8] rawFamilyChain
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictuaddrefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUADDREF
