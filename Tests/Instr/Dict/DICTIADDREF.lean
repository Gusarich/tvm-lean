import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIADDREF

/-!
INSTRUCTION: DICTIADDREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictDictSet` matches only `.dictSet` instructions; non-dict-set instructions must
     continue to the next handler via `next`.

2. [B2] Stack precondition + immediate decoding.
   - Four stack pops are required: value ref, key int, maybe dictionary root, and key width `n`.
   - Stack underflow (`stkUnd`) and invalid `n` via `popNatUpTo 1023` form distinct branches.

3. [B3] Integer-key shaping/validation.
   - `popInt` type and `.nan` handling.
   - Signed key bounds are enforced by `dictKeyBits?` and map to `.rangeChk`.

4. [B4] Dict add semantics.
   - `.add` mode uses `dictSetRefWithCells ... .add`.
   - Insert-path: new root produced, pushed bool `-1`.
   - Duplicate-key path: existing root preserved, pushed bool `0`.
   - Returned `created` cells add to gas with `cellCreateGasPrice`.

5. [B5] Dictionary-engine error handling.
   - Malformed dictionary shapes and unsupported internal paths are surfaced as dictionary errors.

6. [B6] Encoder branch.
   - Canonical DICTIADDREF is `0xF435`.
   - Invalid non-int unsigned shape must be `.invOpcode`.
   - Neighboring family opcodes (`0xF434`..`0xF437`) must be distinguishable by decode/assemble.

7. [B7] Decoder branch.
   - `0xF435` decodes to DICTIADDREF and adjacent opcodes decode to corresponding `.dictSet` variants.
   - Truncated prefix fails decode.

8. [B8] Gas branch.
   - Base budget + dynamic `created * cellCreateGasPrice` must both be validated with exact and off-by-one tests.

TOTAL BRANCHES: 8
-/

private def suiteId : InstrId :=
  { name := "DICTIADDREF" }

private def instr : Instr :=
  .dictSet true false true .add

private def dictiaddrefInstr : Instr := instr

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictiaddrefInstr])
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

private def runDictiaddrefDirect : Array Value → Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet dictiaddrefInstr

private def runDictiaddrefFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet (.pushInt (.num 123))
    (VM.push (intV 909)) stack

private def expectedDictSetRefAdd
    (label : String)
    (root : Option Cell)
    (n : Nat)
    (key : Int)
    (value : Cell) : Array Value :=
  let keyBits :=
    match dictKeyBits? key n false with
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
        match dictKeyBits? k n false with
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
private def dictValC : Cell := Cell.mkOrdinary (natToBits 0xC1 8) #[Cell.empty]
private def badDict : Cell := Cell.mkOrdinary (natToBits 0x55 7) #[]

private def dictSigned8Single : Cell :=
  mkDictSetRefRoot! "dict/iaddref/single" 8 #[(5, dictValA)]
private def dictSigned8Double : Cell :=
  mkDictSetRefRoot! "dict/iaddref/double" 8 #[(5, dictValA), (-5, dictValB)]
private def dictSigned8Deep : Cell :=
  mkDictSetRefRoot! "dict/iaddref/deep" 8 #[(5, dictValA), (-5, dictValB), (7, dictValC), (-1, dictValA)]
private def dictSigned257Single : Cell :=
  mkDictSetRefRoot! "dict/iaddref/257" 257 #[(0, dictValA)]

private def rawF434 : Cell := Cell.mkOrdinary (natToBits 0xF434 16) #[]
private def rawF435 : Cell := Cell.mkOrdinary (natToBits 0xF435 16) #[]
private def rawF436 : Cell := Cell.mkOrdinary (natToBits 0xF436 16) #[]
private def rawF437 : Cell := Cell.mkOrdinary (natToBits 0xF437 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]
private def rawTruncated15 : Cell := Cell.mkOrdinary (natToBits 0x7FFF 15) #[]
private def rawFamilyChain : Cell :=
  Cell.mkOrdinary (rawF434.bits ++ rawF435.bits ++ rawF436.bits ++ rawF437.bits) #[]

private def dictiaddrefCreated (root : Option Cell) (n : Nat) (key : Int) (value : Cell) : Nat :=
  let keyBits :=
    match dictKeyBits? key n false with
    | some bits => bits
    | none => panic! s!"dictiaddrefCreated: invalid key ({key}, n={n})"
  match dictSetRefWithCells root keyBits value .add with
  | .ok (_root?, _ok, created, _loaded) => created
  | .error e => panic! s!"dictiaddrefCreated failed: {reprStr e}"

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def createdInsertEmpty8 : Nat := dictiaddrefCreated none 8 5 dictValA
private def createdInsertSingle8 : Nat := dictiaddrefCreated (some dictSigned8Single) 8 77 dictValB
private def createdInsertDeep8 : Nat := dictiaddrefCreated (some dictSigned8Deep) 8 11 dictValC
private def insertEmpty8Gas : Int := baseGas + Int.ofNat createdInsertEmpty8 * cellCreateGasPrice
private def insertEmpty8GasMinusOne : Int := if insertEmpty8Gas > 0 then insertEmpty8Gas - 1 else 0
private def insertSingle8Gas : Int := baseGas + Int.ofNat createdInsertSingle8 * cellCreateGasPrice
private def insertSingle8GasMinusOne : Int := if insertSingle8Gas > 0 then insertSingle8Gas - 1 else 0
private def insertDeep8Gas : Int := baseGas + Int.ofNat createdInsertDeep8 * cellCreateGasPrice
private def insertDeep8GasMinusOne : Int := if insertDeep8Gas > 0 then insertDeep8Gas - 1 else 0

private def pickFuzzValue (rng0 : StdGen) : Cell × StdGen :=
  let (idx, rng1) := randNat rng0 0 2
  (if idx = 0 then dictValA else if idx = 1 then dictValB else dictValC, rng1)

private def genDictiaddrefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (value, rng2) := pickFuzzValue rng1
  let (tinyKey, rng3) := pickTinyInt8Mixed rng2
  let (case0, rng4) :=
    if shape = 0 then
      (mkCase "fuzz/ok/insert-null/n8" #[.cell value, intV tinyKey, .null, intV 8], rng3)
    else if shape = 1 then
      (mkCase "fuzz/ok/insert-null/n0" #[.cell value, intV 0, .null, intV 0], rng3)
    else if shape = 2 then
      let (key, rng4a) :=
        let (flip, rng4b) := randBool rng3
        (if flip then 0 else (-1), rng4b)
      (mkCase "fuzz/ok/insert-null/n1" #[.cell value, intV key, .null, intV 1], rng4a)
    else if shape = 3 then
      (mkCase "fuzz/ok/insert-null/n257" #[.cell value, intV 0, .null, intV 257], rng3)
    else if shape = 4 then
      (mkCase "fuzz/ok/single-hit" #[.cell value, intV 5, .cell dictSigned8Single, intV 8], rng3)
    else if shape = 5 then
      (mkCase "fuzz/ok/single-miss" #[.cell value, intV 77, .cell dictSigned8Single, intV 8], rng3)
    else if shape = 6 then
      (mkCase "fuzz/ok/double-miss" #[.cell value, intV 99, .cell dictSigned8Double, intV 8], rng3)
    else if shape = 7 then
      (mkCase "fuzz/ok/deep-miss" #[.cell value, intV 11, .cell dictSigned8Deep, intV 8], rng3)
    else if shape = 8 then
      (mkCase "fuzz/ok/with-tail" #[.cell value, intV 12, .cell dictSigned8Single, intV 8] (#[dictiaddrefInstr, .pushInt (.num 42)]), rng3)
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
      (mkCodeCase "fuzz/err/decode-raw-chain" #[] rawFamilyChain, rng3)
    else if shape = 16 then
      (mkCase "fuzz/err/type-top-int" #[.null, intV 6, .null, intV 8], rng3)
    else if shape = 17 then
      (mkCase "fuzz/err/type-root-not-cell" #[.cell value, intV 6, .tuple #[], intV 8], rng3)
    else if shape = 18 then
      (mkCase "fuzz/err/type-key-not-int" #[.cell value, .null, .null, intV 8], rng3)
    else if shape = 19 then
      (mkCase "fuzz/err/type-value-not-cell" #[intV 9, intV 6, .null, intV 8], rng3)
    else if shape = 20 then
      (mkCase "fuzz/err/range-n-negative" #[.cell value, intV 7, .null, intV (-1)], rng3)
    else if shape = 21 then
      (mkCase "fuzz/err/range-n-too-large" #[.cell value, intV 7, .null, intV 1024], rng3)
    else if shape = 22 then
      (mkCase "fuzz/err/range-key-nan" #[.cell dictValA, .int .nan, .null, intV 8], rng3)
    else if shape = 23 then
      (mkCase "fuzz/err/range-key-too-large" #[.cell value, intV 256, .null, intV 8], rng3)
    else if shape = 24 then
      (mkCase "fuzz/err/malformed-root" #[.cell value, intV 0, .cell badDict, intV 8], rng3)
    else if shape = 25 then
      let code := #[.pushInt (.num insertEmpty8Gas), .tonEnvOp .setGasLimit, dictiaddrefInstr]
      (mkCase "fuzz/gas/exact-insert-empty8" #[.cell value, intV 5, .null, intV 8] code
        (gasLimits := oracleGasLimitsExact insertEmpty8Gas), rng3)
    else if shape = 26 then
      let code := #[.pushInt (.num insertEmpty8GasMinusOne), .tonEnvOp .setGasLimit, dictiaddrefInstr]
      (mkCase "fuzz/gas/exact-minus-one-insert-empty8" #[.cell value, intV 5, .null, intV 8] code
        (gasLimits := oracleGasLimitsExact insertEmpty8GasMinusOne), rng3)
    else
      let code := #[.pushInt (.num insertSingle8Gas), .tonEnvOp .setGasLimit, dictiaddrefInstr]
      (mkCase "fuzz/gas/exact-insert-single8" #[.cell value, intV 77, .cell dictSigned8Single, intV 8] code
        (gasLimits := oracleGasLimitsExact insertSingle8Gas), rng3)
  let (tag, rng5) := randNat rng4 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "fallback"
          (runDictiaddrefFallback #[])
          #[intV 909] },
    { name := "unit/encoding/assemble-exact" -- [B6]
      run := do
        match assembleCp0 [dictiaddrefInstr] with
        | .ok c =>
            if c.bits = natToBits 0xF435 16 then
              pure ()
            else
              throw (IO.userError s!"unexpected bits {c.bits} for DICTIADDREF")
        | .error e =>
            throw (IO.userError s!"DICTIADDREF assemble failed: {e}") },
    { name := "unit/encoding/invalid-unsigned-non-int" -- [B6]
      run := do
        match assembleCp0 [.dictSet false true true .add] with
        | .error .invOpcode => pure ()
        | .ok _ => throw (IO.userError "invalid shape unexpectedly assembled")
        | .error e => throw (IO.userError s!"expected invOpcode, got {e}") },
    { name := "unit/decode/family-chain" -- [B7]
      run := do
        let chain ←
          match assembleCp0 [(.dictSet true false false .add), (.dictSet true false true .add), (.dictSet true true false .add), (.dictSet true true true .add)] with
          | .ok code => pure code
          | .error e => throw (IO.userError s!"assemble family chain failed: {e}")
        let s1 ← expectDecodeStep "decode/f434" (Slice.ofCell chain) (.dictSet true false false .add) 16
        let s2 ← expectDecodeStep "decode/f435" s1 (.dictSet true false true .add) 16
        let s3 ← expectDecodeStep "decode/f436" s2 (.dictSet true true false .add) 16
        let _ ← expectDecodeStep "decode/f437" s3 (.dictSet true true true .add) 16
        pure () },
    { name := "unit/decode/truncated8" -- [B8]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode unexpectedly accepted truncated bits: {instr}, bits={bits}") },
    { name := "unit/runtime/ok-insert-empty" -- [B2][B3][B4]
      run := do
        let expected := expectedDictSetRefAdd "unit/runtime/ok-insert-empty" none 8 5 dictValA
        expectOkStack "ok-insert-empty"
          (runDictiaddrefDirect #[.cell dictValA, intV 5, .null, intV 8])
          expected },
    { name := "unit/runtime/ok-hit-root" -- [B4]
      run := do
        let expected := expectedDictSetRefAdd "unit/runtime/ok-hit-root" (some dictSigned8Single) 8 5 dictValC
        expectOkStack "ok-hit-root"
          (runDictiaddrefDirect #[.cell dictValC, intV 5, .cell dictSigned8Single, intV 8])
          expected },
    { name := "unit/runtime/underflow-types-range"
      run := do
        expectErr "underflow-empty" (runDictiaddrefDirect #[]) .stkUnd
        expectErr "underflow-three" (runDictiaddrefDirect #[.cell dictValA, intV 8, .null]) .stkUnd
        expectErr "type-n-top" (runDictiaddrefDirect #[.cell dictValA, intV 5, .null, .null]) .typeChk
        expectErr "type-root" (runDictiaddrefDirect #[.cell dictValA, intV 5, .tuple #[], intV 8]) .typeChk
        expectErr "type-key" (runDictiaddrefDirect #[.cell dictValA, .null, .null, intV 8]) .typeChk
        expectErr "type-value" (runDictiaddrefDirect #[intV 5, intV 7, .null, intV 8]) .typeChk
        expectErr "range-n-negative" (runDictiaddrefDirect #[.cell dictValA, intV 5, .null, intV (-1)]) .rangeChk
        expectErr "range-n-too-large" (runDictiaddrefDirect #[.cell dictValA, intV 5, .null, intV 1024]) .rangeChk
        expectErr "range-key-nan" (runDictiaddrefDirect #[.cell dictValA, .int .nan, .null, intV 8]) .rangeChk
        expectErr "range-key-out-of-range" (runDictiaddrefDirect #[.cell dictValA, intV 256, .null, intV 8]) .rangeChk }
  ]
  oracle := #[
    mkCodeCase "ok/raw/f435" #[.cell dictValA, intV 1, .null, intV 8] rawF435
    ,
    mkCodeCase "ok/raw/f434" #[.cell dictValA, intV 1, .null, intV 8] rawF434
    ,
    mkCodeCase "ok/raw/f436" #[.cell dictValA, intV 1, .null, intV 8] rawF436
    ,
    mkCodeCase "ok/raw/f437" #[.cell dictValA, intV 1, .null, intV 8] rawF437
    ,
    mkCase "ok/insert-null/n8" #[.cell dictValA, intV 5, .null, intV 8]
    ,
    mkCase "ok/insert-null/n0" #[.cell dictValA, intV 0, .null, intV 0]
    ,
    mkCase "ok/insert-null/n1" #[.cell dictValA, intV (-1), .null, intV 1]
    ,
    mkCase "ok/insert-null/n257" #[.cell dictValA, intV 0, .null, intV 257]
    ,
    mkCase "ok/single-miss" #[.cell dictValB, intV 77, .cell dictSigned8Single, intV 8]
    ,
    mkCase "ok/double-root-hit" #[.cell dictValB, intV 5, .cell dictSigned8Double, intV 8]
    ,
    mkCase "ok/deep-root-miss" #[.cell dictValC, intV 11, .cell dictSigned8Deep, intV 8]
    ,
    mkCase "ok/with-tail" #[.cell dictValA, intV 7, .cell dictSigned8Single, intV 8] (#[dictiaddrefInstr, .pushInt (.num 123)])
    ,
    mkCase "err/underflow-empty" #[]
    ,
    mkCase "err/underflow-one-item" #[.cell dictValA]
    ,
    mkCase "err/underflow-two-items" #[.cell dictValA, intV 7]
    ,
    mkCase "err/type-top-int" #[.null, intV 7, .null, intV 8]
    ,
    mkCase "err/type-root-non-cell" #[.cell dictValA, intV 7, .tuple #[], intV 8]
    ,
    mkCase "err/type-key-not-int" #[.cell dictValA, .null, .null, intV 8]
    ,
    mkCase "err/type-value-not-cell" #[intV 1, intV 7, .null, intV 8]
    ,
    mkCase "err/range-n-negative" #[.cell dictValA, intV 7, .null, intV (-1)]
    ,
    mkCase "err/range-n-too-large" #[.cell dictValA, intV 7, .null, intV 1024]
    ,
    mkCase "err/range-key-nan" #[.cell dictValA, .int .nan, .null, intV 8]
    ,
    mkCase "err/range-key-out-of-range" #[.cell dictValA, intV 256, .null, intV 8]
    ,
    mkCase "err/range-key-too-small" #[.cell dictValA, intV (-129), .null, intV 8]
    ,
    mkCase "err/root-malformed" #[.cell dictValA, intV 0, .cell badDict, intV 8]
    ,
    mkCodeCase "err/decode-truncated8" #[] rawTruncated8
    ,
    mkCodeCase "err/decode-truncated15" #[] rawTruncated15
    ,
    mkCodeCase "err/decode-chain" #[] rawFamilyChain
    ,
    mkCase "gas/exact/insert-empty" #[.cell dictValA, intV 5, .null, intV 8] (#[.pushInt (.num insertEmpty8Gas), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact insertEmpty8Gas)
    ,
    mkCase "gas/exact-minus-one/insert-empty" #[.cell dictValA, intV 5, .null, intV 8] (#[.pushInt (.num insertEmpty8GasMinusOne), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact insertEmpty8GasMinusOne)
    ,
    mkCase "gas/exact/single-hit" #[.cell dictValA, intV 5, .cell dictSigned8Single, intV 8] (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact baseGas)
    ,
    mkCase "gas/exact-minus-one/single-hit" #[.cell dictValA, intV 5, .cell dictSigned8Single, intV 8] (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact baseGasMinusOne)
    ,
    mkCase "gas/exact/insert-single8" #[.cell dictValC, intV 77, .cell dictSigned8Single, intV 8] (#[.pushInt (.num insertSingle8Gas), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact insertSingle8Gas)
    ,
    mkCase "gas/exact-minus-one/insert-single8" #[.cell dictValC, intV 77, .cell dictSigned8Single, intV 8] (#[.pushInt (.num insertSingle8GasMinusOne), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact insertSingle8GasMinusOne)
    ,
    mkCase "gas/exact/insert-deep8" #[.cell dictValA, intV 11, .cell dictSigned8Deep, intV 8] (#[.pushInt (.num insertDeep8Gas), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact insertDeep8Gas)
    ,
    mkCase "gas/exact-minus-one/insert-deep8" #[.cell dictValA, intV 11, .cell dictSigned8Deep, intV 8] (#[.pushInt (.num insertDeep8GasMinusOne), .tonEnvOp .setGasLimit, dictiaddrefInstr])
      (oracleGasLimitsExact insertDeep8GasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictiaddrefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIADDREF
