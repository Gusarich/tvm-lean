import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTADD

/-!
INSTRUCTION: DICTADD

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch
   - `.dictSet` is handled by `execInstrDictDictSet` and other instructions fall through via `next`.
2. [B2] Stack arity and order checks
   - The operation checks for 4 values first (`checkUnderflow 4`): `n`, `dict`, `key`, `value`.
3. [B3] `n` validation via `popNatUpTo 1023`
   - `n` must be an integer and in `[0, 1023]`; non-int, NaN, negative, or out-of-range raises.
4. [B4] Dictionary root shape
   - `popMaybeCell` accepts only `Value.cell` or `Value.null`; any other type raises `.typeChk`.
5. [B5] Key materialization (non-int key mode)
   - `popSlice` requires a slice key.
   - Insufficient key bits for width `n` raises `.cellUnd`.
6. [B6] Value materialization
   - value must be `Value.slice`; any other value raises `.typeChk`.
7. [B7] Dictionary add semantics
   - On missing key, runtime inserts and pushes `-1`.
   - On existing key, root is preserved and pushed with `0`.
8. [B8] Malformed root behavior
   - Invalid dictionary roots can throw `.dictErr`.
9. [B9] Assembler constraints
   - Canonical form is `.dictSet false false false .add` -> `0xF432`.
   - `.dictSet false true false .add` is invalid because `unsigned` is not defined for non-int keys.
10. [B10] Decoder behavior
   - `0xf432`..`0xf437` all decode to the add forms (flags: byRef/unsigned for signed variants).
   - Out-of-range neighbors and truncated opcode words must decode as `.invOpcode`.
11. [B11] Gas accounting
   - Base gas is from `computeExactGasBudget`.
   - Insertion branches add `created * cellCreateGasPrice`.
   - `exact` budgets succeed; `exact-1` budgets fail.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn].
-/

private def suiteId : InstrId :=
  { name := "DICTADD" }

private def instr : Instr :=
  .dictSet false false false .add

private def dispatchSentinel : Int := 13021

private def rawF431 : Cell := Cell.mkOrdinary (natToBits 0xf431 16) #[]
private def rawF432 : Cell := Cell.mkOrdinary (natToBits 0xf432 16) #[]
private def rawF433 : Cell := Cell.mkOrdinary (natToBits 0xf433 16) #[]
private def rawF434 : Cell := Cell.mkOrdinary (natToBits 0xf434 16) #[]
private def rawF435 : Cell := Cell.mkOrdinary (natToBits 0xf435 16) #[]
private def rawF436 : Cell := Cell.mkOrdinary (natToBits 0xf436 16) #[]
private def rawF437 : Cell := Cell.mkOrdinary (natToBits 0xf437 16) #[]
private def rawF438 : Cell := Cell.mkOrdinary (natToBits 0xf438 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def rawOpcodeChain : Cell :=
  Cell.mkOrdinary (natToBits 0xf432 16 ++ natToBits 0xf433 16 ++ natToBits 0xf434 16 ++ natToBits 0xf435 16 ++ natToBits 0xf436 16 ++ natToBits 0xf437 16) #[]

private def key8A : BitString := natToBits 0x55 8
private def key8B : BitString := natToBits 0xaa 8
private def key8C : BitString := natToBits 0x33 8
private def key8D : BitString := natToBits 0xcc 8
private def key8E : BitString := natToBits 0x17 8
private def key4 : BitString := natToBits 0b1010 4
private def key3 : BitString := natToBits 0b101 3
private def key1A : BitString := natToBits 0b1 1
private def key1B : BitString := natToBits 0b0 1
private def key0 : BitString := #[]
private def key16 : BitString := natToBits 0xbeef 16

private def slice8A : Slice := mkSliceFromBits key8A
private def slice8B : Slice := mkSliceFromBits key8B
private def slice8C : Slice := mkSliceFromBits key8C
private def slice8D : Slice := mkSliceFromBits key8D
private def slice8E : Slice := mkSliceFromBits key8E
private def slice4 : Slice := mkSliceFromBits key4
private def slice3 : Slice := mkSliceFromBits key3
private def slice1A : Slice := mkSliceFromBits key1A
private def slice1B : Slice := mkSliceFromBits key1B
private def slice0 : Slice := mkSliceFromBits key0
private def slice16 : Slice := mkSliceFromBits key16

private def valueA : Slice := mkSliceFromBits (natToBits 0xa1 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0xb2 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0xc3 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0xd4 8)

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1011 4) #[]

private def mkDictSetSliceRoot!
    (label : String)
    (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetSliceWithCells root k v .set with
      | .ok (some root', _, _, _) => root := root'
      | .ok (none, _, _, _) => panic! s!"{label}: unexpected empty root on set"
      | .error e => panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: no root built from empty entries"

private def dictCreatedOnAdd (root : Option Cell) (keyBits : BitString) (value : Slice) : Nat :=
  match dictSetSliceWithCells root keyBits value .add with
  | .ok (_, _, created, _) => created
  | .error e => panic! s!"dictSetSliceWithCells failed while computing created: {reprStr e}"

private def dictSingle8A : Cell := mkDictSetSliceRoot! "dict/single8A" #[(key8A, valueA)]
private def dictSingle8B : Cell := mkDictSetSliceRoot! "dict/single8B" #[(key8B, valueB)]
private def dictPair8 : Cell := mkDictSetSliceRoot! "dict/pair8" #[(key8A, valueA), (key8B, valueC)]
private def dictSingle16 : Cell := mkDictSetSliceRoot! "dict/single16" #[(key16, valueD)]
private def dictSingle1 : Cell := mkDictSetSliceRoot! "dict/single1" #[(key1A, valueA)]
private def dictSingle0 : Cell := mkDictSetSliceRoot! "dict/single0" #[(key0, valueD)]

private def insertRootEmpty8C : Cell := mkDictSetSliceRoot! "dict/insert-empty-8c" #[(key8C, valueC)]
private def insertRoot8AtoB : Cell := mkDictSetSliceRoot! "dict/insert-8a-8b" #[(key8A, valueA), (key8B, valueB)]
private def insertRoot1Ato1B : Cell := mkDictSetSliceRoot! "dict/insert-1a-1b" #[(key1A, valueA), (key1B, valueB)]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def missEmpty8Gas : Int :=
  baseGas + Int.ofNat (dictCreatedOnAdd none key8C valueC) * cellCreateGasPrice

private def missPair8Gas : Int :=
  baseGas + Int.ofNat (dictCreatedOnAdd (some dictSingle8A) key8B valueB) * cellCreateGasPrice

private def missSingle1Gas : Int :=
  baseGas + Int.ofNat (dictCreatedOnAdd (some dictSingle1) key1B valueB) * cellCreateGasPrice

private def missZeroGas : Int :=
  baseGas + Int.ofNat (dictCreatedOnAdd none key0 valueD) * cellCreateGasPrice

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

private def mkGasProgram (limit : Int) : Array Instr :=
  #[.pushInt (.num limit), .tonEnvOp .setGasLimit, instr]

private def runDictAddDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet (.pushInt (.num dispatchSentinel)) (pure ()) stack

private def runDictAddDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits} bits)")

private def expectAssembleInvOpcode (label : String) (code : Instr) : IO Unit := do
  match assembleCp0 [code] with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble failure")

private def genDictAddFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/err/underflow-one" ((#[] : Array Value) ++ [intV 8]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow-two" ((#[] : Array Value) ++ [intV 8, Value.slice slice8A]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/err/underflow-three" ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8A, Value.null]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/err/n-negative" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV (-1)]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/n-too-large" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV 1024]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/n-nan" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, Value.int .nan]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/dict-not-cell" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.tuple #[], intV 8]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/key-not-slice" ((#[] : Array Value) ++ [Value.slice valueA, intV 11, Value.cell dictSingle8A, intV 8]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/value-not-slice" ((#[] : Array Value) ++ [intV 11, Value.slice slice8A, Value.cell dictSingle8A, intV 8]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/key-too-short" ((#[] : Array Value) ++ [Value.slice valueB, Value.slice slice3, Value.cell dictSingle8A, intV 8]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/malformed-root" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell malformedDict, intV 8]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss/null/8" ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8D, Value.null, intV 8]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/ok/hit/single8" ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8A, Value.cell dictSingle8A, intV 8]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/ok/miss/insert-into-single" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8E, Value.cell dictSingle8A, intV 8]), rng1)
    else if shape = 15 then
      (mkCodeCase "fuzz/raw/f431" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF431, rng1)
    else if shape = 16 then
      (mkCodeCase "fuzz/raw/invalid-8-bit" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF4, rng1)
    else if shape = 17 then
      (mkCase "fuzz/gas/exact-hit" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8A, Value.cell dictSingle8A, intV 8])
        (mkGasProgram baseGas)
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 18 then
      (mkCase "fuzz/gas/exact-minus-one-hit" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8A, Value.cell dictSingle8A, intV 8])
        (mkGasProgram baseGasMinusOne)
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else
      (mkCase "fuzz/gas/insert-single" ((#[] : Array Value) ++ [Value.slice valueB, Value.slice slice8B, Value.cell dictSingle8A, intV 8])
        (mkGasProgram missPair8Gas)
        (oracleGasLimitsExact missPair8Gas), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st ←
          match runDictAddDispatchFallback ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV 8]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"unit/dispatch/fallback: {reprStr e}")
        if st == ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV 8, Value.int (.num dispatchSentinel)]) then
          pure ()
        else
          throw (IO.userError s!"dispatch/fallback: expected unchanged stack, got {reprStr st}") },
    { name := "unit/encode/valid" -- [B9]
      run := do
        match assembleCp0 [instr] with
        | .error e =>
            throw (IO.userError s!"unit/encode/valid: expected success, got {e}")
        | .ok code =>
            if code.bits != natToBits 0xf432 16 || !code.refs.isEmpty then
              throw (IO.userError "unit/encode/valid: unexpected encoding") },
    { name := "unit/encode/invalid-unsigned" -- [B9]
      run := do
        expectAssembleInvOpcode "unit/encode/invalid-unsigned" (.dictSet false true false .add) },
    { name := "unit/decode/chain" -- [B10]
      run := do
        let s : Slice := Slice.ofCell rawOpcodeChain
        let s1 ← expectDecodeStep "unit/decode/f432" s (.dictSet false false false .add) 16
        let s2 ← expectDecodeStep "unit/decode/f433" s1 (.dictSet false false true .add) 16
        let s3 ← expectDecodeStep "unit/decode/f434" s2 (.dictSet true false false .add) 16
        let s4 ← expectDecodeStep "unit/decode/f435" s3 (.dictSet true false true .add) 16
        let s5 ← expectDecodeStep "unit/decode/f436" s4 (.dictSet true true false .add) 16
        let _ ← expectDecodeStep "unit/decode/f437" s5 (.dictSet true true true .add) 16 },
    { name := "unit/decode/invalid-opcodes" -- [B10]
      run := do
        expectDecodeInvOpcode "unit/decode/f431" rawF431
        expectDecodeInvOpcode "unit/decode/f438" rawF438
        expectDecodeInvOpcode "unit/decode/truncated-8" rawF4 },
    { name := "unit/runtime/insert" -- [B7]
      run := do
        expectOkStack "unit/runtime/insert-empty-8" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8C, Value.null, intV 8]))
          ((#[] : Array Value) ++ [ Value.cell insertRootEmpty8C, intV (-1) ])
        expectOkStack "unit/runtime/insert-pair" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8B, Value.cell dictSingle8A, intV 8]))
          ((#[] : Array Value) ++ [ Value.cell insertRoot8AtoB, intV (-1) ]) },
    { name := "unit/runtime/hit" -- [B7]
      run := do
        expectOkStack "unit/runtime/hit-single8" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8A, Value.cell dictSingle8A, intV 8]))
          ((#[] : Array Value) ++ [ Value.cell dictSingle8A, intV 0 ])
        expectOkStack "unit/runtime/hit-single1" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice0, Value.cell dictSingle0, intV 0]))
          ((#[] : Array Value) ++ [ Value.cell dictSingle0, intV 0 ]) },
    { name := "unit/runtime/keep-tail" -- [B7]
      run := do
        let tail := intV 1001
        expectOkStack "unit/runtime/tail-preserved" (runDictAddDirect ((#[] : Array Value) ++ [tail, Value.slice valueA, Value.slice slice8D, Value.cell dictSingle8A, intV 8]))
          ((#[] : Array Value) ++ [tail, Value.cell insertRoot8AtoB, intV (-1)]) },
    { name := "unit/runtime/errors" -- [B2][B3][B4][B5][B6][B8]
      run := do
        expectErr "unit/err/underflow-empty" (runDictAddDirect #[]) .stkUnd
        expectErr "unit/err/underflow-one" (runDictAddDirect ((#[] : Array Value) ++ [intV 8])) .stkUnd
        expectErr "unit/err/underflow-two" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A])) .stkUnd
        expectErr "unit/err/underflow-three" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A])) .stkUnd
        expectErr "unit/err/n-not-int" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, Value.tuple #[]])) .typeChk
        expectErr "unit/err/n-nan" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, Value.int .nan])) .rangeChk
        expectErr "unit/err/n-negative" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV (-1)])) .rangeChk
        expectErr "unit/err/n-too-large" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV 1024])) .rangeChk
        expectErr "unit/err/dict-not-cell" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.tuple #[], intV 8])) .typeChk
        expectErr "unit/err/key-not-slice" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.int (.num 11), Value.cell dictSingle8A, intV 8])) .typeChk
        expectErr "unit/err/value-not-slice" (runDictAddDirect ((#[] : Array Value) ++ [Value.int (.num 11), Value.slice slice8A, Value.cell dictSingle8A, intV 8])) .typeChk
        expectErr "unit/err/key-too-short" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice3, Value.cell dictSingle8A, intV 8])) .cellUnd
        expectErr "unit/err/malformed-root" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell malformedDict, intV 8])) .dictErr },
    { name := "unit/runtime/gas-branch" -- [B11]
      run := do
        expectOkStack "unit/runtime/base-hit" (runDictAddDirect ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice1A, Value.cell dictSingle1, intV 1]))
          ((#[] : Array Value) ++ [ Value.cell dictSingle1, intV 0 ])
        let hitStack := ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice3, Value.null, intV 3])
        expectOkStack "unit/runtime/hit-empty-non-zero" (runDictAddDirect hitStack)
          ((#[] : Array Value) ++ [ Value.cell (mkDictSetSliceRoot! "dict/hit" #[(key3, valueA)]), intV (-1) ]) }
  ]
  oracle := #[
    -- [B7]
    mkCase "oracle/ok/miss-null-8-c" ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8C, Value.null, intV 8])
      (gasLimits := oracleGasLimitsExact missEmpty8Gas)
      |> (fun c => c),
    mkCase "oracle/ok/miss-null-8-d" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8D, Value.null, intV 8])
      (gasLimits := oracleGasLimitsExact missEmpty8Gas),
    mkCase "oracle/ok/miss-null-16" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice16, Value.null, intV 16]),
    mkCase "oracle/ok/miss-null-1" ((#[] : Array Value) ++ [Value.slice valueB, Value.slice slice1B, Value.null, intV 1]),
    mkCase "oracle/ok/miss-null-0" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice0, Value.null, intV 0])
      (gasLimits := oracleGasLimitsExact missZeroGas),
    -- [B7]
    mkCase "oracle/ok/hit-single8-a" ((#[] : Array Value) ++ [Value.slice valueB, Value.slice slice8A, Value.cell dictSingle8A, intV 8]),
    mkCase "oracle/ok/hit-single8-b" ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8B, Value.cell dictSingle8B, intV 8]),
    mkCase "oracle/ok/hit-pair-a" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8A, Value.cell dictPair8, intV 8]),
    mkCase "oracle/ok/hit-pair-b" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8B, Value.cell dictPair8, intV 8]),
    mkCase "oracle/ok/hit-single-0" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice0, Value.cell dictSingle0, intV 0]),
    mkCase "oracle/ok/miss-into-single" ((#[] : Array Value) ++ [Value.slice valueC, Value.slice slice8E, Value.cell dictSingle8A, intV 8]),
    mkCase "oracle/ok/miss-into-pair" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8E, Value.cell dictPair8, intV 8]),
    -- [B2][B3][B4][B5][B6][B8]
    mkCase "oracle/err/underflow-empty" #[],
    mkCase "oracle/err/underflow-one" ((#[] : Array Value) ++ [intV 8]),
    mkCase "oracle/err/underflow-two" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A]),
    mkCase "oracle/err/underflow-three" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A]),
    mkCase "oracle/err/n-not-int" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, Value.tuple #[]]),
    mkCase "oracle/err/n-nan" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, Value.int .nan]),
    mkCase "oracle/err/n-negative" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV (-1)]),
    mkCase "oracle/err/n-too-large" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell dictSingle8A, intV 1024]),
    mkCase "oracle/err/dict-not-cell" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.builder Builder.empty, intV 8]),
    mkCase "oracle/err/key-not-slice" ((#[] : Array Value) ++ [Value.slice valueA, Value.int (.num 11), Value.cell dictSingle8A, intV 8]),
    mkCase "oracle/err/value-not-slice" ((#[] : Array Value) ++ [Value.int (.num 11), Value.slice slice8A, Value.cell dictSingle8A, intV 8]),
    mkCase "oracle/err/key-too-short" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice3, Value.cell dictSingle8A, intV 8]),
    mkCase "oracle/err/malformed-root" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.cell malformedDict, intV 8]),
    -- [B10]
    mkCodeCase "oracle/dec/f432" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF432,
    mkCodeCase "oracle/dec/f433" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF433,
    mkCodeCase "oracle/dec/f434" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF434,
    mkCodeCase "oracle/dec/f435" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF435,
    mkCodeCase "oracle/dec/f436" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF436,
    mkCodeCase "oracle/dec/f437" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF437,
    mkCodeCase "oracle/dec/f431-invalid" ((#[] : Array Value) ++ [Value.slice valueA, Value.slice slice8A, Value.null, intV 8]) rawF431,
    mkCodeCase "oracle/dec/invalid-truncated" #[] rawF4,
    -- [B10]
    mkCase "oracle/gas/exact/hit" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8A, Value.cell dictSingle8A, intV 8])
      (mkGasProgram baseGas)
      (oracleGasLimitsExact baseGas),
    mkCase "oracle/gas/exact-minus-one/hit" ((#[] : Array Value) ++ [Value.slice valueD, Value.slice slice8A, Value.cell dictSingle8A, intV 8])
      (mkGasProgram baseGasMinusOne)
      (oracleGasLimitsExactMinusOne baseGasMinusOne),
    mkCase "oracle/gas/exact/miss-pair" ((#[] : Array Value) ++ [Value.slice valueB, Value.slice slice8B, Value.cell dictSingle8A, intV 8])
      (mkGasProgram missPair8Gas)
      (oracleGasLimitsExact missPair8Gas),
    mkCase "oracle/gas/exact-minus-one/miss-pair" ((#[] : Array Value) ++ [Value.slice valueB, Value.slice slice8B, Value.cell dictSingle8A, intV 8])
      (mkGasProgram (if missPair8Gas > 0 then missPair8Gas - 1 else 0))
      (oracleGasLimitsExactMinusOne (if missPair8Gas > 0 then missPair8Gas - 1 else 0)),
    mkCase "oracle/gas/exact/miss-1bit" ((#[] : Array Value) ++ [Value.slice valueB, Value.slice slice1B, Value.cell dictSingle1, intV 1])
      (mkGasProgram missSingle1Gas)
      (oracleGasLimitsExact missSingle1Gas)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictAddFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTADD
