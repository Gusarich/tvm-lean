import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREMMAXREF

/-!
INSTRUCTION: DICTREMMAXREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `execInstrDictDictGetMinMax` handles only `.dictGetMinMax` and delegates all
     other opcodes to `next`.

2. [B2] Runtime preamble / stack validation.
   - `checkUnderflow 2` requires both `n` and dictionary value.
   - `popNatUpTo 1023` validates key width and integer type for `n`.
   - `popMaybeCell` rejects non-cell/top values while allowing `null`.

3. [B3] Dictionary lookup miss paths.
   - Null/empty dictionary returns `(none, [])`.
   - Non-empty dictionary can still miss when all keys compare greater/less than requested
     minimum path for the chosen max/min direction.

4. [B4] Remove miss branch.
   - `remove` branch receives `dict = none` or `some root` with no match and pushes
     previous dictionary root (or `null`), then pushes `0`.

5. [B5] Remove hit path.
   - On hit, `dictDeleteWithCells` is called.
   - `oldVal` must be `some` on hit; `none` would raise `.dictErr` (defensive branch).
   - Removing the final element returns `null`; removing from a larger dictionary
     returns a new non-null root.
   - Delete path may create new cells and charge `created * cellCreateGasPrice`.

6. [B6] By-ref output materialization.
   - `byRef = true` requires returned `Slice` value to be exactly `0 bits + 1 ref`.
   - Any payload with bits or a wrong reference shape (e.g. plain slice value) raises `.dictErr`.

7. [B7] Non-int key reconstruction.
   - `intKey = false`, so key is reconstructed as a slice from `n` bits.
   - This path always consumes `cellCreateGasPrice` gas.

8. [B8] Assembler encoding.
   - `.dictGetMinMax 27` (opcode `0xF49B`) is valid.
   - Invalid args are rejected:
     - args in gap ranges (e.g. `24`) are `invOpcode`.
     - args > 31 are `rangeChk`.

9. [B9] Decoder behavior.
   - Family decode accepts neighboring opcodes `0xF49A..0xF49F` and maps gaps.
   - Truncated/gapped bitstreams are errors.

10. [B10] Gas accounting.
   - Base execution cost must succeed with exact gas.
   - Base-minus-one should fail (`out_of_gas`).
   - Remove-hit paths add `created * cellCreateGasPrice` surcharge.
   - Key reconstruction for non-int always adds one `cellCreateGasPrice` in addition to delete costs.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTREMMAXREF" }

private def instr : Instr :=
  .dictGetMinMax 27

private def maxKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n true true with
  | .ok (some (_, keyBits), _) => some keyBits
  | _ => none

private def dictDeleteCreated (root : Cell) (n : Nat) : Nat :=
  match maxKeyBits root n with
  | some keyBits =>
      match dictDeleteWithCells (some root) keyBits with
      | .ok (_, _, created, _) => created
      | .error _ => 0
  | none => 0

private def mkDictSetRefRootBits! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (keyBits, v) := entry
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting"
      | .error e =>
          panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def mkDictSetSliceRootBits! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (keyBits, v) := entry
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting"
      | .error e =>
          panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def asSlice (bits : BitString) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits #[])

private def asValueSlice (bits : BitString) : Value :=
  .slice (asSlice bits)

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC 8) #[]
private def badValueSlice : Slice := mkSliceFromBits (natToBits 0xF0 8)

private def dictNull : Value := .null

private def dictSingleRef8 : Cell :=
  mkDictSetRefRootBits! "dictSingleRef8" #[(natToBits 5 8, valueA)]
private def dictSingleRef8Alt : Cell :=
  mkDictSetRefRootBits! "dictSingleRef8Alt" #[(natToBits 128 8, valueA)]
private def dictTwoRef8 : Cell :=
  mkDictSetRefRootBits! "dictTwoRef8" #[(natToBits 0 8, valueA), (natToBits 255 8, valueB)]
private def dictTwoRef8AfterMax : Cell :=
  mkDictSetRefRootBits! "dictTwoRef8AfterMax" #[(natToBits 0 8, valueA)]
private def dictThreeRef8 : Cell :=
  mkDictSetRefRootBits! "dictThreeRef8" #[(natToBits 1 8, valueA), (natToBits 128 8, valueB), (natToBits 200 8, valueC)]
private def dictSingleRef0 : Cell :=
  mkDictSetRefRootBits! "dictSingleRef0" #[(#[], valueA)]
private def dictSingleRef257 : Cell :=
  mkDictSetRefRootBits! "dictSingleRef257" #[(natToBits 1 257, valueA)]
private def dictTwoRef257 : Cell :=
  mkDictSetRefRootBits! "dictTwoRef257" #[(natToBits 0 257, valueA), (natToBits ((1 <<< 256) + 1) 257, valueB)]
private def dictSingleRef1023 : Cell :=
  mkDictSetRefRootBits! "dictSingleRef1023" #[(natToBits 0 1023, valueA)]
private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRootBits! "dictSliceSingle8" #[(natToBits 5 8, badValueSlice)]
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def key8_0 : BitString := natToBits 0 8
private def key8_5 : BitString := natToBits 5 8
private def key8_128 : BitString := natToBits 128 8
private def key8_200 : BitString := natToBits 200 8
private def key8_255 : BitString := natToBits 255 8

private def key0_8 : BitString := key8_0
private def keySingleRef0 : BitString := #[]

private def twoRef8Created : Nat := dictDeleteCreated dictTwoRef8 8
private def twoRef8Penalty : Int := Int.ofNat twoRef8Created * cellCreateGasPrice
private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def removeTwoRef8Gas : Int := baseGas + twoRef8Penalty
private def removeTwoRef8GasMinusOne : Int := if removeTwoRef8Gas > 0 then removeTwoRef8Gas - 1 else 0

private def rawOpcodeF49A : Cell := Cell.mkOrdinary (natToBits 0xF49A 16) #[]
private def rawOpcodeF49B : Cell := Cell.mkOrdinary (natToBits 0xF49B 16) #[]
private def rawOpcodeF49C : Cell := Cell.mkOrdinary (natToBits 0xF49C 16) #[]
private def rawOpcodeF49D : Cell := Cell.mkOrdinary (natToBits 0xF49D 16) #[]
private def rawOpcodeF49E : Cell := Cell.mkOrdinary (natToBits 0xF49E 16) #[]
private def rawOpcodeF49F : Cell := Cell.mkOrdinary (natToBits 0xF49F 16) #[]
private def rawOpcodeF498 : Cell := Cell.mkOrdinary (natToBits 0xF498 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

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

private def mkRawCase
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCodeCase name stack code gasLimits fuel

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV 909)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

def genDictRemMaxRefCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/miss/null-n0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/miss/null-n8" #[dictNull, intV 8], rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/miss/null-n257" #[dictNull, intV 257], rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/miss/null-n1023" #[dictNull, intV 1023], rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/hit/single8" #[.cell dictSingleRef8, intV 8], rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/hit/single8-alt" (#[.cell dictSingleRef8Alt, intV 8]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/hit/two8" (#[.cell dictTwoRef8, intV 8]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/hit/three8" (#[.cell dictThreeRef8, intV 8]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/hit/single0" (#[.cell dictSingleRef0, intV 0]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/hit/single257" (#[.cell dictSingleRef257, intV 257]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/hit/two257" (#[.cell dictTwoRef257, intV 257]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/ok/hit/single1023" (#[.cell dictSingleRef1023, intV 1023]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/ok/miss/non-empty-width-mismatch" (#[.cell dictSingleRef8, intV 16]), rng1)
    else if shape = 13 then
      (mkRawCase "fuzz/raw/gap-f498" (#[.cell dictSingleRef8, intV 8]) rawOpcodeF498, rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/underflow-one" (#[dictNull]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-key-nan" ((#[Value.cell dictSingleRef8, Value.int .nan] : Array Value)), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-dict-noncell" (#[.tuple #[], intV 8]), rng1)
    else if shape = 18 then
      (mkRawCase "fuzz/err/type-n-null" (#[.cell dictSingleRef8, dictNull]) rawOpcodeF49B, rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/n-negative" (#[.cell dictSingleRef8, intV (-1)]), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/n-too-large" (#[.cell dictSingleRef8, intV 1024]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/malformed-root" (#[.cell malformedDict, intV 8]), rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/byref-value-slice" (#[.cell dictSliceSingle8, intV 8]), rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/base-exact" (#[dictNull, intV 8])
        (#[ 
          .pushInt (.num baseGas),
          .tonEnvOp .setGasLimit,
          instr
        ]) (oracleGasLimitsExact baseGas), rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/base-minus-one" (#[dictNull, intV 8])
        (#[ 
          .pushInt (.num baseGasMinusOne),
          .tonEnvOp .setGasLimit,
          instr
        ]) (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else
      (mkRawCase "fuzz/code/raw/f49b" (#[Value.cell dictSingleRef8, intV 8] : Array Value) rawOpcodeF49B, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback"
          (runDispatchFallback #[intV 1, intV 2])
          #[intV 1, intV 2, intV 909]
          },
    { name := "unit/opcode/assemble/exact" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF49B 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF49B bits, got {c.bits}")
        | .error e =>
          throw (IO.userError s!"assemble DICTREMMAXREF failed: {reprStr e}") },
    { name := "unit/opcode/assemble/reject-invalid-args" -- [B8]
      run := do
        match assembleCp0 [Instr.dictGetMinMax 24] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted gap arg=24")
        | .error _ => pure ()
        match assembleCp0 [Instr.dictGetMinMax 32] with
        | .ok _ => throw (IO.userError "assemble unexpectedly accepted out-of-range arg=32")
        | .error _ => pure () },
    { name := "unit/decode/branches" -- [B9]
      run := do
        let s0 : Slice := Slice.ofCell (Cell.mkOrdinary (rawOpcodeF49A.bits ++ rawOpcodeF49B.bits ++ rawOpcodeF49C.bits ++ rawOpcodeF49D.bits) #[])
        let s1 ← expectDecodeStep "decode/prev" s0 (.dictGetMinMax 26) 16
        let s2 ← expectDecodeStep "decode/self" s1 (.dictGetMinMax 27) 16
        let s3 ← expectDecodeStep "decode/next" s2 (.dictGetMinMax 28) 16
        let s4 ← expectDecodeStep "decode/nextnext" s3 (.dictGetMinMax 29) 16
        if s4.bitsRemaining + s4.refsRemaining != 0 then
          throw (IO.userError "decode did not consume full stream") },
    { name := "unit/decode/truncated-or-gap" -- [B9]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode")
        match decodeCp0WithBits (Slice.ofCell rawOpcodeF498) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted gap opcode") },
    { name := "unit/exec/miss-null" -- [B3][B4]
      run := do
        expectOkStack "miss-null-0"
          (runDirect #[dictNull, intV 0])
          #[dictNull, intV 0]
        expectOkStack "miss-null-8"
          (runDirect #[dictNull, intV 8])
          #[dictNull, intV 0]
        expectOkStack "miss-null-257"
          (runDirect #[dictNull, intV 257])
          #[dictNull, intV 0] },
    { name := "unit/exec/hit/single-8-removal" -- [B4][B5][B6][B7]
      run := do
        expectOkStack "single8"
          (runDirect #[.cell dictSingleRef8, intV 8 ])
          #[.null, .cell valueA, asValueSlice key8_5, intV (-1) ] },
    { name := "unit/exec/hit/single-8-alt-removal" -- [B4][B5][B6][B7]
      run := do
        expectOkStack "single8-alt"
          (runDirect #[.cell dictSingleRef8Alt, intV 8 ])
          #[.null, .cell valueA, asValueSlice key8_128, intV (-1) ] },
    { name := "unit/exec/hit/two8-removal" -- [B4][B5][B6][B7]
      run := do
        expectOkStack "two8"
          (runDirect #[.cell dictTwoRef8, intV 8 ])
          #[.cell dictTwoRef8AfterMax, .cell valueB, asValueSlice key8_255, intV (-1) ] },
    { name := "unit/exec/miss-non-empty-width-mismatch" -- [B3]
      run := do
        expectErr "non-empty-miss-16"
          (runDirect #[.cell dictTwoRef8, intV 16 ])
          .cellUnd },
    { name := "unit/exec/malformed-root" -- [B4][B5]
      run := do
        expectErr "malformed-root" (runDirect #[.cell malformedDict, intV 8 ]) .cellUnd },
    { name := "unit/exec/byref-shape-invalid" -- [B6]
      run := do
        expectErr "bad-ref-value" (runDirect #[.cell dictSliceSingle8, intV 8 ]) .dictErr },
    { name := "unit/exec/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "n-negative" (runDirect (#[.cell dictSingleRef8, intV (-1)])) .rangeChk
        expectErr "n-too-large" (runDirect (#[.cell dictSingleRef8, intV 1024])) .rangeChk },
    { name := "unit/exec/type-errors" -- [B2]
      run := do
        expectErr "key-top-int" (runDirect (#[.cell valueA, intV 8])) .dictErr
        expectErr "key-tuple" (runDirect (#[.tuple #[], intV 8])) .typeChk
        expectErr "dict-not-cell" (runDirect (#[.cont (.quit 0), intV 8])) .typeChk } ]
  oracle := #[
    mkCase "ok/miss/null/0" (#[dictNull, intV 0] : Array Value), -- [B3][B4]
    mkCase "ok/miss/null/8" (#[dictNull, intV 8] : Array Value), -- [B3][B4]
    mkCase "ok/miss/null/257" (#[dictNull, intV 257] : Array Value), -- [B3][B4]
    mkCase "ok/miss/null/1023" (#[dictNull, intV 1023] : Array Value), -- [B3][B4]
    mkCase "ok/miss/non-empty/n16" (#[Value.cell dictSingleRef8, intV 16] : Array Value), -- [B3][B4]
    mkCase "ok/miss/alt-width/n4" (#[Value.cell dictSingleRef257, intV 4] : Array Value), -- [B3][B4]
    mkCase "ok/hit/single8" (#[Value.cell dictSingleRef8, intV 8] : Array Value), -- [B4][B5][B6][B7]
    mkCase "ok/hit/single8alt" (#[Value.cell dictSingleRef8Alt, intV 8] : Array Value), -- [B4][B5][B6][B7]
    mkCase "ok/hit/two8" (#[Value.cell dictTwoRef8, intV 8] : Array Value), -- [B4][B5][B6][B7]
    mkCase "ok/hit/three8" (#[Value.cell dictThreeRef8, intV 8] : Array Value), -- [B4][B5][B6][B7]
    mkCase "ok/hit/single257" (#[Value.cell dictSingleRef257, intV 257] : Array Value), -- [B4][B5][B6][B7]
    mkCase "ok/hit/two257" (#[Value.cell dictTwoRef257, intV 257] : Array Value), -- [B4][B5][B6][B7]
    mkCase "ok/hit/single1023" (#[Value.cell dictSingleRef1023, intV 1023] : Array Value), -- [B4][B5][B7]
    mkCase "ok/hit/single0" (#[Value.cell dictSingleRef0, intV 0] : Array Value), -- [B4][B5][B6][B7]
    mkRawCase "ok/code/raw/f49b" (#[dictNull, intV 8]) rawOpcodeF49B, -- [B9]
    mkRawCase "ok/code/raw/f49a" (#[dictNull, intV 8]) rawOpcodeF49A, -- [B9]
    mkRawCase "ok/code/raw/f49c" (#[dictNull, intV 8]) rawOpcodeF49C, -- [B9]
    mkRawCase "ok/code/raw/f49d" (#[dictNull, intV 8]) rawOpcodeF49D, -- [B9]
    mkRawCase "ok/code/raw/f49f" (#[dictNull, intV 8]) rawOpcodeF49F, -- [B9]
    mkCase "ok/code/neighbors" (#[.cell dictSingleRef8, intV 8]) (#[.dictGetMinMax 27]), -- [B9]
    mkCase "err/underflow/empty" (#[]), -- [B2]
    mkCase "err/underflow/one-item" (#[dictNull]), -- [B2]
    mkCase "err/underflow/two-items" (#[dictNull, intV 8]), -- [B2]
    mkCase "err/type/top-int" (#[.cell valueA, intV 8]), -- [B2]
    mkCase "err/type/top-tuple" (#[.tuple #[], intV 8]), -- [B2]
    mkCase "err/type/dict-not-cell" (#[.cont (.quit 0), intV 8]), -- [B2]
    mkCase "err/type/key-non-int" (#[Value.cell dictSingleRef8, Value.slice badValueSlice]), -- [B2]
    mkCase "err/type/key-nan" (#[Value.cell dictSingleRef8, Value.int .nan]), -- [B2]
    mkCase "err/n/negative" (#[.cell dictSingleRef8, intV (-1)]), -- [B2]
    mkCase "err/n/too-large" (#[.cell dictSingleRef8, intV 1024]), -- [B2]
    mkCase "err/root-non-dict" (#[.cell malformedDict, intV 8]), -- [B4][B5]
    mkCase "err/bad-ref-value" (#[.cell dictSliceSingle8, intV 8]), -- [B6]
    mkRawCase "err/raw/f498-gap" (#[.cell dictSingleRef8, intV 8]) rawOpcodeF498, -- [B9]
    mkRawCase "err/raw/truncated8" #[] rawTruncated8, -- [B9]
    mkCase "gas/exact-miss" (#[dictNull, intV 8])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas), -- [B10]
    mkCase "gas/exact-minus-one-miss" (#[dictNull, intV 8])
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne), -- [B10]
    mkCase "gas/remove-two-ref8" (#[.cell dictTwoRef8, intV 8 ])
      (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwoRef8Gas), -- [B5][B10]
    mkCase "gas/remove-two-ref8-oog" (#[.cell dictTwoRef8, intV 8])
      (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwoRef8GasMinusOne), -- [B5][B10]
    mkCase "ok/code/raw/f49a-after" (#[.cell dictSingleRef8, intV 8]) (#[.dictGetMinMax 26]), -- [B9]
    mkRawCase "ok/code/raw/f49e" (#[.cell dictSingleRef8, intV 8]) rawOpcodeF49E -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictRemMaxRefCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREMMAXREF
