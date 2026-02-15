import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREMMAX

/-!
INSTRUCTION: DICTREMMAX

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictDictGetMinMax` matches only `.dictGetMinMax` and forwards all other
     opcodes to `next`.

2. [B2] Runtime preamble.
   - `checkUnderflow 2` rejects stacks with fewer than two items.
   - `popNatUpTo 1023` validates `n` for key width and number type.
   - `popMaybeCell` accepts `.null` and valid dict roots and rejects top/non-cell dictionary values.

3. [B3] Dictionary miss paths.
   - `.null` root and width-mismatch on non-empty roots are misses.
   - Miss path keeps dictionary unchanged and pushes only `0`.

4. [B4] Dictionary error paths.
   - malformed dictionary cell can raise `.cellUnd`.

5. [B5] Remove-hit path.
   - `remove` mode finds max key/value pair and deletes that key.
   - removed dictionary root is pushed first (`null` if last key removed).
   - deleted key/value are pushed next, followed by `-1`.

6. [B6] Slice-value materialization.
   - `byRef = false` pushes value as `.slice`.
   - value shape mismatches are delegated to dictionary dictionary traversal failure paths.

7. [B7] Key reconstruction.
   - `intKey = false` rebuilds the key as slice of `n` bits and charges `cellCreateGasPrice`.

8. [B8] Assembler encoding.
   - `.dictGetMinMax 26` is valid and encodes to `0xF49A`.
   - unsupported args in gap ranges are `.invOpcode`.
   - `>31` is `.rangeChk`.

9. [B9] Decoder behavior.
   - `0xF49A..0xF49F` are decoder hits.
   - gap `0xF498` and truncated bitstreams are decode errors.

10. [B10] Gas accounting.
   - exact base-gas miss path succeeds and base-minus-one fails.
   - remove-hit paths add delete-creation gas and one key-rebuild gas unit.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTREMMAX" }

private def instr : Instr :=
  .dictGetMinMax 26

private def fallbackSentinel : Int :=
  12_345_678

private def asSlice (bits : BitString) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits #[])

private def mkDictSetSliceRootBits! (label : String) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (keyBits, value) := entry
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting"
      | .error e =>
          panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: dictionary remained empty"

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

private def sampleValueA : Slice := mkSliceFromBits (natToBits 0xA 8)
private def sampleValueB : Slice := mkSliceFromBits (natToBits 0xB 8)
private def sampleValueC : Slice := mkSliceFromBits (natToBits 0xC 8)

private def valueSliceA : Value := .slice sampleValueA
private def valueSliceB : Value := .slice sampleValueB
private def valueSliceC : Value := .slice sampleValueC

private def dictNull : Value := .null

private def key0 : BitString := #[]
private def key8_1 : BitString := natToBits 1 8
private def key8_7 : BitString := natToBits 7 8
private def key8_128 : BitString := natToBits 128 8
private def key8_200 : BitString := natToBits 200 8
private def key8_255 : BitString := natToBits 255 8
private def key257_1 : BitString := natToBits 1 257
private def key1023_0 : BitString := natToBits 0 1023

private def keySlice8_1 : Slice := asSlice key8_1
private def keySlice8_7 : Slice := asSlice key8_7
private def keySlice8_128 : Slice := asSlice key8_128
private def keySlice8_200 : Slice := asSlice key8_200
private def keySlice8_255 : Slice := asSlice key8_255

private def dictSingle0 : Cell :=
  mkDictSetSliceRootBits! "dictSingle0" #[(key0, sampleValueA)]
private def dictSingle8 : Cell :=
  mkDictSetSliceRootBits! "dictSingle8" #[(key8_7, sampleValueB)]
private def dictSingle8Alt : Cell :=
  mkDictSetSliceRootBits! "dictSingle8Alt" #[(key8_128, sampleValueC)]
private def dictTwo8 : Cell :=
  mkDictSetSliceRootBits! "dictTwo8" #[(key8_7, sampleValueA), (key8_255, sampleValueB)]
private def dictTwo8AfterMax : Cell :=
  mkDictSetSliceRootBits! "dictTwo8AfterMax" #[(key8_7, sampleValueA)]
private def dictThree8 : Cell :=
  mkDictSetSliceRootBits! "dictThree8" #[(key8_1, sampleValueA), (key8_7, sampleValueB), (key8_200, sampleValueC)]
private def dictThree8AfterMax : Cell :=
  mkDictSetSliceRootBits! "dictThree8AfterMax" #[(key8_1, sampleValueA), (key8_128, sampleValueB)]
private def dictSingle257 : Cell :=
  mkDictSetSliceRootBits! "dictSingle257" #[(key257_1, sampleValueA)]
private def dictTwo257 : Cell :=
  mkDictSetSliceRootBits! "dictTwo257" #[(natToBits 0 257, sampleValueB), (key257_1, sampleValueC)]
private def dictTwo257AfterMax : Cell :=
  mkDictSetSliceRootBits! "dictTwo257AfterMax" #[(natToBits 0 257, sampleValueB)]
private def dictSingle1023 : Cell :=
  mkDictSetSliceRootBits! "dictSingle1023" #[(key1023_0, sampleValueA)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def two8Created : Nat := dictDeleteCreated dictTwo8 8
private def two257Created : Nat := dictDeleteCreated dictTwo257 257

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def keySliceGas : Int := cellCreateGasPrice
private def removeTwo8Gas : Int := baseGas + keySliceGas + Int.ofNat two8Created * cellCreateGasPrice
private def removeTwo8GasMinusOne : Int := if removeTwo8Gas > 0 then removeTwo8Gas - 1 else 0
private def removeTwo257Gas : Int := baseGas + keySliceGas + Int.ofNat two257Created * cellCreateGasPrice
private def removeTwo257GasMinusOne : Int := if removeTwo257Gas > 0 then removeTwo257Gas - 1 else 0

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

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits decoded, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decode did not consume full stream")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (expected : Excno)
    (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectHitShape
    (label : String)
    (result : Except Excno (Array Value))
    (expectNullRoot : Bool) : IO Unit := do
  match result with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")
  | .ok st =>
      match st with
      | #[root, .slice _, .slice _, flag] =>
          if expectNullRoot then
            if root != .null then
              throw (IO.userError s!"{label}: expected null root, got {reprStr root}")
          else
            match root with
            | .cell _ => pure ()
            | _ => throw (IO.userError s!"{label}: expected cell root, got {reprStr root}")
          if flag != intV (-1) then
            throw (IO.userError s!"{label}: expected flag -1, got {reprStr flag}")
      | _ =>
          throw (IO.userError s!"{label}: expected [root, slice, slice, -1], got {reprStr st}")

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV fallbackSentinel)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

def genDictRemMaxCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" (#[dictNull, intV 0]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/8" (#[dictNull, intV 8]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/257" (#[dictNull, intV 257]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/1023" (#[dictNull, intV 1023]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/single8" (#[ .cell dictSingle8, intV 8]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/single8-alt" (#[ .cell dictSingle8Alt, intV 8]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/two8" (#[ .cell dictTwo8, intV 8]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/three8" (#[ .cell dictThree8, intV 8]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/single0" (#[ .cell dictSingle0, intV 0]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/hit/single257" (#[ .cell dictSingle257, intV 257]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/hit/two257" (#[ .cell dictTwo257, intV 257]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/hit/single1023" (#[ .cell dictSingle1023, intV 1023]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/miss/width-mismatch" (#[ .cell dictSingle8, intV 16]), rng1)
    else if shape = 13 then
      (mkRawCase "fuzz/raw/gap-f498" (#[ .cell dictSingle8, intV 8]) rawOpcodeF498, rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/underflow-one" (#[dictNull]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-key-nan" ((#[Value.cell dictSingle8, Value.int .nan] : Array Value)), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/type-root-tuple" (#[ .tuple #[], intV 8]), rng1)
    else if shape = 18 then
      (mkRawCase "fuzz/raw/truncated8" (#[ .cell dictSingle8, intV 8]) rawTruncated8, rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/n-negative" (#[ .cell dictSingle8, intV (-1) ]), rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/n-too-large" (#[ .cell dictSingle8, intV 1024 ]), rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/root-type-cont" (#[ .cont (.quit 0), intV 8]), rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/malformed-root" (#[ .cell malformedDict, intV 8]), rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/base-exact" (#[dictNull, intV 8])
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/base-minus-one" (#[dictNull, intV 8])
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else if shape = 25 then
      (mkCase "fuzz/gas/remove-two8" (#[ .cell dictTwo8, intV 8 ])
        (#[.pushInt (.num removeTwo8Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact removeTwo8Gas), rng1)
    else if shape = 26 then
      (mkCase "fuzz/gas/remove-two8-minus-one" (#[ .cell dictTwo8, intV 8 ])
        (#[.pushInt (.num removeTwo8GasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne removeTwo8GasMinusOne), rng1)
    else if shape = 27 then
      (mkCase "fuzz/gas/remove-two257" (#[ .cell dictTwo257, intV 257 ])
        (#[.pushInt (.num removeTwo257Gas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact removeTwo257Gas), rng1)
    else
      (mkCase "fuzz/gas/remove-two257-minus-one" (#[ .cell dictTwo257, intV 257 ])
        (#[.pushInt (.num removeTwo257GasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne removeTwo257GasMinusOne), rng1)
  (let (tag, rng3) := randNat rng2 0 999_999; ({ case0 with name := s!"{case0.name}/{tag}" }, rng3))

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "dispatch/fallback"
          (runDispatchFallback (#[intV 8, intV 9]))
          (#[intV 8, intV 9, intV fallbackSentinel]) },
    { name := "unit/asm/assemble-ok" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF49A 16 then
              throw (IO.userError "DICTREMMAX should assemble to 0xF49A")
        | .error e =>
            throw (IO.userError s!"DICTREMMAX assemble failed: {reprStr e}") },
    { name := "unit/asm/reject-invalid-args" -- [B8]
      run := do
        expectAssembleErr "asm-gap-24" .invOpcode (.dictGetMinMax 24)
        expectAssembleErr "asm-gap-32" .rangeChk (.dictGetMinMax 32) },
    { name := "unit/decode/branches" -- [B9]
      run := do
        let s0 : Slice :=
          Slice.ofCell (Cell.mkOrdinary (rawOpcodeF49A.bits ++ rawOpcodeF49B.bits ++ rawOpcodeF49C.bits ++ rawOpcodeF49D.bits) #[])
        let s1 ← expectDecodeStep "decode/prev" s0 (.dictGetMinMax 26) 16
        let s2 ← expectDecodeStep "decode/self" s1 (.dictGetMinMax 27) 16
        let s3 ← expectDecodeStep "decode/next" s2 (.dictGetMinMax 28) 16
        let s4 ← expectDecodeStep "decode/nextnext" s3 (.dictGetMinMax 29) 16
        if s4.bitsRemaining + s4.refsRemaining != 0 then
          throw (IO.userError "decode did not consume full stream") },
    { name := "unit/decode/truncated-or-gap" -- [B9]
      run := do
        expectDecodeErr "decode/f498-gap" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode/truncated8" rawTruncated8 .invOpcode },
    { name := "unit/exec/miss/null" -- [B3][B4]
      run := do
        expectOkStack "miss-null-0" (runDirect (#[dictNull, intV 0])) (#[dictNull, intV 0])
        expectOkStack "miss-null-8" (runDirect (#[dictNull, intV 8])) (#[dictNull, intV 0])
        expectOkStack "miss-null-1023" (runDirect (#[dictNull, intV 1023])) (#[dictNull, intV 0]) },
    { name := "unit/exec/hit/single0" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-single0" (runDirect (#[ .cell dictSingle0, intV 0])) true },
    { name := "unit/exec/hit/single8" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-single8" (runDirect (#[ .cell dictSingle8, intV 8])) true },
    { name := "unit/exec/hit/single8-alt" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-single8-alt" (runDirect (#[ .cell dictSingle8Alt, intV 8])) true },
    { name := "unit/exec/hit/two8" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-two8" (runDirect (#[ .cell dictTwo8, intV 8])) false },
    { name := "unit/exec/hit/three8" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-three8" (runDirect (#[ .cell dictThree8, intV 8])) false },
    { name := "unit/exec/hit/single257" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-single257" (runDirect (#[ .cell dictSingle257, intV 257])) true },
    { name := "unit/exec/hit/two257" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-two257" (runDirect (#[ .cell dictTwo257, intV 257])) false },
    { name := "unit/exec/hit/single1023" -- [B5][B6][B7]
      run := do
        expectHitShape "hit-single1023" (runDirect (#[ .cell dictSingle1023, intV 1023])) true },
    { name := "unit/exec/miss/width-mismatch" -- [B3]
      run := do
        expectErr "miss-width-mismatch" (runDirect (#[ .cell dictSingle8, intV 16 ])) .cellUnd },
    { name := "unit/exec/malformed-root" -- [B4]
      run := do
        expectErr "malformed-root" (runDirect (#[ .cell malformedDict, intV 8])) .cellUnd },
    { name := "unit/exec/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "n-nan" (runDirect (#[ .cell dictSingle8, Value.int .nan ])) .rangeChk
        expectErr "n-negative" (runDirect (#[ .cell dictSingle8, intV (-1) ]) ) .rangeChk
        expectErr "n-too-large" (runDirect (#[ .cell dictSingle8, intV 1024 ]) ) .rangeChk },
    { name := "unit/exec/type-errors" -- [B2]
      run := do
        expectErr "root-tuple" (runDirect (#[ .tuple #[], intV 8 ])) .typeChk
        expectErr "root-cont" (runDirect (#[ .cont (.quit 0), intV 8 ])) .typeChk } ]
  oracle := #[
    mkCase "oracle/underflow/empty" #[] , -- [B2]
    mkCase "oracle/underflow/one-item" (#[dictNull]) , -- [B2]
    mkCase "oracle/miss/null/0" (#[dictNull, intV 0]), -- [B3][B4]
    mkCase "oracle/miss/null/8" (#[dictNull, intV 8]), -- [B3][B4]
    mkCase "oracle/miss/null/16" (#[dictNull, intV 16]), -- [B3][B4]
    mkCase "oracle/miss/null/1023" (#[dictNull, intV 1023]), -- [B3][B4]
    mkCase "oracle/hit/single0" (#[ .cell dictSingle0, intV 0]), -- [B5][B6][B7]
    mkCase "oracle/hit/single8" (#[ .cell dictSingle8, intV 8]), -- [B5][B6][B7]
    mkCase "oracle/hit/single8-alt" (#[ .cell dictSingle8Alt, intV 8]), -- [B5][B6][B7]
    mkCase "oracle/hit/two8" (#[ .cell dictTwo8, intV 8]), -- [B5][B6][B7]
    mkCase "oracle/hit/three8" (#[ .cell dictThree8, intV 8]), -- [B5][B6][B7]
    mkCase "oracle/hit/single257" (#[ .cell dictSingle257, intV 257]), -- [B5][B6][B7]
    mkCase "oracle/hit/two257" (#[ .cell dictTwo257, intV 257]), -- [B5][B6][B7]
    mkCase "oracle/hit/single1023" (#[ .cell dictSingle1023, intV 1023]), -- [B5][B6][B7]
    mkCase "oracle/miss/width-mismatch" (#[ .cell dictSingle8, intV 16]), -- [B3]
    mkRawCase "oracle/code/f49a" (#[dictNull, intV 8]) rawOpcodeF49A, -- [B8][B9]
    mkRawCase "oracle/code/f49b" (#[dictNull, intV 8]) rawOpcodeF49B, -- [B8][B9]
    mkRawCase "oracle/code/f49c" (#[dictNull, intV 8]) rawOpcodeF49C, -- [B8][B9]
    mkRawCase "oracle/code/f49d" (#[dictNull, intV 8]) rawOpcodeF49D, -- [B8][B9]
    mkRawCase "oracle/code/f49e" (#[dictNull, intV 8]) rawOpcodeF49E, -- [B8][B9]
    mkRawCase "oracle/code/f49f" (#[dictNull, intV 8]) rawOpcodeF49F, -- [B8][B9]
    mkRawCase "oracle/code/f49e-with-args" (#[ .cell dictSingle8, intV 8]) rawOpcodeF49E, -- [B9]
    mkRawCase "oracle/code/f498-gap" (#[ .cell dictSingle8, intV 8]) rawOpcodeF498, -- [B9]
    mkRawCase "oracle/code/truncated8" #[] rawTruncated8, -- [B9]
    mkCase "oracle/type-error/underflow-empty" #[], -- [B2]
    mkCase "oracle/type-error/underflow-one" (#[dictNull]), -- [B2]
    mkCase "oracle/type-error/key-nan" ((#[ Value.cell dictSingle8, Value.int .nan ] : Array Value)), -- [B2]
    mkCase "oracle/type-error/root-tuple" ((#[ Value.tuple #[], intV 8 ] : Array Value)), -- [B3]
    mkCase "oracle/type-error/root-cont" (#[ .cont (.quit 0), intV 8]), -- [B3]
    mkCase "oracle/type-error/n-negative" (#[ .cell dictSingle8, intV (-1) ]), -- [B2]
    mkCase "oracle/type-error/n-too-large" (#[ .cell dictSingle8, intV 1024 ]), -- [B2]
    mkCase "oracle/type-error/root-malformed" (#[ .cell malformedDict, intV 8]), -- [B4]
    mkCase "oracle/gas/base-exact" (#[dictNull, intV 8])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas), -- [B10]
    mkCase "oracle/gas/base-minus-one" (#[dictNull, intV 8])
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne), -- [B10]
    mkCase "oracle/gas/remove-two8" (#[ .cell dictTwo8, intV 8 ])
      (#[.pushInt (.num removeTwo8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwo8Gas), -- [B10]
    mkCase "oracle/gas/remove-two8-minus-one" (#[ .cell dictTwo8, intV 8 ])
      (#[.pushInt (.num removeTwo8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwo8GasMinusOne), -- [B10]
    mkCase "oracle/gas/remove-two257" (#[ .cell dictTwo257, intV 257 ])
      (#[.pushInt (.num removeTwo257Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwo257Gas), -- [B10]
    mkCase "oracle/gas/remove-two257-minus-one" (#[ .cell dictTwo257, intV 257 ])
      (#[.pushInt (.num removeTwo257GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwo257GasMinusOne) -- [B10]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictRemMaxCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREMMAX
