import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREMMIN

/-!
INSTRUCTION: DICTUREMMIN

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch path.
   `.dictGetMinMax` is handled by `execInstrDictDictGetMinMax`; all other instructions call `next`.

2. [B2] Runtime preamble and validation.
   `checkUnderflow 2` enforces dictionary and width. `popNatUpTo` uses `maxN = 256` because this is unsigned integer-key mode.
   Errors from this phase are `stkUnd` and `rangeChk`.

3. [B3] Dictionary root typing.
   `popMaybeCell` accepts only `.null` and `.cell`; all other top-stack types are rejected with `typeChk`.

4. [B4] Miss / empty behavior.
   `none` dictionary, mismatched-key-width mismatch, and misses return `[dictRootOrNull, 0]` without mutation.

5. [B5] Hit + remove path.
   For `DICTUREMMIN` (`args5 = 22`): `byRef=false`, `intKey=true`, `unsigned=true`, `fetchMax=false`, `remove=true`.
   On hit, stack must become `[dictOut, valueSlice, keyInt, -1]` and dictionary key is removed.

6. [B6] Unsigned key reconstruction and boundaries.
   `unsigned=true` means keys are decoded as `bitsToNat`, so ordering is natural unsigned order (not two's-complement).
   Boundary widths/keys to hit: `n=0`, `n=1`, `n=256`, key `0`, and key `2^256-1`.

7. [B7] Remove/delete rebuild.
   `dictDeleteWithCells` may fail (`dictErr`) or succeed with `oldVal` and `newRoot`, then `created` contributes
   `created * cellCreateGasPrice` only when `created > 0`.
   After remove, root is `.null` if emptied or `.cell` otherwise.

8. [B8] Assembler encoding.
   `.dictGetMinMax 22` must assemble to `0xF496`. In-family disallowed `17` and `24` are `.invOpcode`.
   `33` is rejected by `.rangeChk`.
   (No other variable-encoding behaviors were found.)

9. [B9] Decoder behavior.
   `0xF492..0xF497` decode to `.dictGetMinMax 18..23`.
   `0xF491`, `0xF498`, and truncated `0xF4` are `.invOpcode`.

10. [B10] Gas accounting.
    Hit/miss both use base budget (no key-slice allocation fee because `intKey` path).
    Base exact gas should succeed, exact-minus-one should fail.
    Hit+remove may consume additional `cellCreateGasPrice * created` from dictionary rebuild.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
-/

private def suiteId : InstrId :=
  { name := "DICTUREMMIN" }

private def instr : Instr :=
  .dictGetMinMax 22

private def fallbackSentinel : Int := 123_901

private def maxUInt256 : Int := Int.ofNat ((1 <<< 256) - 1)

private def maxKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n false true with
  | .ok (some (_, keyBits), _) => some keyBits
  | _ => none

private def dictDeleteCreated (root : Cell) (n : Nat) : Nat :=
  match maxKeyBits root n with
  | some keyBits =>
      match dictDeleteWithCells (some root) keyBits with
      | .ok (_, _, created, _) => created
      | .error _ => 0
  | none => 0

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC 8) #[]
private def badValueSlice : Slice := mkSliceFromBits (natToBits 0xF0 8)
private def badRootSlice : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0x01 8) #[])

private def dictNull : Value := .null

private def dictSingle0N0 : Cell :=
  mkDictSetRefRoot! "dictSingle0N0" 0 #[(0, valueA)]
private def dictSingle8 : Cell :=
  mkDictSetRefRoot! "dictSingle8" 8 #[(7, valueA)]
private def dictSingle8Alt : Cell :=
  mkDictSetRefRoot! "dictSingle8Alt" 8 #[(13, valueB)]
private def dictTwo8 : Cell :=
  mkDictSetRefRoot! "dictTwo8" 8 #[(7, valueA), (13, valueB)]
private def dictTwo8AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwo8AfterMin" 8 #[(13, valueB)]
private def dictThree8 : Cell :=
  mkDictSetRefRoot! "dictThree8" 8 #[(1, valueA), (7, valueB), (255, valueC)]
private def dictThree8AfterMin : Cell :=
  mkDictSetRefRoot! "dictThree8AfterMin" 8 #[(7, valueB), (255, valueC)]

private def dictSingle256Zero : Cell :=
  mkDictSetRefRoot! "dictSingle256Zero" 256 #[(0, valueA)]
private def dictSingle256Max : Cell :=
  mkDictSetRefRoot! "dictSingle256Max" 256 #[(maxUInt256, valueB)]
private def dictTwo256 : Cell :=
  mkDictSetRefRoot! "dictTwo256" 256 #[(0, valueA), (maxUInt256, valueC)]
private def dictTwo256AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwo256AfterMin" 256 #[(maxUInt256, valueC)]
private def dictThree256 : Cell :=
  mkDictSetRefRoot! "dictThree256" 256 #[(0, valueA), (1, valueB), (maxUInt256, valueC)]
private def dictThree256AfterMin : Cell :=
  mkDictSetRefRoot! "dictThree256AfterMin" 256 #[(1, valueB), (maxUInt256, valueC)]

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(7, badValueSlice)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def two8Created : Nat := dictDeleteCreated dictTwo8 8
private def three8Created : Nat := dictDeleteCreated dictThree8 8
private def two256Created : Nat := dictDeleteCreated dictTwo256 256
private def three256Created : Nat := dictDeleteCreated dictThree256 256
private def two8Penalty : Int := Int.ofNat two8Created * cellCreateGasPrice
private def three8Penalty : Int := Int.ofNat three8Created * cellCreateGasPrice
private def two256Penalty : Int := Int.ofNat two256Created * cellCreateGasPrice
private def three256Penalty : Int := Int.ofNat three256Created * cellCreateGasPrice

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def removeTwo8Gas : Int := baseGas + two8Penalty
private def removeTwo8GasMinusOne : Int := if removeTwo8Gas > 0 then removeTwo8Gas - 1 else 0
private def removeThree8Gas : Int := baseGas + three8Penalty
private def removeThree8GasMinusOne : Int := if removeThree8Gas > 0 then removeThree8Gas - 1 else 0
private def removeTwo256Gas : Int := baseGas + two256Penalty
private def removeTwo256GasMinusOne : Int := if removeTwo256Gas > 0 then removeTwo256Gas - 1 else 0
private def removeThree256Gas : Int := baseGas + three256Penalty
private def removeThree256GasMinusOne : Int := if removeThree256Gas > 0 then removeThree256Gas - 1 else 0

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]
private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def rawOpcodeF496 : Cell := raw16 0xF496
private def rawOpcodeF495 : Cell := raw16 0xF495
private def rawOpcodeF497 : Cell := raw16 0xF497
private def rawOpcodeF491 : Cell := raw16 0xF491
private def rawOpcodeF498 : Cell := raw16 0xF498
private def rawOpcodeF4 : Cell := raw8 0xF4

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

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV fallbackSentinel)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")

private def expectAssembleErr
    (label : String)
    (i : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [i] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def genDictURemMinFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (bucket, rng1) := randNat rng0 0 99
  let (case0, rng2) :=
    if bucket < 35 then
      let (shape, rng2') := randNat rng1 0 11
      if shape = 0 then
        (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng2')
      else if shape = 1 then
        (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng2')
      else if shape = 2 then
        (mkCase "fuzz/miss/null/256" #[dictNull, intV 256], rng2')
      else if shape = 3 then
        (mkCase "fuzz/hit/single8" #[.cell dictSingle8, intV 8], rng2')
      else if shape = 4 then
        (mkCase "fuzz/hit/single8-alt" #[.cell dictSingle8Alt, intV 8], rng2')
      else if shape = 5 then
        (mkCase "fuzz/hit/two8" #[.cell dictTwo8, intV 8], rng2')
      else if shape = 6 then
        (mkCase "fuzz/hit/three8" #[.cell dictThree8, intV 8], rng2')
      else if shape = 7 then
        (mkCase "fuzz/hit/single256-zero" #[.cell dictSingle256Zero, intV 256], rng2')
      else if shape = 8 then
        (mkCase "fuzz/hit/single256-max" #[.cell dictSingle256Max, intV 256], rng2')
      else if shape = 9 then
        (mkCase "fuzz/hit/two256" #[.cell dictTwo256, intV 256], rng2')
      else if shape = 10 then
        (mkCase "fuzz/hit/three256" #[.cell dictThree256, intV 256], rng2')
      else
        (mkCase "fuzz/hit/slice-value" #[.cell dictSliceSingle8, intV 8], rng2')
    else if bucket < 65 then
      let (shape, rng2') := randNat rng1 0 8
      if shape = 0 then
        (mkCase "fuzz/err/underflow/empty" #[], rng2')
      else if shape = 1 then
        (mkCase "fuzz/err/underflow/one" #[dictNull], rng2')
      else if shape = 2 then
        (mkCase "fuzz/err/type-root-slice" #[.slice badRootSlice, intV 8], rng2')
      else if shape = 3 then
        (mkCase "fuzz/err/type-root-tuple" #[.tuple #[], intV 8], rng2')
      else if shape = 4 then
        (mkCase "fuzz/err/type-root-cont" #[.cont (.quit 0), intV 8], rng2')
      else if shape = 5 then
        (mkCase "fuzz/err/nan" #[.cell dictSingle8, .int .nan], rng2')
      else if shape = 6 then
        (mkCase "fuzz/err/n-negative" #[.cell dictSingle8, intV (-1)], rng2')
      else if shape = 7 then
        (mkCase "fuzz/err/n-too-large" #[.cell dictSingle8, intV 257], rng2')
      else
        (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng2')
    else if bucket < 85 then
      let (shape, rng2') := randNat rng1 0 8
      if shape = 0 then
        (mkCase "fuzz/gas/base" #[dictNull, intV 8]
          (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExact baseGas), rng2')
      else if shape = 1 then
        (mkCase "fuzz/gas/base-minus-one" #[dictNull, intV 8]
          (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExactMinusOne baseGasMinusOne), rng2')
      else if shape = 2 then
        (mkCase "fuzz/gas/remove-two8" #[.cell dictTwo8, intV 8]
          (#[.pushInt (.num removeTwo8Gas), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExact removeTwo8Gas), rng2')
      else if shape = 3 then
        (mkCase "fuzz/gas/remove-two8-oog" #[.cell dictTwo8, intV 8]
          (#[.pushInt (.num removeTwo8GasMinusOne), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExactMinusOne removeTwo8GasMinusOne), rng2')
      else if shape = 4 then
        (mkCase "fuzz/gas/remove-three8" #[.cell dictThree8, intV 8]
          (#[.pushInt (.num removeThree8Gas), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExact removeThree8Gas), rng2')
      else if shape = 5 then
        (mkCase "fuzz/gas/remove-three8-oog" #[.cell dictThree8, intV 8]
          (#[.pushInt (.num removeThree8GasMinusOne), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExactMinusOne removeThree8GasMinusOne), rng2')
      else if shape = 6 then
        (mkCase "fuzz/gas/remove-two256" #[.cell dictTwo256, intV 256]
          (#[.pushInt (.num removeTwo256Gas), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExact removeTwo256Gas), rng2')
      else
        (mkCase "fuzz/gas/remove-two256-oog" #[.cell dictTwo256, intV 256]
          (#[.pushInt (.num removeTwo256GasMinusOne), .tonEnvOp .setGasLimit, instr])
          (oracleGasLimitsExactMinusOne removeTwo256GasMinusOne), rng2')
    else
      let (shape, rng2') := randNat rng1 0 5
      if shape = 0 then
        (mkCodeCase "fuzz/code/f496" #[dictNull, intV 256] rawOpcodeF496, rng2')
      else if shape = 1 then
        (mkCodeCase "fuzz/code/f495" #[dictNull, intV 256] rawOpcodeF495, rng2')
      else if shape = 2 then
        (mkCodeCase "fuzz/code/f497" #[dictNull, intV 256] rawOpcodeF497, rng2')
      else if shape = 3 then
        (mkCodeCase "fuzz/code/gap-491" #[dictNull, intV 8] rawOpcodeF491, rng2')
      else if shape = 4 then
        (mkCodeCase "fuzz/code/gap-498" #[dictNull, intV 8] rawOpcodeF498, rng2')
      else
        (mkCodeCase "fuzz/code/truncated" #[] rawOpcodeF4, rng2')
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
          #[intV 1, intV 2, intV fallbackSentinel]
    },
    { name := "unit/asm/assemble/valid" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF496 16 then
              throw (IO.userError s!"expected opcode 0xF496 bits, got {reprStr c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTUREMMIN failed: {reprStr e}")
    },
    { name := "unit/asm/assemble/gaps" -- [B8]
      run := do
        expectAssembleErr "assemble-gap-17" (.dictGetMinMax 17) .invOpcode
        expectAssembleErr "assemble-gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "assemble-range" (.dictGetMinMax 33) .rangeChk
    },
    { name := "unit/decode/branches" -- [B9]
      run := do
        let stream : Slice :=
          Slice.ofCell
            (Cell.mkOrdinary
              (rawOpcodeF495.bits ++
                rawOpcodeF496.bits ++
                rawOpcodeF497.bits)
              #[])
        let s1 ← expectDecodeStep "decode-f495" stream (.dictGetMinMax 21) 16
        let s2 ← expectDecodeStep "decode-f496" s1 (.dictGetMinMax 22) 16
        let s3 ← expectDecodeStep "decode-f497" s2 (.dictGetMinMax 23) 16
        if s3.bitsRemaining + s3.refsRemaining != 0 then
          throw (IO.userError "decode did not consume full stream")
    },
    { name := "unit/decode/invalid-or-truncated" -- [B9]
      run := do
        expectDecodeErr "decode-gap-before" rawOpcodeF491 .invOpcode
        expectDecodeErr "decode-gap-after" rawOpcodeF498 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode
    },
    { name := "unit/exec/miss-null" -- [B4]
      run := do
        expectOkStack "miss-null-8" (runDirect #[dictNull, intV 8]) #[dictNull, intV 0]
        expectOkStack "miss-null-256" (runDirect #[dictNull, intV 256]) #[dictNull, intV 0]
    },
    { name := "unit/exec/hit/single" -- [B5]
      run := do
        expectOkStack "single8" (runDirect #[.cell dictSingle8, intV 8])
          #[.null, .slice (Slice.ofCell valueA), intV 7, intV (-1)]
        expectOkStack "single8-alt" (runDirect #[.cell dictSingle8Alt, intV 8])
          #[.null, .slice (Slice.ofCell valueB), intV 13, intV (-1)]
        expectOkStack "single256-max" (runDirect #[.cell dictSingle256Max, intV 256])
          #[.null, .slice (Slice.ofCell valueB), intV maxUInt256, intV (-1)]
    },
    { name := "unit/exec/hit/multi" -- [B7]
      run := do
        expectOkStack "two8-remove-min" (runDirect #[.cell dictTwo8, intV 8])
          #[.cell dictTwo8AfterMin, .slice (Slice.ofCell valueA), intV 7, intV (-1)]
        expectOkStack "three8-remove-min" (runDirect #[.cell dictThree8, intV 8])
          #[.cell dictThree8AfterMin, .slice (Slice.ofCell valueA), intV 1, intV (-1)]
        expectOkStack "two256-remove-min" (runDirect #[.cell dictTwo256, intV 256])
          #[.cell dictTwo256AfterMin, .slice (Slice.ofCell valueC), intV 0, intV (-1)]
        expectOkStack "three256-remove-min" (runDirect #[.cell dictThree256, intV 256])
          #[.cell dictThree256AfterMin, .slice (Slice.ofCell valueB), intV 1, intV (-1)]
    },
    { name := "unit/exec/width-mismatch" -- [B4]
      run := do
        expectOkStack "width-mismatch-16" (runDirect #[.cell dictSingle8, intV 16])
          #[.cell dictSingle8, intV 0]
        expectOkStack "width-mismatch-257" (runDirect #[.cell dictSingle8, intV 257])
          #[.cell dictSingle8, intV 0]
    },
    { name := "unit/exec/marshal-slice-value" -- [B5]
      run := do
        expectOkStack "slice-value" (runDirect #[.cell dictSliceSingle8, intV 8])
          #[.null, .slice badValueSlice, intV 7, intV (-1)]
    },
    { name := "unit/exec/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd
    },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "n-nan" (runDirect #[dictNull, .int .nan]) .rangeChk
        expectErr "n-negative" (runDirect #[dictNull, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDirect #[dictNull, intV 257]) .rangeChk
    },
    { name := "unit/exec/type-errors" -- [B3]
      run := do
        expectErr "root-slice" (runDirect #[.slice badValueSlice, intV 8]) .typeChk
        expectErr "root-tuple" (runDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDirect #[.cont (.quit 0), intV 8]) .typeChk
    },
    { name := "unit/exec/malformed-root" -- [B11]
      run := do
        expectErr "bad-dict-root" (runDirect #[.cell malformedDict, intV 8]) .cellUnd
    }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0], -- [B4]
    mkCase "oracle/miss/null/8" #[dictNull, intV 8], -- [B4]
    mkCase "oracle/miss/null/256" #[dictNull, intV 256], -- [B4]
    mkCase "oracle/miss/empty-cell/8" #[.cell (Cell.mkOrdinary (natToBits 0 1) #[]), intV 8], -- [B4]
    mkCase "oracle/miss/empty-cell/256" #[.cell (Cell.mkOrdinary (natToBits 0 1) #[]), intV 256], -- [B4]
    mkCase "oracle/miss/mismatch-16" #[.cell dictSingle8, intV 16], -- [B4]
    mkCase "oracle/miss/mismatch-257" #[.cell dictSingle8, intV 257], -- [B4]
    mkCase "oracle/hit/single8" #[.cell dictSingle8, intV 8], -- [B5][B6][B7]
    mkCase "oracle/hit/single8-alt" #[.cell dictSingle8Alt, intV 8], -- [B5][B6]
    mkCase "oracle/hit/two8" #[.cell dictTwo8, intV 8], -- [B5][B7]
    mkCase "oracle/hit/three8" #[.cell dictThree8, intV 8], -- [B5][B7]
    mkCase "oracle/hit/single256-zero" #[.cell dictSingle256Zero, intV 256], -- [B5][B6][B7]
    mkCase "oracle/hit/single256-max" #[.cell dictSingle256Max, intV 256], -- [B5][B6][B7]
    mkCase "oracle/hit/two256" #[.cell dictTwo256, intV 256], -- [B5][B6][B7]
    mkCase "oracle/hit/three256" #[.cell dictThree256, intV 256], -- [B5][B6][B7]
    mkCase "oracle/hit/slice-value" #[.cell dictSliceSingle8, intV 8], -- [B5]
    mkCase "oracle/err/underflow-empty" #[], -- [B2]
    mkCase "oracle/err/underflow-one" #[dictNull], -- [B2]
    mkCase "oracle/err/type-root-slice" #[.slice badValueSlice, intV 8], -- [B3]
    mkCase "oracle/err/type-root-tuple" #[.tuple #[], intV 8], -- [B3]
    mkCase "oracle/err/type-root-cont" #[.cont (.quit 0), intV 8], -- [B3]
    mkCase "oracle/err/nan" #[.cell dictSingle8, .int .nan], -- [B2]
    mkCase "oracle/err/n-negative" #[.cell dictSingle8, intV (-1)], -- [B2]
    mkCase "oracle/err/n-too-large" #[.cell dictSingle8, intV 257], -- [B2]
    mkCase "oracle/err/malformed-root" #[.cell malformedDict, intV 8], -- [B11]
    mkCodeCase "oracle/code/f496" #[dictNull, intV 8] rawOpcodeF496, -- [B8][B9]
    mkCodeCase "oracle/code/f495" #[dictNull, intV 8] rawOpcodeF495, -- [B8][B9]
    mkCodeCase "oracle/code/f497" #[dictNull, intV 8] rawOpcodeF497, -- [B8][B9]
    mkCodeCase "oracle/code/gap/491" #[dictNull, intV 8] rawOpcodeF491, -- [B8][B9]
    mkCodeCase "oracle/code/gap/498" #[dictNull, intV 8] rawOpcodeF498, -- [B8][B9]
    mkCodeCase "oracle/code/truncated8" #[] rawOpcodeF4, -- [B9]
    mkCase "oracle/gas/base" #[dictNull, intV 8]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact baseGas), -- [B10]
    mkCase "oracle/gas/base-minus-one" #[dictNull, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne baseGasMinusOne), -- [B10]
    mkCase "oracle/gas/remove-two8" #[.cell dictTwo8, intV 8]
      (#[.pushInt (.num removeTwo8Gas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact removeTwo8Gas), -- [B10]
    mkCase "oracle/gas/remove-two8-oog" #[.cell dictTwo8, intV 8]
      (#[.pushInt (.num removeTwo8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwo8GasMinusOne), -- [B10]
    mkCase "oracle/gas/remove-three8" #[.cell dictThree8, intV 8]
      (#[.pushInt (.num removeThree8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeThree8Gas), -- [B10]
    mkCase "oracle/gas/remove-three8-oog" #[.cell dictThree8, intV 8]
      (#[.pushInt (.num removeThree8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeThree8GasMinusOne), -- [B10]
    mkCase "oracle/gas/remove-two256" #[.cell dictTwo256, intV 256]
      (#[.pushInt (.num removeTwo256Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwo256Gas), -- [B10]
    mkCase "oracle/gas/remove-two256-oog" #[.cell dictTwo256, intV 256]
      (#[.pushInt (.num removeTwo256GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwo256GasMinusOne), -- [B10]
    mkCase "oracle/gas/remove-three256" #[.cell dictThree256, intV 256]
      (#[.pushInt (.num removeThree256Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeThree256Gas), -- [B10]
    mkCase "oracle/gas/remove-three256-oog" #[.cell dictThree256, intV 256]
      (#[.pushInt (.num removeThree256GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeThree256GasMinusOne) -- [B10]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictURemMinFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREMMIN
