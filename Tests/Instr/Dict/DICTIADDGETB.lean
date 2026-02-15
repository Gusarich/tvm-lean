import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIADDGETB

/-!
INSTRUCTION: DICTIADDGETB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictExt` handles `.dictExt (.mutGetB true _ .add)` and dispatch falls through via `next` for non-matching instructions.

2. [B2] Operand stack arity and order.
   - `checkUnderflow 4` is enforced before mutation:
     `new_value_builder`, `key`, `dict`, `n`.

3. [B3] `n` validation via `popNatUpTo 1023`.
   - Negative, `NaN`, and `>1023` reject with `rangeChk` in both Lean and C++.

4. [B4] Integer-key conversion (`dictKeyBits?`) semantics.
   - Signed mode (`unsigned = false`) and unsigned mode (`unsigned = true`) apply different range checks.
   - `n = 0` with non-zero key is invalid for both modes.
   - Signed/unsigned overflow/underflow paths map to `rangeChk`.

5. [B5] Runtime success/miss branch for `.add`.
   - For missing key, `dictLookupSetBuilderWithCells` inserts and pushes:
     `new_root, -1`.
   - `dictLookupSetBuilderWithCells` may allocate cells; gas includes
     `created * cellCreateGasPrice`.

6. [B6] Runtime success/hit branch for `.add`.
   - For existing key, old value slice is pushed followed by `0`.
   - No new cells are created on the hot path for existing keys.

7. [B7] Type-check/runtime validation branches.
   - Builder value, dictionary root, key, and `n` types are validated in order by `VM.popBuilder`, `popInt`, `popMaybeCell`, and `popNatUpTo`.
   - Type mismatches produce `typeChk` or `rangeChk` analogously.

8. [B8] Dictionary structure branch.
   - Malformed dictionary roots propagate `.dictErr`.

9. [B9] Assembler encoding.
   - CP0 assembler can emit `dictExt` instructions for this opcode family; assembly should round-trip via decoder.

10. [B10] Decoder boundaries and opcode mapping.
   - `0xf456` decodes to `DICTIADDGETB` in signed mode (`.mutGetB true false .add`).
   - `0xf457` decodes to `DICTIADDGETB` unsigned mode (`.mutGetB true true .add`).
   - Adjacent boundaries:
     `0xf455` (`DICTUADDGETB`) and `0xf458` are not `DICTIADDGETB` forms; neighbors are expected to decode as different instructions or `.invOpcode`.
   - Decoding only reads 16-bit fixed opcodes in this family.

11. [B11] Gas accounting.
   - `computeExactGasBudget` validates base gas behavior.
   - Exact-gas-minus-one paths are covered for miss branches where created-cell gas is included.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn].
-/

private def dictIAddGetBId : InstrId :=
  { name := "DICTIADDGETB" }

private def instrSigned : Instr :=
  .dictExt (.mutGetB true false .add)

private def instrUnsigned : Instr :=
  .dictExt (.mutGetB true true .add)

private def rawF455 : Cell := Cell.mkOrdinary (natToBits 0xf455 16) #[]
private def rawF456 : Cell := Cell.mkOrdinary (natToBits 0xf456 16) #[]
private def rawF457 : Cell := Cell.mkOrdinary (natToBits 0xf457 16) #[]
private def rawF458 : Cell := Cell.mkOrdinary (natToBits 0xf458 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def valueA : Builder := Builder.empty.storeBits (natToBits 0xA1 8)
private def valueB : Builder := Builder.empty.storeBits (natToBits 0xB2 8)
private def valueC : Builder := Builder.empty.storeBits (natToBits 0xC3 8)
private def valueD : Builder := Builder.empty.storeBits (natToBits 0xD4 8)

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkDictRootInt! (label : String) (n : Nat) (unsigned : Bool) (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      let keyBits : BitString :=
        match dictKeyBits? k n unsigned with
        | some bits => bits
        | none => panic! s!"{label}: invalid int key {k} for n={n}, unsigned={unsigned}"
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: dictionary insertion returned empty root"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: no entries"

private def dictSigned4 : Cell :=
  mkDictRootInt! "dict/signed/4" 4 false #[(-8, valueA), (-1, valueB), (3, valueC), (7, valueD)]

private def dictUnsigned4 : Cell :=
  mkDictRootInt! "dict/unsigned/4" 4 true #[(0, valueA), (2, valueB), (7, valueC), (15, valueD)]

private def dictSigned8 : Cell :=
  mkDictRootInt! "dict/signed/8" 8 false #[(-128, valueA), (-1, valueB), (0, valueC), (41, valueD)]

private def dictUnsigned8 : Cell :=
  mkDictRootInt! "dict/unsigned/8" 8 true #[(0, valueA), (1, valueB), (200, valueC), (255, valueD)]

private def dictSigned0 : Cell :=
  mkDictRootInt! "dict/signed/0" 0 false #[(0, valueA)]

private def dictUnsigned0 : Cell :=
  mkDictRootInt! "dict/unsigned/0" 0 true #[(0, valueB)]

private def mkDictCaseStack (newValue : Builder) (key : Int) (dict : Value) (n : Int) : Array Value :=
  #[.builder newValue, .int (.num key), dict, intV n]

private def mkDictIAddGetBCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSigned])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  {
    name := name
    instr := dictIAddGetBId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel
  }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  {
    name := name
    instr := dictIAddGetBId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel
  }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (instr : Instr)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkDictIAddGetBCase name
    stack
    #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]
    gasLimits
    fuel

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded}")

private def expectAssembleOk16 (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c => do
      let rest ← expectDecodeStep label (Slice.ofCell c) instr 16
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected no trailing bits")
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")

private def runDictIAddGetBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDictIAddGetBDispatch (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (.int (.num 777))) stack

private def dictKeyBits! (label : String) (n : Nat) (unsigned : Bool) (key : Int) : BitString :=
  match dictKeyBits? key n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid key {key} for n={n}, unsigned={unsigned}"

private def createdBitsForAdd (n : Nat) (unsigned : Bool) (key : Int) : Nat :=
  let keyBits : BitString := dictKeyBits! "created-bits" n unsigned key
  match dictLookupSetBuilderWithCells none keyBits valueA .add with
  | .ok (_, _, _, created, _) => created
  | .error e =>
      panic! s!"dictLookupSetBuilderWithCells failed while precomputing created cells: {reprStr e}"

private def dictIAddGetBSignedExactGas : Int :=
  computeExactGasBudget instrSigned

private def dictIAddGetBUnequalExactGas : Int :=
  computeExactGasBudget instrUnsigned

private def dictIAddGetBSignedMissGas : Int :=
  dictIAddGetBSignedExactGas + (Int.ofNat (createdBitsForAdd 4 false 6)) * cellCreateGasPrice

private def dictIAddGetBUnequalMissGas : Int :=
  dictIAddGetBUnequalExactGas + (Int.ofNat (createdBitsForAdd 4 true 4)) * cellCreateGasPrice

private def dictIAddGetBSignedMissGasMinusOne : Int :=
  if dictIAddGetBSignedMissGas > 0 then dictIAddGetBSignedMissGas - 1 else 0

private def dictIAddGetBUnequalMissGasMinusOne : Int :=
  if dictIAddGetBUnequalMissGas > 0 then dictIAddGetBUnequalMissGas - 1 else 0

private def genDictIAddGetBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (isUnsigned, rng2) := randBool rng1
  let (tag, rng3) := randNat rng2 0 999_999
  let (case0, rng4) :=
    match shape with
    | 0 =>
        let stack : Array Value :=
          if isUnsigned then
            mkDictCaseStack valueA 2 (.null) 4
          else
            mkDictCaseStack valueA (-2) .null 4
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/ok/miss/null/4" stack #[instr], rng3)
    | 1 =>
        let stack : Array Value :=
          if isUnsigned then
            mkDictCaseStack valueA 3 (.null) 0
          else
            mkDictCaseStack valueA 0 (.null) 0
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/ok/miss/null/0" stack #[instr], rng3)
    | 2 =>
        let stack : Array Value :=
          if isUnsigned then
            mkDictCaseStack valueA 3 (.cell dictUnsigned4) 4
          else
            mkDictCaseStack valueA 6 (.cell dictSigned4) 4
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/ok/miss/non-empty/4" stack #[instr], rng3)
    | 3 =>
        let stack : Array Value :=
          if isUnsigned then
            mkDictCaseStack valueA 255 (.cell dictUnsigned8) 8
          else
            mkDictCaseStack valueA (-128) (.cell dictSigned8) 8
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/ok/hit/4" stack #[instr], rng3)
    | 4 =>
        let stack : Array Value :=
          if isUnsigned then
            mkDictCaseStack valueB 15 (.cell dictUnsigned4) 4
          else
            mkDictCaseStack valueB 7 (.cell dictSigned4) 4
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/ok/hit/max-boundary/4" stack #[instr], rng3)
    | 5 =>
        let stack : Array Value :=
          mkDictCaseStack valueC 0 (.cell (if isUnsigned then dictUnsigned4 else dictSigned4)) 0
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/ok/hit/0" stack #[instr], rng3)
    | 6 =>
        let stack : Array Value :=
          mkDictCaseStack valueA 2 (.cell dictUnsigned4) 4
        (mkDictIAddGetBCase "fuzz/err/key-range/signed/low" stack #[instrUnsigned], rng3)
    | 7 =>
        if isUnsigned then
          let stack : Array Value :=
            mkDictCaseStack valueA (-1) (.cell dictUnsigned8) 8
          (mkDictIAddGetBCase "fuzz/err/key-range/unsigned/negative" stack #[instrUnsigned], rng3)
        else
          let stack : Array Value :=
            mkDictCaseStack valueA 8 (.cell dictSigned4) 4
          (mkDictIAddGetBCase "fuzz/err/key-range/signed/high" stack #[instrSigned], rng3)
    | 8 =>
        if isUnsigned then
          let stack : Array Value :=
            mkDictCaseStack valueA 16 (.cell dictUnsigned4) 4
          (mkDictIAddGetBCase "fuzz/err/key-range/unsigned/high" stack #[instrUnsigned], rng3)
        else
          let stack : Array Value :=
            mkDictCaseStack valueA (-9) (.cell dictSigned4) 4
          (mkDictIAddGetBCase "fuzz/err/key-range/signed/low" stack #[instrSigned], rng3)
    | 9 =>
        if isUnsigned then
          let stack : Array Value :=
            mkDictCaseStack valueA 1 (.cell dictUnsigned4) 0
          (mkDictIAddGetBCase "fuzz/err/key-range/unsigned/zero-nonzero" stack #[instrUnsigned], rng3)
        else
          let stack : Array Value :=
            mkDictCaseStack valueA 1 (.cell dictSigned4) 0
          (mkDictIAddGetBCase "fuzz/err/key-range/signed/zero-nonzero" stack #[instrSigned], rng3)
    | 10 =>
        let stack : Array Value :=
          mkDictCaseStack valueA 3 (.cell dictSigned4) (-1)
        (mkDictIAddGetBCase "fuzz/err/n-negative" stack #[instrSigned], rng3)
    | 11 =>
        let stack : Array Value :=
          mkDictCaseStack valueA 3 (.cell dictSigned4) 1024
        (mkDictIAddGetBCase "fuzz/err/n-too-large" stack #[instrSigned], rng3)
    | 12 =>
        let stack : Array Value :=
          mkDictCaseStack valueA 3 (.cell dictSigned4) (-1)
        (mkDictIAddGetBCase "fuzz/err/n-negative" stack #[instrUnsigned], rng3)
    | 13 =>
        let stack : Array Value :=
          #[.builder valueA, .int (.num 3), .cell dictUnsigned4, .int .nan]
        (mkDictIAddGetBCase "fuzz/err/n-nan" stack #[instrUnsigned], rng3)
    | 14 =>
        let stack : Array Value :=
          mkDictCaseStack valueA 42 (.cell dictSigned4) 4
        (mkDictIAddGetBCase "fuzz/err/key-type" stack, rng3)
    | 15 =>
        let stack : Array Value :=
          mkDictCaseStack valueA 5 (.int (.num 11)) 4
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/err/dict-type" stack #[instr], rng3)
    | 16 =>
        let stack : Array Value :=
          #[.int (.num 42), .int (.num 5), .cell dictUnsigned4, intV 4]
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/err/value-type" stack #[instr], rng3)
    | 17 =>
        let stack : Array Value :=
          mkDictCaseStack valueA 5 (.cell malformedDictRoot) 4
        let instr := if isUnsigned then instrUnsigned else instrSigned
        (mkDictIAddGetBCase "fuzz/err/malformed-root" stack #[instr], rng3)
    | 18 =>
        let stack : Array Value := #[]
        (mkDictIAddGetBCase "fuzz/underflow/empty" stack, rng3)
    | 19 =>
        let stack : Array Value := #[.builder valueA]
        (mkDictIAddGetBCase "fuzz/underflow/one" stack, rng3)
    | 20 =>
        let stack : Array Value := #[.builder valueA, .int (.num 11)]
        (mkDictIAddGetBCase "fuzz/underflow/two" stack, rng3)
    | 21 =>
        let stack : Array Value :=
          #[.builder valueA, .int (.num 11), .cell dictUnsigned4]
        (mkDictIAddGetBCase "fuzz/underflow/three" stack, rng3)
    | 22 =>
        let stack : Array Value := mkDictCaseStack valueA 6 (.null) 4
        if isUnsigned then
          (mkGasCase "fuzz/gas/miss/unsigned/exact" stack instrUnsigned dictIAddGetBUnequalMissGas (oracleGasLimitsExact dictIAddGetBUnequalMissGas), rng3)
        else
          (mkGasCase "fuzz/gas/miss/signed/exact" stack instrSigned dictIAddGetBSignedMissGas (oracleGasLimitsExact dictIAddGetBSignedMissGas), rng3)
    | 23 =>
        let stack : Array Value := mkDictCaseStack valueA 6 (.null) 4
        if isUnsigned then
          (mkGasCase "fuzz/gas/miss/unsigned/exact-minus-one" stack instrUnsigned dictIAddGetBUnequalMissGasMinusOne (oracleGasLimitsExactMinusOne dictIAddGetBUnequalMissGasMinusOne), rng3)
        else
          (mkGasCase "fuzz/gas/miss/signed/exact-minus-one" stack instrSigned dictIAddGetBSignedMissGasMinusOne (oracleGasLimitsExactMinusOne dictIAddGetBSignedMissGasMinusOne), rng3)
    | _ =>
        let key := if isUnsigned then 3 else 4
        let stack : Array Value :=
          mkDictCaseStack valueA key (if isUnsigned then .cell dictUnsigned4 else .cell dictSigned4) 4
        if isUnsigned then
          (mkGasCase "fuzz/gas/hit/unsigned/exact" stack instrUnsigned dictIAddGetBUnequalExactGas (oracleGasLimitsExact dictIAddGetBUnequalExactGas), rng3)
        else
          (mkGasCase "fuzz/gas/hit/signed/exact" stack instrSigned dictIAddGetBSignedExactGas (oracleGasLimitsExact dictIAddGetBSignedExactGas), rng3)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

def suite : InstrSuite where
  id := dictIAddGetBId
  unit := #[
    { name := "unit/dispatch/next"
      run := do
        expectOkStack "dispatch/next"
          (runDictIAddGetBDispatch (mkDictCaseStack valueA 3 (.cell dictSigned4) 4))
          (mkDictCaseStack valueA 3 (.cell dictSigned4) 4 ++ #[.int (.num 777)])
    }
    ,
    { name := "unit/decoder/f456"
      run := do
        let _ ← expectDecodeStep "decode/f456" (Slice.ofCell rawF456) instrSigned 16
    }
    ,
    { name := "unit/decoder/f457"
      run := do
        let _ ← expectDecodeStep "decode/f457" (Slice.ofCell rawF457) instrUnsigned 16
    }
    ,
    { name := "unit/decoder/f455-f458"
      run := do
        let _ ← expectDecodeStep "decode/f455" (Slice.ofCell rawF455) (.dictExt (.mutGetB false false .add)) 16
        expectDecodeInvOpcode "decode/f458" rawF458
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/f4-8bit should fail")
    }
    ,
    { name := "unit/asm/encodes"
      run := do
        expectAssembleOk16 "asm/signed" instrSigned
        expectAssembleOk16 "asm/unsigned" instrUnsigned
    }
    ,
    { name := "unit/runtime/validation"
      run := do
        expectErr "underflow" (runDictIAddGetBDirect instrSigned #[]) .stkUnd
        expectErr "n-negative" (runDictIAddGetBDirect instrSigned (mkDictCaseStack valueA 4 (.cell dictSigned4) (-1))) .rangeChk
        expectErr "n-too-large" (runDictIAddGetBDirect instrSigned (mkDictCaseStack valueA 4 (.cell dictSigned4) 1024)) .rangeChk
        expectErr "n-nan" (runDictIAddGetBDirect instrUnsigned #[.builder valueA, .int (.num 4), .cell dictUnsigned4, .int .nan]) .rangeChk
        expectErr "n-type" (runDictIAddGetBDirect instrSigned #[.builder valueA, .int (.num 4), .cell dictSigned4, .tuple #[]]) .typeChk
        expectErr "key-type" (runDictIAddGetBDirect instrSigned #[.builder valueA, .slice (mkSliceFromBits (natToBits 0x03 2)), .cell dictSigned4, intV 4]) .typeChk
        expectErr "dict-type" (runDictIAddGetBDirect instrUnsigned #[.builder valueA, .int (.num 4), .tuple #[], intV 4]) .typeChk
        expectErr "value-type" (runDictIAddGetBDirect instrSigned (#[.int (.num 4), .int (.num 4), .cell dictSigned4, intV 4])) .typeChk
        expectErr "int-range-unsigned" (runDictIAddGetBDirect instrUnsigned (mkDictCaseStack valueA 16 (.cell dictUnsigned4) 4)) .rangeChk
        expectErr "int-range-signed-high" (runDictIAddGetBDirect instrSigned (mkDictCaseStack valueA 8 (.cell dictSigned4) 4)) .rangeChk
        expectErr "int-range-signed-low" (runDictIAddGetBDirect instrSigned (mkDictCaseStack valueA (-9) (.cell dictSigned4) 4)) .rangeChk
        match runDictIAddGetBDirect instrSigned (mkDictCaseStack valueA 4 (.cell malformedDictRoot) 4) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e => throw (IO.userError s!"dict-err: expected dictErr or cellUnd, got {reprStr e}")
        | .ok st => throw (IO.userError s!"dict-err: expected error, got stack {reprStr st}")
      }
  ]
  oracle := #[
    -- [B1] dispatch branch via next fallback.
    mkCodeCase "oracle/code/dispatch-fallback" (mkDictCaseStack valueA 3 (.cell dictSigned4) 4) rawF456
    -- [B2] successful miss in signed mode from empty dictionary.
    , mkDictIAddGetBCase "oracle/ok/miss/signed/null/4" (mkDictCaseStack valueA (-4) .null 4) (#[instrSigned])
    -- [B2] successful miss in unsigned mode from empty dictionary.
    , mkDictIAddGetBCase "oracle/ok/miss/unsigned/null/4" (mkDictCaseStack valueA 6 (.null) 4) (#[instrUnsigned])
    -- [B2] successful miss in signed mode at n=0.
    , mkDictIAddGetBCase "oracle/ok/miss/signed/null/0" (mkDictCaseStack valueA 0 .null 0) (#[instrSigned])
    -- [B2] successful miss in unsigned mode at n=0.
    , mkDictIAddGetBCase "oracle/ok/miss/unsigned/null/0" (mkDictCaseStack valueA 0 .null 0) (#[instrUnsigned])
    -- [B2] successful miss in non-empty signed dictionary.
    , mkDictIAddGetBCase "oracle/ok/miss/signed/non-empty/4" (mkDictCaseStack valueA 5 (.cell dictSigned4) 4) (#[instrSigned])
    -- [B2] successful miss in non-empty unsigned dictionary.
    , mkDictIAddGetBCase "oracle/ok/miss/unsigned/non-empty/4" (mkDictCaseStack valueA 6 (.cell dictUnsigned4) 4) (#[instrUnsigned])
    -- [B5] hit path in signed mode.
    , mkDictIAddGetBCase "oracle/ok/hit/signed/3" (mkDictCaseStack valueA (-1) (.cell dictSigned4) 4) (#[instrSigned])
    -- [B5] hit path boundary max in signed mode.
    , mkDictIAddGetBCase "oracle/ok/hit/signed/max" (mkDictCaseStack valueA 7 (.cell dictSigned4) 4) (#[instrSigned])
    -- [B5] hit path boundary min in signed mode.
    , mkDictIAddGetBCase "oracle/ok/hit/signed/min" (mkDictCaseStack valueA (-8) (.cell dictSigned4) 4) (#[instrSigned])
    -- [B5] hit path in unsigned mode.
    , mkDictIAddGetBCase "oracle/ok/hit/unsigned/2" (mkDictCaseStack valueA 2 (.cell dictUnsigned4) 4) (#[instrUnsigned])
    -- [B5] hit path boundary max in unsigned mode.
    , mkDictIAddGetBCase "oracle/ok/hit/unsigned/max" (mkDictCaseStack valueA 15 (.cell dictUnsigned4) 4) (#[instrUnsigned])
    -- [B5] hit path in zero-width key mode.
    , mkDictIAddGetBCase "oracle/ok/hit/signed/zero" (mkDictCaseStack valueA 0 (.cell dictSigned0) 0) (#[instrSigned])
    -- [B5] hit path in zero-width unsigned mode.
    , mkDictIAddGetBCase "oracle/ok/hit/unsigned/zero" (mkDictCaseStack valueA 0 (.cell dictUnsigned0) 0) (#[instrUnsigned])
    -- [B4] `n` validation errors.
    , mkDictIAddGetBCase "oracle/err/n-negative" (mkDictCaseStack valueA 3 (.cell dictSigned4) (-1)) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/n-too-large" (mkDictCaseStack valueA 3 (.cell dictSigned4) 1024) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/n-nan" #[.builder valueA, .int (.num 3), .cell dictUnsigned4, .int .nan] (#[instrUnsigned])
    , mkDictIAddGetBCase "oracle/err/n-type" #[.builder valueA, .int (.num 3), .cell dictUnsigned4, .tuple #[]] (#[instrUnsigned])
    -- [B4] integer key conversion errors (signed and unsigned ranges).
    , mkDictIAddGetBCase "oracle/err/key-range/unsigned/negative" (mkDictCaseStack valueA (-1) (.cell dictUnsigned4) 4) (#[instrUnsigned])
    , mkDictIAddGetBCase "oracle/err/key-range/unsigned/high" (mkDictCaseStack valueA 16 (.cell dictUnsigned4) 4) (#[instrUnsigned])
    , mkDictIAddGetBCase "oracle/err/key-range/signed/high" (mkDictCaseStack valueA 8 (.cell dictSigned4) 4) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/key-range/signed/low" (mkDictCaseStack valueA (-9) (.cell dictSigned4) 4) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/key-range/signed/zero-nonzero" (mkDictCaseStack valueA 1 (.cell dictSigned4) 0) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/key-range/unsigned/zero-nonzero" (mkDictCaseStack valueA 1 (.cell dictUnsigned4) 0) (#[instrUnsigned])
    -- [B7] type errors.
    , mkDictIAddGetBCase "oracle/err/key-type" #[.builder valueA, .slice (mkSliceFromBits (natToBits 0x3 2)), .cell dictSigned4, intV 4] (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/dict-type" (mkDictCaseStack valueA 4 (.tuple #[]) 4) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/value-type" (#[.int (.num 4), .int (.num 4), .cell dictSigned4, intV 4]) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/value-type/intnan-key" (#[.builder valueA, .int .nan, .cell dictSigned4, intV 4]) (#[instrSigned])
    -- [B8] malformed dictionary structure.
    , mkDictIAddGetBCase "oracle/err/malformed-root/signed" (mkDictCaseStack valueA 4 (.cell malformedDictRoot) 4) (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/malformed-root/unsigned" (mkDictCaseStack valueA 4 (.cell malformedDictRoot) 4) (#[instrUnsigned])
    -- [B7] underflow coverage.
    , mkDictIAddGetBCase "oracle/err/underflow/0" #[] (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/underflow/1" #[.builder valueA] (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/underflow/2" #[.builder valueA, .int (.num 4)] (#[instrSigned])
    , mkDictIAddGetBCase "oracle/err/underflow/3" #[.builder valueA, .int (.num 4), .cell dictSigned4] (#[instrSigned])
    -- [B9] raw opcode decode variants through code cell execution.
    , mkCodeCase "oracle/code/f455" (mkDictCaseStack valueA 5 (.cell dictSigned4) 4) rawF455
    , mkCodeCase "oracle/code/f456" (mkDictCaseStack valueA 5 (.cell dictSigned4) 4) rawF456
    , mkCodeCase "oracle/code/f457" (mkDictCaseStack valueA 6 (.cell dictUnsigned4) 4) rawF457
    , mkCodeCase "oracle/code/f458" (mkDictCaseStack valueA 6 (.cell dictSigned4) 4) rawF458
    -- [B11] gas exactness.
    , mkGasCase "oracle/gas/miss-signed-exact" (mkDictCaseStack valueA 6 (.null) 4) instrSigned dictIAddGetBSignedMissGas (oracleGasLimitsExact dictIAddGetBSignedMissGas)
    , mkGasCase "oracle/gas/miss-signed-exact-minus-one" (mkDictCaseStack valueA 6 (.null) 4) instrSigned dictIAddGetBSignedMissGasMinusOne (oracleGasLimitsExactMinusOne dictIAddGetBSignedMissGasMinusOne)
    , mkGasCase "oracle/gas/miss-unsigned-exact" (mkDictCaseStack valueA 6 (.null) 4) instrUnsigned dictIAddGetBUnequalMissGas (oracleGasLimitsExact dictIAddGetBUnequalMissGas)
    , mkGasCase "oracle/gas/miss-unsigned-exact-minus-one" (mkDictCaseStack valueA 6 (.null) 4) instrUnsigned dictIAddGetBUnequalMissGasMinusOne (oracleGasLimitsExactMinusOne dictIAddGetBUnequalMissGasMinusOne)
    , mkGasCase "oracle/gas/hit-signed-exact" (mkDictCaseStack valueA (-1) (.cell dictSigned4) 4) instrSigned dictIAddGetBSignedExactGas (oracleGasLimitsExact dictIAddGetBSignedExactGas)
    , mkGasCase "oracle/gas/hit-unsigned-exact" (mkDictCaseStack valueA 2 (.cell dictUnsigned4) 4) instrUnsigned dictIAddGetBUnequalExactGas (oracleGasLimitsExact dictIAddGetBUnequalExactGas)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictIAddGetBId
      count := 500
      gen := genDictIAddGetBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIADDGETB
