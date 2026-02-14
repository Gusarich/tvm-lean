import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUADDB

/-
INSTRUCTION: DICTUADDB

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Runtime success path (empty/non-empty dictionary miss):
   - Stack order is `[builder, key, dict?, n]`.
   - `n` is checked by `VM.popNatUpTo 1023`.
   - For integer-key mode (`intKey = true`, `unsigned = true`), key conversion uses
     `dictKeyBits? key n true`.
   - `dictSetBuilderWithCells` with `.add` returns `ok=true` for miss
     (possibly creating dictionary cells).
   - VM pushes `newRoot` and `-1`.
   - If `created > 0`, gas surcharge is `created * cellCreateGasPrice`.

2. [B2] Runtime success path (existing-key hit):
   - For `.add` mode, dictionary miss branch is rejected and `ok=false`.
   - VM leaves unchanged root and pushes `0`.

3. [B3] Runtime underflow path:
   - `VM.checkUnderflow 4` is enforced before value extraction.
   - Any stack with fewer than 4 items raises `.stkUnd`.

4. [B4] Runtime argument and value validation failures:
   - `n` must be in `[0, 1023]` (`.rangeChk` on negative, too large, or NaN).
   - Key must be representable as unsigned `n`-bit integer:
     - `n = 0` accepts only key `0`.
     - negative keys or keys `≥ 2^n` produce `.rangeChk`.
   - `dict` must be maybe-cell and key/value must have correct types for unsigned int-key/builder-path.

5. [B5] Runtime dictionary structural errors:
   - Malformed existing root can return `.dictErr` from dictionary helpers.
   - On failure, already-loaded nodes are registered before rethrow.

6. [B6] Assembler encoding behavior:
   - `.dictSetB true true .add` is not supported by `assembleCp0`.
   - This includes non-integer-key add variants like `.dictSetB false false .add`, `.dictSetB true false .add`, `.dictSetB false true .add`.

7. [B7] Decoder boundary behavior:
   - `0xf453` decodes to `.dictSetB true true .add`.
   - The same family decodes `0xf451` / `0xf452` to `ADDB` and `IADDB` variants.
   - `0xf450` and `0xf454` are invalid.
   - Truncated inputs/aliasing around opcode boundaries must preserve failure semantics.

8. [B8] Gas accounting:
   - Base cost is from `computeExactGasBudget`.
   - Exact base budget succeeds, exact-1 fails.
   - Miss-path with additional `created` nodes must account for `created * cellCreateGasPrice`.

TOTAL BRANCHES: 8
-/

private def dictUADDBId : InstrId := { name := "DICTUADDB" }
private def dictUADDBInstr : Instr := .dictSetB true true .add

private def dictUADDBCode : Cell := Cell.mkOrdinary (natToBits 0xf453 16) #[]
private def dictADDBCode : Cell := Cell.mkOrdinary (natToBits 0xf451 16) #[]
private def dictIADDBCode : Cell := Cell.mkOrdinary (natToBits 0xf452 16) #[]
private def dictUADDBLowerInvalid : Cell := Cell.mkOrdinary (natToBits 0xf450 16) #[]
private def dictUADDBUpperInvalid : Cell := Cell.mkOrdinary (natToBits 0xf454 16) #[]
private def dictUADDBTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xf453 8) #[]

private def builderVal : Builder := Builder.empty.storeBits (natToBits 1 1)
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkDictUnsignedRoot! (label : String) (n : Nat) (keys : Array Int) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for key in keys do
      let keyBits :=
        match dictKeyBits? key n true with
        | some bits => bits
        | none => panic! s!"{label}: key out of range (n={n}, key={key})"
      match dictSetBuilderWithCells root keyBits builderVal .set with
      | .ok (some r, _, _, _) =>
          root := some r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root after insert"
      | .error e =>
          panic! s!"{label}: build failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary output"

private def dictU0 : Cell := mkDictUnsignedRoot! "dict/unsigned/n0" 0 #[0]
private def dictU1 : Cell := mkDictUnsignedRoot! "dict/unsigned/n1" 1 #[0, 1]
private def dictU2 : Cell := mkDictUnsignedRoot! "dict/unsigned/n2" 2 #[1, 2, 3]
private def dictU4 : Cell := mkDictUnsignedRoot! "dict/unsigned/n4" 4 #[3, 12, 15]
private def dictU8 : Cell := mkDictUnsignedRoot! "dict/unsigned/n8" 8 #[42, 200, 255]
private def dictU16 : Cell := mkDictUnsignedRoot! "dict/unsigned/n16" 16 #[256, 2048]
private def dictU32 : Cell := mkDictUnsignedRoot! "dict/unsigned/n32" 32 #[5, 17, 65535]

private def dictUForN (n : Nat) : Value :=
  match n with
  | 0 => .cell dictU0
  | 1 => .cell dictU1
  | 2 => .cell dictU2
  | 4 => .cell dictU4
  | 8 => .cell dictU8
  | 16 => .cell dictU16
  | 32 => .cell dictU32
  | _ => .null

private def hitKeyForN (n : Nat) : Int :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 4 => 3
  | 8 => 42
  | 16 => 256
  | 32 => 5
  | _ => 0

private def missKeyForN (n : Nat) : Int :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 4 => 7
  | 8 => 128
  | 16 => 512
  | 32 => 42
  | _ => 1

private def mkCaseStack
    (n : Int)
    (key : Int)
    (dict : Value := .null)
    (value : Builder := builderVal) : Array Value :=
  #[.builder value, intV key, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictUADDBInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUADDBId
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
    instr := dictUADDBId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictUADDBDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSetB dictUADDBInstr stack

private def runDictUADDBDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSetB dictUADDBInstr (VM.push (intV 1001)) stack

private def expectAssembleInvOpcode (name : String) (expected : Excno) (code : Instr) : IO Unit := do
  match assembleCp0 [code] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{name}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{name}: expected assembler failure {expected}, got success")

private def expectDecodeInvOpcode (name : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{name}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{name}: expected invOpcode, got {reprStr instr} with {bits} bits")

private def expectDecode16 (name : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{name}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{name}: expected no trailing bits")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{name}: expected valid decode, got {e}")

private def opRawSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

private def dictUADDBExactGas : Int := computeExactGasBudget dictUADDBInstr
private def dictUADDBExactGasMinusOne : Int := computeExactGasBudgetMinusOne dictUADDBInstr

private def createdOnInsert (root : Option Cell) (n : Nat) (key : Int) : Nat :=
  match dictKeyBits? key n true with
  | none => 0
  | some keyBits =>
      match dictSetBuilderWithCells root keyBits builderVal .add with
      | .ok (_, _ok, created, _) => created
      | .error _ => 0

private def dictUADDBInsertGasN4Empty : Int :=
  dictUADDBExactGas + Int.ofNat (createdOnInsert none 4 7) * cellCreateGasPrice

private def dictUADDBInsertGasN4NonEmpty : Int :=
  dictUADDBExactGas + Int.ofNat (createdOnInsert (some dictU4) 4 7) * cellCreateGasPrice

private def dictUADDBInsertGasN4EmptyMinusOne : Int :=
  if dictUADDBInsertGasN4Empty > 0 then dictUADDBInsertGasN4Empty - 1 else 0

private def dictUADDBInsertGasN4NonEmptyMinusOne : Int :=
  if dictUADDBInsertGasN4NonEmpty > 0 then dictUADDBInsertGasN4NonEmpty - 1 else 0

private def pickNForFuzz (rng0 : StdGen) : Nat × StdGen :=
  let (raw, rng1) := randNat rng0 0 7
  let n : Nat :=
    match raw with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | 4 => 5
    | 5 => 8
    | 6 => 16
    | _ => 32
  (n, rng1)

private def pickInRangeKeyUnsigned (n : Nat) (rng0 : StdGen) : Int × StdGen :=
  if n = 0 then
    (0, rng0)
  else
    let maxNat : Nat := (1 <<< n) - 1
    let max : Int := Int.ofNat maxNat
    let maxHalf : Int := Int.ofNat (maxNat / 2)
    let (mode, rng1) := randNat rng0 0 5
    let pick : Int :=
      if mode = 0 then
        0
      else if mode = 1 then
        max
      else if mode = 2 then
        maxHalf
      else if mode = 3 then
        1
      else
        max - 1
    (pick, rng1)

private def pickOutOfRangeKeyUnsigned (n : Nat) (rng0 : StdGen) : Int × StdGen :=
  if n = 0 then
    (1, rng0)
  else
    let max : Int := Int.ofNat ((1 <<< n) - 1)
    let (mode, rng1) := randNat rng0 0 3
    if mode = 0 then
      (max + 1, rng1)
    else if mode = 1 then
      (max + 2, rng1)
    else
      (-1, rng1)

private def genDICTUADDBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (n, rng2) := pickNForFuzz rng1
  let nI : Int := Int.ofNat n
  let (inRangeKey, rng3) := pickInRangeKeyUnsigned n rng2
  let (outRangeKey, rng4) := pickOutOfRangeKeyUnsigned n rng3
  match shape with
  | 0 =>
      (mkCase "fuzz/underflow/empty" #[], rng1)
  | 1 =>
      (mkCase "fuzz/underflow/one" #[intV 1], rng2)
  | 2 =>
      (mkCase "fuzz/underflow/two" #[intV 1, .cell Cell.empty], rng3)
  | 3 =>
      (mkCase "fuzz/underflow/three" #[.builder builderVal, intV 1, .null], rng4)
  | 4 =>
      (mkCase "fuzz/ok/miss/null" (mkCaseStack nI inRangeKey .null), rng4)
  | 5 =>
      if n = 0 then
        (mkCase "fuzz/ok/miss/null-n0" (mkCaseStack nI 0 .null), rng4)
      else
        (mkCase "fuzz/ok/miss/non-empty" (mkCaseStack nI (missKeyForN n) (dictUForN n)), rng4)
  | 6 =>
      (mkCase "fuzz/ok/miss/prefix-mismatch" (mkCaseStack nI (missKeyForN n) (dictUForN n)), rng4)
  | 7 =>
      (mkCase "fuzz/ok/hit" (mkCaseStack nI (hitKeyForN n) (dictUForN n)), rng4)
  | 8 =>
      (mkCase "fuzz/ok/hit/zero-width" (mkCaseStack 0 0 (.cell dictU0)), rng4)
  | 9 =>
      (mkCase "fuzz/err/key/unsigned-negative" (mkCaseStack nI (-1) .null), rng4)
  | 10 =>
      (mkCase "fuzz/err/key/out-of-range" (mkCaseStack nI outRangeKey .null), rng4)
  | 11 =>
      (mkCase "fuzz/err/n/negative" (mkCaseStack (-1) 0 .null), rng4)
  | 12 =>
      (mkCase "fuzz/err/n/too-large" (mkCaseStack 1024 0 .null), rng4)
  | 13 =>
      (mkCase "fuzz/err/n/nan" #[.builder builderVal, intV 1, .cell dictU1, .int .nan], rng4)
  | 14 =>
      (mkCase "fuzz/err/type/dict" (mkCaseStack nI inRangeKey (.int (.num 7))), rng4)
  | 15 =>
      (mkCase "fuzz/err/type/key" (#[.builder builderVal, .null, .cell dictU4, intV nI]), rng4)
  | 16 =>
      (mkCase "fuzz/err/type/value" (#[(.tuple #[]), intV inRangeKey, .cell dictU4, intV nI]), rng4)
  | 17 =>
      (mkCase "fuzz/err/dict-structural" (mkCaseStack nI inRangeKey (.cell malformedDict)), rng4)
  | 18 =>
      (mkCodeCase "fuzz/decode/uadb" (mkCaseStack 4 7 .null) dictUADDBCode, rng4)
  | 19 =>
      (mkCodeCase "fuzz/decode/iadb" (mkCaseStack 4 7 .null) dictIADDBCode, rng4)
  | 20 =>
      (mkCodeCase "fuzz/decode/adb" (mkCaseStack 4 7 .null) dictADDBCode, rng4)
  | _ =>
      (mkCodeCase "fuzz/decode/invalid-lower" #[] dictUADDBLowerInvalid, rng4)


def suite : InstrSuite where
  id := dictUADDBId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runDictUADDBDispatchFallback #[])
          #[intV 1001] },
    { name := "unit/runtime/ok/miss-on-null"
      run := do
        let expected1 : Cell :=
          mkDictUnsignedRoot! "unit/miss/null/n4" 4 #[5]
        expectOkStack "runtime/miss-null-n4"
          (runDictUADDBDirect (mkCaseStack 4 7 .null))
          #[.cell expected1, intV (-1)] },
    { name := "unit/runtime/ok/hit-preserved"
      run := do
        let existing := mkDictUnsignedRoot! "unit/hit/n4" 4 #[3, 12]
        expectOkStack "runtime/hit"
          (runDictUADDBDirect (mkCaseStack 4 3 (.cell existing)))
          #[.cell existing, intV 0] },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "runtime/underflow-empty" (runDictUADDBDirect #[]) .stkUnd
        expectErr "runtime/underflow-one" (runDictUADDBDirect #[.builder builderVal]) .stkUnd
        expectErr "runtime/underflow-two" (runDictUADDBDirect #[.builder builderVal, intV 1]) .stkUnd
        expectErr "runtime/underflow-three" (runDictUADDBDirect #[.builder builderVal, intV 1, .cell Cell.empty]) .stkUnd },
    { name := "unit/runtime/validation-and-errors"
      run := do
        expectErr "runtime/n-negative" (runDictUADDBDirect (mkCaseStack (-1) 1 .null)) .rangeChk
        expectErr "runtime/n-too-large" (runDictUADDBDirect (mkCaseStack 1024 1 .null)) .rangeChk
        expectErr "runtime/key-too-large" (runDictUADDBDirect (mkCaseStack 4 16 .null)) .rangeChk
        expectErr "runtime/key-negative" (runDictUADDBDirect (mkCaseStack 4 (-1) .null)) .rangeChk
        expectErr "runtime/n-zero-with-nonzero-key" (runDictUADDBDirect (mkCaseStack 0 1 .null)) .rangeChk
        expectErr "runtime/dict-type" (runDictUADDBDirect (mkCaseStack 4 3 (.int (.num 7)))) .typeChk
        expectErr "runtime/key-type" (runDictUADDBDirect (#[.builder builderVal, .null, .cell dictU4, intV 4])) .typeChk
        expectErr "runtime/value-type" (runDictUADDBDirect (#[(.int (.num 1)), intV 3, .cell dictU4, intV 4])) .typeChk
        expectErr "runtime/dict-err" (runDictUADDBDirect (mkCaseStack 4 3 (.cell malformedDict))) .dictErr },
    { name := "unit/asm-and-decode"
      run := do
        expectAssembleInvOpcode "assemble/uaddb" .invOpcode (.dictSetB true true .add)
        expectAssembleInvOpcode "assemble/iadb" .invOpcode (.dictSetB true false .add)
        expectAssembleInvOpcode "assemble/adb" .invOpcode (.dictSetB false false .add)
        expectDecode16 "decode/uadb" dictUADDBCode (.dictSetB true true .add)
        expectDecode16 "decode/iadb" dictIADDBCode (.dictSetB true false .add)
        expectDecode16 "decode/adb" dictADDBCode (.dictSetB false false .add)
        expectDecodeInvOpcode "decode/invalid-lower" dictUADDBLowerInvalid
        expectDecodeInvOpcode "decode/invalid-upper" dictUADDBUpperInvalid
        expectDecodeInvOpcode "decode/truncated-8" dictUADDBTruncated8 }
  ]
  oracle := #[
    -- [B1] Unsigned miss on empty dictionary.
    mkCase "oracle/ok/miss-empty-n0-key0" (mkCaseStack 0 0 .null),
    -- [B1] Unsigned miss on empty dictionary.
    mkCase "oracle/ok/miss-empty-n1-key1" (mkCaseStack 1 1 .null),
    -- [B1] Unsigned miss on empty dictionary.
    mkCase "oracle/ok/miss-empty-n4-key7" (mkCaseStack 4 7 .null),
    -- [B1] Unsigned miss on empty dictionary.
    mkCase "oracle/ok/miss-empty-n8-key255" (mkCaseStack 8 255 .null),
    -- [B1] Unsigned miss in non-empty dictionary with diverging path.
    mkCase "oracle/ok/miss-nonempty-n2-key1" (mkCaseStack 2 1 (.cell dictU2)),
    -- [B1] Unsigned miss in non-empty dictionary.
    mkCase "oracle/ok/miss-nonempty-n4-key7" (mkCaseStack 4 7 (.cell dictU4)),
    -- [B1] Miss under mixed root (additional boundary check).
    mkCase "oracle/ok/miss-nonempty-n8-key128" (mkCaseStack 8 128 (.cell dictU8)),

    -- [B2] Existing-key hit preserves root.
    mkCase "oracle/ok/hit-n0-key0" (mkCaseStack 0 0 (.cell dictU0)),
    -- [B2] Existing-key hit preserves root.
    mkCase "oracle/ok/hit-n1-key1" (mkCaseStack 1 1 (.cell dictU1)),
    -- [B2] Existing-key hit preserves root.
    mkCase "oracle/ok/hit-n4-key3" (mkCaseStack 4 3 (.cell dictU4)),
    -- [B2] Existing-key hit preserves root.
    mkCase "oracle/ok/hit-n4-key12" (mkCaseStack 4 12 (.cell dictU4)),
    -- [B2] Existing-key hit in wider width.
    mkCase "oracle/ok/hit-n8-key42" (mkCaseStack 8 42 (.cell dictU8)),
    -- [B2] Existing-key hit with another width.
    mkCase "oracle/ok/hit-n16-key256" (mkCaseStack 16 256 (.cell dictU16)),

    -- [B3] Key range underflow for n=0.
    mkCase "oracle/err/key-range/n0-key1" (mkCaseStack 0 1 .null),
    -- [B3] Negative key is rejected.
    mkCase "oracle/err/key-range/negative" (mkCaseStack 4 (-1) .null),
    -- [B3] Key too large is rejected.
    mkCase "oracle/err/key-range/overflow-4" (mkCaseStack 4 16 .null),
    -- [B3] Key too large is rejected (mid-size).
    mkCase "oracle/err/key-range/overflow-8" (mkCaseStack 8 256 .null),
    -- [B3] Key overflow at wider size.
    mkCase "oracle/err/key-range/overflow-16" (mkCaseStack 16 65536 .null),
    -- [B4] Stack underflow and argument-order family.
    mkCase "oracle/err/underflow/empty" #[],
    -- [B4] Stack underflow and argument-order family.
    mkCase "oracle/err/underflow/one" #[intV 1],
    -- [B4] Stack underflow and argument-order family.
    mkCase "oracle/err/underflow/two" #[intV 1, .cell Cell.empty],
    -- [B4] Stack underflow and argument-order family.
    mkCase "oracle/err/underflow/three" #[.builder builderVal, intV 1, .cell dictU4],

    -- [B4] n/stack/range validation.
    mkCase "oracle/err/n-range/negative" (mkCaseStack (-1) 0 .null),
    -- [B4] n/stack/range validation.
    mkCase "oracle/err/n-range/too-large" (mkCaseStack 1024 0 .null),
    -- [B4] n/stack/range validation.
    mkCase "oracle/err/n-range/nan" (#[(.builder builderVal), intV 1, .cell dictU4, .int .nan]),

    -- [B4] Type validation failure.
    mkCase "oracle/err/type/dict" (mkCaseStack 4 3 (.int (.num 7))),
    -- [B4] Type validation failure.
    mkCase "oracle/err/type/key" (#[.builder builderVal, .null, .cell dictU4, intV 4]),
    -- [B4] Type validation failure.
    mkCase "oracle/err/type/value" (#[(.int (.num 1)), intV 3, .cell dictU4, intV 4]),

    -- [B5] Malformed root branch.
    mkCase "oracle/err/dict-structural" (mkCaseStack 4 3 (.cell malformedDict)),
    -- [B5] Malformed root branch (same failure family, same depth).
    mkCase "oracle/err/dict-structural-n8" (mkCaseStack 8 42 (.cell malformedDict)),

    -- [B7] Decoder boundaries and opcode families.
    mkCodeCase "oracle/decode/uadb" (mkCaseStack 4 3 .null) dictUADDBCode,
    -- [B7] Decoder boundaries and opcode families.
    mkCodeCase "oracle/decode/iadb" (mkCaseStack 4 3 .null) dictIADDBCode,
    -- [B7] Decoder boundaries and opcode families.
    mkCodeCase "oracle/decode/adb" (mkCaseStack 4 3 .null) dictADDBCode,
    -- [B7] Decoder boundaries and opcode families.
    mkCodeCase "oracle/decode/invalid-lower" #[] dictUADDBLowerInvalid,
    -- [B7] Decoder boundaries and opcode families.
    mkCodeCase "oracle/decode/invalid-upper" #[] dictUADDBUpperInvalid,
    -- [B7] Decoder/truncation branch.
    mkCodeCase "oracle/decode/truncated-8" #[] dictUADDBTruncated8,

    -- [B8] Exact base gas succeeds with no extra created penalty on deterministic hit.
    mkCase "oracle/gas/exact-hit"
      (mkCaseStack 4 3 (.cell dictU4))
      (#[.pushInt (.num dictUADDBExactGas), .tonEnvOp .setGasLimit, dictUADDBInstr])
      (oracleGasLimitsExact dictUADDBExactGas),
    -- [B8] Exact-1 gas for base budget fails.
    mkCase "oracle/gas/exact-hit-minus-one"
      (mkCaseStack 4 3 (.cell dictU4))
      (#[.pushInt (.num dictUADDBExactGasMinusOne), .tonEnvOp .setGasLimit, dictUADDBInstr])
      (oracleGasLimitsExactMinusOne dictUADDBExactGasMinusOne),
    -- [B8] Empty-root miss gas includes dynamic create penalty.
    mkCase "oracle/gas/exact-miss-empty"
      (mkCaseStack 4 7 .null)
      (#[.pushInt (.num dictUADDBInsertGasN4Empty), .tonEnvOp .setGasLimit, dictUADDBInstr])
      (oracleGasLimitsExact dictUADDBInsertGasN4Empty),
    -- [B8] Empty-root miss gas penalty branch: exact-1 fails.
    mkCase "oracle/gas/exact-miss-empty-minus-one"
      (mkCaseStack 4 7 .null)
      (#[.pushInt (.num dictUADDBInsertGasN4EmptyMinusOne), .tonEnvOp .setGasLimit, dictUADDBInstr])
      (oracleGasLimitsExactMinusOne dictUADDBInsertGasN4EmptyMinusOne),
    -- [B8] Non-empty miss can have broader create penalty term.
    mkCase "oracle/gas/exact-miss-non-empty"
      (mkCaseStack 4 7 (.cell dictU4))
      (#[.pushInt (.num dictUADDBInsertGasN4NonEmpty), .tonEnvOp .setGasLimit, dictUADDBInstr])
      (oracleGasLimitsExact dictUADDBInsertGasN4NonEmpty),
    -- [B8] Non-empty miss penalty minus one branch.
    mkCase "oracle/gas/exact-miss-non-empty-minus-one"
      (mkCaseStack 4 7 (.cell dictU4))
      (#[.pushInt (.num dictUADDBInsertGasN4NonEmptyMinusOne), .tonEnvOp .setGasLimit, dictUADDBInstr])
      (oracleGasLimitsExactMinusOne dictUADDBInsertGasN4NonEmptyMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictUADDBId
      count := 500
      gen := genDICTUADDBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUADDB
