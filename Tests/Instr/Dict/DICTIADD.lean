import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIADD

/-
INSTRUCTION: DICTIADD

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1: Runtime success path] Signed and unsigned add-mode insertion on missing key:
   - Stack order is [value, key, dict, n].
   - key bits are formed through `dictKeyBits?` and `dictSet*WithCells`.
   - success pushes new dictionary root and `-1`.

2. [B2: Runtime duplicate path] Add on existing key:
   - `dictSet*WithCells` returns `ok = false` and existing root for both by-ref and slice payload paths.
   - success pushes existing root and `0`.

3. [B3: Key / n conversion errors] Invalid bit-size or key conversion failures map to:
   - `n = 0` with non-zero key (`cellUnd`),
   - signed overflow/underflow around [-2^(n-1), 2^(n-1)-1],
   - unsigned overflow/underflow, and
   - NaN key / malformed bit conversion.

4. [B4: Underflow and argument type errors] This instruction requires 4 stack items.
   - Missing values must produce `.stkUnd` before any numeric conversion.
   - Wrong types on stack after underflow must produce `.typeChk` in pop order (dict root, key, new value).
   - invalid `n` gives `.rangeChk`.

5. [B5: Structural dictionary errors] Malformed dictionary roots should raise `dictErr`.

6. [B6: Assembler encoding] `.dictSet true unsigned byRef .add` has defined encodings:
   - 0xf432 / 0xf433 for signed, by-ref clear/set.
   - 0xf436 / 0xf437 for unsigned, by-ref clear/set.
   - Non-int-key combinations (e.g., `.dictSet false true false .add`) are unsupported and must encode as `.invOpcode`.

7. [B7: Decoder boundaries] `Codepage` decode maps 0xf432..0xf437 to `.dictSet true unsigned byRef .add`.
   - Adjacent opcodes below/above the range must decode as `.invOpcode`.

8. [B8: Gas accounting] Base instruction gas is validated with exact/minus-one execution budgets.
   - Miss-path uses creation, which adds dynamic dictionary gas.
   - Hit-path is deterministic (`created = 0`) and suitable for exact/minus-one gas probes.

9. [B9: Fuzzer branch coverage] Any branch not explicitly hit by oracle tests must be reachable by the fuzzer:
   - success/failure, byRef toggles, signed/unsigned key mode, malformed roots, and both underflow/type/range families.

TOTAL BRANCHES: 9
-/

private def dictIAddId : InstrId := { name := "DICTIADD" }

private def mkInstr (unsigned byRef : Bool) : Instr :=
  .dictSet true unsigned byRef .add

private def mkValidSliceValue : Slice :=
  mkSliceFromBits (natToBits 0x55 8)

private def mkValidRefValue : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def mkBadSliceValue : Slice :=
  mkSliceFromBits (natToBits 0xEE 8)

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictRootSlice! (label : String) (key : Int) (n : Nat) (unsigned : Bool) (value : Slice) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n unsigned with
    | some bits => bits
    | none => panic! s!"{label}: invalid key ({key}, n={n}, unsigned={unsigned})"
  match dictSetSliceWithCells none keyBits value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected dict root, got none"
  | .error e => panic! s!"{label}: dict set failed: {reprStr e}"

private def mkDictRootRef! (label : String) (key : Int) (n : Nat) (unsigned : Bool) (value : Cell) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n unsigned with
    | some bits => bits
    | none => panic! s!"{label}: invalid key ({key}, n={n}, unsigned={unsigned})"
  match dictSetRefWithCells none keyBits value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected dict root, got none"
  | .error e => panic! s!"{label}: dict set failed: {reprStr e}"

private def dictSignedHitSlice : Cell :=
  mkDictRootSlice! "dict/signed/hit/slice" (-3) 4 false mkValidSliceValue

private def dictSignedHitRef : Cell :=
  mkDictRootRef! "dict/signed/hit/ref" (-3) 4 false mkValidRefValue

private def dictSignedOtherKey : Cell :=
  mkDictRootSlice! "dict/signed/other/key" 2 4 false mkValidSliceValue

private def dictUnsignedHitSlice : Cell :=
  mkDictRootSlice! "dict/unsigned/hit/slice" 13 4 true mkValidSliceValue

private def dictUnsignedHitRef : Cell :=
  mkDictRootRef! "dict/unsigned/hit/ref" 13 4 true mkValidRefValue

private def dictUnsignedOtherKey : Cell :=
  mkDictRootSlice! "dict/unsigned/other/key" 2 4 true mkValidSliceValue

private def dictZeroKeySigned : Cell :=
  mkDictRootSlice! "dict/zero/key/signed" 0 0 false mkValidSliceValue

private def dictZeroKeyUnsigned : Cell :=
  mkDictRootSlice! "dict/zero/key/unsigned" 0 0 true mkValidSliceValue

private def mkCaseStack
    (unsigned byRef : Bool)
    (key : Int)
    (dict : Value)
    (n : Int)
    (newValue : Value := if byRef then .cell mkValidRefValue else .slice mkValidSliceValue)
    : Array Value :=
  #[newValue, .int (.num key), dict, .int (.num n)]

private def mkCaseStackWithNVal
    (unsigned byRef : Bool)
    (key : Int)
    (dict : Value)
    (n : IntVal)
    (newValue : Value := if byRef then .cell mkValidRefValue else .slice mkValidSliceValue)
    : Array Value :=
  #[newValue, .int (.num key), dict, .int n]

private def caseDictIAdd
    (name : String)
    (unsigned byRef : Bool)
    (stack : Array Value)
    (program : Array Instr := #[mkInstr unsigned byRef])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIAddId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr} with {bits} bits")

private def expectAssembleInvOpcode (label : String) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected .invOpcode, got encoded {reprStr c}")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def dictIAddExactGas : Int :=
  computeExactGasBudget (mkInstr false false)

private def dictIAddExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr false false)

private def runDictIAddDirect (unsigned byRef : Bool) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet (mkInstr unsigned byRef) stack

private def pickNForFuzz (rng0 : StdGen) : Nat × StdGen :=
  let (choice, rng1) := randNat rng0 0 7
  let n : Nat :=
    match choice with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | 4 => 5
    | 5 => 8
    | 6 => 16
    | _ => 32
  (n, rng1)

private def keyInRange (n : Nat) : Int :=
  if n = 0 then
    0
  else
    0

private def keyOutOfRange (unsigned : Bool) (n : Nat) : Int :=
  if n = 0 then
    1
  else if unsigned then
    Int.ofNat (1 <<< n)
  else
    -(Int.ofNat (1 <<< (n - 1)) + 1)

private def genDictIAddFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (unsigned, rng2) := randBool rng1
  let (byRef, rng3) := randBool rng2
  let (n, rng4) := pickNForFuzz rng3
  let nVal : Int := Int.ofNat n
  let keyOK := keyInRange n
  let keyBad := keyOutOfRange unsigned n
  let rootHit : Value := if unsigned then .cell dictUnsignedHitSlice else .cell dictSignedHitSlice
  let rootOther : Value := if unsigned then .cell dictUnsignedOtherKey else .cell dictSignedOtherKey
  let malformedByRef : Value := if byRef then .slice mkBadSliceValue else .cell malformedDictRoot
  match shape with
  | 0 =>
      (caseDictIAdd "fuzz/underflow/empty" unsigned byRef #[], rng1)
  | 1 =>
      (caseDictIAdd "fuzz/underflow/one" unsigned byRef #[intV 1], rng2)
  | 2 =>
      (caseDictIAdd "fuzz/underflow/two" unsigned byRef #[intV 1, .null], rng3)
  | 3 =>
      (caseDictIAdd "fuzz/underflow/three" unsigned byRef #[intV 1, .null, intV keyOK], rng4)
  | 4 =>
      (caseDictIAdd "fuzz/ok/miss/null" unsigned byRef
        (mkCaseStack unsigned byRef keyOK .null nVal), rng4)
  | 5 =>
      (caseDictIAdd "fuzz/ok/miss/non-empty" unsigned byRef
        (mkCaseStack unsigned byRef keyOK rootOther nVal), rng4)
  | 6 =>
      (caseDictIAdd "fuzz/ok/hit/replaces" unsigned byRef
        (mkCaseStack unsigned byRef keyOK rootHit nVal), rng4)
  | 7 =>
      (caseDictIAdd "fuzz/err/key-range/out-of-range" unsigned byRef
        (mkCaseStack unsigned byRef keyBad .null nVal), rng4)
  | 8 =>
      (caseDictIAdd "fuzz/err/n-negative" unsigned byRef
        (mkCaseStack unsigned byRef keyOK .null (-1)), rng4)
  | 9 =>
      (caseDictIAdd "fuzz/err/n-too-large" unsigned byRef
        (mkCaseStack unsigned byRef keyOK .null 1024), rng4)
  | 10 =>
      (caseDictIAdd "fuzz/err/n-nan" unsigned byRef
        (mkCaseStackWithNVal unsigned byRef keyOK .null .nan), rng4)
  | 11 =>
      (caseDictIAdd "fuzz/err/dict-type" unsigned byRef
        (mkCaseStack unsigned byRef keyOK (.tuple #[]) nVal), rng4)
  | 12 =>
      (caseDictIAdd "fuzz/err/key-type" unsigned byRef
        (#[if byRef then .cell mkValidRefValue else .slice mkValidSliceValue, .null, .cell dictSignedOtherKey, intV 4]), rng4)
  | 13 =>
      (caseDictIAdd "fuzz/err/new-value-type" unsigned byRef
        (mkCaseStack unsigned byRef keyOK .null nVal malformedByRef), rng4)
  | 14 =>
      (caseDictIAdd "fuzz/err/malformed-root" unsigned byRef
        (mkCaseStack unsigned byRef 0 (.cell malformedDictRoot) nVal), rng4)
  | _ =>
      (caseDictIAdd "fuzz/default" unsigned byRef
        (mkCaseStack unsigned byRef keyOK .null nVal), rng4)


def suite : InstrSuite where
  id := dictIAddId
  unit := #[
    { name := "unit/runtime/ok/insert/nonref"
      run := do
        let expectedRoot : Cell := mkDictRootSlice! "unit/insert/nonref" (-2) 4 false mkValidSliceValue
        expectOkStack "unit/runtime/ok/insert/nonref"
          (runDictIAddDirect false false (mkCaseStack false false (-2) .null 4))
          #[.cell expectedRoot, intV (-1)]
    }
    ,
    { name := "unit/runtime/ok/insert/byref"
      run := do
        let expectedRoot : Cell := mkDictRootRef! "unit/insert/byref" (2) 4 false mkValidRefValue
        expectOkStack "unit/runtime/ok/insert/byref"
          (runDictIAddDirect false true (mkCaseStack false true (2) .null 4))
          #[.cell expectedRoot, intV (-1)]
    }
    ,
    { name := "unit/runtime/ok/hit"
      run := do
        expectOkStack "unit/runtime/ok/hit"
          (runDictIAddDirect false false (mkCaseStack false false (-3) (.cell dictSignedHitSlice) 4))
          #[.cell dictSignedHitSlice, intV 0]
    }
    ,
    { name := "unit/asm/encode/signed-reffalse"
      run := do
        match assembleCp0 [mkInstr false false] with
        | .ok c =>
            if c == Cell.mkOrdinary (natToBits 0xf432 16) #[] then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/signed-reffalse: unexpected opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/signed-reffalse: {e}")
    }
    ,
    { name := "unit/asm/encode/signed-reftrue"
      run := do
        match assembleCp0 [mkInstr false true] with
        | .ok c =>
            if c == Cell.mkOrdinary (natToBits 0xf433 16) #[] then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/signed-reftrue: unexpected opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/signed-reftrue: {e}")
    }
    ,
    { name := "unit/asm/encode/unsigned-reffalse"
      run := do
        match assembleCp0 [mkInstr true false] with
        | .ok c =>
            if c == Cell.mkOrdinary (natToBits 0xf436 16) #[] then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/unsigned-reffalse: unexpected opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/unsigned-reffalse: {e}")
    }
    ,
    { name := "unit/asm/encode/unsigned-reftrue"
      run := do
        match assembleCp0 [mkInstr true true] with
        | .ok c =>
            if c == Cell.mkOrdinary (natToBits 0xf437 16) #[] then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/unsigned-reftrue: unexpected opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/unsigned-reftrue: {e}")
    }
    ,
    { name := "unit/asm/encode/invalid-non-int-key"
      run := do
        expectAssembleInvOpcode "unit/asm/encode/invalid-non-int-key" (.dictSet false false false .add)
    }
    ,
    { name := "unit/decoder/valid-range"
      run := do
        let s432 : Slice := mkSliceFromBits (natToBits 0xf432 16)
        let _ ← expectDecodeStep "unit/decoder/f432" s432 (mkInstr false false) 16
        let s433 : Slice := mkSliceFromBits (natToBits 0xf433 16)
        let _ ← expectDecodeStep "unit/decoder/f433" s433 (mkInstr false true) 16
        let s436 : Slice := mkSliceFromBits (natToBits 0xf436 16)
        let _ ← expectDecodeStep "unit/decoder/f436" s436 (mkInstr true false) 16
        let s437 : Slice := mkSliceFromBits (natToBits 0xf437 16)
        let _ ← expectDecodeStep "unit/decoder/f437" s437 (mkInstr true true) 16
        pure ()
    }
    ,
    { name := "unit/decoder/invalid-range"
      run := do
        expectDecodeInvOpcode "unit/decoder/f431" 0xf431
        expectDecodeInvOpcode "unit/decoder/f438" 0xf438
    }
  ]
  oracle := #[
    -- [B1] runtime success: signed insert, empty dict, slice payload.
    caseDictIAdd "oracle/ok/signed/miss/nonref/n4" false false (mkCaseStack false false (-3) .null 4)
    -- [B1] runtime success: signed insert, empty dict, ref payload.
    , caseDictIAdd "oracle/ok/signed/miss/byref/n4" false true (mkCaseStack false true (-4) .null 4)
    -- [B1] runtime success: unsigned insert, empty dict, slice payload.
    , caseDictIAdd "oracle/ok/unsigned/miss/nonref/n4" true false (mkCaseStack true false 13 (.null) 4)
    -- [B1] runtime success: unsigned insert, empty dict, ref payload.
    , caseDictIAdd "oracle/ok/unsigned/miss/byref/n4" true true (mkCaseStack true true 13 (.null) 4)
    -- [B1] runtime success: signed zero-width key on empty root.
    , caseDictIAdd "oracle/ok/signed/miss/n0" false false (mkCaseStack false false 0 .null 0)
    -- [B1] runtime success: unsigned zero-width key on empty root.
    , caseDictIAdd "oracle/ok/unsigned/miss/n0" true false (mkCaseStack true false 0 .null 0)
    -- [B1] runtime success: signed non-empty miss path.
    , caseDictIAdd "oracle/ok/signed/miss/non-empty" false false (mkCaseStack false false (-2) (.cell dictSignedOtherKey) 4)
    -- [B1] runtime success: unsigned non-empty miss path.
    , caseDictIAdd "oracle/ok/unsigned/miss/non-empty" true false (mkCaseStack true false 14 (.cell dictUnsignedOtherKey) 4)

    -- [B2] runtime duplicate: existing signed key, slice payload.
    , caseDictIAdd "oracle/ok/signed/hit/nonref" false false (mkCaseStack false false (-3) (.cell dictSignedHitSlice) 4)
    -- [B2] runtime duplicate: existing signed key, ref payload.
    , caseDictIAdd "oracle/ok/signed/hit/byref" false true (mkCaseStack false true (-3) (.cell dictSignedHitRef) 4)
    -- [B2] runtime duplicate: existing unsigned key, slice payload.
    , caseDictIAdd "oracle/ok/unsigned/hit/nonref" true false (mkCaseStack true false (13) (.cell dictUnsignedHitSlice) 4)
    -- [B2] runtime duplicate: existing unsigned key, ref payload.
    , caseDictIAdd "oracle/ok/unsigned/hit/byref" true true (mkCaseStack true true (13) (.cell dictUnsignedHitRef) 4)
    -- [B2] runtime duplicate: zero-width key already present.
    , caseDictIAdd "oracle/ok/zero/hit/nonref" false false (mkCaseStack false false 0 (.cell dictZeroKeySigned) 0)

    -- [B3] key conversion failure: signed range overflow.
    , caseDictIAdd "oracle/err/key-range/signed/high" false false (mkCaseStack false false (8) .null 4)
    -- [B3] key conversion failure: signed range underflow.
    , caseDictIAdd "oracle/err/key-range/signed/low" false false (mkCaseStack false false (-9) .null 4)
    -- [B3] key conversion failure: unsigned negative key.
    , caseDictIAdd "oracle/err/key-range/unsigned/negative" true false (mkCaseStack true false (-1) .null 4)
    -- [B3] key conversion failure: unsigned overflow.
    , caseDictIAdd "oracle/err/key-range/unsigned/high" true false (mkCaseStack true false (16) .null 4)
    -- [B3] key conversion failure: n=0 non-zero key (signed).
    , caseDictIAdd "oracle/err/key-range/signed/nzero" false false (mkCaseStack false false (1) .null 0)
    -- [B3] key conversion failure: n=0 non-zero key (unsigned).
    , caseDictIAdd "oracle/err/key-range/unsigned/nzero" true false (mkCaseStack true false (1) .null 0)

    -- [B4] argument range/type: n negative.
    , caseDictIAdd "oracle/err/n-negative" false false (mkCaseStack false false (-2) .null (-1))
    -- [B4] argument range/type: n too large.
    , caseDictIAdd "oracle/err/n-too-large" false false (mkCaseStack false false (0) .null 1024)
    -- [B4] argument range/type: n is NaN.
    , caseDictIAdd "oracle/err/n-nan" false false (mkCaseStackWithNVal false false (0) .null .nan)
    -- [B4] type check: dict root is not maybe-cell.
    , caseDictIAdd "oracle/err/dict-type" false false (mkCaseStack false false (1) (.tuple #[]) 4)
    -- [B4] type check: key is not int.
    , caseDictIAdd "oracle/err/key-type" false false #[.slice mkValidSliceValue, .null, .cell dictSignedOtherKey, intV 4]
    -- [B4] type check: wrong value type for non-ref path.
    , caseDictIAdd "oracle/err/value-type/nonref" false false (mkCaseStack false false 1 (.cell dictSignedOtherKey) 4 (.cell malformedDictRoot))
    -- [B4] type check: wrong value type for by-ref path.
    , caseDictIAdd "oracle/err/value-type/byref" false true (mkCaseStack false true 1 (.cell dictSignedOtherKey) 4 (.slice mkBadSliceValue))

    -- [B5] dictionary structural error: malformed root.
    , caseDictIAdd "oracle/err/malformed-root" false false (mkCaseStack false false 1 (.cell malformedDictRoot) 4)
    -- [B5] dictionary structural error: malformed root with unsigned/byref variation.
    , caseDictIAdd "oracle/err/malformed-root-unsigned-byref" true true (mkCaseStack true true 1 (.cell malformedDictRoot) 4)

    -- [B6] underflow: empty stack.
    , caseDictIAdd "oracle/err/underflow/empty" false false #[]
    -- [B6] underflow: one item.
    , caseDictIAdd "oracle/err/underflow/one" false false #[intV 1]
    -- [B6] underflow: two items.
    , caseDictIAdd "oracle/err/underflow/two" false false #[intV 1, .null]
    -- [B6] underflow: three items.
    , caseDictIAdd "oracle/err/underflow/three" false false #[intV 1, .cell dictSignedOtherKey, intV 4]

    -- [B7] exact-gas success on deterministic duplicate (no creation).
    , caseDictIAdd "oracle/gas/exact-hit" false false (mkCaseStack false false (-3) (.cell dictSignedHitSlice) 4)
        (#[.pushInt (.num dictIAddExactGas), .tonEnvOp .setGasLimit, mkInstr false false])
        (oracleGasLimitsExact dictIAddExactGas)
    -- [B7] exact-minus-one should fail on deterministic duplicate (no creation).
    , caseDictIAdd "oracle/gas/exact-minus-one" false false (mkCaseStack false false (-3) (.cell dictSignedHitSlice) 4)
        (#[.pushInt (.num dictIAddExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false false])
        (oracleGasLimitsExact dictIAddExactGasMinusOne)
    -- [B7] exact-gas branch for by-ref duplicate path.
    , caseDictIAdd "oracle/gas/exact-hit-byref" false true (mkCaseStack false true (-3) (.cell dictSignedHitRef) 4)
        (#[.pushInt (.num dictIAddExactGas), .tonEnvOp .setGasLimit, mkInstr false true])
        (oracleGasLimitsExact dictIAddExactGas)

    -- [B9] fuzz-friendly seeds for additional shape coverage.
    , caseDictIAdd "oracle/fuzz/shapes/zero-key/alt" false false (mkCaseStack false false 0 (.cell dictZeroKeySigned) 0)
    , caseDictIAdd "oracle/fuzz/shapes/unsigned/miss-alt" true false (mkCaseStack true false 4 (.cell dictUnsignedOtherKey) 4)
    , caseDictIAdd "oracle/fuzz/shapes/unsigned/hit-alt" true true (mkCaseStack true true 13 (.cell dictUnsignedHitRef) 4)
    , caseDictIAdd "oracle/fuzz/shapes/key-out-of-range-unsigned" true false (mkCaseStack true false 16 .null 4)
    , caseDictIAdd "oracle/fuzz/shapes/key-out-of-range-signed" false false (mkCaseStack false false (-9) .null 4)
    , caseDictIAdd "oracle/fuzz/shapes/nan-key" false false #[.slice mkValidSliceValue, .int .nan, .null, intV 4]
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictIAddFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIADD
