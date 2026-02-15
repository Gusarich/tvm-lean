import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTISET

/-
INSTRUCTION: DICTISET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Runtime success path] Signed dictionary-set with integer key and value slice succeeds by:
   - constructing an n-bit key from an integer using `dictKeyBits?`.
   - running `set` mode dictionary insertion/overwrite through `dictSetSliceWithCells`.
   - pushing the resulting root on stack; when root is `none` it pushes `.null`.

2. [Edge key-range path] Signed-key encoding has strict bounds:
   - `n = 0` accepts only key `0` and rejects any non-zero key via `.rangeChk`.
   - For `n > 0`, keys outside `[−2^(n−1), 2^(n−1)−1]` are rejected as `.rangeChk`.
   - `n` too large (`> 1023`) is rejected by `popNatUpTo` as `.rangeChk`.

3. [Type/range error path] Input typing/order path:
   - non-int key triggers `.typeChk`.
   - malformed `n` values (`.nan` or negative) trigger `.rangeChk`.
   - value-type mismatch (`slice` vs `ref`) triggers `.typeChk` depending on by-ref flag.
   - malformed root and non-cell roots trigger `.dictErr`/`.typeChk` as appropriate.

4. [Underflow/error path] Requires exactly 4 stack items (`newValue`, `key`, `root`, `n`).
   - 0..3 items hit `.stkUnd`.

5. [Assembler encoding] `.dictSet` encoding for this instruction is:
   - signed non-ref: opcode `0xf414`
   - signed ref: opcode `0xf415`
   - `.dictSet false true ...` is unsupported and must assemble to `.invOpcode`.

6. [Decoder behavior] Decode range is `0xf412`..`0xf417` with the DICTISET forms at `0xf414` and `0xf415`:
   - adjacent opcodes decode to neighboring dictionary modes (`DICTSET`/`DICTUSET`) and must not alias to DICTISET.
   - `0xf411` and `0xf418` are outside this set and must decode as `.invOpcode`.

7. [Gas accounting]
   - There is base gas for DICTISET plus dynamic gas for created cells (`cellCreateGasPrice * created`).
   - Deterministic hit-path is suitable for exact-gas checks; miss-path may add variable create cost.
   - Exact-gas and exact-gas-minus-one branches must validate success/failure semantics on a hit path.

8. [Fuzzer branch coverage] Branches not directly enumerated in oracle tests (especially miss-path, by-ref combinations, malformed roots, and type-family errors) must be weighted into fuzz input generation.

9. [Decoder/assembler round-trip] Valid signed forms encode and decode symmetrically.

TOTAL BRANCHES: 9
-/

private def dictISetId : InstrId := { name := "DICTISET" }

private def mkInstr (byRef : Bool) : Instr :=
  .dictSet true false byRef .set

private def mkValidSliceValue : Slice :=
  mkSliceFromBits (natToBits 0x55 8)

private def mkValidRefValue : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def mkBadSliceValue : Slice :=
  mkSliceFromBits (natToBits 0xEE 8)

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictRootSlice! (label : String) (key : Int) (n : Nat) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n false with
    | some bits => bits
    | none => panic! s!"{label}: invalid key ({key}, n={n})"
  match dictSetSliceWithCells none keyBits mkValidSliceValue .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected dict root, got none"
  | .error e =>
      panic! s!"{label}: dict set failed: {reprStr e}"

private def mkDictRootRef! (label : String) (key : Int) (n : Nat) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n false with
    | some bits => bits
    | none => panic! s!"{label}: invalid key ({key}, n={n})"
  match dictSetRefWithCells none keyBits mkValidRefValue .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! s!"{label}: expected dict root, got none"
  | .error e =>
      panic! s!"{label}: dict set failed: {reprStr e}"

private def dictSignedHitSlice : Cell :=
  mkDictRootSlice! "dict/signed/hit/slice" (-3) 4

private def dictSignedHitRef : Cell :=
  mkDictRootRef! "dict/signed/hit/ref" (-3) 4

private def dictSignedOtherSlice : Cell :=
  mkDictRootSlice! "dict/signed/other/slice" (2) 4

private def dictSignedOtherRef : Cell :=
  mkDictRootRef! "dict/signed/other/ref" (2) 4

private def dictSignedZeroSlice : Cell :=
  mkDictRootSlice! "dict/signed/zero/slice" (0) 0

private def dictSignedZeroRef : Cell :=
  mkDictRootRef! "dict/signed/zero/ref" (0) 0

private def dictSignedHighSlice : Cell :=
  mkDictRootSlice! "dict/signed/high/slice" (7) 4

private def dictSignedHighRef : Cell :=
  mkDictRootRef! "dict/signed/high/ref" (7) 4

private def dictSignedLowSlice : Cell :=
  mkDictRootSlice! "dict/signed/low/slice" (-8) 4

private def dictSignedLowRef : Cell :=
  mkDictRootRef! "dict/signed/low/ref" (-8) 4

private def dictSignedN1Slice : Cell :=
  mkDictRootSlice! "dict/signed/n1/slice" 0 1

private def dictSignedN1Ref : Cell :=
  mkDictRootRef! "dict/signed/n1/ref" 0 1

private def mkCaseStack
    (byRef : Bool)
    (key : Int)
    (dict : Value)
    (n : Int)
    (newValue : Value := if byRef then .cell mkValidRefValue else .slice mkValidSliceValue)
    : Array Value :=
  #[newValue, .int (.num key), dict, .int (.num n)]

private def mkCaseStackWithNVal
    (byRef : Bool)
    (key : Int)
    (dict : Value)
    (n : IntVal)
    (newValue : Value := if byRef then .cell mkValidRefValue else .slice mkValidSliceValue)
    : Array Value :=
  #[newValue, .int (.num key), dict, .int n]

private def caseDictISet
    (name : String)
    (byRef : Bool)
    (stack : Array Value)
    (program : Array Instr := #[mkInstr byRef])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictISetId
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

private def dictISetExactGas : Int :=
  computeExactGasBudget (mkInstr false)

private def dictISetExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr false)

private def runDictISetDirect (byRef : Bool) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet (mkInstr byRef) stack

private def keyOutOfRangeSigned (n : Nat) : Int :=
  if n = 0 then
    1
  else
    Int.ofNat (1 <<< (n - 1))

private def keyOutOfRangeSignedLow (n : Nat) : Int :=
  if n = 0 then
    1
  else
    -Int.ofNat (1 <<< (n - 1)) - 1

private def pickNForFuzz (rng0 : StdGen) : Nat × StdGen :=
  let (choice, rng1) := randNat rng0 0 9
  let n : Nat :=
    match choice with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | 4 => 8
    | 5 => 16
    | 6 => 32
    | 7 => 64
    | 8 => 128
    | _ => 1023
  (n, rng1)

private def genDictISetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (byRef, rng2) := randBool rng1
  let (n, rng3) := pickNForFuzz rng2
  let nVal : Int := Int.ofNat n
  let keyOK : Int := 0
  let keyHigh : Int := keyOutOfRangeSigned n
  let keyLow : Int := keyOutOfRangeSignedLow n
  let rootHit : Value := if byRef then .cell dictSignedHitRef else .cell dictSignedHitSlice
  let rootOther : Value := if byRef then .cell dictSignedOtherRef else .cell dictSignedOtherSlice
  let malformedByRef : Value := if byRef then .slice mkBadSliceValue else .cell malformedDictRoot
  match shape with
  | 0 =>
      (caseDictISet "fuzz/underflow/empty" byRef #[], rng3)
  | 1 =>
      (caseDictISet "fuzz/underflow/one" byRef #[intV 1], rng3)
  | 2 =>
      (caseDictISet "fuzz/underflow/two" byRef #[intV 1, .null], rng3)
  | 3 =>
      (caseDictISet "fuzz/underflow/three" byRef #[.slice mkValidSliceValue, intV keyOK, .null], rng3)
  | 4 =>
      (caseDictISet "fuzz/ok/empty/non-ref" byRef (mkCaseStack byRef (-3) .null nVal), rng3)
  | 5 =>
      (caseDictISet "fuzz/ok/empty/non-empty" byRef (mkCaseStack byRef (-3) rootOther nVal), rng3)
  | 6 =>
      (caseDictISet "fuzz/ok/hit" byRef (mkCaseStack byRef (-3) rootHit nVal), rng3)
  | 7 =>
      (caseDictISet "fuzz/err/key/high" byRef (mkCaseStack byRef keyHigh rootOther nVal), rng3)
  | 8 =>
      (caseDictISet "fuzz/err/key/low" byRef (mkCaseStack byRef keyLow rootOther nVal), rng3)
  | 9 =>
      (caseDictISet "fuzz/err/key/nzero" byRef (mkCaseStack byRef 1 .null 0), rng3)
  | 10 =>
      (caseDictISet "fuzz/err/n/negative" byRef (mkCaseStack byRef 0 .null (-1)), rng3)
  | 11 =>
      (caseDictISet "fuzz/err/n/too-large" byRef (mkCaseStack byRef 0 .null 1024), rng3)
  | 12 =>
      (caseDictISet "fuzz/err/n/nan" byRef (mkCaseStackWithNVal byRef 0 .null .nan), rng3)
  | 13 =>
      (caseDictISet "fuzz/err/type/key" byRef (#[.slice mkValidSliceValue, .null, .cell dictSignedOtherSlice, intV 4]), rng3)
  | 14 =>
      (caseDictISet "fuzz/err/type/value" byRef (#[malformedByRef, intV keyOK, .null, intV 4]), rng3)
  | 15 =>
      (caseDictISet "fuzz/err/type/dict" byRef (mkCaseStack byRef 0 (.tuple #[]) 4), rng3)
  | 16 =>
      (caseDictISet "fuzz/err/dict/malformed" byRef (mkCaseStack byRef 0 (.cell malformedDictRoot) 4), rng3)
  | 17 =>
      (caseDictISet "fuzz/ok/reference-path" true (mkCaseStack true 7 (.cell dictSignedOtherRef) 4), rng3)
  | 18 =>
      (caseDictISet "fuzz/ok/reference-hit" true (mkCaseStack true (-3) (.cell dictSignedHitRef) 4), rng3)
  | _ =>
      (caseDictISet "fuzz/default" byRef (mkCaseStack byRef 0 .null 4), rng3)


def suite : InstrSuite where
  id := dictISetId
  unit := #[
    { name := "unit/asm/encode/signed-non-ref"
      run := do
        match assembleCp0 [mkInstr false] with
        | .ok c =>
            if c == Cell.mkOrdinary (natToBits 0xf414 16) #[] then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/signed-non-ref: unexpected opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/signed-non-ref: {e}")
    }
    ,
    { name := "unit/asm/encode/signed-ref"
      run := do
        match assembleCp0 [mkInstr true] with
        | .ok c =>
            if c == Cell.mkOrdinary (natToBits 0xf415 16) #[] then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/signed-ref: unexpected opcode")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/signed-ref: {e}")
    }
    ,
    { name := "unit/asm/assemble-invalid/non-int-key"
      run := do
        expectAssembleInvOpcode "unit/asm/assemble-invalid/non-int-key" (.dictSet false true true .set)
    }
    ,
    { name := "unit/decoder/valid-signed-forms"
      run := do
        let s414 : Slice := mkSliceFromBits (natToBits 0xf414 16)
        let s415 : Slice := mkSliceFromBits (natToBits 0xf415 16)
        let _ ← expectDecodeStep "unit/decoder/signed/non-ref" s414 (mkInstr false) 16
        let _ ← expectDecodeStep "unit/decoder/signed/ref" s415 (mkInstr true) 16
        pure ()
    }
    ,
    { name := "unit/decoder/adjacent-instructions"
      run := do
        let s413 : Slice := mkSliceFromBits (natToBits 0xf413 16)
        let s416 : Slice := mkSliceFromBits (natToBits 0xf416 16)
        let _ ← expectDecodeStep "unit/decoder/adjacent-slice-set" s413 (.dictSet false false true .set) 16
        let _ ← expectDecodeStep "unit/decoder/adjacent-unsigned-set" s416 (.dictSet true true false .set) 16
        pure ()
    }
    ,
    { name := "unit/decoder/inv-range"
      run := do
        expectDecodeInvOpcode "unit/decoder/invalid-low" 0xf411
        expectDecodeInvOpcode "unit/decoder/invalid-high" 0xf418
    }
  ]
  oracle := #[
    -- [B1] runtime miss/hit success (non-ref): empty and non-empty.
    caseDictISet "oracle/ok/miss/empty" false (mkCaseStack false (-3) .null 4)
    ,
    caseDictISet "oracle/ok/miss/n0" false (mkCaseStack false 0 .null 0)
    ,
    caseDictISet "oracle/ok/miss/n1023" false (mkCaseStack false 0 .null 1023)
    ,
    caseDictISet "oracle/ok/miss/non-empty" false (mkCaseStack false 2 (.cell dictSignedHitSlice) 4)
    ,
    caseDictISet "oracle/ok/hit/non-empty" false (mkCaseStack false (-3) (.cell dictSignedHitSlice) 4)
    ,
    caseDictISet "oracle/ok/hit/zero-width" false (mkCaseStack false 0 (.cell dictSignedZeroSlice) 0)
    ,
    caseDictISet "oracle/ok/replace/high-boundary" false (mkCaseStack false 0 (.cell dictSignedHighSlice) 4)
    ,
    caseDictISet "oracle/ok/replace/low-boundary" false (mkCaseStack false 0 (.cell dictSignedLowSlice) 4)
    ,
    caseDictISet "oracle/ok/hit/n1" false (mkCaseStack false 0 (.cell dictSignedN1Slice) 1)
    ,
    caseDictISet "oracle/ok/ignore-non-empty-existing" false (mkCaseStack false 0 (.cell dictSignedOtherSlice) 4)

    -- [B1] runtime by-ref success: miss and hit.
    ,
    caseDictISet "oracle/ok/ref/miss" true (mkCaseStack true (-3) .null 4)
    ,
    caseDictISet "oracle/ok/ref/hit" true (mkCaseStack true (-3) (.cell dictSignedHitRef) 4)
    ,
    caseDictISet "oracle/ok/ref/empty-n1" true (mkCaseStack true 0 .null 1)

    -- [B2] key conversion edge failures.
    ,
    caseDictISet "oracle/err/key-range/high" false (mkCaseStack false (keyOutOfRangeSigned 4) (.cell dictSignedOtherSlice) 4)
    ,
    caseDictISet "oracle/err/key-range/low" false (mkCaseStack false (keyOutOfRangeSignedLow 4) (.cell dictSignedOtherSlice) 4)
    ,
    caseDictISet "oracle/err/key-range/nzero" false (mkCaseStack false 1 (.cell dictSignedOtherSlice) 0)
    ,
    caseDictISet "oracle/err/key-type" false (#[.slice mkValidSliceValue, .null, .cell dictSignedOtherSlice, intV 4])
    ,
    caseDictISet "oracle/err/key-type/ref" true (#[.cell mkValidRefValue, .slice mkValidSliceValue, .cell dictSignedOtherRef, intV 4])

    -- [B3] `n` argument and type-family errors.
    ,
    caseDictISet "oracle/err/n-negative" false (mkCaseStack false (-3) (.cell dictSignedOtherSlice) (-1))
    ,
    caseDictISet "oracle/err/n-too-large" false (mkCaseStack false (-3) (.cell dictSignedOtherSlice) 1024)
    ,
    caseDictISet "oracle/err/n-nan" false (mkCaseStackWithNVal false (-3) (.cell dictSignedOtherSlice) .nan)
    ,
    caseDictISet "oracle/err/type-root" false (mkCaseStack false (-3) (.tuple #[]) 4)
    ,
    caseDictISet "oracle/err/value-type" false (mkCaseStack false (-3) (.cell dictSignedOtherSlice) 4 (.cell malformedDictRoot))
    ,
    caseDictISet "oracle/err/value-type-ref" true (mkCaseStack true (-3) (.cell dictSignedOtherRef) 4 (.slice mkBadSliceValue))

    -- [B4] malformed dictionary structure errors.
    ,
    caseDictISet "oracle/err/malformed-root" false (mkCaseStack false (-3) (.cell malformedDictRoot) 4)
    ,
    caseDictISet "oracle/err/malformed-root-ref" true (mkCaseStack true (-3) (.cell malformedDictRoot) 4)

    -- [B4] underflow path.
    ,
    caseDictISet "oracle/err/underflow-empty" false #[]
    ,
    caseDictISet "oracle/err/underflow-one" false #[intV 1]
    ,
    caseDictISet "oracle/err/underflow-two" false #[intV 1, .null]
    ,
    caseDictISet "oracle/err/underflow-three" false #[.slice mkValidSliceValue, intV 0, .null]

    -- [B7] gas accounting exact/minus-one (hit path avoids variable cell-create gas).
    ,
    caseDictISet "oracle/gas/exact-hit" false (mkCaseStack false (-3) (.cell dictSignedHitSlice) 4)
      (#[.pushInt (.num dictISetExactGas), .tonEnvOp .setGasLimit, mkInstr false]) (oracleGasLimitsExact dictISetExactGas)
    ,
    caseDictISet "oracle/gas/exact-minus-one" false (mkCaseStack false (-3) (.cell dictSignedHitSlice) 4)
      (#[.pushInt (.num dictISetExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false]) (oracleGasLimitsExactMinusOne dictISetExactGasMinusOne)
    ,
    caseDictISet "oracle/gas/exact-hit-ref" true (mkCaseStack true (-3) (.cell dictSignedHitRef) 4)
      (#[.pushInt (.num dictISetExactGas), .tonEnvOp .setGasLimit, mkInstr true]) (oracleGasLimitsExact dictISetExactGas)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictISetId
      count := 500
      gen := genDictISetFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTISET
