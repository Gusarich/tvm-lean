import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUADDGETREF

/-!
INSTRUCTION: DICTUADDGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success path on missing key (`.add` mode).
   - Pops operands as `(newValue: Cell, key: Int, dictRoot, n)`.
   - `popNatUpTo Dictionary::max_key_bits` validates `n`.
   - `dictKeyBits?` with unsigned flag converts key for the selected width.
   - On miss, `dictLookupSetRefWithCells` writes the provided new value and returns `none`.
   - Output pushes new root and boolean `0` (`false`).

2. [B2] Runtime success path on existing key.
   - `dictLookupSetRefWithCells` finds existing value and returns `some`.
   - Root is updated and old value is extracted through `extractRefOrThrow`.
   - Output is new root and the extracted old value cell.

3. [B3] Key conversion and range errors.
   - Unsigned key conversion fails for negative key, key outside width range, and `n=0` with key != 0.
   - Also fails for malformed key values (`.nan`) and propagates `rangeChk`.

4. [B4] `n` validation errors.
   - `n < 0`, `n > 1023`, and `.nan` are rejected before dictionary work by `popNatUpTo`.
   - This branch manifests as `rangeChk`.

5. [B5] Stack typing and underflow.
   - `.checkUnderflow 4` must be satisfied before decoding operands.
   - `newValue` must be a cell, `key` must be int, and `dictRoot` must be null or cell.

6. [B6] Root/value-shape decode errors.
   - Malformed dictionary roots fail through dictionary parsing.
   - Existing dictionary values that are not extractable as refs fail `extractRefOrThrow`.

7. [B7] Decoder behavior.
   - `0xf43f` decodes to `.dictExt (.mutGet true true true .add)`.
   - Aliases in family range: `0xf43e` (`DICTUADDGET`) and `0xf43d` (`DICTIADDGETREF`) are valid decodings.
   - `0xf439` and `0xf440` are `.invOpcode`.
   - Truncated 8-bit opcode must be `.invOpcode`.

8. [B8] Assembler behavior.
   - CP0 assembler encodes this opcode family (this instruction assembles to `0xf43f`).

9. [B9] Gas accounting.
   - Exact base gas / exact-minus-one branches are exercised with explicit budgeted programs.
   - Runtime gas consumption also depends on dictionary structure, handled by dedicated fuzz variants and exact-bounds cases.

TOTAL BRANCHES: 9

Every branch above is represented in oracle tests or explicit fuzzer generation.
-/

private def dictUAddGetRefId : InstrId :=
  { name := "DICTUADDGETREF" }

private def mkInstr : Instr :=
  .dictExt (.mutGet true true true .add)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawF439 : Cell := raw16 0xf439
private def rawF43E : Cell := raw16 0xf43e
private def rawF43D : Cell := raw16 0xf43d
private def rawF43F : Cell := raw16 0xf43f
private def rawF440 : Cell := raw16 0xf440
private def rawF4 : Cell := raw16 0xf4

private def normalNewValue : Value :=
  .cell (Cell.mkOrdinary (natToBits 0xC0 8) #[])

private def badNewValue : Value :=
  .slice (mkSliceFromBits (natToBits 0x55 8))

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0xA5 8) #[]
private def valueCellB : Cell := Cell.mkOrdinary (natToBits 0x5A 8) #[]
private def valueCellC : Cell := Cell.mkOrdinary (natToBits 0x3C 8) #[]
private def malformedRefValue : Cell := Cell.mkOrdinary (natToBits 0xFF 8) #[]

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0x9A 8)
private def valueSliceB : Slice := mkSliceFromBits (natToBits 0xA9 8)

private def mkDictCaseStack (newVal : Value) (key : Value) (dict : Value) (n : Value) : Array Value :=
  #[newVal, key, dict, n]

private def mkDictRootRef! (label : String) (pairs : Array (Int × Nat × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, n, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: key ({k}) out of range for n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: insertion returned no root"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def mkDictRootSlice! (label : String) (pairs : Array (Int × Nat × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, n, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: key ({k}) out of range for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: insertion returned no root"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictRef4Single : Cell :=
  mkDictRootRef! "dict/ref4/single" #[(7, 4, valueCellA)]

private def dictRef4Miss : Cell :=
  mkDictRootRef! "dict/ref4/miss" #[(2, 4, valueCellB)]

private def dictRef4Pair : Cell :=
  mkDictRootRef! "dict/ref4/pair" #[(7, 4, valueCellA), (11, 4, valueCellB)]

private def dictRef1Pair : Cell :=
  mkDictRootRef! "dict/ref1/pair" #[(0, 1, valueCellA), (1, 1, valueCellB)]

private def dictRefN0 : Cell :=
  mkDictRootRef! "dict/ref/n0" #[(0, 0, valueCellC)]

private def dictRefMalformedValue : Cell :=
  mkDictRootSlice! "dict/malformed-ref-value" #[(5, 4, valueSliceA)]

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr}")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def expectAssembleOk16 (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok cell =>
      match decodeCp0WithBits (Slice.ofCell cell) with
      | .error e =>
          throw (IO.userError s!"{label}: expected decode success, got {e}")
      | .ok (decoded, bits, rest) =>
          if decoded != instr then
            throw (IO.userError s!"{label}: expected {reprStr instr}, got {reprStr decoded}")
          else if bits != 16 then
            throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
          else if rest.bitsRemaining + rest.refsRemaining != 0 then
            throw (IO.userError s!"{label}: expected end-of-stream decode")

private def caseDictUAddGetRef
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUAddGetRefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def dictUAddGetRefExactGas : Int :=
  computeExactGasBudget mkInstr

private def dictUAddGetRefExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne mkInstr

private def exactGasProgram (limit : Int) : Array Instr :=
  #[.pushInt (.num limit), .tonEnvOp .setGasLimit, mkInstr]

private def genDictUAddGetRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    match shape with
    | 0 =>
        (caseDictUAddGetRef
          "fuzz/ok/miss/null/n4"
          (mkDictCaseStack normalNewValue (.int (.num 7)) .null (intV 4)), rng2)
    | 1 =>
        (caseDictUAddGetRef
          "fuzz/ok/miss/null/n0"
          (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 0)), rng2)
    | 2 =>
        (caseDictUAddGetRef
          "fuzz/ok/miss/null/n1023"
          (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 1023)), rng2)
    | 3 =>
        (caseDictUAddGetRef
          "fuzz/ok/miss/non-empty/n4"
          (mkDictCaseStack normalNewValue (.int (.num 5)) (.cell dictRef4Miss) (intV 4)), rng2)
    | 4 =>
        (caseDictUAddGetRef
          "fuzz/ok/hit/n4"
          (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (intV 4)), rng2)
    | 5 =>
        (caseDictUAddGetRef
          "fuzz/ok/hit/n1"
          (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dictRef1Pair) (intV 1)), rng2)
    | 6 =>
        (caseDictUAddGetRef
          "fuzz/ok/hit/n0"
          (mkDictCaseStack normalNewValue (.int (.num 0)) (.cell dictRefN0) (intV 0)), rng2)
    | 7 =>
        (caseDictUAddGetRef
          "fuzz/err/key-negative"
          (mkDictCaseStack normalNewValue (.int (.num (-1))) (.cell dictRef4Single) (intV 4)), rng2)
    | 8 =>
        (caseDictUAddGetRef
          "fuzz/err/key-out-of-range"
          (mkDictCaseStack normalNewValue (.int (.num 16)) (.cell dictRef4Single) (intV 4)), rng2)
    | 9 =>
        (caseDictUAddGetRef
          "fuzz/err/key-n1-nonzero"
          (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dictRefN0) (intV 0)), rng2)
    | 10 =>
        (caseDictUAddGetRef
          "fuzz/err/key-nan"
          (mkDictCaseStack normalNewValue (.int .nan) (.cell dictRef4Single) (intV 4)), rng2)
    | 11 =>
        (caseDictUAddGetRef
          "fuzz/err/n-negative"
          (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (intV (-1))), rng2)
    | 12 =>
        (caseDictUAddGetRef
          "fuzz/err/n-too-large"
          (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (intV 1024)), rng2)
    | 13 =>
        (caseDictUAddGetRef
          "fuzz/err/n-nan"
          (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (.int .nan)), rng2)
    | 14 =>
        (caseDictUAddGetRef
          "fuzz/err/dict-type"
          (mkDictCaseStack normalNewValue (.int (.num 7)) (.tuple #[]) (intV 4)), rng2)
    | 15 =>
        (caseDictUAddGetRef
          "fuzz/err/key-type"
          (mkDictCaseStack normalNewValue (.slice valueSliceA) (.cell dictRef4Single) (intV 4)), rng2)
    | 16 =>
        (caseDictUAddGetRef
          "fuzz/err/value-type"
          (mkDictCaseStack badNewValue (.int (.num 7)) (.cell dictRef4Single) (intV 4)), rng2)
    | 17 =>
        (caseDictUAddGetRef
          "fuzz/err/underflow/0" #[], rng2)
    | 18 =>
        (caseDictUAddGetRef "fuzz/err/underflow/1" #[normalNewValue], rng2)
    | 19 =>
        (caseDictUAddGetRef "fuzz/err/underflow/2" #[normalNewValue, .int (.num 7)], rng2)
    | 20 =>
        (caseDictUAddGetRef
          "fuzz/err/underflow/3" #[normalNewValue, .int (.num 7), .null], rng2)
    | 21 =>
        (caseDictUAddGetRef
          "fuzz/err/malformed-root" (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell malformedDictRoot) (intV 4)), rng2)
    | 22 =>
        (caseDictUAddGetRef
          "fuzz/err/ref-shape-mismatch" (mkDictCaseStack normalNewValue (.int (.num 5)) (.cell dictRefMalformedValue) (intV 4)), rng2)
    | 23 =>
        (caseDictUAddGetRef
          "fuzz/gas/exact" (mkDictCaseStack normalNewValue (.int (.num 7)) .null (intV 4))
          (exactGasProgram dictUAddGetRefExactGas)
          (oracleGasLimitsExact dictUAddGetRefExactGas), rng2)
    | 24 =>
        (caseDictUAddGetRef
          "fuzz/gas/exact-minus-one" (mkDictCaseStack normalNewValue (.int (.num 7)) .null (intV 4))
          (exactGasProgram dictUAddGetRefExactGasMinusOne)
          (oracleGasLimitsExactMinusOne dictUAddGetRefExactGasMinusOne), rng2)
    | 25 =>
        (caseDictUAddGetRef
          "fuzz/ok/miss/root-single-key4"
          (mkDictCaseStack normalNewValue (.int (.num 12)) (.cell dictRef4Miss) (intV 4)), rng2)
    | 26 =>
        (caseDictUAddGetRef
          "fuzz/ok/miss/root-pair-key4"
          (mkDictCaseStack normalNewValue (.int (.num 3)) (.cell dictRef4Pair) (intV 4)), rng2)
    | 27 =>
        (caseDictUAddGetRef
          "fuzz/ok/hit/pair-key4"
          (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dictRef4Pair) (intV 4)), rng2)
    | 28 =>
        (caseDictUAddGetRef
          "fuzz/err/key-range/n1"
          (mkDictCaseStack normalNewValue (.int (.num 2)) (.cell dictRef1Pair) (intV 1)), rng2)
    | _ =>
        (caseDictUAddGetRef
          "fuzz/ok/miss/null/odd-n"
          (mkDictCaseStack normalNewValue (.int (.num 12345)) .null (intV 8)), rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := dictUAddGetRefId
  unit := #[
    { name := "unit/decoder/decode/f43f"
      run := do
        let _ ←
          match decodeCp0WithBits (Slice.ofCell rawF43F) with
          | .ok (instr, _, _) =>
              if instr == mkInstr then
                pure ()
              else
                throw (IO.userError s!"unit/decoder/decode/f43f: got {reprStr instr}")
          | .error e =>
              throw (IO.userError s!"unit/decoder/decode/f43f: expected success, got {e}")
    }
    ,
    { name := "unit/decoder/decode/alias/f43e"
      run := do
        let _ ←
          match decodeCp0WithBits (Slice.ofCell rawF43E) with
          | .ok (instr, _, _) =>
              if instr == .dictExt (.mutGet true true false .add) then
                pure ()
              else
                throw (IO.userError s!"unit/decoder/decode/f43e: got {reprStr instr}")
          | .error e =>
              throw (IO.userError s!"unit/decoder/decode/f43e: expected success, got {e}")
    }
    ,
    { name := "unit/decoder/decode/alias/f43d"
      run := do
        let _ ←
          match decodeCp0WithBits (Slice.ofCell rawF43D) with
          | .ok (instr, _, _) =>
              if instr == .dictExt (.mutGet true false true .add) then
                pure ()
              else
                throw (IO.userError s!"unit/decoder/decode/f43d: got {reprStr instr}")
          | .error e =>
              throw (IO.userError s!"unit/decoder/decode/f43d: expected success, got {e}")
    }
    ,
    { name := "unit/decoder/decode/invalid-below"
      run := do
        expectDecodeInvOpcode "unit/decoder/decode/f439" 0xf439
    }
    ,
    { name := "unit/decoder/decode/invalid-above"
      run := do
        expectDecodeInvOpcode "unit/decoder/decode/f440" 0xf440
    }
    ,
    { name := "unit/decoder/decode/truncated8"
      run := do
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits 0xF4 8) #[])) with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"unit/decoder/decode/truncated8: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"unit/decoder/decode/truncated8: expected invOpcode, got {reprStr instr}/{bits}")
    }
    ,
    { name := "unit/asm/encode/ok"
      run := do
        expectAssembleOk16 "unit/asm/encode/ok" mkInstr
    }
  ]
  oracle := #[
    -- [B1] success miss path: null root, n=4.
    caseDictUAddGetRef "oracle/ok/miss/null/n4" (mkDictCaseStack normalNewValue (.int (.num 7)) .null (intV 4))
    -- [B1] success miss path: null root, n=0.
    , caseDictUAddGetRef "oracle/ok/miss/null/n0" (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 0))
    -- [B1] success miss path: null root, n=1023.
    , caseDictUAddGetRef "oracle/ok/miss/null/n1023" (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 1023))
    -- [B1] success miss path: non-empty root, absent key.
    , caseDictUAddGetRef "oracle/ok/miss/non-empty/n4" (mkDictCaseStack normalNewValue (.int (.num 5)) (.cell dictRef4Miss) (intV 4))
    -- [B1] success miss path: non-empty root and n=1.
    , caseDictUAddGetRef "oracle/ok/miss/non-empty/n1" (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dictRef1Pair) (intV 1))
    -- [B2] success hit path: existing key n=4.
    , caseDictUAddGetRef "oracle/ok/hit/n4" (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (intV 4))
    -- [B2] success hit path: existing key n=1.
    , caseDictUAddGetRef "oracle/ok/hit/n1" (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dictRef1Pair) (intV 1))
    -- [B2] success hit path: n=0 key.
    , caseDictUAddGetRef "oracle/ok/hit/n0" (mkDictCaseStack normalNewValue (.int (.num 0)) (.cell dictRefN0) (intV 0))
    -- [B3] key conversion failure: negative unsigned key.
    , caseDictUAddGetRef "oracle/err/key/negative" (mkDictCaseStack normalNewValue (.int (.num (-1))) (.cell dictRef4Single) (intV 4))
    -- [B3] key conversion failure: key above max for n=4.
    , caseDictUAddGetRef "oracle/err/key/high" (mkDictCaseStack normalNewValue (.int (.num 16)) (.cell dictRef4Single) (intV 4))
    -- [B3] key conversion failure: key invalid for n=1.
    , caseDictUAddGetRef "oracle/err/key/high/n1" (mkDictCaseStack normalNewValue (.int (.num 2)) (.cell dictRef1Pair) (intV 1))
    -- [B3] key conversion failure: non-zero key at n=0.
    , caseDictUAddGetRef "oracle/err/key/n0-nonzero" (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dictRefN0) (intV 0))
    -- [B3] key conversion failure: NaN key.
    , caseDictUAddGetRef "oracle/err/key/nan" (mkDictCaseStack normalNewValue (.int .nan) (.cell dictRef4Single) (intV 4))
    -- [B4] n validation failure: negative n.
    , caseDictUAddGetRef "oracle/err/n/negative" (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (intV (-1)))
    -- [B4] n validation failure: n greater than 1023.
    , caseDictUAddGetRef "oracle/err/n/too-large" (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (intV 1024))
    -- [B4] n validation failure: NaN n.
    , caseDictUAddGetRef "oracle/err/n/nan" (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dictRef4Single) (.int .nan))
    -- [B5] stack type failure: dict root type.
    , caseDictUAddGetRef "oracle/err/dict/type" (mkDictCaseStack normalNewValue (.int (.num 7)) (.tuple #[]) (intV 4))
    -- [B5] stack type failure: key type.
    , caseDictUAddGetRef "oracle/err/key/type" (mkDictCaseStack normalNewValue (.slice valueSliceA) (.cell dictRef4Single) (intV 4))
    -- [B5] stack type failure: new value must be cell.
    , caseDictUAddGetRef "oracle/err/newvalue/type" (mkDictCaseStack badNewValue (.int (.num 7)) (.cell dictRef4Single) (intV 4))
    -- [B6] malformed dict root shape.
    , caseDictUAddGetRef "oracle/err/malformed-root" (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell malformedDictRoot) (intV 4))
    -- [B6] by-ref shape error: existing value not extractable as ref.
    , caseDictUAddGetRef "oracle/err/ref-shape" (mkDictCaseStack normalNewValue (.int (.num 5)) (.cell dictRefMalformedValue) (intV 4))
    -- [B5] stack underflow: empty stack.
    , caseDictUAddGetRef "oracle/err/underflow/empty" #[]
    -- [B5] stack underflow: one item.
    , caseDictUAddGetRef "oracle/err/underflow/one" (#[(normalNewValue)])
    -- [B5] stack underflow: two items.
    , caseDictUAddGetRef "oracle/err/underflow/two" (#[normalNewValue, .int (.num 7)])
    -- [B5] stack underflow: three items.
    , caseDictUAddGetRef "oracle/err/underflow/three" (#[normalNewValue, .int (.num 7), .null])
    -- [B9] gas branch: exact budget should execute.
    , caseDictUAddGetRef "oracle/gas/exact" (mkDictCaseStack normalNewValue (.int (.num 7)) .null (intV 4))
      (exactGasProgram dictUAddGetRefExactGas)
      (oracleGasLimitsExact dictUAddGetRefExactGas)
    -- [B9] gas branch: exact-minus-one should fail.
    , caseDictUAddGetRef "oracle/gas/exact-minus-one" (mkDictCaseStack normalNewValue (.int (.num 7)) .null (intV 4))
      (exactGasProgram dictUAddGetRefExactGasMinusOne)
      (oracleGasLimitsExactMinusOne dictUAddGetRefExactGasMinusOne)
    -- [B3] boundary/alias confirmation with n=4 and pair root.
    , caseDictUAddGetRef "oracle/ok/hit/composite-4" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dictRef4Pair) (intV 4))
    -- [B3] boundary hit on max n-width style key.
    , caseDictUAddGetRef "oracle/ok/hit/composite-n0" (mkDictCaseStack normalNewValue (.int (.num 0)) (.cell dictRefN0) (intV 0))
    -- [B1] boundary miss on one-bit dictionary.
    , caseDictUAddGetRef "oracle/ok/miss/n1-alt" (mkDictCaseStack normalNewValue (.int (.num 3)) (.cell dictRef1Pair) (intV 1))
    -- [B1] miss at very large width.
    , caseDictUAddGetRef "oracle/ok/miss/null/n1023-alt" (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 1023))
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictUAddGetRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUADDGETREF
