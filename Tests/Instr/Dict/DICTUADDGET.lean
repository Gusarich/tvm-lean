import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUADDGET

/-!
INSTRUCTION: DICTUADDGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success path when the key is absent (`.add` on missing key).
   - Operands popped in order: new value (slice), integer key, dictionary root (or null), and `n`.
   - `popNatUpTo Dictionary::max_key_bits` succeeds and `dictKeyBits?` returns a valid `n`-bit key.
   - `dictLookupSetSliceWithCells` inserts value and returns `oldVal? = none`.
   - Output is `(newRoot, -1?)`? For `.add`, success pushes `0` via `pushBool false`.

2. [B2] Runtime success path when the key is present.
   - Existing key lookup succeeds and `oldVal? = some`.
   - New root is still returned and the old value slice is pushed in addition to `0`.

3. [B3] Key conversion failure on unsigned integer keys.
   - `dictKeyBits?` is used for unsigned conversion.
   - Negative index, index outside `[0, 2^n - 1]`, or malformed `n = 0` with nonzero key all fail before dictionary mutation.
   - Lean surfaces this as `rangeChk`; C++ behavior is equivalent for this path with `integer_key(..., quiet=true)` and explicit `cellUnd` checks in `exec_dict_setget`.

4. [B4] Numeric stack validation.
   - `n` must be in `[0,1023]`; underflow and `NaN` are rejected by `popNatUpTo` with `rangeChk` semantics.
   - `new value` must be a slice; dict root must be `.null` or cell.

5. [B5] Stack typing and underflow.
   - Stack underflow before consumption (`checkUnderflow 4`) is explicit.
   - `key` is required as integer, and `dict root` required as `null` or cell.

6. [B6] Dictionary root and payload shape failures.
   - Malformed root cells and dictionary parse/read failures propagate as dictionary errors through `dictLookupSetSliceWithCells`.
   - Old values are slices in this branch, so value-shape extraction failures are not exercised here, unlike REF variants.

7. [B7] Decoder behavior.
   - `0xf43a..0xf43f` all decode to `.dictExt (.mutGet ... .add)` forms.
   - `0xf43e` maps to `DICTUADDGET`.
   - Adjacent instructions in the same slot decode to related ops: `0xf43c` (`DICTIADDGET`) and `0xf43f` (`DICTUADDGETREF`).
   - `0xf439` and `0xf440` are outside the range and must decode to `.invOpcode`.

8. [B8] Assembler encoding.
   - CP0 assembler encodes `.dictExt (.mutGet ... .add)` opcodes (this instruction assembles to `0xf43e`).

9. [B9] Gas accounting.
   - Base gas is checked via `computeExactGasBudget` / `computeExactGasBudgetMinusOne`.
   - Variable dictionary cost exists via `consumeCreatedGas` and is covered by miss/hit/fuzz inputs that may insert new cells.

TOTAL BRANCHES: 9

Every oracle test below is tagged [Bn].
-/

private def dictUAddGetId : InstrId :=
  { name := "DICTUADDGET" }

private def mkInstr : Instr :=
  .dictExt (.mutGet true true false .add)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawF439 : Cell := raw16 0xf439
private def rawF43a : Cell := raw16 0xf43a
private def rawF43c : Cell := raw16 0xf43c
private def rawF43d : Cell := raw16 0xf43d
private def rawF43e : Cell := raw16 0xf43e
private def rawF43f : Cell := raw16 0xf43f
private def rawF440 : Cell := raw16 0xf440
private def rawF4 : Cell := raw16 0xf4

private def keySlice4 (v : Nat) : Slice := mkSliceFromBits (natToBits v 4)
private def keySlice1 (v : Nat) : Slice := mkSliceFromBits (natToBits v 1)
private def keySlice0 : Slice := mkSliceFromBits #[]
private def keySlice1023Zero : Slice := mkSliceFromBits (Array.replicate 1023 false)

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def valueSliceB : Slice := mkSliceFromBits (natToBits 0x5A 8)
private def valueSliceC : Slice := mkSliceFromBits (natToBits 0xC3 8)
private def valueSliceD : Slice := mkSliceFromBits (natToBits 0x3C 8)

private def normalNewValue : Value :=
  .slice valueSliceA

private def badNewValue : Value :=
  .cell (Cell.mkOrdinary (natToBits 0xAB 8) #[])

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictCaseStack (newVal : Value) (key : Value) (dict : Value) (n : Value) : Array Value :=
  #[newVal, key, dict, n]

private def mkDictCase (name : String) (stack : Array Value)
    (program : Array Instr := #[mkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUAddGetId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkDictRootSliceUnsigned! (label : String) (entries : Array (Int × Nat × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (idx, n, value) := entry
      let keyBits : BitString :=
        match dictKeyBits? idx n true with
        | some bs => bs
        | none => panic! s!"{label}: invalid unsigned key ({idx}) for n={n}"
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: dictionary insertion did not produce root"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: no entries"

private def dict4Hit : Cell :=
  mkDictRootSliceUnsigned! "dict/slice/4/hit" #[(11, 4, valueSliceB)]

private def dict4Miss : Cell :=
  mkDictRootSliceUnsigned! "dict/slice/4/miss" #[(2, 4, valueSliceC)]

private def dict4Pair : Cell :=
  mkDictRootSliceUnsigned! "dict/slice/4/pair" #[(4, 4, valueSliceA), (15, 4, valueSliceD)]

private def dict1Pair : Cell :=
  mkDictRootSliceUnsigned! "dict/slice/1/pair" #[(0, 1, valueSliceA), (1, 1, valueSliceB)]

private def dictZero : Cell :=
  mkDictRootSliceUnsigned! "dict/slice/0/key0" #[(0, 0, valueSliceA)]

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr}")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def expectDecode (label : String) (opcode : Nat) (instr : Instr) : IO Unit := do
  let _ ←
    match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
    | .ok (decoded, _, _) =>
        if decoded == instr then
          pure ()
        else
          throw (IO.userError s!"{label}: got {reprStr decoded}")
    | .error e =>
        throw (IO.userError s!"{label}: expected success, got {e}")

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

private def dictUAddGetExactGas : Int :=
  computeExactGasBudget mkInstr

private def dictUAddGetExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne mkInstr

private def exactGasProgram (limit : Int) : Array Instr :=
  #[.pushInt (.num limit), .tonEnvOp .setGasLimit, mkInstr]

private def genDictUAddGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    match shape with
    | 0 =>
        (mkDictCase
          "fuzz/ok/miss/null/4"
          (mkDictCaseStack normalNewValue (.int (.num 3)) .null (intV 4)), rng2)
    | 1 =>
        (mkDictCase
          "fuzz/ok/miss/null/0"
          (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 0)), rng2)
    | 2 =>
        (mkDictCase
          "fuzz/ok/miss/null/1023"
          (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 1023)), rng2)
    | 3 =>
        (mkDictCase
          "fuzz/ok/miss/non-empty/4"
          (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dict4Hit) (intV 4)), rng2)
    | 4 =>
        (mkDictCase
          "fuzz/ok/miss/boundary/1"
          (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dict1Pair) (intV 1)), rng2)
    | 5 =>
        (mkDictCase
          "fuzz/ok/miss/boundary/max"
          (mkDictCaseStack normalNewValue (.int (.num 14)) (.cell dict4Pair) (intV 4)), rng2)
    | 6 =>
        (mkDictCase
          "fuzz/ok/hit/4"
          (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (intV 4)), rng2)
    | 7 =>
        (mkDictCase
          "fuzz/ok/hit/4-max"
          (mkDictCaseStack normalNewValue (.int (.num 15)) (.cell dict4Pair) (intV 4)), rng2)
    | 8 =>
        (mkDictCase
          "fuzz/ok/hit/1"
          (mkDictCaseStack normalNewValue (.int (.num 0)) (.cell dict1Pair) (intV 1)), rng2)
    | 9 =>
        (mkDictCase
          "fuzz/ok/hit/0"
          (mkDictCaseStack normalNewValue (.int (.num 0)) (.cell dictZero) (intV 0)), rng2)
    | 10 =>
        (mkDictCase
          "fuzz/err/key-range/negative"
          (mkDictCaseStack normalNewValue (.int (.num (-1))) (.cell dict4Miss) (intV 4)), rng2)
    | 11 =>
        (mkDictCase
          "fuzz/err/key-range/too-large"
          (mkDictCaseStack normalNewValue (.int (.num 16)) (.cell dict4Miss) (intV 4)), rng2)
    | 12 =>
        (mkDictCase
          "fuzz/err/key-range/bit0-violation"
          (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dictZero) (intV 0)), rng2)
    | 13 =>
        (mkDictCase
          "fuzz/err/key-range/high-for-n1"
          (mkDictCaseStack normalNewValue (.int (.num 2)) (.cell dict4Miss) (intV 1)), rng2)
    | 14 =>
        (mkDictCase
          "fuzz/err/key-range/nan"
          (mkDictCaseStack normalNewValue (.int .nan) (.cell dict4Miss) (intV 4)), rng2)
    | 15 =>
        (mkDictCase
          "fuzz/err/n-negative"
          (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dict4Miss) (intV (-1))), rng2)
    | 16 =>
        (mkDictCase
          "fuzz/err/n-too-large"
          (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Miss) (intV 1024)), rng2)
    | 17 =>
        (mkDictCase
          "fuzz/err/n-nan"
          (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Miss) (.int .nan)), rng2)
    | 18 =>
        (mkDictCase
          "fuzz/err/dict-type"
          (mkDictCaseStack normalNewValue (.int (.num 11)) (.tuple #[]) (intV 4)), rng2)
    | 19 =>
        (mkDictCase
          "fuzz/err/key-type"
          (mkDictCaseStack normalNewValue (.slice (keySlice4 11)) (.cell dict4Miss) (intV 4)), rng2)
    | 20 =>
        (mkDictCase
          "fuzz/err/newvalue-type"
          (mkDictCaseStack badNewValue (.int (.num 11)) (.cell dict4Miss) (intV 4)), rng2)
    | 21 =>
        (mkDictCase
          "fuzz/err/underflow/0" #[], rng2)
    | 22 =>
        (mkDictCase
          "fuzz/err/underflow/1" (#[intV 4]), rng2)
    | 23 =>
        (mkDictCase
          "fuzz/err/underflow/2" (#[normalNewValue, intV 11]), rng2)
    | 24 =>
        (mkDictCase
          "fuzz/err/malformed-root" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell malformedDictRoot) (intV 4)), rng2)
    | _ =>
        (mkDictCase
          "fuzz/gas/exact" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (intV 4))
            (exactGasProgram dictUAddGetExactGas)
            (oracleGasLimitsExact dictUAddGetExactGas), rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := dictUAddGetId
  unit := #[
    { name := "unit/decoder/decode/f43e"
      run := do
        expectDecode "unit/decoder/decode/f43e" 0xf43e mkInstr
    }
    ,
    { name := "unit/decoder/decode/f43c-int-alias"
      run := do
        expectDecode "unit/decoder/decode/f43c" 0xf43c (.dictExt (.mutGet true false false .add))
    }
    ,
    { name := "unit/decoder/decode/f43d-ref-alias"
      run := do
        expectDecode "unit/decoder/decode/f43d" 0xf43d (.dictExt (.mutGet true false true .add))
    }
    ,
    { name := "unit/decoder/decode/f43f-unsigned-ref-alias"
      run := do
        expectDecode "unit/decoder/decode/f43f" 0xf43f (.dictExt (.mutGet true true true .add))
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
    { name := "unit/decoder/decode/f43a-nonint-aliased"
      run := do
        expectDecode "unit/decoder/decode/f43a" 0xf43a (.dictExt (.mutGet false false false .add))
    }
    ,
    { name := "unit/decoder/decode/truncated8"
      run := do
        expectDecode "unit/decoder/decode/truncated8" 0xf4 .nop
    }
    ,
    { name := "unit/asm/encode/ok"
      run := do
        expectAssembleOk16 "unit/asm/encode/ok" mkInstr
    }
  ]
  oracle := #[
    -- [B1] runtime success: absent key in null root, n=4.
    mkDictCase "oracle/ok/miss/null/4" (mkDictCaseStack normalNewValue (.int (.num 3)) .null (intV 4))
    -- [B1] runtime success: absent key in null root, n=0.
    , mkDictCase "oracle/ok/miss/null/0" (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 0))
    -- [B1] runtime success: absent key in null root, n=1023.
    , mkDictCase "oracle/ok/miss/null/1023" (mkDictCaseStack normalNewValue (.int (.num 0)) .null (intV 1023))
    -- [B1] runtime success: absent key in non-empty root, n=4.
    , mkDictCase "oracle/ok/miss/non-empty/4" (mkDictCaseStack normalNewValue (.int (.num 7)) (.cell dict4Hit) (intV 4))
    -- [B1] runtime success: boundary non-empty miss, n=1.
    , mkDictCase "oracle/ok/miss/boundary/1" (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dict1Pair) (intV 1))
    -- [B1] runtime success: boundary non-empty miss at n=4.
    , mkDictCase "oracle/ok/miss/boundary/4-max" (mkDictCaseStack normalNewValue (.int (.num 14)) (.cell dict4Pair) (intV 4))
    -- [B2] runtime success: hit existing key in n=4 dictionary.
    , mkDictCase "oracle/ok/hit/4/11" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (intV 4))
    -- [B2] runtime success: hit max-bit-key in n=4 dictionary.
    , mkDictCase "oracle/ok/hit/4/15" (mkDictCaseStack normalNewValue (.int (.num 15)) (.cell dict4Pair) (intV 4))
    -- [B2] runtime success: hit in n=1 dictionary.
    , mkDictCase "oracle/ok/hit/1/0" (mkDictCaseStack normalNewValue (.int (.num 0)) (.cell dict1Pair) (intV 1))
    -- [B2] runtime success: hit in n=1 dictionary for alternate key.
    , mkDictCase "oracle/ok/hit/1/1" (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dict1Pair) (intV 1))
    -- [B2] runtime success: hit in zero-bit dictionary.
    , mkDictCase "oracle/ok/hit/n0" (mkDictCaseStack normalNewValue (.int (.num 0)) (.cell dictZero) (intV 0))
    -- [B3] runtime failure: unsigned key negative.
    , mkDictCase "oracle/err/key-range/negative" (mkDictCaseStack normalNewValue (.int (.num (-1))) (.cell dict4Hit) (intV 4))
    -- [B3] runtime failure: key above max for n=4.
    , mkDictCase "oracle/err/key-range/high" (mkDictCaseStack normalNewValue (.int (.num 16)) (.cell dict4Hit) (intV 4))
    -- [B3] runtime failure: key too large for n=1.
    , mkDictCase "oracle/err/key-range/high/n1" (mkDictCaseStack normalNewValue (.int (.num 2)) (.cell dict4Miss) (intV 1))
    -- [B3] runtime failure: non-zero key for n=0.
    , mkDictCase "oracle/err/key-range/nonzero/n0" (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dict4Miss) (intV 0))
    -- [B3] runtime failure: NaN key.
    , mkDictCase "oracle/err/key-range/nan" (mkDictCaseStack normalNewValue (.int .nan) (.cell dict4Hit) (intV 4))
    -- [B4] runtime failure: invalid n (negative).
    , mkDictCase "oracle/err/n-negative" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (intV (-1)))
    -- [B4] runtime failure: invalid n above 1023.
    , mkDictCase "oracle/err/n-too-large" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (intV 1024))
    -- [B4] runtime failure: n is NaN.
    , mkDictCase "oracle/err/n-nan" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (.int .nan))
    -- [B5] runtime failure: key type check (not integer).
    , mkDictCase "oracle/err/key-type" (mkDictCaseStack normalNewValue (.slice (keySlice4 11)) (.cell dict4Hit) (intV 4))
    -- [B5] runtime failure: value type check (not slice).
    , mkDictCase "oracle/err/value-type" (mkDictCaseStack badNewValue (.int (.num 11)) (.cell dict4Hit) (intV 4))
    -- [B5] runtime failure: dict root type check.
    , mkDictCase "oracle/err/dict-type" (mkDictCaseStack normalNewValue (.int (.num 11)) (.tuple #[]) (intV 4))
    -- [B6] runtime failure: malformed dictionary root shape.
    , mkDictCase "oracle/err/malformed-root" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell malformedDictRoot) (intV 4))
    -- [B6] runtime underflow: empty stack.
    , mkDictCase "oracle/err/underflow/empty" (#[])
    -- [B6] runtime underflow: missing key.
    , mkDictCase "oracle/err/underflow/missing-key" (#[(normalNewValue), (.int (.num 11)), (.cell dict4Hit)])
    -- [B6] runtime underflow: missing n.
    , mkDictCase "oracle/err/underflow/missing-n" (#[(normalNewValue), (.int (.num 11)), (.cell dict4Hit)])
    -- [B6] runtime underflow: missing dict.
    , mkDictCase "oracle/err/underflow/missing-dict" (#[(normalNewValue), (.int (.num 11)), (intV 4)])
    -- [B7] gas branch exact: hit input should execute under exact budget.
    , mkDictCase "oracle/gas/exact" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (intV 4))
      (exactGasProgram dictUAddGetExactGas)
      (oracleGasLimitsExact dictUAddGetExactGas)
    -- [B7] gas branch exact-minus-one: expected out-of-gas.
    , mkDictCase "oracle/gas/exact-minus-one" (mkDictCaseStack normalNewValue (.int (.num 11)) (.cell dict4Hit) (intV 4))
      (exactGasProgram dictUAddGetExactGasMinusOne)
      (oracleGasLimitsExactMinusOne dictUAddGetExactGasMinusOne)
    -- [B1] runtime success: miss in non-empty root while preserving other bits.
    , mkDictCase "oracle/ok/miss/non-empty-1bit" (mkDictCaseStack normalNewValue (.int (.num 1)) (.cell dict1Pair) (intV 1))
    -- [B2] runtime success: hit in composite root with additional entries.
    , mkDictCase "oracle/ok/hit/composite" (mkDictCaseStack normalNewValue (.int (.num 4)) (.cell dict4Pair) (intV 4))
    -- [B4] boundary n test: maximum allowed n value with miss.
    , mkDictCase "oracle/ok/n-max-1023" (mkDictCaseStack normalNewValue (.int (.num 0)) (.null) (intV 1023))
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictUAddGetFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUADDGET
