import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIADDGETREF

/-!
INSTRUCTION: DICTIADDGETREF

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success path (dictionary miss, REF mode):
   - `checkUnderflow 4`, `popNatUpTo` succeeds, `dictRoot?` is popped, key conversion succeeds,
     `popCell` obtains new value.
   - `dictLookupSetRefWithCells` misses, returns `none`.
   - Result stack is new root plus boolean `false`.

2. [B2] Runtime success path (dictionary hit, REF mode):
   - Same preamble as B1, but lookup finds existing key and returns `oldVal? = some`.
   - `extractRefOrThrow` succeeds only when existing value is exactly one ref and empty bit payload,
     then pushes old value as cell and `true`.

3. [B3] Key-conversion and width-check failures:
   - For `int` key mode, `dictKeyBits?` validates signed keys against width `n`.
   - Signed out-of-range keys (including too large positive and too small negative)
     and non-zero key when `n = 0` yield `.rangeChk` in this instruction mode.
   - `NaN` key also yields `.rangeChk`.

4. [B4] `n` validation and malformed operands for key/path setup:
   - `popNatUpTo 1023` rejects negative `n`, `n > 1023`, and `.nan` before dictionary operations.

5. [B5] Stack typing and underflow:
   - Underflow is checked before any pops (`checkUnderflow 4`).
   - Wrong stack types for dict root, key, or new value trigger `.typeChk`/runtime pop errors as expected by
     the pop order (`dict`, `key`, `newValue`, then `n` is already consumed).

6. [B6] Structure/parsing errors:
   - Malformed dictionary roots and malformed existing value cells (non-ref stored value) both propagate to errors
     through `dictLookupSetRefWithCells` / `extractRefOrThrow`.

7. [B7] Decoder boundaries:
   - `0xf43a..0xf43f` decodes as `.dictExt (.mutGet intKey bool byRef .add)` with bit fields.
   - `0xf43d` is the signed-by-ref `DICTIADDGETREF` variant.
   - `0xf43c` and `0xf43e` are neighboring ADDGET variants; `0xf43f` is unsigned by-ref.
   - `0xf439` / `0xf440` are decoder boundaries and must be `.invOpcode`; truncated 8-bit opcode must also fail.

8. [B8] Assembler encoding:
   - `encodeCp0` is unsupported for any `.dictExt` (`.invOpcode`).

9. [B9] Gas accounting:
   - Instruction gas follows exact/`computeExactGasBudget` base for fixed opcode behavior;
     explicit exact and exact-minus-one branches are included.

TOTAL BRANCHES: 9

Every branch above is covered by oracle/unit tests or fuzz targets.
-/

private def dictIAddGetRefId : InstrId := { name := "DICTIADDGETREF" }

private def mkInstr : Instr :=
  .dictExt (.mutGet true false true .add)

private def raw16 (opcode : Nat) : Cell :=
  Cell.mkOrdinary (natToBits opcode 16) #[]

private def rawF43C : Cell := raw16 0xf43c
private def rawF43D : Cell := raw16 0xf43d
private def rawF43E : Cell := raw16 0xf43e
private def rawF43F : Cell := raw16 0xf43f
private def rawF439 : Cell := raw16 0xf439
private def rawF440 : Cell := raw16 0xf440
private def rawF4 : Cell := raw16 0xf4

private def validNewValue : Value :=
  .cell (Cell.mkOrdinary (natToBits 0xA0 8) #[])

private def badNewValue : Value :=
  .slice (mkSliceFromBits (natToBits 0x55 8))

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0x9A 8)
private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0x3C 8) #[]
private def valueCellB : Cell := Cell.mkOrdinary (natToBits 0x5A 8) #[]
private def valueCellC : Cell := Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 0b111 3) #[]

private def mkDictRootRef! (label : String) (pairs : Array (Int × Nat × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for (key, n, value) in pairs do
      let keyBits : BitString :=
        match dictKeyBits? key n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid key ({key}) for n={n}"
      match dictSetRefWithCells root keyBits value .set with
      | .ok (some nextRoot, _ok, _created, _loaded) =>
          root := nextRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dictSetRefWithCells returned none"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary not allowed"

private def mkDictRootSlice! (label : String) (pairs : Array (Int × Nat × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for (key, n, value) in pairs do
      let keyBits : BitString :=
        match dictKeyBits? key n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid key ({key}) for n={n}"
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some nextRoot, _ok, _created, _loaded) =>
          root := nextRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dictSetSliceWithCells returned none"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary not allowed"

private def dictSigned4Hit : Cell :=
  mkDictRootRef! "dict/signed4/hit" #[(3, 4, valueCellA)]

private def dictSigned4Other : Cell :=
  mkDictRootRef! "dict/signed4/other" #[(2, 4, valueCellB)]

private def dictSigned4Pair : Cell :=
  mkDictRootRef! "dict/signed4/pair" #[(3, 4, valueCellA), (-4, 4, valueCellB)]

private def dictSigned1Pair : Cell :=
  mkDictRootRef! "dict/signed1/pair" #[( -1, 1, valueCellB), (0, 1, valueCellC)]

private def dictSigned0Single : Cell :=
  mkDictRootRef! "dict/signed0/single" #[(0, 0, valueCellA)]

private def dictSignedMalformedValue : Cell :=
  mkDictRootSlice! "dict/signed/malformed-value" #[(3, 4, valueSliceA)]

private def caseDictIAddGetRef
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIAddGetRefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStack (newValue : Value) (key : Value) (dict : Value) (n : Value) : Array Value :=
  #[newValue, key, dict, n]

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr}")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def dictIAddGetRefExactGas : Int :=
  computeExactGasBudget mkInstr

private def dictIAddGetRefExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mkInstr

private def exactGasProgram (limit : Int) : Array Instr :=
  #[.pushInt (.num limit), .tonEnvOp .setGasLimit, mkInstr]

private def genDictIAddGetRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 30
  let (tag, rng2) := randNat rng1 0 999_999
  let (baseCase, rng3) :=
    match shape with
    | 0 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/miss/null/{tag}")
          (mkStack validNewValue (intV 3) .null (intV 4)), rng2)
    | 1 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/miss/null/n0/{tag}")
          (mkStack validNewValue (intV 0) .null (intV 0)), rng2)
    | 2 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/miss/null/n1023/{tag}")
          (mkStack validNewValue (intV 0) .null (intV 1023)), rng2)
    | 3 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/miss/non-empty/{tag}")
          (mkStack validNewValue (intV 2) (.cell dictSigned4Other) (intV 4)), rng2)
    | 4 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/hit/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 4)), rng2)
    | 5 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/hit/pair/{tag}")
          (mkStack validNewValue (intV (-4)) (.cell dictSigned4Pair) (intV 4)), rng2)
    | 6 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/hit/n1/{tag}")
          (mkStack validNewValue (intV 0) (.cell dictSigned1Pair) (intV 1)), rng2)
    | 7 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/hit/n0/{tag}")
          (mkStack validNewValue (intV 0) (.cell dictSigned0Single) (intV 0)), rng2)
    | 8 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/key/high/{tag}")
          (mkStack validNewValue (intV 8) (.cell dictSigned4Hit) (intV 4)), rng2)
    | 9 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/key/low/{tag}")
          (mkStack validNewValue (intV (-9)) (.cell dictSigned4Hit) (intV 4)), rng2)
    | 10 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/key/n1-high/{tag}")
          (mkStack validNewValue (intV 1) (.cell dictSigned1Pair) (intV 1)), rng2)
    | 11 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/key/nan/{tag}")
          (mkStack validNewValue (.int .nan) (.cell dictSigned4Hit) (intV 4)), rng2)
    | 12 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/key/n0-nonzero/{tag}")
          (mkStack validNewValue (intV 1) (.cell dictSigned0Single) (intV 0)), rng2)
    | 13 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/n/negative/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV (-1))), rng2)
    | 14 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/n/too-large/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 1024)), rng2)
    | 15 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/n/nan/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (.int .nan)), rng2)
    | 16 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/dict-type/{tag}")
          (mkStack validNewValue (intV 3) (.tuple #[]) (intV 4)), rng2)
    | 17 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/key-type/{tag}")
          (mkStack validNewValue (.slice (mkSliceFromBits (natToBits 0xA0 8)) ) (.cell dictSigned4Hit) (intV 4)), rng2)
    | 18 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/newvalue-type/{tag}")
          (mkStack badNewValue (intV 3) (.cell dictSigned4Hit) (intV 4)), rng2)
    | 19 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/malformed-root/{tag}")
          (mkStack validNewValue (intV 3) (.cell malformedDictRoot) (intV 4)), rng2)
    | 20 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/ref-shape/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSignedMalformedValue) (intV 4)), rng2)
    | 21 =>
        (caseDictIAddGetRef (s!"fuzz/err/underflow/0/{tag}") #[], rng2)
    | 22 =>
        (caseDictIAddGetRef (s!"fuzz/err/underflow/1/{tag}") #[validNewValue], rng2)
    | 23 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/underflow/2/{tag}") #[validNewValue, intV 3], rng2)
    | 24 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/underflow/3/{tag}") #[validNewValue, intV 3, .null], rng2)
    | 25 =>
        (caseDictIAddGetRef
          (s!"fuzz/gas/exact/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 4))
          (exactGasProgram dictIAddGetRefExactGas)
          (oracleGasLimitsExact dictIAddGetRefExactGas), rng2)
    | 26 =>
        (caseDictIAddGetRef
          (s!"fuzz/gas/exact-minus-one/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 4))
          (exactGasProgram dictIAddGetRefExactMinusOne)
          (oracleGasLimitsExactMinusOne dictIAddGetRefExactMinusOne), rng2)
    | 27 =>
        (caseDictIAddGetRef
          (s!"fuzz/ok/miss/pair/{tag}")
          (mkStack validNewValue (intV 1) (.cell dictSigned4Pair) (intV 4)), rng2)
    | 28 =>
        (caseDictIAddGetRef
          (s!"fuzz/err/key/high-aligned/{tag}")
          (mkStack validNewValue (intV (-8)) (.cell dictSigned4Other) (intV 3)), rng2)
    | _ =>
        (caseDictIAddGetRef
          (s!"fuzz/default/{tag}")
          (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 4)), rng2)
  ({ baseCase with name := s!"{baseCase.name}" }, rng3)

def suite : InstrSuite where
  id := dictIAddGetRefId
  unit := #[
    { name := "unit/decoder/decode/f43d"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43d 16)
        let _ ← expectDecodeStep "decode/f43d" s mkInstr 16
    },
    { name := "unit/decoder/decode/f43c"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43c 16)
        let _ ← expectDecodeStep "decode/f43c" s (.dictExt (.mutGet true false false .add)) 16
    },
    { name := "unit/decoder/decode/f43e"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43e 16)
        let _ ← expectDecodeStep "decode/f43e" s (.dictExt (.mutGet true true false .add)) 16
    },
    { name := "unit/decoder/decode/f43f"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43f 16)
        let _ ← expectDecodeStep "decode/f43f" s (.dictExt (.mutGet true true true .add)) 16
    },
    { name := "unit/decoder/decode/invalid-below"
      run := do
        expectDecodeInvOpcode "decode/f439" 0xf439
    },
    { name := "unit/decoder/decode/invalid-above"
      run := do
        expectDecodeInvOpcode "decode/f440" 0xf440
    },
    { name := "unit/decoder/decode/truncated8"
      run := do
        expectDecodeInvOpcode "decode/truncated8" 0xf4
    },
    { name := "unit/asm/encode/not-supported"
      run := do
        match assembleCp0 [mkInstr] with
        | .ok _ =>
            throw (IO.userError "unit/asm/encode/not-supported: expected invOpcode, got success")
        | .error e =>
            if e = .invOpcode then
              pure ()
            else
              throw (IO.userError s!"unit/asm/encode/not-supported: expected invOpcode, got {e}")
    }
  ]
  oracle := #[
    -- [B1] runtime success: miss on null root (n=4).
    caseDictIAddGetRef "oracle/ok/miss/null/n4" (mkStack validNewValue (intV 3) .null (intV 4))
    -- [B1] runtime success: miss on null root (n=0).
    , caseDictIAddGetRef "oracle/ok/miss/null/n0" (mkStack validNewValue (intV 0) .null (intV 0))
    -- [B1] runtime success: miss on null root (n=1023).
    , caseDictIAddGetRef "oracle/ok/miss/null/n1023" (mkStack validNewValue (intV 0) .null (intV 1023))
    -- [B1] runtime success: miss in non-empty root (n=4).
    , caseDictIAddGetRef "oracle/ok/miss/non-empty" (mkStack validNewValue (intV 1) (.cell dictSigned4Other) (intV 4))
    -- [B1] runtime success: miss in non-empty pair root (n=4).
    , caseDictIAddGetRef "oracle/ok/miss/non-empty/pair" (mkStack validNewValue (intV 1) (.cell dictSigned4Pair) (intV 4))
    -- [B1] runtime success: miss at n=1 boundary key.
    , caseDictIAddGetRef "oracle/ok/miss/n1" (mkStack validNewValue (intV 1) (.cell dictSigned1Pair) (intV 1))
    -- [B2] runtime success: hit returns old value as ref, bool true (n=4).
    , caseDictIAddGetRef "oracle/ok/hit/n4" (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 4))
    -- [B2] runtime success: hit returns old value as ref, bool true (n=4, second key).
    , caseDictIAddGetRef "oracle/ok/hit/n4/b" (mkStack validNewValue (intV (-4)) (.cell dictSigned4Pair) (intV 4))
    -- [B2] runtime success: hit on n=1 root.
    , caseDictIAddGetRef "oracle/ok/hit/n1" (mkStack validNewValue (intV 0) (.cell dictSigned1Pair) (intV 1))
    -- [B2] runtime success: hit on n=0 root.
    , caseDictIAddGetRef "oracle/ok/hit/n0" (mkStack validNewValue (intV 0) (.cell dictSigned0Single) (intV 0))
    -- [B3] key out of range on positive side (n=4).
    , caseDictIAddGetRef "oracle/err/key-range/positive" (mkStack validNewValue (intV 8) (.cell dictSigned4Hit) (intV 4))
    -- [B3] key out of range on signed negative side (n=4).
    , caseDictIAddGetRef "oracle/err/key-range/negative" (mkStack validNewValue (intV (-9)) (.cell dictSigned4Hit) (intV 4))
    -- [B3] key out of range for n=1.
    , caseDictIAddGetRef "oracle/err/key-range/n1" (mkStack validNewValue (intV 1) (.cell dictSigned1Pair) (intV 1))
    -- [B3] non-zero key with zero width key is rejected.
    , caseDictIAddGetRef "oracle/err/key-range/n0-nonzero" (mkStack validNewValue (intV 1) (.cell dictSigned0Single) (intV 0))
    -- [B3] key conversion fails on NaN.
    , caseDictIAddGetRef "oracle/err/key/nan" (mkStack validNewValue (.int .nan) (.cell dictSigned4Hit) (intV 4))
    -- [B3] signed boundary failure for n=4 using -8? check with malformed pair root.
    , caseDictIAddGetRef "oracle/err/key-range/boundary-negative" (mkStack validNewValue (intV (-9)) (.cell dictSigned4Pair) (intV 4))
    -- [B4] n validation failure: negative n.
    , caseDictIAddGetRef "oracle/err/n/negative" (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV (-1)))
    -- [B4] n validation failure: >1023.
    , caseDictIAddGetRef "oracle/err/n/too-large" (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 1024))
    -- [B4] n validation failure: NaN.
    , caseDictIAddGetRef "oracle/err/n/nan" (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (.int .nan))
    -- [B5] underflow (empty stack).
    , caseDictIAddGetRef "oracle/err/underflow/empty" #[]
    -- [B5] underflow (one item).
    , caseDictIAddGetRef "oracle/err/underflow/one" #[validNewValue]
    -- [B5] underflow (two items).
    , caseDictIAddGetRef "oracle/err/underflow/two" #[validNewValue, intV 1]
    -- [B5] underflow (three items).
    , caseDictIAddGetRef "oracle/err/underflow/three" #[validNewValue, intV 1, .null]
    -- [B5] stack type error: dict root must be cell or null.
    , caseDictIAddGetRef "oracle/err/type/dict" (mkStack validNewValue (intV 3) (.tuple #[]) (intV 4))
    -- [B5] stack type error: key must be int.
    , caseDictIAddGetRef "oracle/err/type/key" (mkStack validNewValue (.slice valueSliceA) (.cell dictSigned4Hit) (intV 4))
    -- [B5] stack type error: new value must be cell in by-ref mode.
    , caseDictIAddGetRef "oracle/err/type/newvalue" (mkStack badNewValue (intV 3) (.cell dictSigned4Hit) (intV 4))
    -- [B6] malformed existing dict root.
    , caseDictIAddGetRef "oracle/err/malformed-root" (mkStack validNewValue (intV 3) (.cell malformedDictRoot) (intV 4))
    -- [B6] malformed existing stored value for ref extraction.
    , caseDictIAddGetRef "oracle/err/ref-shape" (mkStack validNewValue (intV 3) (.cell dictSignedMalformedValue) (intV 4))
    -- [B9] exact gas succeeds.
    , caseDictIAddGetRef "oracle/gas/exact" (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 4))
      (exactGasProgram dictIAddGetRefExactGas)
      (oracleGasLimitsExact dictIAddGetRefExactGas)
    -- [B9] exact-minus-one gas fails.
    , caseDictIAddGetRef "oracle/gas/exact-minus-one" (mkStack validNewValue (intV 3) (.cell dictSigned4Hit) (intV 4))
      (exactGasProgram dictIAddGetRefExactMinusOne)
      (oracleGasLimitsExactMinusOne dictIAddGetRefExactMinusOne)
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictIAddGetRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIADDGETREF
