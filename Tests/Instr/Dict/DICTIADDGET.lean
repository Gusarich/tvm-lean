import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIADDGET

/-!
INSTRUCTION: DICTIADDGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success when the key is absent for `DICTIADDGET`:
   - `popNatUpTo` accepts `n`, `popMaybeCell` returns optional root, int key is valid.
   - `dictLookupSetSliceWithCells`/`dictLookupSetRefWithCells` in `mode=.add` returns `oldVal? = none`.
   - Result: new root is pushed, then `false` (`-1`) is pushed (via `pushBool false` because add mode sets `ok_f := false`).

2. [B2] Runtime success when the key exists for both slice-based and by-ref values:
   - `oldVal? = some` for non-ref branch pushes old value slice + `false`.
   - by-ref branch requires an old value slice of exactly one reference and zero remaining bits; valid case pushes old value as cell + `false`.

3. [B3] Runtime extract/shape failures:
   - Integer index path in `.mutGet`: `dictKeyBits?` returns `none` for out-of-range index -> for `.add`, this is converted to `cellUnd`.
   - by-ref branch with existing key but malformed stored value triggers `extractRefOrThrow` → `dictErr` (`cell must have no bits and exactly one reference`).

4. [B4] Runtime numeric and typing error branches:
   - Underflow before execution (`VM.checkUnderflow 4`): stack size < 4.
   - `popNatUpTo 1023`: negative, `NaN`, or >1023 => `rangeChk`.
   - `popMaybeCell` and `popSlice`/`popCell`/`popInt`: wrong top-type => `typeChk`.

5. [B5] Decoder boundaries:
   - `Codepage/Cp0.lean` maps `0xf43a..0xf43f` to `.dictExt (.mutGet intKey=true unsigned=? byRef=? .add)`.
   - byRef = bit0, unsigned = bit1 (only meaningful when intKey=1 from the opcode range).
   - lower/upper gaps around the range must fail to decode as `DICTIADDGET`.

6. [B6] Assembler encoding:
   - `Asm/Cp0.lean` currently falls through `.dictExt _` to `invOpcode`, so no `.dictExt` encoding path exists.
   - This is intentionally a negative category: any attempt to assemble `DICTIADDGET` must fail.

7. [B7] Gas accounting:
   - Base `instrGas` follows fixed 16-bit cost accounting (`gasPerInstr + 16` for this class).
   - Dictionary-specific dynamic charges are injected via `consumeCreatedGas`, `registerCellLoad`, and friends in `execInstrDictExt`.
   - Both exact-budget and exact-minus-one (out-of-gas) harness cases are needed.

8. [B8] Fuzzer branch coverage:
   - Explicit fuzz shapes must hit success, miss, hit, underflow, range/type errors, malformed root, and malformed stored-ref paths with bounded branching over unsigned/byRef flags.

Total branches: 8

Every branch listed above has at least one tagged oracle test or direct unit case below.
-/

private def dictIAddGetId : InstrId := { name := "DICTIADDGET" }

private def mkInstr (unsigned byRef : Bool) : Instr :=
  .dictExt (.mutGet true unsigned byRef .add)

private def mkDictCaseStack (newVal : Value) (key : Value) (dict : Value) (n : Value) : Array Value :=
  #[newVal, key, dict, n]

private def normalNewValue (byRef : Bool) : Value :=
  if byRef then
    .cell (Cell.mkOrdinary (natToBits 0xC0 8) #[])
  else
    .slice (mkSliceFromBits (natToBits 0x1F 8))

private def badNewValue (byRef : Bool) : Value :=
  if byRef then
    .slice (mkSliceFromBits (natToBits 0x80 8))
  else
    .cell (Cell.mkOrdinary (natToBits 0xAB 8) #[])

private def invalidNewSlice : Slice := mkSliceFromBits (natToBits 0x55 8)
private def validValCell : Cell := Cell.mkOrdinary (natToBits 0x5A 8) #[]

private def mkDictRootSlice! (label : String) (key : Int) (n : Nat) (unsigned : Bool) (value : Slice) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n unsigned with
    | some kb => kb
    | none => panic! s!"{label}: invalid key ({key}, n={n}, unsigned={unsigned})"
  match dictSetSliceWithCells none keyBits value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _, _, _) => panic! s!"{label}: no dict root produced"
  | .error e => panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"

private def mkDictRootRef! (label : String) (key : Int) (n : Nat) (unsigned : Bool) (value : Cell) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n unsigned with
    | some kb => kb
    | none => panic! s!"{label}: invalid key ({key}, n={n}, unsigned={unsigned})"
  match dictSetRefWithCells none keyBits value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _, _, _) => panic! s!"{label}: no dict root produced"
  | .error e => panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"

private def dictUnsignedHitSlice : Cell :=
  mkDictRootSlice! "dict/unsigned/hit/slice" 13 4 true (mkSliceFromBits (natToBits 0x5 4))

private def dictUnsignedHitRef : Cell :=
  mkDictRootRef! "dict/unsigned/hit/ref" 13 4 true validValCell

private def dictUnsignedOtherKey : Cell :=
  mkDictRootSlice! "dict/unsigned/other/key" 2 4 true (mkSliceFromBits (natToBits 0xA 4))

private def dictUnsignedMalformedRefLike : Cell :=
  mkDictRootSlice! "dict/unsigned/invalid-ref-shape" 10 4 true invalidNewSlice

private def dictSignedHitSlice : Cell :=
  mkDictRootSlice! "dict/signed/hit/slice" (-3) 4 false (mkSliceFromBits (natToBits 0x6 3))

private def dictSignedHitRef : Cell :=
  mkDictRootRef! "dict/signed/hit/ref" (-3) 4 false validValCell

private def dictSignedOtherKey : Cell :=
  mkDictRootSlice! "dict/signed/other/key" (-1) 4 false (mkSliceFromBits (natToBits 0xD 3))

private def dictSignedMalformedRefLike : Cell :=
  mkDictRootSlice! "dict/signed/invalid-ref-shape" (-6) 4 false invalidNewSlice

private def dictN0HitSlice : Cell :=
  mkDictRootSlice! "dict/n0/hit/slice" 0 0 true (mkSliceFromBits #[])

private def dictN0HitRef : Cell :=
  mkDictRootRef! "dict/n0/hit/ref" 0 0 false validValCell

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def caseStack
    (_unsigned byRef : Bool)
    (dict : Value)
    (key : Int)
    (n : Int)
    : Array Value :=
  mkDictCaseStack (normalNewValue byRef) (.int (.num key)) dict (.int (.num n))

private def caseDictMutGet
    (name : String)
    (unsigned byRef : Bool)
    (stack : Array Value)
    (program : Array Instr := #[mkInstr unsigned byRef])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIAddGetId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr}")
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def dictIAddGetExactGas : Int :=
  computeExactGasBudget (mkInstr true false)

private def dictIAddGetExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr true false)

private def genDictIAddGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (unsigned, rng2) := randBool rng1
  let (byRef, rng3) := randBool rng2
  let (tag, rng4) := randNat rng3 0 999_999
  match shape with
  | 0 =>
      let stack : Array Value := caseStack unsigned byRef .null (if unsigned then 11 else (-2)) 4
      (caseDictMutGet (s!"/fuzz/miss/{tag}") unsigned byRef stack, rng4)
  | 1 =>
      let (stack, _) :=
        if byRef then
          (mkDictCaseStack (normalNewValue true) (intV (if unsigned then 13 else (-3)))
            (if unsigned then .cell dictUnsignedHitRef else .cell dictSignedHitRef) (.int (.num 4)), (0 : Nat))
        else
          (mkDictCaseStack (normalNewValue false) (intV (if unsigned then 13 else (-3)))
            (if unsigned then .cell dictUnsignedHitSlice else .cell dictSignedHitSlice) (.int (.num 4)), 0)
      (caseDictMutGet (s!"/fuzz/hit/{tag}") unsigned byRef stack, rng4)
  | 2 =>
      if byRef then
        let stack : Array Value :=
          mkDictCaseStack (normalNewValue true) (intV (if unsigned then 10 else (-6)))
            (if unsigned then .cell dictUnsignedMalformedRefLike else .cell dictSignedMalformedRefLike) (.int (.num 4))
        (caseDictMutGet (s!"/fuzz/ref-shape-error/{tag}") unsigned byRef stack, rng4)
      else
        let stack : Array Value := caseStack unsigned false .null (if unsigned then 7 else (-2)) 4
        (caseDictMutGet (s!"/fuzz/miss-as-fallback/{tag}") unsigned false stack, rng4)
  | 3 =>
      let (badIdx, rng5) := randBool rng4
      let idx : Int :=
        if unsigned then
          if badIdx then 16 else (-1)
        else
          if badIdx then 8 else (-9)
      let stack := caseStack unsigned byRef .null idx 4
      (caseDictMutGet (s!"/fuzz/key-out-of-range/{tag}") unsigned byRef stack, rng5)
  | 4 =>
      let (mode, rng5) := randNat rng4 0 2
      let nVal : Value :=
        if mode = 0 then intV (-1) else if mode = 1 then intV 1024 else .int .nan
      let stack := mkDictCaseStack (normalNewValue byRef) (if unsigned then intV 13 else intV (-3)) .null nVal
      (caseDictMutGet (s!"/fuzz/n-out-of-range/{tag}") unsigned byRef stack, rng5)
  | 5 =>
      let stack : Array Value :=
        mkDictCaseStack (normalNewValue byRef) (intV (if unsigned then 1 else (-1))) (.tuple #[]) (intV 4)
      (caseDictMutGet (s!"/fuzz/dict-type-error/{tag}") unsigned byRef stack, rng4)
  | 6 =>
      let stack : Array Value :=
        mkDictCaseStack (normalNewValue byRef) (if unsigned then .slice invalidNewSlice else .slice invalidNewSlice) .null (intV 4)
      (caseDictMutGet (s!"/fuzz/key-type-error/{tag}") unsigned byRef stack, rng4)
  | 7 =>
      let stack : Array Value :=
        mkDictCaseStack (badNewValue byRef) (intV (if unsigned then 13 else (-3))) .null (intV 4)
      (caseDictMutGet (s!"/fuzz/newvalue-type-error/{tag}") unsigned byRef stack, rng4)
  | 8 =>
      let (sz, rng5) := randNat rng4 0 3
      let stack : Array Value :=
        match sz with
        | 0 => #[]
        | 1 => #[intV 1]
        | 2 => #[intV 1, intV 2]
        | _ => #[intV 1, intV 2, intV 3]
      (caseDictMutGet (s!"/fuzz/underflow/{tag}") unsigned byRef stack, rng5)
  | 9 =>
      let stack : Array Value :=
        mkDictCaseStack (normalNewValue byRef) (intV (if unsigned then 6 else (-2)) ) (if unsigned then .cell dictUnsignedOtherKey else .cell dictSignedOtherKey) (intV 4)
      (caseDictMutGet (s!"/fuzz/non-empty-miss/{tag}") unsigned byRef stack, rng4)
  | 10 =>
      let stack : Array Value :=
        mkDictCaseStack (normalNewValue byRef) (intV 0) .null (intV 0)
      (caseDictMutGet (s!"/fuzz/n-zero/{tag}") unsigned byRef stack, rng4)
  | 11 =>
      let stack : Array Value :=
        mkDictCaseStack (normalNewValue byRef) (intV (if unsigned then 9 else (-4))) (if unsigned then .cell dictUnsignedHitSlice else .cell dictSignedHitSlice) (intV 4)
      (caseDictMutGet (s!"/fuzz/hit/{tag}") unsigned byRef stack, rng4)
  | 12 =>
      let stack : Array Value :=
        mkDictCaseStack (normalNewValue byRef) (if unsigned then intV 13 else intV (-3))
          (.cell malformedDictRoot) (intV 4)
      (caseDictMutGet (s!"/fuzz/malformed-root/{tag}") unsigned byRef stack, rng4)
  | _ =>
      let stack := mkDictCaseStack (normalNewValue byRef) (intV (if unsigned then 13 else (-3))) (if unsigned then .cell dictUnsignedHitRef else .cell dictSignedHitRef) (intV 4)
      (caseDictMutGet (s!"/fuzz/default/{tag}") unsigned byRef stack, rng4)

def suite : InstrSuite where
  id := dictIAddGetId
  unit := #[
    { name := "unit/decoder/decode/f43a"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43a 16)
        let _ ← expectDecodeStep "decode/f43a" s (mkInstr true false) 16
    }
    ,
    { name := "unit/decoder/decode/f43c-unsigned-false"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43c 16)
        let _ ← expectDecodeStep "decode/f43c" s (mkInstr false false) 16
    }
    ,
    { name := "unit/decoder/decode/f43b"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43b 16)
        let _ ← expectDecodeStep "decode/f43b" s (mkInstr true true) 16
    }
    ,
    { name := "unit/decoder/decode/f43f"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf43f 16)
        let _ ← expectDecodeStep "decode/f43f" s (mkInstr true true) 16
    }
    ,
    { name := "unit/decoder/decode/invalid-below"
      run := do
        expectDecodeInvOpcode "decode/f439" 0xf439
    }
    ,
    { name := "unit/decoder/decode/invalid-above"
      run := do
        expectDecodeInvOpcode "decode/f440" 0xf440
    }
    ,
    { name := "unit/asm/encode/not-supported"
      run := do
        match assembleCp0 [mkInstr true false] with
        | .ok _ =>
            throw (IO.userError "asm/encode/not-supported: expected invOpcode, got success")
        | .error e =>
            if e = .invOpcode then
              pure ()
            else
              throw (IO.userError s!"asm/encode/not-supported: expected invOpcode, got {e}")
    }
  ]
  oracle := #[
    -- [B1] runtime success: empty dict, non-ref insertion, unsigned key.
    caseDictMutGet "oracle/ok/miss/byref-false/unsigned/4" true false
      (caseStack true false .null 7 4)
    -- [B1] runtime success: empty dict, by-ref insertion, unsigned key.
    , caseDictMutGet "oracle/ok/miss/byref-true/unsigned/4" true true
      (caseStack true true .null 7 4)
    -- [B1] runtime success: empty dict, non-ref insertion, signed key.
    , caseDictMutGet "oracle/ok/miss/byref-false/signed/4" false false
      (caseStack false false .null (-2) 4)
    -- [B1] runtime success: empty dict, by-ref insertion, signed key.
    , caseDictMutGet "oracle/ok/miss/byref-true/signed/4" false true
      (caseStack false true .null (-2) 4)
    -- [B1] runtime success: non-empty dict miss with unsigned key.
    , caseDictMutGet "oracle/ok/miss/non-empty/byref-false/unsigned/4" true false
      (caseStack true false (.cell dictUnsignedOtherKey) 2 4)
    -- [B1] runtime success: non-empty dict miss with signed key.
    , caseDictMutGet "oracle/ok/miss/non-empty/byref-false/signed/4" false false
      (caseStack false false (.cell dictSignedOtherKey) (-2) 4)
    -- [B2] runtime success: existing key -> old slice returned, bool false (unsigned variant).
    , caseDictMutGet "oracle/ok/hit/byref-false/unsigned/4" true false
      (caseStack true false (.cell dictUnsignedHitSlice) 13 4)
    -- [B2] runtime success: existing key -> old ref returned, bool false.
    , caseDictMutGet "oracle/ok/hit/byref-true/unsigned/4" true true
      (mkDictCaseStack (normalNewValue true) (intV 13) (.cell dictUnsignedHitRef) (intV 4))
    -- [B2] runtime success: existing key -> old slice returned (signed variant).
    , caseDictMutGet "oracle/ok/hit/byref-false/signed/4" false false
      (caseStack false false (.cell dictSignedHitSlice) (-3) 4)
    -- [B2] runtime success: existing key -> old ref returned (signed variant).
    , caseDictMutGet "oracle/ok/hit/byref-true/signed/4" false true
      (mkDictCaseStack (normalNewValue true) (intV (-3)) (.cell dictSignedHitRef) (intV 4))
    -- [B1] runtime success: zero-bit key insert in unsigned mode, empty dict.
    , caseDictMutGet "oracle/ok/zero-key/miss/byref-false" true false
      (mkDictCaseStack (normalNewValue false) (intV 0) .null (intV 0))
    -- [B1] runtime success: zero-bit key insert in signed mode, existing root.
    , caseDictMutGet "oracle/ok/zero-key/hit/byref-false" true false
      (mkDictCaseStack (normalNewValue false) (intV 0) (.cell dictN0HitSlice) (intV 0))
    -- [B3] runtime failure: unsigned-mode key out of range (positive overflow).
    , caseDictMutGet "oracle/err/key-range/unsigned-positive" true false
      (mkDictCaseStack (normalNewValue false) (intV 16) .null (intV 4))
    -- [B3] runtime failure: unsigned-mode key out of range (negative index).
    , caseDictMutGet "oracle/err/key-range/unsigned-negative" true false
      (mkDictCaseStack (normalNewValue false) (intV (-1)) .null (intV 4))
    -- [B3] runtime failure: signed-mode key out of range (high side).
    , caseDictMutGet "oracle/err/key-range/signed-high" false false
      (mkDictCaseStack (normalNewValue false) (intV 8) .null (intV 4))
    -- [B3] runtime failure: signed-mode key out of range (low side).
    , caseDictMutGet "oracle/err/key-range/signed-low" false false
      (mkDictCaseStack (normalNewValue false) (intV (-9)) .null (intV 4))
    -- [B3] runtime failure: zero-bit key with non-zero key value (unsigned mode).
    , caseDictMutGet "oracle/err/key-range/n-zero-nonzero/unsigned" true false
      (mkDictCaseStack (normalNewValue false) (intV 1) .null (intV 0))
    -- [B3] runtime failure: zero-bit key with non-zero key value (signed mode).
    , caseDictMutGet "oracle/err/key-range/n-zero-nonzero/signed" false false
      (mkDictCaseStack (normalNewValue false) (intV 1) .null (intV 0))
    -- [B4] runtime failure: `n` negative.
    , caseDictMutGet "oracle/err/n-negative" true false
      (mkDictCaseStack (normalNewValue false) (intV 7) .null (intV (-1)))
    -- [B4] runtime failure: `n` exceeds 1023.
    , caseDictMutGet "oracle/err/n-too-large" true false
      (mkDictCaseStack (normalNewValue false) (intV 3) .null (intV 1024))
    -- [B4] runtime failure: `n` is NaN.
    , caseDictMutGet "oracle/err/n-nan" true false
      (mkDictCaseStack (normalNewValue false) (intV 3) .null (.int .nan))
    -- [B4] runtime failure: `n` type-check and dict root type-check path.
    , caseDictMutGet "oracle/err/dict-type" true false
      (mkDictCaseStack (normalNewValue false) (intV 3) (.tuple #[]) (intV 4))
    -- [B4] runtime failure: key type-check.
    , caseDictMutGet "oracle/err/key-type" true false
      (mkDictCaseStack (normalNewValue false) (.slice invalidNewSlice) (.null) (intV 4))
    -- [B4] runtime failure: by-ref insertion requires cell, but a slice is provided.
    , caseDictMutGet "oracle/err/newvalue-type/byref" true true
      (mkDictCaseStack (badNewValue true) (intV 3) .null (intV 4))
    -- [B4] runtime failure: non-ref insertion requires slice, but a cell is provided.
    , caseDictMutGet "oracle/err/newvalue-type/non-ref" true false
      (mkDictCaseStack (badNewValue false) (intV 3) .null (intV 4))
    -- [B3] runtime failure: existing stored value malformed for by-ref extract shape.
    , caseDictMutGet "oracle/err/ref-shape/non-ref-value" true true
      (mkDictCaseStack (normalNewValue true) (intV 10) (.cell dictUnsignedMalformedRefLike) (intV 4))
    -- [B6] runtime failure: malformed dictionary root not parseable as dict.
    , caseDictMutGet "oracle/err/malformed-root" true true
      (mkDictCaseStack (normalNewValue true) (intV 10) (.cell malformedDictRoot) (intV 4))
    -- [B7] runtime underflow: empty stack.
    , caseDictMutGet "oracle/err/underflow/empty" true false #[]
    -- [B7] runtime underflow: one item.
    , caseDictMutGet "oracle/err/underflow/one-item" true false
      #[intV 1]
    -- [B7] runtime underflow: two items.
    , caseDictMutGet "oracle/err/underflow/two-items" true false
      (mkDictCaseStack (normalNewValue false) (intV 1) (intV 2) (intV 3))
    -- [B7] runtime underflow: three items.
    , caseDictMutGet "oracle/err/underflow/three-items" true false
      (mkDictCaseStack (normalNewValue false) (intV 1) (.cell Cell.empty) (intV 3))
    -- [B9] exact gas branch should execute.
    , caseDictMutGet "oracle/gas/exact" true false
      (mkDictCaseStack (normalNewValue false) (intV 13) .null (intV 4))
      (#[.pushInt (.num dictIAddGetExactGas), .tonEnvOp .setGasLimit, mkInstr true false])
      (oracleGasLimitsExact dictIAddGetExactGas)
    -- [B9] exact-minus-one gas should fail.
    , caseDictMutGet "oracle/gas/exact-minus-one" true false
      (mkDictCaseStack (normalNewValue false) (intV 13) .null (intV 4))
      (#[.pushInt (.num dictIAddGetExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr true false])
      (oracleGasLimitsExact dictIAddGetExactGasMinusOne)
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictIAddGetFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIADDGET
