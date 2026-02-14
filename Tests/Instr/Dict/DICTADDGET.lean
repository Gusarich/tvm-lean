import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTADDGET

/-!
INSTRUCTION: DICTADDGET

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success for miss:
   - `n` validated by `popNatUpTo 1023`.
   - Dictionary root is popped as optional cell (`null`/`cell`).
   - Non-int key (`VM.popSlice`) is read and must have `n` bits.
   - `dictLookupSetSliceWithCells` runs with `.add`, returns `oldVal? = none`, and pushes
     `(newRoot, -1)` where `-1` is encoded as `Bool.true`.

2. [B2] Runtime success for hit:
   - For byRef = false: key exists, old value is pushed as a slice, then `0`.
   - For byRef = true: key exists, `extractRefOrThrow` is used on old slice and if it is exactly
     one-ref-and-no-bits, pushes that `.cell`, then `0`.

3. [B3] Key shortness and type checks:
   - Non-int path returns `none` when requested bits are missing.
   - For both byRef modes in `.add`, `keyBits? = none` is converted to `.cellUnd` (no mutation).
   - `key` value is not a slice (`int`, `cell`, `null`, `tuple`, etc.) causes `typeChk`.

4. [B4] Numeric validation and operand typing:
   - `n` must be int in `[0,1023]`; negative, >1023, or `.nan` are `rangeChk`.
   - `checkUnderflow 4` catches 0..3 depth stacks.
   - `dict`/`newValue` type mismatches (`typeChk`) and `byRef` value mismatches (`slice` vs `cell`) are errors.

5. [B5] Dictionary shape failures:
   - malformed dictionary root (non-dict payload) raises `.dictErr`.
   - byRef hit path with malformed old value shape (not one-reference payload) raises `.dictErr`.

6. [B6] Decoder boundaries:
   - `0xf43a` and `0xf43b` map to `.dictExt (.mutGet false false false .add)` and
     `.dictExt (.mutGet false false true .add)`.
   - `0xf43c` / `0xf43d` map to integer-key variants (same handler, different opcode family).
   - `0xf439` / `0xf440` and truncated forms must decode as `.invOpcode`.

7. [B7] Assembler encoding:
   - `assembleCp0` has no `.dictExt` clause and must fail with `.invOpcode`.

8. [B8] Gas accounting:
   - Instruction-level budget is constant (`computeExactGasBudget` / minus-one helper).
   - `execInstrDictExt` additionally charges variable dictionary create/load cost through `consumeCreatedGas`
     and cell-load registration in successful mutation paths.
   - Exact and exact-minus-one branches should be covered.

TOTAL BRANCHES: 8

Each oracle test below is tagged [Bn] to the branch(es) it exercises.
Any remaining or uncovered branch is intentionally covered by fuzz.
-/

private def dictAddGetId : InstrId :=
  { name := "DICTADDGET" }

private def mkInstr (byRef : Bool) : Instr :=
  .dictExt (.mutGet false false byRef .add)

private def rawF43A : Cell := Cell.mkOrdinary (natToBits 0xf43a 16) #[]
private def rawF43B : Cell := Cell.mkOrdinary (natToBits 0xf43b 16) #[]
private def rawF43C : Cell := Cell.mkOrdinary (natToBits 0xf43c 16) #[]
private def rawF43D : Cell := Cell.mkOrdinary (natToBits 0xf43d 16) #[]
private def rawF439 : Cell := Cell.mkOrdinary (natToBits 0xf439 16) #[]
private def rawF440 : Cell := Cell.mkOrdinary (natToBits 0xf440 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

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

private def valueSliceA : Slice := mkSliceFromBits (natToBits 0x5A 8)
private def valueSliceB : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def invalidNewSlice : Slice := mkSliceFromBits (natToBits 0x55 8)
private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0xC0 8) #[]

private def key4A : BitString := natToBits 0xA 4
private def key4B : BitString := natToBits 0x3 4
private def key4C : BitString := natToBits 0x5 4
private def key3 : BitString := natToBits 0b101 3
private def key0 : BitString := #[]
private def key1023 : BitString := Array.replicate 1023 true

private def keySlice4A : Slice := mkSliceFromBits key4A
private def keySlice4B : Slice := mkSliceFromBits key4B
private def keySlice4C : Slice := mkSliceFromBits key4C
private def keySlice4Short : Slice := mkSliceFromBits key3
private def keySlice0 : Slice := mkSliceFromBits key0
private def keySlice1023 : Slice := mkSliceFromBits key1023

private def mkDictRootSlice! (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetSliceWithCells root k v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: insertion did not produce root"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def mkDictRootRef! (label : String) (pairs : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetRefWithCells root k v .set with
      | .ok (some root', _ok, _created, _loaded) =>
          root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: insertion did not produce root"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictSlice4Single : Cell :=
  mkDictRootSlice! "dict/slice/single/4" #[(key4A, valueSliceA)]
private def dictSlice4Miss : Cell :=
  mkDictRootSlice! "dict/slice/miss/4" #[(key4B, valueSliceB)]
private def dictRef4Single : Cell :=
  mkDictRootRef! "dict/ref/single/4" #[(key4A, valueCellA)]
private def dictRef4Miss : Cell :=
  mkDictRootRef! "dict/ref/miss/4" #[(key4B, valueCellA)]
private def dictSliceMalformedRefLike : Cell :=
  mkDictRootSlice! "dict/ref-shape/error" #[(key4C, invalidNewSlice)]
private def dictSliceN0 : Cell :=
  mkDictRootSlice! "dict/n0/single" #[(#[], valueSliceB)]
private def dictRefN0 : Cell :=
  mkDictRootRef! "dict/n0/single/ref" #[(#[], valueCellA)]
private def dictSlice1023 : Cell :=
  mkDictRootSlice! "dict/n1023/single" #[(key1023, valueSliceA)]
private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def caseDictAddGet
    (name : String)
    (byRef : Bool)
    (stack : Array Value)
    (program : Array Instr := #[mkInstr byRef])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictAddGetId
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

private def expectAssembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected invOpcode, got success")

private def dictAddGetExactGas : Int :=
  computeExactGasBudget (mkInstr false)
private def dictAddGetExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr false)
private def dictAddGetExactGasByRef : Int :=
  computeExactGasBudget (mkInstr true)
private def dictAddGetExactGasMinusOneByRef : Int :=
  computeExactGasBudgetMinusOne (mkInstr true)

private def dictAddGetGasProgram (gas : Int) (byRef : Bool) : Array Instr :=
  #[.pushInt (.num gas), .tonEnvOp .setGasLimit, mkInstr byRef]

private def genDictAddGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    match shape with
    | 0 =>
        (caseDictAddGet "fuzz/miss/null/notref" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4B) .null (intV 4)), rng2)
    | 1 =>
        (caseDictAddGet "fuzz/miss/null/byref" true
          (mkDictCaseStack (normalNewValue true) (.slice keySlice4B) .null (intV 4)), rng2)
    | 2 =>
        (caseDictAddGet "fuzz/hit/notref" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV 4)), rng2)
    | 3 =>
        (caseDictAddGet "fuzz/hit/byref" true
          (mkDictCaseStack (normalNewValue true) (.slice keySlice4A) (.cell dictRef4Single) (intV 4)), rng2)
    | 4 =>
        (caseDictAddGet "fuzz/nonempty-miss/notref" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4C) (.cell dictSlice4Miss) (intV 4)), rng2)
    | 5 =>
        (caseDictAddGet "fuzz/nonempty-miss/byref" true
          (mkDictCaseStack (normalNewValue true) (.slice keySlice4C) (.cell dictRef4Miss) (intV 4)), rng2)
    | 6 =>
        (caseDictAddGet "fuzz/key-short/notref" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4Short) (.cell dictSlice4Single) (intV 4)), rng2)
    | 7 =>
        (caseDictAddGet "fuzz/key-short/byref" true
          (mkDictCaseStack (normalNewValue true) (.slice keySlice4Short) (.cell dictRef4Single) (intV 4)), rng2)
    | 8 =>
        (caseDictAddGet "fuzz/key-short-zero" false
          (mkDictCaseStack (normalNewValue false) (intV 3) (.cell dictSlice4Single) (intV 0)), rng2)
    | 9 =>
        (caseDictAddGet "fuzz/n-negative" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV (-1))), rng2)
    | 10 =>
        (caseDictAddGet "fuzz/n-too-large" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV 1024)), rng2)
    | 11 =>
        (caseDictAddGet "fuzz/n-nan" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (.int .nan)), rng2)
    | 12 =>
        (caseDictAddGet "fuzz/dict-type-error" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.tuple #[]) (intV 4)), rng2)
    | 13 =>
        (caseDictAddGet "fuzz/key-type-error" false
          (mkDictCaseStack (normalNewValue false) (intV 3) (.cell dictSlice4Single) (intV 4)), rng2)
    | 14 =>
        (caseDictAddGet "fuzz/newvalue-type/notref" false
          (mkDictCaseStack (badNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV 4)), rng2)
    | 15 =>
        (caseDictAddGet "fuzz/newvalue-type/byref" true
          (mkDictCaseStack (badNewValue true) (.slice keySlice4A) (.cell dictSlice4Single) (intV 4)), rng2)
    | 16 =>
        (caseDictAddGet "fuzz/ref-shape" true
          (mkDictCaseStack (normalNewValue true) (.slice keySlice4C) (.cell dictSliceMalformedRefLike) (intV 4)), rng2)
    | 17 =>
        (caseDictAddGet "fuzz/malformed-root" false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell malformedDictRoot) (intV 4)), rng2)
    | 18 =>
        (caseDictAddGet "fuzz/malformed-root-byref" true
          (mkDictCaseStack (normalNewValue true) (.slice keySlice4A) (.cell malformedDictRoot) (intV 4)), rng2)
    | 19 =>
        let underflow : Array Value := #[normalNewValue true, (.slice keySlice4A), .cell dictSlice4Single]
        (caseDictAddGet "fuzz/underflow" true underflow, rng2)
    | 20 =>
        (caseDictAddGet "fuzz/gas/exact"
          false
          (mkDictCaseStack (normalNewValue false) (.slice keySlice4B) .null (intV 4))
          (dictAddGetGasProgram dictAddGetExactGas false)
          (oracleGasLimitsExact dictAddGetExactGas), rng2)
    | _ =>
        let (under, rng3) := randBool rng2
        let byRef : Bool := under
        let program := dictAddGetGasProgram (if byRef then dictAddGetExactGasByRef else dictAddGetExactGas) byRef
        let gasLimits :=
          if byRef then
            oracleGasLimitsExact dictAddGetExactGasByRef
          else
            oracleGasLimitsExact dictAddGetExactGas
        (caseDictAddGet "fuzz/gas/exact-random-byref"
          byRef
          (mkDictCaseStack (normalNewValue byRef) (.slice keySlice4A) .null (intV 4))
          program
          gasLimits, rng3)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := dictAddGetId
  unit := #[
    { name := "unit/decoder/decode/f43a"
      run := do
        let _ ← expectDecodeStep "decode/f43a" (Slice.ofCell rawF43A) (.dictExt (.mutGet false false false .add)) 16
        pure ()
    }
    ,
    { name := "unit/decoder/decode/f43b"
      run := do
        let _ ← expectDecodeStep "decode/f43b" (Slice.ofCell rawF43B) (.dictExt (.mutGet false false true .add)) 16
        pure ()
    }
    ,
    { name := "unit/decoder/decode/f43c-aliased-int"
      run := do
        let _ ← expectDecodeStep "decode/f43c" (Slice.ofCell rawF43C) (.dictExt (.mutGet true false false .add)) 16
        pure ()
    }
    ,
    { name := "unit/decoder/decode/f43d-aliased-int-byref"
      run := do
        let _ ← expectDecodeStep "decode/f43d" (Slice.ofCell rawF43D) (.dictExt (.mutGet true false true .add)) 16
        pure ()
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
    { name := "unit/decoder/decode/truncated8"
      run := do
        expectDecodeInvOpcode "decode/truncated8" 0xf4
    }
    ,
    { name := "unit/asm/encode/not-supported"
      run := do
        expectAssembleInvOpcode "asm/not-supported" (mkInstr false)
    }
  ]
  oracle := #[
    -- [B1] runtime success: empty dict miss without by-ref.
    caseDictAddGet "oracle/ok/miss/notref/4" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4B) .null (intV 4))
    -- [B1] runtime success: empty dict miss with by-ref insertion.
    , caseDictAddGet "oracle/ok/miss/byref/4" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4B) .null (intV 4))
    -- [B1] runtime success: n=0 empty-key insert.
    , caseDictAddGet "oracle/ok/miss/n0/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice0) .null (intV 0))
    -- [B1] runtime success: n=0 empty-key insert with by-ref.
    , caseDictAddGet "oracle/ok/miss/n0/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice0) .null (intV 0))
    -- [B1] runtime success: n=1023 miss on empty root.
    , caseDictAddGet "oracle/ok/miss/n1023" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice1023) .null (intV 1023))
    -- [B1] runtime success: non-empty dictionary miss with not-ref insertion.
    , caseDictAddGet "oracle/ok/miss/non-empty/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4B) (.cell dictSlice4Miss) (intV 4))
    -- [B1] runtime success: non-empty dictionary miss with by-ref insertion.
    , caseDictAddGet "oracle/ok/miss/non-empty/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4B) (.cell dictRef4Miss) (intV 4))
    -- [B2] runtime success: by-ref false hit pushes old slice and 0.
    , caseDictAddGet "oracle/ok/hit/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV 4))
    -- [B2] runtime success: by-ref true hit with extractable old cell and 0.
    , caseDictAddGet "oracle/ok/hit/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4A) (.cell dictRef4Single) (intV 4))
    -- [B2] runtime success: n=0 hit path on empty-key entry without by-ref.
    , caseDictAddGet "oracle/ok/hit/n0/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice0) (.cell dictSliceN0) (intV 0))
    -- [B2] runtime success: n=0 hit path on empty-key entry with by-ref.
    , caseDictAddGet "oracle/ok/hit/n0/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice0) (.cell dictRefN0) (intV 0))
    -- [B3] runtime failure: key too short (not enough bits) for requested n.
    , caseDictAddGet "oracle/err/key-short/notref" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4Short) (.cell dictSlice4Single) (intV 4))
    -- [B3] runtime failure: key too short for requested n in by-ref mode.
    , caseDictAddGet "oracle/err/key-short/byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4Short) (.cell dictRef4Single) (intV 4))
    -- [B4] runtime failure: negative n.
    , caseDictAddGet "oracle/err/n-negative" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV (-1)))
    -- [B4] runtime failure: n greater than 1023.
    , caseDictAddGet "oracle/err/n-too-large" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV 1024))
    -- [B4] runtime failure: n is NaN.
    , caseDictAddGet "oracle/err/n-nan" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (.int .nan))
    -- [B4] runtime failure: dict root has wrong type.
    , caseDictAddGet "oracle/err/dict-type" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.tuple #[]) (intV 4))
    -- [B4] runtime failure: key has wrong type (int, not slice).
    , caseDictAddGet "oracle/err/key-type-int" false
      (mkDictCaseStack (normalNewValue false) (intV 7) (.cell dictSlice4Single) (intV 4))
    -- [B4] runtime failure: key has wrong type (null, not slice).
    , caseDictAddGet "oracle/err/key-type-null" false
      (mkDictCaseStack (normalNewValue false) (intV 0) (.cell dictSlice4Single) (intV 4))
    -- [B4] runtime failure: non-ref mode expects slice new value.
    , caseDictAddGet "oracle/err/newvalue-type/notref" false
      (mkDictCaseStack (badNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV 4))
    -- [B4] runtime failure: by-ref mode expects cell new value.
    , caseDictAddGet "oracle/err/newvalue-type/byref" true
      (mkDictCaseStack (badNewValue true) (.slice keySlice4A) (.cell dictRef4Single) (intV 4))
    -- [B5] runtime failure: old value is malformed for by-ref extraction (not a single-reference slice).
    , caseDictAddGet "oracle/err/ref-shape" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4C) (.cell dictSliceMalformedRefLike) (intV 4))
    -- [B5] runtime failure: malformed root in not-ref mode.
    , caseDictAddGet "oracle/err/malformed-root" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell malformedDictRoot) (intV 4))
    -- [B5] runtime failure: malformed root in by-ref mode.
    , caseDictAddGet "oracle/err/malformed-root-byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4A) (.cell malformedDictRoot) (intV 4))
    -- [B4] runtime underflow with empty stack.
    , caseDictAddGet "oracle/err/underflow/empty" false #[]
    -- [B4] runtime underflow with one item.
    , caseDictAddGet "oracle/err/underflow/one" false
      (#[intV 1])
    -- [B4] runtime underflow with two items.
    , caseDictAddGet "oracle/err/underflow/two" false
      (mkDictCaseStack (normalNewValue false) (intV 2) .null (intV 3))
    -- [B4] runtime underflow with three items.
    , caseDictAddGet "oracle/err/underflow/three" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4A) (.cell dictSlice4Single) (intV 4) |>.take 3)
    -- [B8] exact gas branch with miss and not-ref mode.
    , caseDictAddGet "oracle/gas/exact" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4B) .null (intV 4))
      (dictAddGetGasProgram dictAddGetExactGas false)
      (oracleGasLimitsExact dictAddGetExactGas)
    -- [B8] exact minus one should fail due gas budget.
    , caseDictAddGet "oracle/gas/exact-minus-one" false
      (mkDictCaseStack (normalNewValue false) (.slice keySlice4B) .null (intV 4))
      (dictAddGetGasProgram dictAddGetExactGasMinusOne false)
      (oracleGasLimitsExactMinusOne dictAddGetExactGasMinusOne)
    -- [B8] exact gas branch with by-ref mode.
    , caseDictAddGet "oracle/gas/exact-byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4B) .null (intV 4))
      (dictAddGetGasProgram dictAddGetExactGasByRef true)
      (oracleGasLimitsExact dictAddGetExactGasByRef)
    -- [B8] exact minus one should fail with by-ref mode.
    , caseDictAddGet "oracle/gas/exact-minus-one-byref" true
      (mkDictCaseStack (normalNewValue true) (.slice keySlice4B) .null (intV 4))
      (dictAddGetGasProgram dictAddGetExactGasMinusOneByRef true)
      (oracleGasLimitsExactMinusOne dictAddGetExactGasMinusOneByRef)
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genDictAddGetFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTADDGET
