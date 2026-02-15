import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTISETB

/-
INSTRUCTION: DICTISETB

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1: Runtime success branch (empty root)]:
   - `VM.checkUnderflow 4` succeeds and `popNatUpTo 1023` yields a valid width.
   - On `dictCell = .null`, `.dictSetB true false .set` with signed key and builder value builds a
     new one-node dictionary.
   - `dictSetBuilderWithCells` returns `ok = true` and pushes the new root.
2. [B2: Runtime success branch (existing key)]:
   - Signed integer keys hit existing entries and still push a new root (old value replaced),
     with `.set` returning `ok = true`.
3. [B3: Runtime prefix/branch update]:
   - Signed key insertion that diverges from an existing edge creates a fork/prefix node
     and rebuilds the path with `created > 0`.
   - On success, `created` contributes variable gas `created * cellCreateGasPrice`.
4. [B4: Key-size/range validation]:
   - `popNatUpTo 1023` rejects non-numeric/NaN/negative/too-large bit-size (`.rangeChk`).
   - `dictKeyBits?` returns `none` for out-of-range signed ints and for `n = 0` with non-zero key.
5. [B5: Type/stack validation]:
   - Stack underflow before any pop yields `.stkUnd`.
   - Dict must be maybe-cell; key must be int; top value must be builder.
   - Violations are reported via `.typeChk` or `.typeChk`-style argument order checks.
6. [B6: Dictionary structural errors]:
   - Malformed roots can produce `.dictErr` from `dictSetBuilderWithCells` with loaded-cell tracking.
7. [B7: Assembler encoding]:
   - `.dictSetB true false .set` encodes to `0xf442`.
   - `.dictSetB true true .set` encodes to `0xf443`.
   - `.dictSetB true false .replace` is rejected (`.invOpcode`); the replace-family uses `.dictReplaceB`.
   - `.dictSetB true false .add` encodes to `0xf452` (DICTIADDB).
8. [B8: Decoder behavior]:
   - Decoder maps `0xf441..0xf443` to `.dictSetB` set variants.
   - Adjacent opcodes `0xf440` and `0xf444` fail with `.invOpcode`.
9. [B9: Gas accounting]:
   - Base cost uses `computeExactGasBudget` and should pass/fail at exact/minus-one.
   - Success with `created > 0` must additionally consume `cellCreateGasPrice * created`.

TOTAL BRANCHES: 9
-/

private def dictISetBId : InstrId := { name := "DICTISETB" }
private def dictISetBInstr : Instr := .dictSetB true false .set

private def dictSETBCode : Cell := Cell.mkOrdinary (natToBits 0xf441 16) #[]
private def dictISETBCode : Cell := Cell.mkOrdinary (natToBits 0xf442 16) #[]
private def dictUSETBCode : Cell := Cell.mkOrdinary (natToBits 0xf443 16) #[]
private def dictIADDBCode : Cell := Cell.mkOrdinary (natToBits 0xf452 16) #[]
private def dictISETBLowerInvalid : Cell := Cell.mkOrdinary (natToBits 0xf440 16) #[]
private def dictISETBUpperInvalid : Cell := Cell.mkOrdinary (natToBits 0xf444 16) #[]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b01010 5) #[]

private def builderA : Builder := Builder.empty.storeBits (natToBits 0xA1 8)
private def builderB : Builder := Builder.empty.storeBits (natToBits 0xB2 8)
private def builderC : Builder := Builder.empty.storeBits (natToBits 0xC3 8)
private def builderD : Builder := Builder.empty.storeBits (natToBits 0xD4 8)
private def builderE : Builder := Builder.empty.storeBits (natToBits 0xE5 8)

private def mkDictFromIntPairs! (label : String) (n : Nat) (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some bits => bits
        | none => panic! s!"DICTISETB: {label}: invalid key k={k}, n={n}"
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some c, _ok, _created, _loaded) =>
          root := some c
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"DICTISETB: {label}: expected dictionary root, got none"
      | .error e =>
          panic! s!"DICTISETB: {label}: dict set failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTISETB: {label}: empty dictionary"

private def mkSetFromInt!
    (label : String) (root : Option Cell) (n : Nat) (key : Int) (value : Builder := builderA) : Cell :=
  let keyBits :=
    match dictKeyBits? key n false with
    | some bits => bits
    | none => panic! s!"DICTISETB: {label}: invalid key k={key}, n={n}"
  match dictSetBuilderWithCells root keyBits value .set with
  | .ok (some c, _ok, _created, _loaded) => c
  | .ok (none, _ok, _created, _loaded) => panic! s!"DICTISETB: {label}: expected dictionary root, got none"
  | .error e => panic! s!"DICTISETB: {label}: dict set failed ({reprStr e})"

private def dictSigned0 : Cell :=
  mkDictFromIntPairs! "dict/signed/0" 0 #[(0, builderA)]

private def dictSigned1 : Cell :=
  mkDictFromIntPairs! "dict/signed/1" 1 #[
    (-1, builderA),
    (0, builderB)
  ]

private def dictSigned4 : Cell :=
  mkDictFromIntPairs! "dict/signed/4" 4 #[
    (-8, builderA),
    (-1, builderB),
    (0, builderC),
    (7, builderD)
  ]

private def dictSigned8 : Cell :=
  mkDictFromIntPairs! "dict/signed/8" 8 #[
    (-128, builderA),
    (-1, builderB),
    (0, builderC),
    (42, builderD),
    (127, builderE)
  ]

private def mkISETBStack
    (n : Int)
    (key : Int)
    (dict : Value := .null)
    (value : Builder := builderA) : Array Value :=
  #[.builder value, .int (.num key), dict, .int (.num n)]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictISetBId
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
    instr := dictISetBId
    initStack := stack
    codeCell? := some code
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (gas : Int)
    (gasLimits : OracleGasLimits) : OracleCase :=
  mkCase name stack
    #[.pushInt (.num gas), .tonEnvOp .setGasLimit, dictISetBInstr]
    gasLimits

private def runDICTISETBDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSetB dictISetBInstr stack

private def expectAssembleErr (label : String) (expected : Excno) (i : Instr) : IO Unit := do
  match assembleCp0 [i] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure {expected}, got success")

private def expectDecode16 (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected no trailing bits/refs")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected valid decode, got {e}")

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr} with {bits} bits")

private def dictISETBExactGas : Int := computeExactGasBudget dictISetBInstr
private def dictISETBExactGasMinusOne : Int := computeExactGasBudgetMinusOne dictISetBInstr
private def dictISETBMissGas : Int := dictISETBExactGas + cellCreateGasPrice
private def dictISETBMissGasMinusOne : Int :=
  if dictISETBMissGas > 0 then dictISETBMissGas - 1 else 0

private def pickNForFuzz (rng0 : StdGen) : Nat × StdGen :=
  let (raw, rng1) := randNat rng0 0 10
  let n : Nat :=
    match raw with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | 4 => 8
    | 5 => 16
    | 6 => 32
    | 7 => 64
    | 8 => 128
    | 9 => 256
    | _ => 32
  (n, rng1)

private def signedOutOfRangeHigh (n : Nat) : Int :=
  if n = 0 then
    1
  else
    Int.ofNat (1 <<< (n - 1))

private def signedOutOfRangeLow (n : Nat) : Int :=
  if n = 0 then
    1
  else
    - (Int.ofNat (1 <<< (n - 1)) + 1)

private def genDICTISETBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  let (n, rng2) := pickNForFuzz rng1
  if shape < 4 then
    (mkCase (s!"fuzz/underflow/{shape + 1}") (match shape with
      | 0 => #[]
      | 1 => #[intV 1]
      | 2 => #[intV 1, .cell Cell.empty]
      | _ => #[.builder builderA, intV 1, .null]), rng2)
  else if shape < 6 then
    let c :=
      if shape = 4 then
        mkCase "fuzz/range/n-negative" (mkISETBStack (-1) 1 .null)
      else
        mkCase "fuzz/range/n-too-large" (mkISETBStack 1024 1 .null)
    (c, rng2)
  else if shape < 8 then
    let key := if shape = 6 then signedOutOfRangeHigh 4 else signedOutOfRangeLow 4
    (mkCase (if shape = 6 then "fuzz/range/signed-key-high" else "fuzz/range/signed-key-low")
      (mkISETBStack 4 key .null), rng2)
  else if shape < 10 then
    let c :=
      if shape = 8 then mkCase "fuzz/range/n0-nonzero" (mkISETBStack 0 1)
      else mkCase "fuzz/range/key-nan" (#[.builder builderA, .int .nan, .null, intV 4])
    (c, rng2)
  else if shape < 14 then
    let c :=
      if shape = 10 then
        mkCase "fuzz/ok/miss/null" (mkISETBStack 4 2 .null)
      else if shape = 11 then
        mkCase "fuzz/ok/hit/signed4" (mkISETBStack 4 (-8) (.cell dictSigned4))
      else if shape = 12 then
        mkCase "fuzz/ok/miss/non-empty-prefix" (mkISETBStack 4 2 (.cell dictSigned4))
      else
        mkCase "fuzz/ok/hit/signed1" (mkISETBStack 1 (-1) (.cell dictSigned1))
    (c, rng2)
  else if shape < 20 then
    let c :=
      if shape = 14 then
        mkCase "fuzz/err/dict-type" (mkISETBStack 4 1 (.int (.num 7)))
      else if shape = 15 then
        mkCase "fuzz/err/key-not-int" (#[.builder builderA, .slice (mkSliceFromBits (natToBits 3 4)), .null, intV 4])
      else if shape = 16 then
        mkCase "fuzz/err/value-not-builder" (#[.slice (mkSliceFromBits (natToBits 3 4)), .int (.num 3), .null, intV 4])
      else if shape = 17 then
        mkCase "fuzz/err/key-nan" (#[.builder builderA, .int .nan, .null, intV 4])
      else
        mkCase "fuzz/err/malformed-root" (mkISETBStack 4 1 (.cell malformedDict))
    (c, rng2)
  else if shape < 24 then
    if shape = 20 then
      (mkGasCase "fuzz/gas/exact-hit" (mkISETBStack 4 (-8) (.cell dictSigned4))
        dictISETBExactGas (oracleGasLimitsExact dictISETBExactGas), rng2)
    else if shape = 21 then
      (mkGasCase "fuzz/gas/exact-hit-minus-one" (mkISETBStack 4 (-8) (.cell dictSigned4))
        dictISETBExactGasMinusOne (oracleGasLimitsExactMinusOne dictISETBExactGasMinusOne), rng2)
    else if shape = 22 then
      (mkGasCase "fuzz/gas/miss" (mkISETBStack 4 2 .null)
        dictISETBMissGas (oracleGasLimitsExact dictISETBMissGas), rng2)
    else
      (mkGasCase "fuzz/gas/miss-minus-one" (mkISETBStack 4 2 .null)
        dictISETBMissGasMinusOne (oracleGasLimitsExactMinusOne dictISETBMissGasMinusOne), rng2)
  else
    let (sel, rng3) := randNat rng2 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/random/prefix-hit" (mkISETBStack 8 127 (.cell dictSigned8))
      else if sel = 1 then
        mkCase "fuzz/random/prefix-miss" (mkISETBStack 8 55 (.cell dictSigned8))
      else if sel = 2 then
        mkCase "fuzz/random/type-dict" (mkISETBStack 4 1 (.tuple #[]))
      else if sel = 3 then
        mkCase "fuzz/random/nan-key" (#[(.builder builderA), .int .nan, .null, intV 4])
      else if sel = 4 then
        mkCodeCase "fuzz/random/code-0xf442" (mkISETBStack 4 1 (.null)) dictISETBCode
      else
        mkCase (s!"fuzz/random/malformed-{n}") (mkISETBStack 4 1 (.cell malformedDict))
    (c, rng3)

def suite : InstrSuite where
  id := dictISetBId
  unit := #[
    { name := "unit/asm/encode/signed"
      run := do
        match assembleCp0 [dictISetBInstr] with
        | .ok c =>
            if c == dictISETBCode then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/signed: unexpected opcode encoding")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/signed: expected success, got {e}")
    },
    { name := "unit/asm/invalid-non-set-and-unsigned"
      run := do
        expectAssembleErr "unit/asm/invalid-non-set" .invOpcode (.dictSetB true false .replace)
        match assembleCp0 [.dictSetB true false .add] with
        | .ok c =>
            if c == dictIADDBCode then
              pure ()
            else
              throw (IO.userError "unit/asm/add: unexpected opcode encoding")
        | .error e =>
            throw (IO.userError s!"unit/asm/add: expected success, got {e}")
        match assembleCp0 [.dictSetB true true .set] with
        | .ok c =>
            if c == dictUSETBCode then
              pure ()
            else
              throw (IO.userError "unit/asm/unsigned-set: unexpected opcode encoding")
        | .error e =>
            throw (IO.userError s!"unit/asm/unsigned-set: expected success, got {e}")
    },
    { name := "unit/decode/valid-and-neighbors"
      run := do
        expectDecode16 "unit/decode/f442" dictISETBCode (dictISetBInstr)
        expectDecode16 "unit/decode/f441" dictSETBCode (.dictSetB false false .set)
        expectDecode16 "unit/decode/f443" dictUSETBCode (.dictSetB true true .set)
        expectDecodeInvOpcode "unit/decode/invalid-lower" dictISETBLowerInvalid
        expectDecodeInvOpcode "unit/decode/invalid-upper" dictISETBUpperInvalid
    },
    { name := "unit/exec/ok-empty-null"
      run := do
        let expected : Cell :=
          mkSetFromInt! "unit/exec/ok-empty-null" none 1 0 builderA
        expectOkStack "unit/exec/ok-empty-null"
          (runDICTISETBDirect (mkISETBStack 1 0 .null))
          #[.cell expected]
    },
    { name := "unit/exec/ok-replace-existing"
      run := do
        let expected : Cell :=
          mkSetFromInt! "unit/exec/ok-replace-existing" (some dictSigned4) 4 0 builderB
        expectOkStack "unit/exec/ok-replace-existing"
          (runDICTISETBDirect (mkISETBStack 4 0 (.cell dictSigned4) builderB))
          #[.cell expected]
    },
    { name := "unit/exec/err/range-and-types"
      run := do
        expectErr "unit/exec/err/range/n-negative" (runDICTISETBDirect (mkISETBStack (-1) 1 .null)) .rangeChk
        expectErr "unit/exec/err/range/n-too-large" (runDICTISETBDirect (mkISETBStack 1024 1 .null)) .rangeChk
        expectErr "unit/exec/err/range/n-zero-key" (runDICTISETBDirect (mkISETBStack 0 1 .null)) .rangeChk
        expectErr "unit/exec/err/range/key-high" (runDICTISETBDirect (mkISETBStack 4 8 .null)) .rangeChk
        expectErr "unit/exec/err/range/key-low" (runDICTISETBDirect (mkISETBStack 4 (-9) .null)) .rangeChk
        expectErr "unit/exec/err/type-dict" (runDICTISETBDirect (mkISETBStack 4 1 (.int (.num 7))) ) .typeChk
        expectErr "unit/exec/err/type-key" (runDICTISETBDirect (#[.builder builderA, .slice (mkSliceFromBits (natToBits 1 4)), .null, intV 4])) .typeChk
        expectErr "unit/exec/err/type-value" (runDICTISETBDirect (#[.int (.num 7), .int (.num 3), .null, intV 4])) .typeChk
        expectErr "unit/exec/err/key-nan" (runDICTISETBDirect (#[.builder builderA, .int .nan, .null, intV 4])) .rangeChk
        expectErr "unit/exec/err/dict-malformed" (runDICTISETBDirect (mkISETBStack 4 1 (.cell malformedDict))) .dictErr
    },
    { name := "unit/exec/err/underflow"
      run := do
        expectErr "unit/exec/err/underflow-empty" (runDICTISETBDirect #[]) .stkUnd
        expectErr "unit/exec/underflow-one" (runDICTISETBDirect #[.builder builderA]) .stkUnd
        expectErr "unit/exec/underflow-two" (runDICTISETBDirect #[.builder builderA, intV 1]) .stkUnd
        expectErr "unit/exec/underflow-three" (runDICTISETBDirect #[.builder builderA, intV 4, .cell dictSigned4]) .stkUnd
    }
  ]
  oracle := #[
    -- [B1] empty-dict miss case (create-new-root path).
    mkCase "ok/miss/null/n0" (mkISETBStack 0 0 .null),
    -- [B1] empty-dict miss with one-bit key.
    mkCase "ok/miss/null/n1" (mkISETBStack 1 1 .null),
    -- [B1] empty-dict miss with 4-bit key.
    mkCase "ok/miss/null/n4" (mkISETBStack 4 3 .null),
    -- [B1] empty-dict miss with 8-bit key.
    mkCase "ok/miss/null/n8" (mkISETBStack 8 13 .null),
    -- [B2] existing signed-key update at minimum in-width boundary.
    mkCase "ok/hit/signed/n4-min" (mkISETBStack 4 (-8) (.cell dictSigned4)),
    -- [B2] existing signed-key update at maximum in-width boundary.
    mkCase "ok/hit/signed/n4-max" (mkISETBStack 4 7 (.cell dictSigned4)),
    -- [B2] existing signed-key replacement on single-bit root.
    mkCase "ok/hit/signed/n1" (mkISETBStack 1 0 (.cell dictSigned1)),
    -- [B2] existing signed-key replacement with larger width.
    mkCase "ok/hit/signed/n8-mid" (mkISETBStack 8 42 (.cell dictSigned8)),
    -- [B3] non-empty miss causing prefix/fork updates.
    mkCase "ok/miss/prefix-n4" (mkISETBStack 4 2 (.cell dictSigned4)),
    -- [B3] non-empty miss at larger width.
    mkCase "ok/miss/prefix-n8" (mkISETBStack 8 55 (.cell dictSigned8)),
    -- [B4] zero-width signed key must be zero; non-zero is invalid.
    mkCase "err/range/n0-nonzero" (mkISETBStack 0 1 .null),
    -- [B4] signed key overflow for n=4.
    mkCase "err/range/signed-high" (mkISETBStack 4 8 .null),
    -- [B4] signed key underflow for n=4.
    mkCase "err/range/signed-low" (mkISETBStack 4 (-9) .null),
    -- [B4] `n` negative.
    mkCase "err/range/n-negative" (mkISETBStack (-1) 0 .null),
    -- [B4] `n` too large.
    mkCase "err/range/n-too-large" (mkISETBStack 1024 0 .null),
    -- [B4] `n` NaN path.
    mkCase "err/range/n-nan" (#[.builder builderA, .int (.num 1), .null, .int .nan]),
    -- [B4] key NaN path.
    mkCase "err/range/key-nan" (#[.builder builderA, .int .nan, .null, intV 4]),
    -- [B5] underflow: empty stack.
    mkCase "err/underflow/empty" #[],
    -- [B5] underflow: one item.
    mkCase "err/underflow/one" #[.builder builderA],
    -- [B5] underflow: two items.
    mkCase "err/underflow/two" #[.builder builderA, .cell Cell.empty],
    -- [B5] underflow: three items.
    mkCase "err/underflow/three" #[.builder builderA, .int (.num 4), .cell dictSigned4],
    -- [B5] dictionary type mismatch.
    mkCase "err/type/dict" (mkISETBStack 4 3 (.int (.num 7))),
    -- [B5] key type mismatch.
    mkCase "err/type/key-not-int" (#[.builder builderA, .slice (mkSliceFromBits (natToBits 1 4)), .cell dictSigned4, intV 4]),
    -- [B5] value type mismatch.
    mkCase "err/type/value-not-builder" (#[.int (.num 7), .int (.num 3), .null, intV 4]),
    -- [B5] malformed dictionary root.
    mkCase "err/dict/malformed" (mkISETBStack 4 1 (.cell malformedDict)),
    -- [B6] code-decoding for adjacent opcode families.
    mkCodeCase "code/decode/0xf441" (mkISETBStack 4 1 .null) dictSETBCode,
    mkCodeCase "code/decode/0xf442" (mkISETBStack 4 1 .null) dictISETBCode,
    mkCodeCase "code/decode/0xf443" (mkISETBStack 4 1 .null) dictUSETBCode,
    mkCodeCase "code/decode/invalid-lower" #[] dictISETBLowerInvalid,
    mkCodeCase "code/decode/invalid-upper" #[] dictISETBUpperInvalid,
    -- [B7] exact gas on deterministic hit.
    mkGasCase "gas/exact/hit" (mkISETBStack 4 0 (.cell dictSigned4))
      dictISETBExactGas (oracleGasLimitsExact dictISETBExactGas),
    -- [B7] exact-minus-one failure on deterministic hit.
    mkGasCase "gas/exact/hit-minus-one" (mkISETBStack 4 0 (.cell dictSigned4))
      dictISETBExactGasMinusOne (oracleGasLimitsExactMinusOne dictISETBExactGasMinusOne),
    -- [B7] exact gas on creation path.
    mkGasCase "gas/exact/miss" (mkISETBStack 4 2 .null)
      dictISETBMissGas (oracleGasLimitsExact dictISETBMissGas),
    -- [B7] exact-minus-one failure on creation path.
    mkGasCase "gas/exact/miss-minus-one" (mkISETBStack 4 2 .null)
      dictISETBMissGasMinusOne (oracleGasLimitsExactMinusOne dictISETBMissGasMinusOne),
    -- [B9] extra fuzzer-shape seeds.
    mkCase "fuzz-shape/extra-hit" (mkISETBStack 8 127 (.cell dictSigned8)),
    mkCase "fuzz-shape/extra-miss" (mkISETBStack 8 85 (.cell dictSigned8))
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictISetBId
      count := 500
      gen := genDICTISETBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTISETB
