import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUSETB

/-
INSTRUCTION: DICTUSETB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Runtime semantics] Dispatch and instruction selection.
   - `execInstrDictDictSetB` handles only `.dictSetB`.
   - Non-matching instructions must fall through to `next`.
2. [Runtime semantics, stack shape] Operand stack layout and arity.
   - `checkUnderflow 4` requires `new_value`, `key`, `dict`, `n`.
   - Stacks with fewer than 4 items fail with `.stkUnd`.
3. [Runtime semantics] `n` validation via `popNatUpTo 1023`.
   - Valid `n` includes boundary values and allows `0`.
   - `n = 1023` is valid.
   - `n < 0`, `n = .nan`, and `n > 1023` fail with `.rangeChk`.
4. [Runtime semantics/key path] Key source branch: slice key vs integer key.
   - Non-int key instructions route through `popSlice`/`haveBits`.
   - Int-key instructions call `dictKeyBits?` with unsigned flag and fail with `.rangeChk` on bad range.
   - `n`-bit slice-key extraction with insufficient bits fails with `.cellUnd`.
5. [Runtime semantics/value path] Builder value path.
   - `popBuilder` requires a builder value.
   - Non-builder value fails with `.typeChk`.
6. [Runtime semantics] Dictionary-set behavior (`.set` mode).
   - Valid root (`.null` or `.cell`) and valid inputs always produce a dictionary root on stack.
   - Existing key replacement and new-key insertion are both successful paths.
   - For set mode, any `ok = false` branch is fatal and should not occur on valid inputs.
7. [Runtime semantics] Dictionary mutation errors.
   - Malformed dictionary roots may trigger `.dictErr`/`.cellUnd`.
   - `popMaybeCell` accepts only `.null` and `.cell`; any other type is `.typeChk`.
8. [Assembler encoding] Supported opcodes and rejected modes/ranges.
   - Valid encodings are only set-mode:
     - `0xf441` -> `.dictSetB false false .set`
     - `0xf442` -> `.dictSetB true false .set`
     - `0xf443` -> `.dictSetB true true .set`
   - `.dictSetB` with `mode ≠ .set` must be `.invOpcode`.
   - `.dictSetB` with `intKey = false` and `unsigned = true` must be `.invOpcode`.
9. [Decoder behavior] Opcode decoding.
   - `0xf441..0xf443` decode to the three valid forms above.
   - `0xf440` and `0xf444` must be `.invOpcode`.
   - Truncated 8/15-bit input cannot decode this fixed 16-bit form.
10. [Gas accounting] Base gas + created-cell penalty.
   - Base cost is `computeExactGasBudget` of `.dictSetB false false .set`.
   - Dynamic penalty is `cellCreateGasPrice * created`.
   - Exact and exact-minus-one branches are expected for miss and hit paths using precomputed `created`.
11. [Fuzzer coverage] Branchs not directly mirrored by a dedicated oracle test must be reached by generation.
   - generator must sample both key-family variants, error variants, and boundary values.

TOTAL BRANCHES: 11

Each oracle test below is tagged with the branch(es) it covers.
-/

private def dictSetBId : InstrId :=
  { name := "DICTUSETB" }

private def instrSliceKey : Instr := .dictSetB false false .set
private def instrSigned : Instr := .dictSetB true false .set
private def instrUnsigned : Instr := .dictSetB true true .set

private def invalidModeReplace : Instr := .dictSetB false false .replace
private def invalidModeAdd : Instr := .dictSetB true true .add
private def invalidUnsignedSlice : Instr := .dictSetB false true .set

private def rawF441 : Cell := Cell.mkOrdinary (natToBits 0xf441 16) #[]
private def rawF442 : Cell := Cell.mkOrdinary (natToBits 0xf442 16) #[]
private def rawF443 : Cell := Cell.mkOrdinary (natToBits 0xf443 16) #[]
private def rawF440 : Cell := Cell.mkOrdinary (natToBits 0xf440 16) #[]
private def rawF444 : Cell := Cell.mkOrdinary (natToBits 0xf444 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]
private def rawF4trunc : Cell := Cell.mkOrdinary (natToBits (0xf441 >>> 1) 15) #[]

private def valueA : Builder := Builder.empty.storeBits (natToBits 0xA1 8)
private def valueB : Builder := Builder.empty.storeBits (natToBits 0xB2 8)
private def valueC : Builder := Builder.empty.storeBits (natToBits 0xC3 8)
private def valueD : Builder := Builder.empty.storeBits (natToBits 0xD4 8)

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def key0 : BitString := #[]
private def key1 : BitString := natToBits 0 1
private def key2 : BitString := natToBits 2 4
private def key3 : BitString := natToBits 3 4
private def key4 : BitString := natToBits 4 4
private def key7 : BitString := natToBits 7 4
private def key8 : BitString := natToBits 8 4
private def keyMax4 : BitString := natToBits 15 4
private def key8a : BitString := natToBits 0x7A 8
private def key8b : BitString := natToBits 0xD7 8
private def key1023 : BitString := Array.replicate 1023 true

private def mkSlice4 : Slice := mkSliceFromBits key4
private def mkSlice2 : Slice := mkSliceFromBits key2
private def mkSlice3 : Slice := mkSliceFromBits key3
private def mkSlice8a : Slice := mkSliceFromBits key8a
private def mkSlice8b : Slice := mkSliceFromBits key8b
private def mkSlice0 : Slice := mkSliceFromBits key0
private def mkSlice1023 : Slice := mkSliceFromBits key1023

private def mkDictSetBRootSlice! (label : String) (pairs : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetBuilderWithCells root k v .set with
      | .ok (some root', _ok, _created, _loaded) => root := some root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: expected dictionary root, got none"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty input produced no dictionary root"

private def dictKeyBits! (label : String) (n : Nat) (unsigned : Bool) (k : Int) : BitString :=
  match dictKeyBits? k n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: invalid dict key {k} for n={n}, unsigned={unsigned}"

private def mkDictSetBRootInt! (label : String) (n : Nat) (unsigned : Bool) (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      let bits := dictKeyBits! label n unsigned k
      match dictSetBuilderWithCells root bits v .set with
      | .ok (some root', _ok, _created, _loaded) => root := some root'
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: expected dictionary root, got none"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty input produced no dictionary root"

private def dictSlice4Single : Cell :=
  mkDictSetBRootSlice! "dict/slice/4/single" #[(key3, valueA)]
private def dictSlice4Two : Cell :=
  mkDictSetBRootSlice! "dict/slice/4/two" #[(key3, valueA), (key4, valueB)]
private def dictSlice4Merge : Cell :=
  mkDictSetBRootSlice! "dict/slice/4/merge" #[(key1, valueA), (key2, valueB), (key7, valueC), (key8, valueD)]

private def dictSigned4 : Cell :=
  mkDictSetBRootInt! "dict/int/signed4" 4 false #[(0, valueA), (1, valueB), (-8, valueC), (7, valueD)]
private def dictUnsigned8 : Cell :=
  mkDictSetBRootInt! "dict/int/unsigned8" 8 true #[(0, valueA), (7, valueB), (128, valueC), (255, valueD)]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSliceKey])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictSetBId
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
    instr := dictSetBId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (instr : Instr)
    (gas : Int)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (#[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr]) gasLimits fuel

private def mkSliceStack
    (dict : Value)
    (key : BitString)
    (n : Int)
    (value : Builder := valueA) : Array Value :=
  #[.builder value, .slice (mkSliceFromBits key), dict, intV n]

private def mkIntStack
    (dict : Value)
    (key : Int)
    (n : Int)
    (value : Builder := valueA) : Array Value :=
  #[.builder value, .int (.num key), dict, intV n]

private def expectDecodeOk (label : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected end-of-stream decode")

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr} ({bits} bits)")

private def expectAssembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembly failure")
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def runDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSetB instr stack

private def createdFor (root : Option Cell) (key : BitString) : Nat :=
  match dictSetBuilderWithCells root key valueA .set with
  | .ok (_newRoot, _ok, created, _loaded) => created
  | .error e =>
      panic! s!"DICTUSETB created count precompute failed: {reprStr e}"

private def baseGas : Int := computeExactGasBudget instrSliceKey

private def gasMissSlice : Int :=
  baseGas + Int.ofNat (createdFor none key4) * cellCreateGasPrice
private def gasHitSlice : Int :=
  baseGas + Int.ofNat (createdFor (some dictSlice4Single) key3) * cellCreateGasPrice
private def gasMissSliceN0 : Int :=
  baseGas + Int.ofNat (createdFor none key0) * cellCreateGasPrice
private def gasMissSliceN1023 : Int :=
  baseGas + Int.ofNat (createdFor none key1023) * cellCreateGasPrice

private def gasMissSigned4 : Int :=
  baseGas + Int.ofNat (createdFor (some dictSigned4) (dictKeyBits! "signed4/3" 4 false 3)) * cellCreateGasPrice
private def gasMissUnsigned8 : Int :=
  baseGas + Int.ofNat (createdFor (some dictUnsigned8) (dictKeyBits! "unsigned8/128" 8 true 128)) * cellCreateGasPrice
private def gasMissSigned4MinusOne : Int :=
  if gasMissSigned4 > 0 then gasMissSigned4 - 1 else 0
private def gasMissUnsigned8MinusOne : Int :=
  if gasMissUnsigned8 > 0 then gasMissUnsigned8 - 1 else 0
private def gasMissSliceMinusOne : Int :=
  if gasMissSlice > 0 then gasMissSlice - 1 else 0
private def gasHitSliceMinusOne : Int :=
  if gasHitSlice > 0 then gasHitSlice - 1 else 0
private def gasMissSliceN0MinusOne : Int :=
  if gasMissSliceN0 > 0 then gasMissSliceN0 - 1 else 0
private def gasMissSliceN1023MinusOne : Int :=
  if gasMissSliceN1023 > 0 then gasMissSliceN1023 - 1 else 0

private def genSliceDictKey (rng0 : StdGen) : Nat × StdGen :=
  let (choice, rng1) := randNat rng0 0 4
  let k : Nat :=
    match choice with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 4
    | _ => 1023
  (k, rng1)

private def genDICTUSETBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  let (k4, rng3) := genSliceDictKey rng2
  let (case0, rng4) :=
    match shape with
    | 0 =>
        (mkCase "fuzz/slice/miss/null/4" (mkSliceStack .null key4 4), rng3)
    | 1 =>
        (mkCase "fuzz/slice/miss/null/0" (mkSliceStack .null key0 0), rng3)
    | 2 =>
        (mkCase "fuzz/slice/miss/null/1023" (mkSliceStack .null key1023 1023), rng3)
    | 3 =>
        (mkCase "fuzz/slice/miss/non-empty/4" (mkSliceStack (.cell dictSlice4Merge) key8 4), rng3)
    | 4 =>
        (mkCase "fuzz/slice/hit/4" (mkSliceStack (.cell dictSlice4Single) key3 4), rng3)
    | 5 =>
        (mkCase "fuzz/slice/hit/0" (mkSliceStack (.cell dictSlice4Single) key0 0), rng3)
    | 6 =>
        (mkCase "fuzz/int/signed/hit/4" (mkIntStack (.cell dictSigned4) (-8) 4), rng3)
    | 7 =>
        (mkCase "fuzz/int/signed/miss/4" (mkIntStack (.cell dictSigned4) 6 4), rng3)
    | 8 =>
        (mkCase "fuzz/int/unsigned/hit/8" (mkIntStack (.cell dictUnsigned8) 128 8), rng3)
    | 9 =>
        (mkCase "fuzz/int/unsigned/miss/8" (mkIntStack (.cell dictUnsigned8) 7 8), rng3)
    | 10 =>
        (mkCase "fuzz/key-too-short/4" (mkSliceStack (.cell dictSlice4Two) key8 4), rng3)
    | 11 =>
        (mkCase "fuzz/key-too-short/8" (mkSliceStack (.cell dictSlice4Two) key8 8), rng3)
    | 12 =>
        (mkCase "fuzz/n-negative" (mkSliceStack (.cell dictSlice4Two) key3 (-1)), rng3)
    | 13 =>
        (mkCase "fuzz/n-too-large" (mkSliceStack (.cell dictSlice4Two) key3 1024), rng3)
    | 14 =>
        (mkCase "fuzz/n-nan" (#[.builder valueA, .slice mkSlice4, .cell dictSlice4Two, .int .nan]), rng3)
    | 15 =>
        (mkCase "fuzz/type/key-not-slice" (#[.builder valueA, .int (.num 3), .cell dictSlice4Two, intV 4]), rng3)
    | 16 =>
        (mkCase "fuzz/type/key-not-int" (#[.builder valueB, .slice mkSlice4, .cell dictSigned4, intV 4]), rng3)
    | 17 =>
        (mkCase "fuzz/type/root-not-cell" (#[.builder valueA, .slice mkSlice4, .int (.num 0), intV 4]), rng3)
    | 18 =>
        (mkCase "fuzz/type/value-not-builder/slice" (#[.slice mkSlice3, .slice mkSlice3, .cell dictSlice4Two, intV 4]), rng3)
    | 19 =>
        (mkCase "fuzz/type/value-not-builder/int" (#[.slice mkSlice3, .int (.num 1), .cell dictUnsigned8, intV 8]), rng3)
    | 20 =>
        (mkCase "fuzz/malformed-root/slice" (mkSliceStack (.cell malformedDictRoot) key3 4), rng3)
    | 21 =>
        (mkCase "fuzz/underflow/empty" #[], rng3)
    | 22 =>
        (mkCase "fuzz/underflow/one" #[.builder valueA], rng3)
    | 23 =>
        (mkCase "fuzz/underflow/two" (#[.builder valueA, .slice mkSlice3]), rng3)
    | 24 =>
        (mkCase "fuzz/underflow/three" (#[.builder valueA, .slice mkSlice3, .cell dictSlice4Single]), rng3)
    | 25 =>
        (mkGasCase "fuzz/gas/miss-slice-exact" (mkSliceStack .null key3 4) instrSliceKey gasMissSlice (oracleGasLimitsExact gasMissSlice), rng3)
    | 26 =>
        (mkGasCase "fuzz/gas/miss-slice-exact-minus-one" (mkSliceStack .null key3 4) instrSliceKey gasMissSliceMinusOne (oracleGasLimitsExactMinusOne gasMissSliceMinusOne), rng3)
    | 27 =>
        (mkGasCase "fuzz/gas/hit-slice-exact" (mkSliceStack (.cell dictSlice4Single) key3 4) instrSliceKey gasHitSlice (oracleGasLimitsExact gasHitSlice), rng3)
    | 28 =>
        (mkGasCase "fuzz/gas/hit-slice-exact-minus-one" (mkSliceStack (.cell dictSlice4Single) key3 4) instrSliceKey gasHitSliceMinusOne (oracleGasLimitsExactMinusOne gasHitSliceMinusOne), rng3)
    | 29 =>
        (mkGasCase "fuzz/gas/miss-signed-exact" (mkIntStack (.cell dictSigned4) 3 4) instrSigned gasMissSigned4 (oracleGasLimitsExact gasMissSigned4), rng3)
    | 30 =>
        (mkGasCase "fuzz/gas/miss-signed-exact-minus-one" (mkIntStack (.cell dictSigned4) 3 4) instrSigned gasMissSigned4MinusOne (oracleGasLimitsExactMinusOne gasMissSigned4MinusOne), rng3)
    | 31 =>
        (mkGasCase "fuzz/gas/miss-unsigned-exact" (mkIntStack (.cell dictUnsigned8) 128 8) instrUnsigned gasMissUnsigned8 (oracleGasLimitsExact gasMissUnsigned8), rng3)
    | 32 =>
        (mkGasCase "fuzz/gas/miss-unsigned-exact-minus-one" (mkIntStack (.cell dictUnsigned8) 128 8) instrUnsigned gasMissUnsigned8MinusOne (oracleGasLimitsExactMinusOne gasMissUnsigned8MinusOne), rng3)
    | 33 =>
        (mkGasCase "fuzz/gas/slice-0-exact" (mkSliceStack .null key0 0) instrSliceKey gasMissSliceN0 (oracleGasLimitsExact gasMissSliceN0), rng3)
    | 34 =>
        (mkGasCase "fuzz/gas/slice-0-exact-minus-one" (mkSliceStack .null key0 0) instrSliceKey gasMissSliceN0MinusOne (oracleGasLimitsExactMinusOne gasMissSliceN0MinusOne), rng3)
    | 35 =>
        (mkGasCase "fuzz/gas/slice-1023-exact" (mkSliceStack .null key1023 1023) instrSliceKey gasMissSliceN1023 (oracleGasLimitsExact gasMissSliceN1023), rng3)
    | 36 =>
        (mkGasCase "fuzz/gas/slice-1023-exact-minus-one" (mkSliceStack .null key1023 1023) instrSliceKey gasMissSliceN1023MinusOne (oracleGasLimitsExactMinusOne gasMissSliceN1023MinusOne), rng3)
    | 37 =>
        (mkCodeCase "fuzz/decode/f441" #[] rawF441, rng3)
    | 38 =>
        (mkCodeCase "fuzz/decode/f443" #[] rawF443, rng3)
    | 39 =>
        (mkCodeCase "fuzz/decode/trunc8" #[] rawF4, rng3)
    | _ =>
        (mkGasCase s!"fuzz/n/{k4}" (mkSliceStack .null key0 4) instrSliceKey gasMissSliceN0 (oracleGasLimitsExact gasMissSliceN0), rng3)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

def suite : InstrSuite where
  id := dictSetBId
  unit := #[
    { name := "unit/decoder/decode/f441"
      run := do
        expectDecodeOk "decode/f441" rawF441 instrSliceKey
    },
    { name := "unit/decoder/decode/f442"
      run := do
        expectDecodeOk "decode/f442" rawF442 instrSigned
    },
    { name := "unit/decoder/decode/f443"
      run := do
        expectDecodeOk "decode/f443" rawF443 instrUnsigned
    },
    { name := "unit/decoder/decode/adjacent"
      run := do
        expectDecodeInvOpcode "decode/f440" rawF440
        expectDecodeInvOpcode "decode/f444" rawF444
        expectDecodeInvOpcode "decode/trunc8" rawF4
        expectDecodeInvOpcode "decode/trunc15" rawF4trunc
    },
    { name := "unit/asm/invalid-mode"
      run := do
        expectAssembleInvOpcode "asm/replace" invalidModeReplace
        expectAssembleInvOpcode "asm/add" invalidModeAdd
        expectAssembleInvOpcode "asm/unsigned-slice" invalidUnsignedSlice
    },
    { name := "unit/runtime/validation"
      run := do
        expectErr "unit/runtime/underflow" (runDirect instrSliceKey #[]) .stkUnd
        expectErr "unit/runtime/n-negative" (runDirect instrSliceKey (mkSliceStack (.cell dictSlice4Single) key3 (-1))) .rangeChk
        expectErr "unit/runtime/n-nan" (runDirect instrSliceKey (#[.builder valueA, .slice mkSlice3, .cell dictSlice4Single, .int .nan])) .rangeChk
        expectErr "unit/runtime/key-type" (runDirect instrSliceKey (#[.builder valueA, .int (.num 3), .cell dictSlice4Single, intV 4])) .typeChk
        expectErr "unit/runtime/value-type" (runDirect instrSliceKey (#[.int (.num 7), .slice mkSlice3, .cell dictSlice4Single, intV 4])) .typeChk
        expectErr "unit/runtime/dict-err" (runDirect instrSliceKey (mkSliceStack (.cell malformedDictRoot) key3 4)) .cellUnd
    }
  ]
  oracle := #[
    -- [B3,B4,B6] success path from null root and boundary n.
    mkCase "oracle/ok/slice/miss/null/4" (mkSliceStack .null key4 4),
    -- [B3,B4,B6] success path at n = 0.
    mkCase "oracle/ok/slice/miss/null/0" (mkSliceStack .null key0 0),
    -- [B3,B4,B6] success path at n = 1023.
    mkCase "oracle/ok/slice/miss/null/1023" (mkSliceStack .null key1023 1023),
    -- [B3,B4,B6] miss with preexisting non-empty root.
    mkCase "oracle/ok/slice/miss/non-empty" (mkSliceStack (.cell dictSlice4Single) key8 4),
    -- [B3,B4,B6] hit replacement in existing dictionary.
    mkCase "oracle/ok/slice/hit" (mkSliceStack (.cell dictSlice4Single) key3 4),
    -- [B3,B4,B6] hit replacement with n=0.
    mkCase "oracle/ok/slice/hit/n0" (mkSliceStack (.cell dictSlice4Single) key0 0),
    -- [B4,B6] short but sufficient slice to hit root.
    mkCase "oracle/ok/slice/hit/merge" (mkSliceStack (.cell dictSlice4Merge) key2 4),
    -- [B5,B6] signed int hit.
    mkCase "oracle/ok/int/signed/hit/4" (mkIntStack (.cell dictSigned4) (-8) 4) #[instrSigned],
    -- [B5,B6] signed int miss.
    mkCase "oracle/ok/int/signed/miss/4" (mkIntStack (.cell dictSigned4) 3 4) #[instrSigned],
    -- [B5,B6] unsigned int hit.
    mkCase "oracle/ok/int/unsigned/hit/8" (mkIntStack (.cell dictUnsigned8) (255) 8) #[instrUnsigned],
    -- [B5,B6] unsigned int miss.
    mkCase "oracle/ok/int/unsigned/miss/8" (mkIntStack (.cell dictUnsigned8) (9) 8) #[instrUnsigned],
    -- [B5,B6] unsigned int upper-bound hit.
    mkCase "oracle/ok/int/unsigned/max-hit/8" (mkIntStack (.cell dictUnsigned8) (0) 8) #[instrUnsigned],
    -- [B5,B2] signed key out of range low boundary.
    mkCase "oracle/err/int/signed/out-of-range-low/4" (mkIntStack (.cell dictSigned4) (-9) 4) #[instrSigned],
    -- [B5,B2] signed key out of range high boundary.
    mkCase "oracle/err/int/signed/out-of-range-high/4" (mkIntStack (.cell dictSigned4) 8 4) #[instrSigned],
    -- [B5,B2] unsigned key negative boundary.
    mkCase "oracle/err/int/unsigned/out-of-range-negative/8" (mkIntStack (.cell dictUnsigned8) (-1) 8) #[instrUnsigned],
    -- [B5,B2] unsigned key above max boundary.
    mkCase "oracle/err/int/unsigned/out-of-range-high/8" (mkIntStack (.cell dictUnsigned8) 256 8) #[instrUnsigned],
    -- [B4,B2] integer n zero with non-zero key (signed).
    mkCase "oracle/err/int/signed/n-zero-key" (mkIntStack (.cell dictSigned4) 1 0) #[instrSigned],
    -- [B2] n validation failure: negative.
    mkCase "oracle/err/n/negative/slice" (mkSliceStack (.cell dictSlice4Single) key3 (-1)),
    -- [B2] n validation failure: too large.
    mkCase "oracle/err/n/too-large/slice" (mkSliceStack (.cell dictSlice4Single) key3 1024),
    -- [B2] n validation failure: nan.
    mkCase "oracle/err/n/nan" (#[.builder valueA, .slice mkSlice3, .cell dictSlice4Single, .int .nan]),
    -- [B4] slice key too short.
    mkCase "oracle/err/key-too-short/slice" (mkSliceStack (.cell dictSlice4Single) key8 4),
    -- [B4] key missing entirely for slice key.
    mkCase "oracle/err/key-too-short/slice/zero" (mkSliceStack (.cell dictSlice4Single) key0 1),
    -- [B3,B7] root type error.
    mkCase "oracle/err/root-type/slice" (mkSliceStack (.tuple #[]) key3 4),
    -- [B5] int key type error.
    mkCase "oracle/err/key-type/int" (mkSliceStack (.cell dictUnsigned8) key3 8) #[instrSigned],
    -- [B3] wrong key type for int-key path.
    mkCase "oracle/err/key-type/intpath" (#[.builder valueA, .slice mkSlice3, .cell dictSigned4, intV 4]) #[instrSigned],
    -- [B6] value type error (not builder) for slice.
    mkCase "oracle/err/value-not-builder/slice" (#[.slice mkSlice3, .slice mkSlice3, .cell dictSlice4Single, intV 4]),
    -- [B6] value type error (not builder) for int.
    mkCase "oracle/err/value-not-builder/int" (#[.int (.num 7), .int (.num 3), .cell dictSigned4, intV 4]) #[instrSigned],
    -- [B7] malformed dictionary root.
    mkCase "oracle/err/malformed-root/slice" (mkSliceStack (.cell malformedDictRoot) key3 4),
    -- [B7] malformed dictionary root for int path.
    mkCase "oracle/err/malformed-root/int" (mkIntStack (.cell malformedDictRoot) 3 4) #[instrSigned],
    -- [B1] underflow.
    mkCase "oracle/err/underflow/0" #[],
    -- [B1] underflow.
    mkCase "oracle/err/underflow/1" #[.builder valueA],
    -- [B1] underflow.
    mkCase "oracle/err/underflow/2" (#[.builder valueA, .slice mkSlice3]),
    -- [B1] underflow.
    mkCase "oracle/err/underflow/3" (#[.builder valueA, .slice mkSlice3, .cell dictSlice4Single]),
    -- [B9] raw opcodes decode.
    mkCodeCase "oracle/code/f441" (mkSliceStack .null key4 4) rawF441,
    -- [B9] raw opcode decode.
    mkCodeCase "oracle/code/f442" (mkIntStack .null (-8) 4) rawF442,
    -- [B9] raw opcode decode.
    mkCodeCase "oracle/code/f443" (mkIntStack .null 255 8) rawF443,
    -- [B9] raw opcode decode invalid.
    mkCodeCase "oracle/code/f440-invalid" (mkSliceStack .null key4 4) rawF440,
    -- [B9] raw opcode decode invalid.
    mkCodeCase "oracle/code/f444-invalid" (mkSliceStack .null key4 4) rawF444,
    -- [B9] raw decode truncated failure.
    mkCodeCase "oracle/code/truncated-8" (mkSliceStack .null key4 4) rawF4,
    -- [B9] raw decode truncated failure.
    mkCodeCase "oracle/code/truncated-15" (mkSliceStack .null key4 4) rawF4trunc,
    -- [B10] gas exact.
    mkGasCase "oracle/gas/slice/miss/exact" (mkSliceStack .null key4 4) instrSliceKey gasMissSlice (oracleGasLimitsExact gasMissSlice),
    -- [B10] gas exact-minus-one.
    mkGasCase "oracle/gas/slice/miss/exact-minus-one" (mkSliceStack .null key4 4) instrSliceKey gasMissSliceMinusOne (oracleGasLimitsExactMinusOne gasMissSliceMinusOne),
    -- [B10] gas exact with n=0.
    mkGasCase "oracle/gas/slice/0/miss/exact" (mkSliceStack .null key0 0) instrSliceKey gasMissSliceN0 (oracleGasLimitsExact gasMissSliceN0),
    -- [B10] gas exact-minus-one with n=0.
    mkGasCase "oracle/gas/slice/0/miss/exact-minus-one" (mkSliceStack .null key0 0) instrSliceKey gasMissSliceN0MinusOne (oracleGasLimitsExactMinusOne gasMissSliceN0MinusOne),
    -- [B10] gas exact with n=1023.
    mkGasCase "oracle/gas/slice/1023/miss/exact" (mkSliceStack .null key1023 1023) instrSliceKey gasMissSliceN1023 (oracleGasLimitsExact gasMissSliceN1023),
    -- [B10] gas exact-minus-one with n=1023.
    mkGasCase "oracle/gas/slice/1023/miss/exact-minus-one" (mkSliceStack .null key1023 1023) instrSliceKey gasMissSliceN1023MinusOne (oracleGasLimitsExactMinusOne gasMissSliceN1023MinusOne),
    -- [B10] gas exact for int signed miss.
    mkGasCase "oracle/gas/int/signed/miss/exact" (mkIntStack (.cell dictSigned4) 5 4) instrSigned gasMissSigned4 (oracleGasLimitsExact gasMissSigned4),
    -- [B10] gas exact-minus-one for int signed miss.
    mkGasCase "oracle/gas/int/signed/miss/exact-minus-one" (mkIntStack (.cell dictSigned4) 5 4) instrSigned gasMissSigned4MinusOne (oracleGasLimitsExactMinusOne gasMissSigned4MinusOne),
    -- [B10] gas exact for int unsigned miss.
    mkGasCase "oracle/gas/int/unsigned/miss/exact" (mkIntStack (.cell dictUnsigned8) 128 8) instrUnsigned gasMissUnsigned8 (oracleGasLimitsExact gasMissUnsigned8),
    -- [B10] gas exact-minus-one for int unsigned miss.
    mkGasCase "oracle/gas/int/unsigned/miss/exact-minus-one" (mkIntStack (.cell dictUnsigned8) 128 8) instrUnsigned gasMissUnsigned8MinusOne (oracleGasLimitsExactMinusOne gasMissUnsigned8MinusOne),
    -- [B10] gas exact/hit-slice.
    mkGasCase "oracle/gas/slice/hit/exact" (mkSliceStack (.cell dictSlice4Single) key3 4) instrSliceKey gasHitSlice (oracleGasLimitsExact gasHitSlice),
    -- [B10] gas exact-minus-one/hit-slice.
    mkGasCase "oracle/gas/slice/hit/exact-minus-one" (mkSliceStack (.cell dictSlice4Single) key3 4) instrSliceKey gasHitSliceMinusOne (oracleGasLimitsExactMinusOne gasHitSliceMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictSetBId
      count := 500
      gen := genDICTUSETBFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSETB
