import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTADDGETB

/-
INSTRUCTION: DICTADDGETB

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch and arity validation.
   - `.dictExt (.mutGetB false _ .add)` is handled by `execInstrDictExt`.
   - `checkUnderflow 4` requires `newValueBuilder`, `key`, `dict`, `n`.

2. [B2] `n` validation.
   - `popNatUpTo 1023` validates `n` from stack.
   - Negative, `NaN`, and `>1023` raise `rangeChk`.

3. [B3] Slice-key acquisition.
   - For `intKey = false`, `VM.popSlice` is used and `haveBits n` must hold.
   - If the key is too short, execution stores `none` and later throws `cellUnd` when key bits are required.

4. [B4] Integer-key acquisition (opcode variants `f456`/`f457`).
   - `popInt` + `dictKeyBits?` is used for signed/unsigned modes.
   - Invalid integers or key conversions outside range raise `rangeChk`.

5. [B5] Value materialization.
   - `popBuilder` requires a builder value.
   - Non-builder values (`int`, `slice`, `cell`, etc.) raise `typeChk`.

6. [B6] Runtime success path: add-mode semantics.
   - Miss path: `dictLookupSetBuilderWithCells` returns `none` and push `newRoot`, then `-1`.
   - Hit path: pushes old value as a slice then `0`.

7. [B7] Dictionary payload and structure errors.
   - `dictLookupSetBuilderWithCells` may return `.dictErr` for malformed roots.

8. [B8] Assembler encoding: intentionally unsupported.
   - `.dictExt` instructions are not encoded by CP0 assembler (`.invOpcode`).

9. [B9] Decoder boundaries.
   - `0xf455`, `0xf456`, `0xf457` decode to `.dictExt (.mutGetB false false .add)`
     and `.mutGetB true false .add` variants.
   - Neighboring `0xf454` and `0xf458` must be `.invOpcode`, and 8-bit `0xf4` is truncated/invalid.

10. [B10] Gas accounting.
   - Base gas comes from `computeExactGasBudget`.
   - `.add` miss on previously empty dict may add `created * cellCreateGasPrice`.
   - Exact and exact-minus-one envelopes are both required.

11. [B11] Fuzzer branch coverage.
   - Fuzzer should drive both slice and int-key variants, success/failure, malformed input,
     and exact/exact-minus-one gas branches.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn].
-/

private def dictAddGetBId : InstrId :=
  { name := "DICTADDGETB" }

private def instrSlice : Instr := .dictExt (.mutGetB false false .add)
private def instrSigned : Instr := .dictExt (.mutGetB true false .add)
private def instrSignedUnsigned : Instr := .dictExt (.mutGetB true true .add)

private def rawF455 : Cell := Cell.mkOrdinary (natToBits 0xf455 16) #[]
private def rawF456 : Cell := Cell.mkOrdinary (natToBits 0xf456 16) #[]
private def rawF457 : Cell := Cell.mkOrdinary (natToBits 0xf457 16) #[]
private def rawF454 : Cell := Cell.mkOrdinary (natToBits 0xf454 16) #[]
private def rawF458 : Cell := Cell.mkOrdinary (natToBits 0xf458 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def valueA : Builder := Builder.empty.storeBits (natToBits 0xA1 8)
private def valueB : Builder := Builder.empty.storeBits (natToBits 0xB2 8)
private def valueC : Builder := Builder.empty.storeBits (natToBits 0xC3 8)
private def valueD : Builder := Builder.empty.storeBits (natToBits 0xD4 8)

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def key0 : BitString := #[]
private def key1 : BitString := natToBits 0x1 1
private def key3 : BitString := natToBits 0x5 3
private def key4A : BitString := natToBits 0xA 4
private def key4B : BitString := natToBits 0x3 4
private def key4C : BitString := natToBits 0x1 4
private def key4D : BitString := natToBits 0x7 4
private def key8A : BitString := natToBits 0x5A 8
private def key8B : BitString := natToBits 0xC3 8
private def key8C : BitString := natToBits 0xA5 8
private def key1023 : BitString := Array.replicate 1023 true

private def keySlice4A : Slice := mkSliceFromBits key4A
private def keySlice4B : Slice := mkSliceFromBits key4B
private def keySlice4C : Slice := mkSliceFromBits key4C
private def keySlice4Short : Slice := mkSliceFromBits key3
private def keySlice8A : Slice := mkSliceFromBits key8A
private def keySlice8B : Slice := mkSliceFromBits key8B
private def keySlice8C : Slice := mkSliceFromBits key8C
private def keySlice0 : Slice := mkSliceFromBits key0
private def keySlice1023 : Slice := mkSliceFromBits key1023

private def mkDictRootSlice! (label : String) (pairs : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetBuilderWithCells root k v .add with
      | .ok (some root', _ok, _created, _loaded) => root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: insertion did not produce root"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary build"

private def mkDictRootInt!
    (label : String)
    (n : Nat)
    (unsigned : Bool)
    (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      let keyBits : BitString :=
        match dictKeyBits? k n unsigned with
        | some bits => bits
        | none => panic! s!"{label}: invalid int key {k} for n={n}, unsigned={unsigned}"
      match dictSetBuilderWithCells root keyBits v .add with
      | .ok (some root', _ok, _created, _loaded) => root := some root'
      | .ok (none, _, _, _) =>
          panic! s!"{label}: insertion did not produce root"
      | .error e =>
          panic! s!"{label}: dictSetBuilderWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary build"

private def dictSlice4Single : Cell :=
  mkDictRootSlice! "dict/slice/4/single" #[(key4A, valueA)]

private def dictSlice4Miss : Cell :=
  mkDictRootSlice! "dict/slice/4/miss" #[(key4B, valueB)]

private def dictSlice8 : Cell :=
  mkDictRootSlice! "dict/slice/8" #[(key8A, valueA), (key8B, valueB)]

private def dictSlice0 : Cell :=
  mkDictRootSlice! "dict/slice/0" #[(key0, valueC)]

private def dictSigned4 : Cell :=
  mkDictRootInt! "dict/signed/4" 4 false #[( -2, valueA), (-1, valueB), (4, valueC), (7, valueD)]

private def dictSigned8 : Cell :=
  mkDictRootInt! "dict/signed/8" 8 false #[( -128, valueA), (-1, valueB), (0, valueC), (42, valueD)]

private def dictUnsigned8 : Cell :=
  mkDictRootInt! "dict/unsigned/8" 8 true #[(0, valueA), (1, valueB), (64, valueC), (255, valueD)]

private def mkDictCaseSliceStack
    (value : Builder)
    (key : Slice)
    (dict : Value)
    (n : Int) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

private def mkDictCaseIntStack
    (value : Builder)
    (key : Int)
    (dict : Value)
    (n : Int) : Array Value :=
  #[.builder value, .int (.num key), dict, intV n]

private def mkDictAddGetBCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictAddGetBId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private instance : Coe Instr (Array Instr) where
  coe i := #[i]

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictAddGetBId
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
  mkDictAddGetBCase name
    stack
    (#[ .pushInt (.num gas), .tonEnvOp .setGasLimit, instr ])
    gasLimits
    fuel

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr decoded} ({bits} bits)")

private def expectAssembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure invOpcode")

private def runDictAddGetBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDictAddGetBFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instrSlice (VM.push (.int (.num 777))) stack

private def dictKeyBits! (label : String) (n : Nat) (unsigned : Bool) (key : Int) : BitString :=
  match dictKeyBits? key n unsigned with
  | some b => b
  | none => panic! s!"{label}: invalid key {key} for n={n}, unsigned={unsigned}"

private def createdBitsForAdd (root : Option Cell) (bits : BitString) : Nat :=
  match dictLookupSetBuilderWithCells root bits valueA .add with
  | .ok (_, _, _, created, _loaded) => created
  | .error e =>
      panic! s!"DICTADDGETB: cannot precompute create count: {reprStr e}"

private def createBitsSlice0 : Nat :=
  createdBitsForAdd none (natToBits 0 4)

private def createBitsSlice4 : Nat :=
  createdBitsForAdd none key4C

private def createBitsSliceMiss32 : Nat :=
  createdBitsForAdd none (natToBits 0xD 4)

private def createBitsSigned4 : Nat :=
  createdBitsForAdd none (dictKeyBits! "create-signed4" 4 false 5)

private def createBitsUnsigned4 : Nat :=
  createdBitsForAdd none (dictKeyBits! "create-unsigned4" 4 true 5)

private def dictAddGetBExactGas : Int := computeExactGasBudget instrSlice
private def dictAddGetBMissSliceGas : Int :=
  dictAddGetBExactGas + (Int.ofNat createBitsSlice4 * cellCreateGasPrice)
private def dictAddGetBMissSignedGas : Int :=
  dictAddGetBExactGas + (Int.ofNat createBitsSigned4 * cellCreateGasPrice)
private def dictAddGetBMissUnsignedGas : Int :=
  dictAddGetBExactGas + (Int.ofNat createBitsUnsigned4 * cellCreateGasPrice)
private def dictAddGetBMissSliceGasMinusOne : Int :=
  if dictAddGetBMissSliceGas > 0 then dictAddGetBMissSliceGas - 1 else 0
private def dictAddGetBMissSignedGasMinusOne : Int :=
  if dictAddGetBMissSignedGas > 0 then dictAddGetBMissSignedGas - 1 else 0
private def dictAddGetBMissUnsignedGasMinusOne : Int :=
  if dictAddGetBMissUnsignedGas > 0 then dictAddGetBMissUnsignedGas - 1 else 0

private def genDictAddGetBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    match shape with
    | 0 =>
        (mkDictAddGetBCase
          "fuzz/slice/miss/null/4"
          (mkDictCaseSliceStack valueA keySlice4A .null 4), rng2)
    | 1 =>
        (mkDictAddGetBCase
          "fuzz/slice/miss/null/1023"
          (mkDictCaseSliceStack valueB keySlice1023 .null 1023), rng2)
    | 2 =>
        (mkDictAddGetBCase
          "fuzz/slice/miss/n0"
          (mkDictCaseSliceStack valueC keySlice0 .null 0), rng2)
    | 3 =>
        (mkDictAddGetBCase
          "fuzz/slice/miss/nonempty"
          (mkDictCaseSliceStack valueA keySlice4C (.cell dictSlice4Miss) 4), rng2)
    | 4 =>
        (mkDictAddGetBCase
          "fuzz/slice/hit"
          (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) 4), rng2)
    | 5 =>
        (mkDictAddGetBCase
          "fuzz/int-signed-hit"
          (mkDictCaseIntStack valueA 7 (.cell dictSigned4) 4)
          instrSigned, rng2)
    | 6 =>
        (mkDictAddGetBCase
          "fuzz/int-signed-miss"
          (mkDictCaseIntStack valueA 2 (.cell dictSigned4) 4)
          instrSigned, rng2)
    | 7 =>
        (mkDictAddGetBCase
          "fuzz/int-unsigned-hit"
          (mkDictCaseIntStack valueA 255 (.cell dictUnsigned8) 8)
          instrSignedUnsigned, rng2)
    | 8 =>
        (mkDictAddGetBCase
          "fuzz/int-unsigned-miss"
          (mkDictCaseIntStack valueA 7 (.cell dictUnsigned8) 8)
          instrSignedUnsigned, rng2)
    | 9 =>
        (mkDictAddGetBCase
          "fuzz/key-too-short"
          (mkDictCaseSliceStack valueA keySlice4Short (.cell dictSlice4Single) 4), rng2)
    | 10 =>
        (mkDictAddGetBCase
          "fuzz/n-negative"
          (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) (-1)), rng2)
    | 11 =>
        (mkDictAddGetBCase
          "fuzz/n-too-large"
          (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) 1024), rng2)
    | 12 =>
        (mkDictAddGetBCase
          "fuzz/n-nan"
          (#[.builder valueA, .slice keySlice4A, .cell dictSlice4Single, .int .nan]), rng2)
    | 13 =>
        (mkDictAddGetBCase
          "fuzz/key-int-out-of-range/signed"
          (mkDictCaseIntStack valueA 8 (.cell dictSigned4) 4)
          instrSigned, rng2)
    | 14 =>
        (mkDictAddGetBCase
          "fuzz/key-int-out-of-range/unsigned"
          (mkDictCaseIntStack valueA (-1) (.cell dictUnsigned8) 8)
          instrSignedUnsigned, rng2)
    | 15 =>
        (mkDictAddGetBCase
          "fuzz/type/dict-not-cell"
          (mkDictCaseSliceStack valueA keySlice4A (.int (.num 0)) 4), rng2)
    | 16 =>
        (mkDictAddGetBCase
          "fuzz/type/key-not-slice"
          (#[.builder valueA, .int (.num 5), .cell dictSlice4Single, intV 4]), rng2)
    | 17 =>
        (mkDictAddGetBCase
          "fuzz/type/value-not-builder"
          (#[.int (.num 7), .slice keySlice4A, .cell dictSlice4Single, intV 4]), rng2)
    | 18 =>
        (mkDictAddGetBCase
          "fuzz/underflow/empty" #[] , rng2)
    | 19 =>
        (mkDictAddGetBCase
          "fuzz/underflow/one"
          #[.builder valueA], rng2)
    | 20 =>
        (mkDictAddGetBCase
          "fuzz/underflow/two"
          (#[.builder valueA, .slice keySlice4A]), rng2)
    | 21 =>
        (mkDictAddGetBCase
          "fuzz/underflow/three"
          (#[.builder valueA, .slice keySlice4A, .cell dictSlice4Single]), rng2)
    | 22 =>
        (mkGasCase
          "fuzz/gas/miss-slice-exact"
          (mkDictCaseSliceStack valueA keySlice4C .null 4)
          instrSlice
          dictAddGetBMissSliceGas
          (oracleGasLimitsExact dictAddGetBMissSliceGas),
          rng2)
    | 23 =>
        (mkGasCase
          "fuzz/gas/miss-slice-exact-minus-one"
          (mkDictCaseSliceStack valueA keySlice4C .null 4)
          instrSlice
          dictAddGetBMissSliceGasMinusOne
          (oracleGasLimitsExactMinusOne dictAddGetBMissSliceGasMinusOne),
          rng2)
    | 24 =>
        (mkGasCase
          "fuzz/gas/miss-int-signed-exact"
          (mkDictCaseIntStack valueA 5 (.cell dictSigned4) 4)
          instrSigned
          dictAddGetBMissSignedGas
          (oracleGasLimitsExact dictAddGetBMissSignedGas),
          rng2)
    | _ =>
        (mkGasCase
          "fuzz/gas/miss-int-unsigned-exact-minus-one"
          (mkDictCaseIntStack valueA 3 (.cell dictUnsigned8) 8)
          instrSignedUnsigned
          dictAddGetBMissUnsignedGasMinusOne
          (oracleGasLimitsExactMinusOne dictAddGetBMissUnsignedGasMinusOne),
          rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := dictAddGetBId
  unit := #[
    { name := "unit/dispatch/next"
      run := do
        let expected := mkDictCaseIntStack valueA 1 (.cell dictSigned4) 4 ++ #[.int (.num 777)]
        expectOkStack
          "dispatch/next"
          (runDictAddGetBFallback (mkDictCaseIntStack valueA 1 (.cell dictSigned4) 4))
          expected
    },
    { name := "unit/decoder/decode/f455"
      run := do
        let _ ← expectDecodeStep "decode/f455" (Slice.ofCell rawF455) instrSlice 16
    },
    { name := "unit/decoder/decode/f456"
      run := do
        let _ ← expectDecodeStep "decode/f456" (Slice.ofCell rawF456) instrSigned 16
    },
    { name := "unit/decoder/decode/f457"
      run := do
        let _ ← expectDecodeStep "decode/f457" (Slice.ofCell rawF457) instrSignedUnsigned 16
    },
    { name := "unit/decoder/invalid-adjacent"
      run := do
        expectDecodeInvOpcode "decode/f454" rawF454
        expectDecodeInvOpcode "decode/f458" rawF458
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error _ => pure ()
        | .ok _ =>
            throw (IO.userError "decode/f4-8bit should fail")
    },
    { name := "unit/asm/invOpcode"
      run := do
        expectAssembleInvOpcode "asm/slice" instrSlice
        expectAssembleInvOpcode "asm/signed" instrSigned
        expectAssembleInvOpcode "asm/unsigned" instrSignedUnsigned
    },
    { name := "unit/runtime/validation"
      run := do
        expectErr "underflow" (runDictAddGetBDirect instrSlice #[]) .stkUnd
        expectErr "n-negative" (runDictAddGetBDirect instrSlice (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) (-1))) .rangeChk
        expectErr "n-too-large" (runDictAddGetBDirect instrSlice (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) 1024)) .rangeChk
        expectErr "n-nan" (runDictAddGetBDirect instrSlice (#[.builder valueA, .slice keySlice4A, .cell dictSlice4Single, .int .nan])) .rangeChk
        expectErr "key-short" (runDictAddGetBDirect instrSlice (mkDictCaseSliceStack valueA keySlice4Short (.cell dictSlice4Single) 4)) .cellUnd
        expectErr "key-type" (runDictAddGetBDirect instrSlice (#[.builder valueA, .cell Cell.empty, .cell dictSlice4Single, intV 4])) .typeChk
        expectErr "dict-type" (runDictAddGetBDirect instrSlice (mkDictCaseSliceStack valueA keySlice4A (.int (.num 0)) 4)) .typeChk
        expectErr "value-type" (runDictAddGetBDirect instrSlice (#[.int (.num 5), .slice keySlice4A, .cell dictSlice4Single, intV 4])) .typeChk
        expectErr "int-range" (runDictAddGetBDirect instrSigned (mkDictCaseIntStack valueA 8 (.cell dictSigned4) 4)) .rangeChk
        expectErr "dict-err" (runDictAddGetBDirect instrSlice (mkDictCaseSliceStack valueA keySlice4A (.cell malformedDictRoot) 4)) .dictErr
        expectErr "int-nan" (runDictAddGetBDirect instrSigned (#[.builder valueA, .int (.num 1), .cell dictSigned4, .int .nan])) .rangeChk
      }
  ]
  oracle := #[
    -- [B6] runtime miss/hit success (slice-key).
    mkDictAddGetBCase "oracle/ok/slice/miss/null/4" (mkDictCaseSliceStack valueA keySlice4C .null 4),
    mkDictAddGetBCase "oracle/ok/slice/miss/null/0" (mkDictCaseSliceStack valueB keySlice0 .null 0),
    mkDictAddGetBCase "oracle/ok/slice/miss/null/1023" (mkDictCaseSliceStack valueC keySlice1023 .null 1023),
    mkDictAddGetBCase "oracle/ok/slice/miss/nonempty" (mkDictCaseSliceStack valueA keySlice4C (.cell dictSlice4Miss) 4),
    mkDictAddGetBCase "oracle/ok/slice/hit" (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) 4),
    mkDictAddGetBCase "oracle/ok/slice/hit-zero" (mkDictCaseSliceStack valueC keySlice0 (.cell dictSlice0) 0),
    -- [B4] int-key signed/unsigned modes.
    mkDictAddGetBCase "oracle/ok/int/signed/hit" (mkDictCaseIntStack valueA (-2) (.cell dictSigned4) 4) instrSigned,
    mkDictAddGetBCase "oracle/ok/int/signed/hit/7" (mkDictCaseIntStack valueA 7 (.cell dictSigned4) 4) instrSigned,
    mkDictAddGetBCase "oracle/ok/int/signed/miss" (mkDictCaseIntStack valueA 6 (.cell dictSigned4) 4) instrSigned,
    mkDictAddGetBCase "oracle/ok/int/unsigned/hit" (mkDictCaseIntStack valueA 255 (.cell dictUnsigned8) 8) instrSignedUnsigned,
    mkDictAddGetBCase "oracle/ok/int/unsigned/miss" (mkDictCaseIntStack valueA 7 (.cell dictUnsigned8) 8) instrSignedUnsigned,
    -- [B3] key-size / path failures.
    mkDictAddGetBCase "oracle/err/key-short/4" (mkDictCaseSliceStack valueA keySlice4Short (.cell dictSlice4Single) 4),
    mkDictAddGetBCase "oracle/err/key-short/8" (mkDictCaseSliceStack valueA keySlice4Short (.cell dictSlice8) 8),
    -- [B2] underflow.
    mkDictAddGetBCase "oracle/err/underflow/0" #[],
    mkDictAddGetBCase "oracle/err/underflow/1" #[.builder valueA],
    mkDictAddGetBCase "oracle/err/underflow/2" #[.builder valueA, .slice keySlice4A], -- keep shape stable
    mkDictAddGetBCase "oracle/err/underflow/3" #[.builder valueA, .slice keySlice4A, .cell dictSlice4Miss],
    -- [B2/B5/B4] n validation.
    mkDictAddGetBCase "oracle/err/n-negative" (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) (-1)),
    mkDictAddGetBCase "oracle/err/n-too-large" (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) 1024),
    mkDictAddGetBCase "oracle/err/n-nan" (#[.builder valueA, .slice keySlice4A, .cell dictSlice4Single, .int .nan]),
    -- [B5] type errors.
    mkDictAddGetBCase "oracle/err/dict-type" (mkDictCaseSliceStack valueA keySlice4A (.int (.num 0)) 4),
    mkDictAddGetBCase "oracle/err/key-type" (#[.builder valueA, .cell Cell.empty, .cell dictSlice4Single, intV 4]),
    mkDictAddGetBCase "oracle/err/value-type" (#[.int (.num 7), .slice keySlice4A, .cell dictSlice4Single, intV 4]),
    mkDictAddGetBCase "oracle/err/int-key-nan" (#[.builder valueA, .int (.num 7), .cell dictSigned4, .int .nan]) instrSigned,
    mkDictAddGetBCase "oracle/err/int-key-out-of-range/signed" (mkDictCaseIntStack valueA 8 (.cell dictSigned4) 4) instrSigned,
    mkDictAddGetBCase "oracle/err/int-key-out-of-range/unsigned" (mkDictCaseIntStack valueA (-1) (.cell dictUnsigned8) 8) instrSignedUnsigned,
    -- [B7] malformed root.
    mkDictAddGetBCase "oracle/err/malformed-root" (mkDictCaseSliceStack valueA keySlice4A (.cell malformedDictRoot) 4),
    -- [B9] raw opcode variants.
    mkCodeCase "oracle/code/f455" (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) 4) rawF455,
    mkCodeCase "oracle/code/f456" (mkDictCaseIntStack valueA 1 (.cell dictSigned4) 4) rawF456,
    mkCodeCase "oracle/code/f457" (mkDictCaseIntStack valueA 1 (.cell dictUnsigned8) 8) rawF457,
    -- [B10] gas exactness.
    mkGasCase "oracle/gas/miss-slice-exact" (mkDictCaseSliceStack valueA keySlice4C .null 4) instrSlice dictAddGetBMissSliceGas (oracleGasLimitsExact dictAddGetBMissSliceGas),
    mkGasCase "oracle/gas/miss-slice-exact-minus-one" (mkDictCaseSliceStack valueA keySlice4C .null 4) instrSlice dictAddGetBMissSliceGasMinusOne (oracleGasLimitsExactMinusOne dictAddGetBMissSliceGasMinusOne),
    mkGasCase "oracle/gas/hit-slice-exact" (mkDictCaseSliceStack valueA keySlice4A (.cell dictSlice4Single) 4) instrSlice (dictAddGetBExactGas) (oracleGasLimitsExact dictAddGetBExactGas),
    mkGasCase "oracle/gas/miss-int-signed-exact" (mkDictCaseIntStack valueA 6 (.cell dictSigned4) 4) instrSigned dictAddGetBMissSignedGas (oracleGasLimitsExact dictAddGetBMissSignedGas),
    mkGasCase "oracle/gas/miss-int-signed-exact-minus-one" (mkDictCaseIntStack valueA 6 (.cell dictSigned4) 4) instrSigned dictAddGetBMissSignedGasMinusOne (oracleGasLimitsExactMinusOne dictAddGetBMissSignedGasMinusOne),
    mkGasCase "oracle/gas/miss-int-unsigned-exact" (mkDictCaseIntStack valueA 7 (.cell dictUnsigned8) 8) instrSignedUnsigned dictAddGetBMissUnsignedGas (oracleGasLimitsExact dictAddGetBMissUnsignedGas),
    mkGasCase "oracle/gas/miss-int-unsigned-exact-minus-one" (mkDictCaseIntStack valueA 7 (.cell dictUnsigned8) 8) instrSignedUnsigned dictAddGetBMissUnsignedGasMinusOne (oracleGasLimitsExactMinusOne dictAddGetBMissUnsignedGasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictAddGetBId
      count := 500
      gen := genDictAddGetBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTADDGETB
