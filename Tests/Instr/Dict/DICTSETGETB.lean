import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTSETGETB

/-
INSTRUCTION: DICTSETGETB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch and arity validation.
   - `.dictExt (.mutGetB ...)` is selected via `execInstrDictExt` and the default code path requires
     4 stack items (`newValue`, `key`, `dict`, `n`).
   - Underflow before any key parsing is `.stkUnd`.

2. [B2] `n` validation.
   - `popNatUpTo 1023` accepts only finite 0..1023 values.
   - `-1`, `1024`, and `NaN` all raise `.rangeChk`.

3. [B3] Slice-key extraction.
   - For `intKey=false`, `popSlice` is used and `haveBits n` gates key extraction.
   - If the slice has fewer than `n` bits, execution leaves `none` and later throws `.cellUnd`.

4. [B4] Integer-key extraction and conversion.
   - For `intKey=true`, `popInt` + `dictKeyBits?` are used.
   - Invalid integer keys (NaN or out of range for signed/unsigned mode) raise `.rangeChk`.

5. [B5] Value input must be a builder.
   - `VM.popBuilder` is used, so missing or wrong types for value trigger `.typeChk`.

6. [B6] Runtime success paths for `DICTSETGET` mode.
   - Hit path: when key exists, old value is returned as a slice and flag `-1` (`true`) is pushed.
   - Miss path: in empty dict or non-existing key, new root is returned with no old value and flag `0` (`false`) is pushed.

7. [B7] Structural key lookup failures.
   - Malformed dictionary roots and invalid payload/label invariants raise `.dictErr`.

8. [B8] Assembler encoding behavior.
   - `.dictExt` instructions are not assembled by CP0 (`assembleCp0` returns `invOpcode`).

9. [B9] Decoder opcode boundaries and aliasing.
   - Opcodes `0xf445`, `0xf446`, `0xf447` decode to
     `.mutGetB false false .set`, `.mutGetB true false .set`, `.mutGetB true true .set`.
   - `0xf444` and `0xf448` must fail as `.invOpcode`; too-short bitstrings must also fail.

10. [B10] Gas accounting.
   - Base gas is `computeExactGasBudget` plus variable creation gas on miss paths.
   - Misses must be checked at `exact` and `exact-1` budgets.

11. [B11] Fuzzer branch coverage.
   - Branches are weighted toward key-shape extremes and explicit error generators (type errors,
     key-size failures, malformed roots, and gas boundary checks).

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def dictSetGetBId : InstrId :=
  { name := "DICTSETGETB" }

private def instrSlice : Instr := .dictExt (.mutGetB false false .set)
private def instrSigned : Instr := .dictExt (.mutGetB true false .set)
private def instrSignedUnsigned : Instr := .dictExt (.mutGetB true true .set)

private def rawF445 : Cell := Cell.mkOrdinary (natToBits 0xf445 16) #[]
private def rawF446 : Cell := Cell.mkOrdinary (natToBits 0xf446 16) #[]
private def rawF447 : Cell := Cell.mkOrdinary (natToBits 0xf447 16) #[]
private def rawF444 : Cell := Cell.mkOrdinary (natToBits 0xf444 16) #[]
private def rawF448 : Cell := Cell.mkOrdinary (natToBits 0xf448 16) #[]
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
      match dictSetBuilderWithCells root k v .set with
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
      match dictSetBuilderWithCells root keyBits v .set with
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

private def mkDictSetGetBCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instrSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictSetGetBId
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
    instr := dictSetGetBId
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
  mkDictSetGetBCase name
    stack
    (#[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr])
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
        throw (IO.userError s!"{label}: expected assembler failure invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure invOpcode")

private def runDictSetGetBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDictSetGetBFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instrSlice (VM.push (.int (.num 777))) stack

private def dictKeyBits! (label : String) (n : Nat) (unsigned : Bool) (key : Int) : BitString :=
  match dictKeyBits? key n unsigned with
  | some b => b
  | none => panic! s!"{label}: invalid key {key} for n={n}, unsigned={unsigned}"

private def createdBitsForSet (root : Option Cell) (bits : BitString) : Nat :=
  match dictLookupSetBuilderWithCells root bits valueA .set with
  | .ok (_, _, _ok, created, _loaded) => created
  | .error e =>
      panic! s!"DICTSETGETB: cannot precompute create count: {reprStr e}"

private def createBitsSlice0 : Nat :=
  createdBitsForSet none (natToBits 0 4)

private def createBitsSlice4 : Nat :=
  createdBitsForSet none key4C

private def createBitsSliceMiss32 : Nat :=
  createdBitsForSet none (natToBits 0xD 4)

private def createBitsSigned4 : Nat :=
  createdBitsForSet none (dictKeyBits! "create-signed4" 4 false 5)

private def createBitsUnsigned4 : Nat :=
  createdBitsForSet none (dictKeyBits! "create-unsigned4" 4 true 5)

private def dictSetGetBExactGas : Int := computeExactGasBudget instrSlice
private def dictSetGetBMissSliceGas : Int :=
  dictSetGetBExactGas + (Int.ofNat createBitsSlice4) * cellCreateGasPrice
private def dictSetGetBMissSignedGas : Int :=
  dictSetGetBExactGas + (Int.ofNat createBitsSigned4) * cellCreateGasPrice
private def dictSetGetBMissUnsignedGas : Int :=
  dictSetGetBExactGas + (Int.ofNat createBitsUnsigned4) * cellCreateGasPrice
private def dictSetGetBMissSliceGasMinusOne : Int :=
  if dictSetGetBMissSliceGas > 0 then dictSetGetBMissSliceGas - 1 else 0
private def dictSetGetBMissSignedGasMinusOne : Int :=
  if dictSetGetBMissSignedGas > 0 then dictSetGetBMissSignedGas - 1 else 0
private def dictSetGetBMissUnsignedGasMinusOne : Int :=
  if dictSetGetBMissUnsignedGas > 0 then dictSetGetBMissUnsignedGas - 1 else 0

private def genDictSetGetBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 28
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    match shape with
    | 0 =>
        (mkDictSetGetBCase
          "fuzz/slice/miss/null/4"
          #[.builder valueA, .slice keySlice4A, .null, intV 4], rng2)
    | 1 =>
        (mkDictSetGetBCase
          "fuzz/slice/miss/null/1023"
          #[.builder valueB, .slice keySlice1023, .null, intV 1023], rng2)
    | 2 =>
        (mkDictSetGetBCase
          "fuzz/slice/miss/null/0"
          #[.builder valueC, .slice keySlice0, .null, intV 0], rng2)
    | 3 =>
        (mkDictSetGetBCase
          "fuzz/slice/miss/nonempty"
          #[.builder valueA, .slice keySlice4C, .cell dictSlice4Miss, intV 4], rng2)
    | 4 =>
        (mkDictSetGetBCase
          "fuzz/slice/hit"
          #[.builder valueA, .slice keySlice4A, .cell dictSlice4Single, intV 4], rng2)
    | 5 =>
        (mkDictSetGetBCase
          "fuzz/int-signed-hit"
          (#[.builder valueA, .int (.num 7), .cell dictSigned4, intV 4])
          #[instrSigned], rng2)
    | 6 =>
        (mkDictSetGetBCase
          "fuzz/int-signed-miss"
          (#[.builder valueA, .int (.num 2), .cell dictSigned4, intV 4])
          #[instrSigned], rng2)
    | 7 =>
        (mkDictSetGetBCase
          "fuzz/int-unsigned-hit"
          (#[.builder valueA, .int (.num 255), .cell dictUnsigned8, intV 8])
          #[instrSignedUnsigned], rng2)
    | 8 =>
        (mkDictSetGetBCase
          "fuzz/int-unsigned-miss"
          (#[.builder valueA, .int (.num 7), .cell dictUnsigned8, intV 8])
          #[instrSignedUnsigned], rng2)
    | 9 =>
        (mkDictSetGetBCase
          "fuzz/key-too-short"
          #[.builder valueA, .slice keySlice4Short, .cell dictSlice4Single, intV 4], rng2)
    | 10 =>
        (mkDictSetGetBCase
          "fuzz/n-negative"
          #[.builder valueA, .slice keySlice4A, .cell dictSlice4Single, intV (-1)], rng2)
    | 11 =>
        (mkDictSetGetBCase
          "fuzz/n-too-large"
          #[.builder valueA, .slice keySlice4A, .cell dictSlice4Single, intV 1024], rng2)
    | 12 =>
        (mkDictSetGetBCase
          "fuzz/n-nan"
          #[.builder valueA, .slice keySlice4A, .cell dictSlice4Single, .int .nan], rng2)
    | 13 =>
        (mkDictSetGetBCase
          "fuzz/key-int-out-of-range/signed"
          (#[.builder valueA, .int (.num 8), .cell dictSigned4, intV 4])
          #[instrSigned], rng2)
    | 14 =>
        (mkDictSetGetBCase
          "fuzz/key-int-out-of-range/unsigned"
          (#[.builder valueA, .int (.num (-1)), .cell dictUnsigned8, intV 8])
          #[instrSignedUnsigned], rng2)
    | 15 =>
        (mkDictSetGetBCase
          "fuzz/type/dict-not-cell"
          #[.builder valueA, .slice keySlice4A, .int (.num 0), intV 4], rng2)
    | 16 =>
        (mkDictSetGetBCase
          "fuzz/type/key-not-slice"
          #[.builder valueA, .int (.num 5), .cell dictSlice4Single, intV 4], rng2)
    | 17 =>
        (mkDictSetGetBCase
          "fuzz/type/value-not-builder"
          #[.int (.num 7), .slice keySlice4A, .cell dictSlice4Single, intV 4], rng2)
    | 18 =>
        (mkDictSetGetBCase
          "fuzz/underflow/empty" #[] , rng2)
    | 19 =>
        (mkDictSetGetBCase
          "fuzz/underflow/one"
          #[.builder valueA], rng2)
    | 20 =>
        (mkDictSetGetBCase
          "fuzz/underflow/two"
          #[.builder valueA, .slice keySlice4A], rng2)
    | 21 =>
        (mkDictSetGetBCase
          "fuzz/underflow/three"
          #[.builder valueA, .slice keySlice4A, .cell dictSlice4Single], rng2)
    | 22 =>
        (mkGasCase
          "fuzz/gas/miss-slice-exact"
          #[.builder valueA, .slice keySlice4C, .null, intV 4]
          instrSlice
          dictSetGetBMissSliceGas
          (oracleGasLimitsExact dictSetGetBMissSliceGas),
          rng2)
    | 23 =>
        (mkGasCase
          "fuzz/gas/miss-slice-exact-minus-one"
          #[.builder valueA, .slice keySlice4C, .null, intV 4]
          instrSlice
          dictSetGetBMissSliceGasMinusOne
          (oracleGasLimitsExactMinusOne dictSetGetBMissSliceGasMinusOne),
          rng2)
    | 24 =>
        (mkGasCase
          "fuzz/gas/miss-int-signed-exact"
          (#[.builder valueA, .int (.num 5), .cell dictSigned4, intV 4])
          instrSigned
          dictSetGetBMissSignedGas
          (oracleGasLimitsExact dictSetGetBMissSignedGas),
          rng2)
    | 25 =>
        (mkGasCase
          "fuzz/gas/miss-int-signed-exact-minus-one"
          (#[.builder valueA, .int (.num 5), .cell dictSigned4, intV 4])
          instrSigned
          dictSetGetBMissSignedGasMinusOne
          (oracleGasLimitsExactMinusOne dictSetGetBMissSignedGasMinusOne),
          rng2)
    | 26 =>
        (mkGasCase
          "fuzz/gas/miss-int-unsigned-exact"
          (#[.builder valueA, .int (.num 3), .cell dictUnsigned8, intV 8])
          instrSignedUnsigned
          dictSetGetBMissUnsignedGas
          (oracleGasLimitsExact dictSetGetBMissUnsignedGas),
          rng2)
    | 27 =>
        (mkGasCase
          "fuzz/gas/miss-int-unsigned-exact-minus-one"
          (#[.builder valueA, .int (.num 3), .cell dictUnsigned8, intV 8])
          instrSignedUnsigned
          dictSetGetBMissUnsignedGasMinusOne
          (oracleGasLimitsExactMinusOne dictSetGetBMissUnsignedGasMinusOne),
          rng2)
    | _ =>
        (mkDictSetGetBCase
          "fuzz/malformed-root"
          #[.builder valueA, .slice keySlice4A, .cell malformedDictRoot, intV 4], rng2)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := dictSetGetBId
  unit := #[
    { name := "unit/dispatch/next"
      run := do
        expectOkStack "dispatch/next"
          (runDictSetGetBFallback #[
          .builder valueA
          , .slice keySlice4A
          , .cell dictSigned4
          , intV 4
          ])
          (#[
          .builder valueA
          , .slice keySlice4A
          , .cell dictSigned4
          , intV 4
          , .int (.num 777)
        ])
    },
    { name := "unit/decoder/decode/f445"
      run := do
        let _ ← expectDecodeStep "decode/f445" (Slice.ofCell rawF445) instrSlice 16
    },
    { name := "unit/decoder/decode/f446"
      run := do
        let _ ← expectDecodeStep "decode/f446" (Slice.ofCell rawF446) instrSigned 16
    },
    { name := "unit/decoder/decode/f447"
      run := do
        let _ ← expectDecodeStep "decode/f447" (Slice.ofCell rawF447) instrSignedUnsigned 16
    },
    { name := "unit/decoder/invalid-adjacent"
      run := do
        expectDecodeInvOpcode "decode/f444" rawF444
        expectDecodeInvOpcode "decode/f448" rawF448
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
        expectErr "underflow" (runDictSetGetBDirect instrSlice #[]) .stkUnd
        expectErr "n-negative" (runDictSetGetBDirect instrSlice (#[
          .builder valueA
          , .slice keySlice4A
          , .cell dictSlice4Single
          , intV (-1)
        ])) .rangeChk
        expectErr "n-too-large" (runDictSetGetBDirect instrSlice (#[
          .builder valueA
          , .slice keySlice4A
          , .cell dictSlice4Single
          , intV 1024
        ])) .rangeChk
        expectErr "n-nan" (runDictSetGetBDirect instrSlice (#[
          .builder valueA
          , .slice keySlice4A
          , .cell dictSlice4Single
          , .int .nan
        ])) .rangeChk
        expectErr "key-short" (runDictSetGetBDirect instrSlice (#[
          .builder valueA
          , .slice keySlice4Short
          , .cell dictSlice4Single
          , intV 4
        ])) .cellUnd
        expectErr "key-type" (runDictSetGetBDirect instrSlice (#[
          .builder valueA
          , .cell Cell.empty
          , .cell dictSlice4Single
          , intV 4
        ])) .typeChk
        expectErr "dict-type" (runDictSetGetBDirect instrSlice (#[
          .builder valueA
          , .slice keySlice4A
          , .int (.num 0)
          , intV 4
        ])) .typeChk
        expectErr "value-type" (runDictSetGetBDirect instrSlice (#[
          .int (.num 7)
          , .slice keySlice4A
          , .cell dictSlice4Single
          , intV 4
        ])) .typeChk
        expectErr "int-range" (runDictSetGetBDirect instrSigned (#[
          .builder valueA
          , .int (.num 8)
          , .cell dictSigned4
          , intV 4
        ])) .rangeChk
        expectErr "dict-err" (runDictSetGetBDirect instrSlice (#[
          .builder valueA
          , .slice keySlice4A
          , .cell malformedDictRoot
          , intV 4
        ])) .dictErr
        expectErr "int-nan" (runDictSetGetBDirect instrSigned (#[
          .builder valueA
          , .int (.num 1)
          , .cell dictSigned4
          , .int .nan
        ])) .rangeChk
      }
  ]
  oracle := #[
    -- [B6] runtime success: set overwrite/add behavior.
    mkDictSetGetBCase "oracle/ok/slice/miss/null/4" (#[
      .builder valueA
      , .slice keySlice4C
      , .null
      , intV 4
    ]),
    mkDictSetGetBCase "oracle/ok/slice/miss/null/0" (#[
      .builder valueB
      , .slice keySlice0
      , .null
      , intV 0
    ]),
    mkDictSetGetBCase "oracle/ok/slice/miss/null/1023" (#[
      .builder valueC
      , .slice keySlice1023
      , .null
      , intV 1023
    ]),
    mkDictSetGetBCase "oracle/ok/slice/miss/nonempty" (#[
      .builder valueA
      , .slice keySlice4C
      , .cell dictSlice4Miss
      , intV 4
    ]),
    mkDictSetGetBCase "oracle/ok/slice/hit" (#[
      .builder valueA
      , .slice keySlice4A
      , .cell dictSlice4Single
      , intV 4
    ]),
    mkDictSetGetBCase "oracle/ok/slice/hit-zero" (#[
      .builder valueD
      , .slice keySlice0
      , .cell dictSlice0
      , intV 0
    ]),
    -- [B4] int-key signed/unsigned variants.
    mkDictSetGetBCase "oracle/ok/int/signed/hit" (#[
      .builder valueA
      , .int (.num (-2))
      , .cell dictSigned4
      , intV 4
    ]) #[instrSigned],
    mkDictSetGetBCase "oracle/ok/int/signed/hit-7" (#[
      .builder valueA
      , .int (.num 7)
      , .cell dictSigned4
      , intV 4
    ]) #[instrSigned],
    mkDictSetGetBCase "oracle/ok/int/signed/miss" (#[
      .builder valueA
      , .int (.num 6)
      , .cell dictSigned4
      , intV 4
    ]) #[instrSigned],
    mkDictSetGetBCase "oracle/ok/int/unsigned/hit" (#[
      .builder valueA
      , .int (.num 255)
      , .cell dictUnsigned8
      , intV 8
    ]) #[instrSignedUnsigned],
    mkDictSetGetBCase "oracle/ok/int/unsigned/miss" (#[
      .builder valueA
      , .int (.num 7)
      , .cell dictUnsigned8
      , intV 8
    ]) #[instrSignedUnsigned],
    -- [B3] key-size / short-key failures.
    mkDictSetGetBCase "oracle/err/key-short/4" (#[
      .builder valueA
      , .slice keySlice4Short
      , .cell dictSlice4Single
      , intV 4
    ]),
    mkDictSetGetBCase "oracle/err/key-short/8" (#[
      .builder valueA
      , .slice keySlice4Short
      , .cell dictSlice8
      , intV 8
    ]),
    -- [B2] underflow.
    mkDictSetGetBCase "oracle/err/underflow/0" #[],
    mkDictSetGetBCase "oracle/err/underflow/1" #[.builder valueA],
    mkDictSetGetBCase "oracle/err/underflow/2" #[.builder valueA, .slice keySlice4A],
    mkDictSetGetBCase "oracle/err/underflow/3" #[.builder valueA, .slice keySlice4A, .cell dictSlice4Miss],
    -- [B2/B5/B4] n validation.
    mkDictSetGetBCase "oracle/err/n-negative" (#[
      .builder valueA
      , .slice keySlice4A
      , .cell dictSlice4Single
      , intV (-1)
    ]),
    mkDictSetGetBCase "oracle/err/n-too-large" (#[
      .builder valueA
      , .slice keySlice4A
      , .cell dictSlice4Single
      , intV 1024
    ]),
    mkDictSetGetBCase "oracle/err/n-nan" (#[
      .builder valueA
      , .slice keySlice4A
      , .cell dictSlice4Single
      , .int .nan
    ]),
    -- [B5] type errors.
    mkDictSetGetBCase "oracle/err/dict-type" (#[
      .builder valueA
      , .slice keySlice4A
      , .int (.num 0)
      , intV 4
    ]),
    mkDictSetGetBCase "oracle/err/key-type" #[
      .builder valueA
      , .cell Cell.empty
      , .cell dictSlice4Single
      , intV 4
    ],
    mkDictSetGetBCase "oracle/err/value-type" #[
      .int (.num 7)
      , .slice keySlice4A
      , .cell dictSlice4Single
      , intV 4
    ],
    mkDictSetGetBCase "oracle/err/int-key-nan" (#[
      .builder valueA
      , .int (.num 7)
      , .cell dictSigned4
      , .int .nan
    ]) #[instrSigned],
    mkDictSetGetBCase "oracle/err/int-key-out-of-range/signed" (#[
      .builder valueA
      , .int (.num 8)
      , .cell dictSigned4
      , intV 4
    ]) #[instrSigned],
    mkDictSetGetBCase "oracle/err/int-key-out-of-range/unsigned" (#[
      .builder valueA
      , .int (.num (-1))
      , .cell dictUnsigned8
      , intV 8
    ]) #[instrSignedUnsigned],
    -- [B7] malformed root.
    mkDictSetGetBCase "oracle/err/malformed-root" (#[
      .builder valueA
      , .slice keySlice4A
      , .cell malformedDictRoot
      , intV 4
    ]),
    -- [B9] raw opcode variants.
    mkCodeCase "oracle/code/f445" (#[
      .builder valueA
      , .slice keySlice4A
      , .cell dictSlice4Single
      , intV 4
    ]) rawF445,
    mkCodeCase "oracle/code/f446" (#[
      .builder valueA
      , .int (.num 1)
      , .cell dictSigned4
      , intV 4
    ]) rawF446,
    mkCodeCase "oracle/code/f447" (#[
      .builder valueA
      , .int (.num 1)
      , .cell dictUnsigned8
      , intV 8
    ]) rawF447,
    -- [B10] gas exactness.
    mkGasCase "oracle/gas/miss-slice-exact" (#[
      .builder valueA
      , .slice keySlice4C
      , .null
      , intV 4
    ]) instrSlice dictSetGetBMissSliceGas (oracleGasLimitsExact dictSetGetBMissSliceGas),
    mkGasCase "oracle/gas/miss-slice-exact-minus-one" (#[
      .builder valueA
      , .slice keySlice4C
      , .null
      , intV 4
    ]) instrSlice dictSetGetBMissSliceGasMinusOne (oracleGasLimitsExactMinusOne dictSetGetBMissSliceGasMinusOne),
    mkGasCase "oracle/gas/hit-slice-exact" (#[
      .builder valueA
      , .slice keySlice4A
      , .cell dictSlice4Single
      , intV 4
    ]) instrSlice dictSetGetBExactGas (oracleGasLimitsExact dictSetGetBExactGas),
    mkGasCase "oracle/gas/miss-int-signed-exact" (#[
      .builder valueA
      , .int (.num 6)
      , .cell dictSigned4
      , intV 4
    ]) instrSigned dictSetGetBMissSignedGas (oracleGasLimitsExact dictSetGetBMissSignedGas),
    mkGasCase "oracle/gas/miss-int-signed-exact-minus-one" (#[
      .builder valueA
      , .int (.num 6)
      , .cell dictSigned4
      , intV 4
    ]) instrSigned dictSetGetBMissSignedGasMinusOne (oracleGasLimitsExactMinusOne dictSetGetBMissSignedGasMinusOne),
    mkGasCase "oracle/gas/miss-int-unsigned-exact" (#[
      .builder valueA
      , .int (.num 7)
      , .cell dictUnsigned8
      , intV 8
    ]) instrSignedUnsigned dictSetGetBMissUnsignedGas (oracleGasLimitsExact dictSetGetBMissUnsignedGas),
    mkGasCase "oracle/gas/miss-int-unsigned-exact-minus-one" (#[
      .builder valueA
      , .int (.num 7)
      , .cell dictUnsigned8
      , intV 8
    ]) instrSignedUnsigned dictSetGetBMissUnsignedGasMinusOne (oracleGasLimitsExactMinusOne dictSetGetBMissUnsignedGasMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictSetGetBId
      count := 500
      gen := genDictSetGetBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTSETGETB
