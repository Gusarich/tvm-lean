import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTDEL

/-!
INSTRUCTION: DICTDEL

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch:
   - `execInstrDictExt` handles `.dictExt (.del intKey unsigned)` and routes all other opcodes to
     `next`.

2. [B2] Runtime stack underflow guard:
   - `VM.checkUnderflow 3` is always required and must reject stacks with <3 items.

3. [B3] Runtime operand validation (`n`):
   - `popNatUpTo 1023` handles type + range checks on `n`.
   - `n = .nan` (non-finite integer) and `n < 0` or `n > 1023` must fail with `.rangeChk`.

4. [B4] Runtime type checks:
   - `popMaybeCell` only accepts `.null` or `.cell` as dictionary root; wrong types are `.typeChk`.
   - Slice-key mode: top key must be a `slice`; `.typeChk` otherwise.
   - Int-key mode: top key must be finite `.int`; `.typeChk` for non-int, `.intOv` for `.nan`.

5. [B5] Runtime key construction path:
   - Slice-key mode requires at least `n` bits in key slice; otherwise `.cellUnd`.
   - Int-key mode converts via `dictKeyBits?`; invalid keys (e.g. too-small/too-large for signed/unsigned semantics) must throw `.rangeChk`.

6. [B6] Runtime delete outcome:
   - If key is absent (including empty dictionary), result is `(sameRoot, 0)`.
   - If key is present, result is `(newRootWithoutKey, oldValueSlice, -1)`.
   - Stack tail (values above dictionary op operands) is preserved in both paths.

7. [B7] Runtime malformed dictionary handling:
   - Invalid dictionary structure is reported as `.dictErr` (or lower-level equivalent propagated through
     `dictDeleteWithCells`).

8. [B8] Assembler encoding:
   - `Asm/Cp0` currently does not have a direct encoder for `.dictExt`; encoding any `.dictExt (.del ...)` must return `.invOpcode`.

9. [B9] Decoder behavior:
   - `DICTDEL` decodes from raw opcodes `0xf459..0xf45b`.
   - `0xf459` -> `.dictExt (.del false false)` (slice key).
   - `0xf45a` -> `.dictExt (.del true false)` (signed integer key).
   - `0xf45b` -> `.dictExt (.del true true)` (unsigned integer key).
   - `0xf458` and `0xf45c` must not decode as `DICTDEL` and stay `.invOpcode`.

10. [B10] Gas accounting:
   - Base cost is fixed for decode width 16 (`instrGas ...`).
   - Exact-gas / exact-minus-one paths are meaningful at least for deterministic miss paths (e.g. empty dictionary).
   - Dynamic `consumeCreatedGas` can add extra charge on path-dependent structural rewiring.

TOTAL BRANCHES: 10
Each oracle test below is tagged with `[Bn]`.
-/

private def dictDelId : InstrId :=
  { name := "DICTDEL" }

private def dictDelInstr (intKey unsigned : Bool) : Instr :=
  .dictExt (.del intKey unsigned)

private def dictDelCode (intKey unsigned : Bool) : Nat :=
  0xf459 ||| (if intKey then 2 else 0) ||| (if unsigned then 1 else 0)

private def rawCell16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawCell8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def dictDelSliceCode : Cell :=
  rawCell16 (dictDelCode false false)

private def dictDelIntSignedCode : Cell :=
  rawCell16 (dictDelCode true false)

private def dictDelIntUnsignedCode : Cell :=
  rawCell16 (dictDelCode true true)

private def valueSliceA : Slice :=
  mkSliceFromBits (natToBits 0xA5 8)

private def valueSliceB : Slice :=
  mkSliceFromBits (natToBits 0x3C 8)

private def valueSliceC : Slice :=
  mkSliceFromBits (natToBits 0x77 8)

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def keyBitsFor (idx : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? idx n unsigned with
  | some bs => bs
  | none =>
      panic! s!"expected representable key: idx={idx}, n={n}, unsigned={unsigned}"

private def mkDictSliceRoot! (label : String) (n : Nat) (pairs : Array (Int × Slice)) (unsigned : Bool) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (idx, v) := p
      let keyBits : BitString := keyBitsFor idx n unsigned
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: key insertion unexpectedly returned no root"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {e}"
    match root with
    | some d => d
    | none => panic! s!"{label}: expected non-empty dictionary"

private def dictSlice4Single : Cell :=
  mkDictSliceRoot! "dict/slice/4/single" 4 #[(2, valueSliceA)] false

private def dictSlice4Two : Cell :=
  mkDictSliceRoot! "dict/slice/4/two" 4 #[(2, valueSliceA), (3, valueSliceB)] false

private def dictSlice8Single : Cell :=
  mkDictSliceRoot! "dict/slice/8/single" 8 #[(8, valueSliceA)] false

private def dictSlice8MergeCandidate : Cell :=
  mkDictSliceRoot! "dict/slice/8/merge" 8 #[(2, valueSliceA), (7, valueSliceB)] false

private def dictSliceSigned4 : Cell :=
  mkDictSliceRoot! "dict/slice/signed/4" 4
    #[( -3, valueSliceA), (4, valueSliceB)] false

private def dictSliceUnsigned4 : Cell :=
  mkDictSliceRoot! "dict/slice/unsigned/4" 4
    #[(5, valueSliceA), (9, valueSliceB)] true

private def dictSliceSigned0 : Cell :=
  mkDictSliceRoot! "dict/slice/0/single" 0 #[(0, valueSliceC)] false

private def mkSliceStack (root : Value) (n : Int) (keyBits : BitString) : Array Value :=
  #[root, .slice (mkSliceFromBits keyBits), intV n]

private def mkIntStack (root : Value) (n : Int) (key : Int) : Array Value :=
  #[root, intV key, intV n]

private def dictDelDispatchSentinel : Int := 99221

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := dictDelSliceCode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictDelId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictDelDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runDictDelFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dictDelDispatchSentinel)) stack

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, rest) =>
      if instr != expected ∨ rest.bitsRemaining + rest.refsRemaining ≠ 0 then
        throw (IO.userError s!"{label}: unexpected decode result {reprStr instr}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")

private def dictDelBaseGas : Int :=
  instrGas (dictDelInstr false false) 16

private def dictDelGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictDelBaseGas

private def dictDelGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictDelBaseGas

private def genDICTDEL (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (ks, rng3) := randNat rng1 0 15
    let keyBits := natToBits ks 4
    (mkCase s!"fuzz/slice-hit/{tag}" (mkSliceStack (.cell dictSlice4Single) 4 keyBits) dictDelSliceCode, rng3)
  else if shape = 1 then
    let (ks, rng3) := randNat rng1 0 15
    let keyBits := natToBits ks 4
    (mkCase s!"fuzz/slice-miss-none/{tag}" (mkSliceStack .null 4 keyBits) dictDelSliceCode, rng3)
  else if shape = 2 then
    let (ks, rng3) := randNat rng1 0 15
    let keyBits := natToBits ks 4
    (mkCase s!"fuzz/slice-miss/{tag}" (mkSliceStack (.cell dictSlice4Two) 4 keyBits) dictDelSliceCode, rng3)
  else if shape = 3 then
    let (k, rng3) := randNat rng1 0 3
    let short := natToBits k 3
    (mkCase s!"fuzz/slice-key-underflow/{tag}" (mkSliceStack (.cell dictSlice8Single) 8 short) dictDelSliceCode, rng3)
  else if shape = 4 then
    (mkCase s!"fuzz/int-signed-hit/{tag}" (mkIntStack (.cell dictSliceSigned4) 4 (-3)) dictDelIntSignedCode, rng2)
  else if shape = 5 then
    (mkCase s!"fuzz/int-signed-miss/{tag}" (mkIntStack (.cell dictSliceSigned4) 4 (5)) dictDelIntSignedCode, rng2)
  else if shape = 6 then
    (mkCase s!"fuzz/int-unsigned-hit/{tag}" (mkIntStack (.cell dictSliceUnsigned4) 4 (9)) dictDelIntUnsignedCode, rng2)
  else if shape = 7 then
    (mkCase s!"fuzz/int-unsigned-miss/{tag}" (mkIntStack (.cell dictSliceUnsigned4) 4 (6)) dictDelIntUnsignedCode, rng2)
  else if shape = 8 then
    (mkCase s!"fuzz/int-signed-range-high/{tag}" (mkIntStack (.cell dictSliceSigned4) 4 (8)) dictDelIntSignedCode, rng2)
  else if shape = 9 then
    (mkCase s!"fuzz/int-unsigned-range-high/{tag}" (mkIntStack (.cell dictSliceUnsigned4) 4 (16)) dictDelIntUnsignedCode, rng2)
  else if shape = 10 then
    (mkCase s!"fuzz/int-unsigned-negative/{tag}" (mkIntStack (.cell dictSliceUnsigned4) 4 (-1)) dictDelIntUnsignedCode, rng2)
  else if shape = 11 then
    (mkCase s!"fuzz/int-key-nan/{tag}" (mkIntStack (.cell dictSliceSigned4) 4 (.nan)) dictDelIntSignedCode, rng2)
  else if shape = 12 then
    (mkCase s!"fuzz/type-root-builder/{tag}" #[.builder Builder.empty, .slice (mkSliceFromBits (natToBits 2 4)), intV 4] dictDelSliceCode, rng2)
  else if shape = 13 then
    (mkCase s!"fuzz/malformed-dict/{tag}" (mkSliceStack (.cell malformedDict) 4 (natToBits 2 4)) dictDelSliceCode, rng2)
  else if shape = 14 then
    (mkCase s!"fuzz/decode-below/{tag}" #[] (rawCell16 0xf458), rng2)
  else if shape = 15 then
    (mkCase s!"fuzz/decode-above/{tag}" #[] (rawCell16 0xf45c), rng2)
  else if shape = 16 then
    (mkCase s!"fuzz/truncated/{tag}" #[] (rawCell8 0xf4), rng2)
  else if shape = 17 then
    (mkCase s!"fuzz/n-zero-hit/{tag}" (mkIntStack (.cell dictSliceSigned0) 0 0) dictDelIntSignedCode, rng2)
  else
    (mkCase s!"fuzz/fallback/{tag}" #[] dictDelSliceCode, rng2)

def suite : InstrSuite where
  id := dictDelId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack
          "dispatch-fallback"
          (runDictDelFallback (dictDelInstr false false) #[])
          #[intV dictDelDispatchSentinel]
    },
    { name := "unit/dispatch/match-slice-hit"
      run := do
        expectOkStack
          "match-slice-hit"
          (runDictDelDirect (dictDelInstr false false) (mkSliceStack (.cell dictSlice4Single) 4 (natToBits 2 4)))
          #[.null, valueSliceA, intV (-1)]
    },
    { name := "unit/dispatch/match-slice-miss-preserves-root"
      run := do
        expectOkStack
          "match-slice-miss-preserves-root"
          (runDictDelDirect (dictDelInstr false false) (mkSliceStack (.cell dictSlice4Single) 4 (natToBits 7 4)))
          #[.cell dictSlice4Single, intV 0]
    },
    { name := "unit/dispatch/match-int-hit"
      run := do
        expectOkStack
          "match-int-hit-signed"
          (runDictDelDirect (dictDelInstr true false) (mkIntStack (.cell dictSliceSigned4) 4 (-3)))
          #[.cell (mkDictSliceRoot! "dict/del/signed/tail" 4 #[(4, valueSliceB)] false), valueSliceA, intV (-1)]
        expectOkStack
          "match-int-hit-unsigned"
          (runDictDelDirect (dictDelInstr true true) (mkIntStack (.cell dictSliceUnsigned4) 4 (9)))
          #[.cell (mkDictSliceRoot! "dict/del/unsigned/tail" 4 #[(5, valueSliceA)] true), valueSliceB, intV (-1)]
    },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "underflow-empty" (runDictDelDirect (dictDelInstr false false) #[]) .stkUnd
        expectErr "underflow-one" (runDictDelDirect (dictDelInstr false false) #[(.cell dictSlice4Single)]) .stkUnd
        expectErr "underflow-two" (runDictDelDirect (dictDelInstr false false) (mkSliceStack .null 4 (natToBits 2 4))) .stkUnd
    },
    { name := "unit/runtime/n-type-range"
      run := do
        expectErr "n-type" (runDictDelDirect (dictDelInstr false false)
          #[.cell dictSlice4Single, .slice (mkSliceFromBits (natToBits 2 4)), .cell Cell.empty]) .typeChk
        expectErr "n-nan" (runDictDelDirect (dictDelInstr false false)
          #[.cell dictSlice4Single, .slice (mkSliceFromBits (natToBits 2 4)), .nan]) .rangeChk
        expectErr "n-negative" (runDictDelDirect (dictDelInstr false false) (mkSliceStack (.cell dictSlice4Single) (-1) (natToBits 2 4))) .rangeChk
        expectErr "n-too-large" (runDictDelDirect (dictDelInstr false false) (mkSliceStack (.cell dictSlice4Single) 1024 (natToBits 2 4))) .rangeChk
    },
    { name := "unit/runtime/key-type-and-length"
      run := do
        expectErr "slice-key-type-error" (runDictDelDirect (dictDelInstr false false)
          (mkIntStack (.cell dictSlice4Single) 4 2)) .typeChk
        expectErr "slice-key-underflow" (runDictDelDirect (dictDelInstr false false)
          (mkSliceStack (.cell dictSlice8Single) 8 (natToBits 5 3))) .cellUnd
        expectErr "int-key-type-error" (runDictDelDirect (dictDelInstr true false)
          (mkSliceStack (.cell dictSliceSigned4) 4 (natToBits 2 4))) .typeChk
        expectErr "int-key-nan" (runDictDelDirect (dictDelInstr true false)
          (mkIntStack (.cell dictSliceSigned4) 4 (.nan))) .intOv
    },
    { name := "unit/runtime/key-range"
      run := do
        expectErr "int-signed-out-of-range-positive" (runDictDelDirect (dictDelInstr true false)
          (mkIntStack (.cell dictSliceSigned4) 4 8)) .rangeChk
        expectErr "int-signed-out-of-range-negative" (runDictDelDirect (dictDelInstr true false)
          (mkIntStack (.cell dictSliceSigned4) 4 (-9)) ) .rangeChk
        expectErr "int-unsigned-out-of-range-positive" (runDictDelDirect (dictDelInstr true true)
          (mkIntStack (.cell dictSliceUnsigned4) 4 16)) .rangeChk
        expectErr "int-unsigned-negative" (runDictDelDirect (dictDelInstr true true)
          (mkIntStack (.cell dictSliceUnsigned4) 4 (-1))) .rangeChk
    },
    { name := "unit/runtime/malformed"
      run := do
        expectErr "bad-root-type" (runDictDelDirect (dictDelInstr false false) (mkSliceStack (.builder Builder.empty) 4 (natToBits 2 4))) .typeChk
        expectErr "bad-root-structure" (runDictDelDirect (dictDelInstr false false) (mkSliceStack (.cell malformedDict) 4 (natToBits 2 4))) .dictErr
    },
    { name := "unit/decoder"
      run := do
        expectDecodeOk "decode/slice" dictDelSliceCode (dictDelInstr false false)
        expectDecodeOk "decode/signed" dictDelIntSignedCode (dictDelInstr true false)
        expectDecodeOk "decode/unsigned" dictDelIntUnsignedCode (dictDelInstr true true)
        expectDecodeErr "decode/below-range" (rawCell16 0xf458) .invOpcode
        expectDecodeErr "decode/above-range" (rawCell16 0xf45c) .invOpcode
        expectDecodeErr "decode/truncated-8bit" (rawCell8 0xf4) .invOpcode
    },
    { name := "unit/assembler"
      run := do
        expectAssembleErr "assemble/slice" (dictDelInstr false false) .invOpcode
        expectAssembleErr "assemble/signed" (dictDelInstr true false) .invOpcode
        expectAssembleErr "assemble/unsigned" (dictDelInstr true true) .invOpcode
    }
  ]
  oracle := #[
    -- [B2] Stack underflow variants.
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one" #[.cell dictSlice4Single],
    mkCase "oracle/underflow/two" (mkSliceStack (.cell dictSlice4Single) 4 (natToBits 2 4)),

    -- [B3] `n` type/range errors.
    mkCase "oracle/n-type" (#[(.cell dictSlice4Single), .slice (mkSliceFromBits (natToBits 2 4)), .null]),
    mkCase "oracle/n-nan" (#[(.cell dictSlice4Single), .slice (mkSliceFromBits (natToBits 2 4)), .int .nan]),
    mkCase "oracle/n-negative" (#[(.cell dictSlice4Single), .slice (mkSliceFromBits (natToBits 2 4)), intV (-1)]),
    mkCase "oracle/n-too-large" (#[(.cell dictSlice4Single), .slice (mkSliceFromBits (natToBits 2 4)), intV 1024]),
    mkCase "oracle/n-max" (#[(.cell dictSlice4Single), .slice (mkSliceFromBits (natToBits 2 4)), intV 1023]),

    -- [B4] key/value parsing modes and type checks.
    mkCase "oracle/type/key-not-slice" (mkIntStack (.cell dictSlice4Single) 4 2),
    mkCase "oracle/type/dict-not-cell" (mkSliceStack (.builder Builder.empty) 4 (natToBits 2 4)),
    mkCase "oracle/type/nan-in-key-signed" (mkIntStack (.cell dictSliceSigned4) 4 (.nan)),
    mkCase "oracle/type/nan-in-key-unsigned" (mkIntStack (.cell dictSliceUnsigned4) 4 (.nan)),

    -- [B5] key conversion and key length failures.
    mkCase "oracle/key/slice-underflow" (mkSliceStack (.cell dictSlice8Single) 8 (natToBits 5 3)),
    mkCase "oracle/key/signed-out-of-range-positive" (mkIntStack (.cell dictSliceSigned4) 4 8),
    mkCase "oracle/key/signed-out-of-range-negative" (mkIntStack (.cell dictSliceSigned4) 4 (-9)),
    mkCase "oracle/key/unsigned-out-of-range-positive" (mkIntStack (.cell dictSliceUnsigned4) 4 16),
    mkCase "oracle/key/unsigned-negative" (mkIntStack (.cell dictSliceUnsigned4) 4 (-1)),
    mkCase "oracle/key/overflow-int-to-zero" (mkIntStack (.cell dictSliceSigned0) 0 1),
    mkCase "oracle/key/nzero-dict" (mkIntStack (.cell dictSliceSigned0) 0 0),

    -- [B6] dictionary lookup/deletion behavior.
    mkCase "oracle/delete/slice-miss-empty" (mkSliceStack .null 4 (natToBits 2 4)),
    mkCase "oracle/delete/slice-miss-non-empty" (mkSliceStack (.cell dictSlice4Single) 4 (natToBits 7 4)),
    mkCase "oracle/delete/slice-hit-single" (mkSliceStack (.cell dictSlice4Single) 4 (natToBits 2 4)),
    mkCase "oracle/delete/slice-hit-branch" (mkSliceStack (.cell dictSlice4Two) 4 (natToBits 2 4)),
    mkCase "oracle/delete/int-signed-hit" (mkIntStack (.cell dictSliceSigned4) 4 (-3)),
    mkCase "oracle/delete/int-signed-miss" (mkIntStack (.cell dictSliceSigned4) 4 (6)),
    mkCase "oracle/delete/int-unsigned-hit" (mkIntStack (.cell dictSliceUnsigned4) 4 (9)),
    mkCase "oracle/delete/int-unsigned-miss" (mkIntStack (.cell dictSliceUnsigned4) 4 (6)),
    mkCase "oracle/delete/with-tail-hit-preserved"
      #[intV 77, .cell dictSlice4Single, .slice (mkSliceFromBits (natToBits 2 4)), intV 4],
    mkCase "oracle/delete/with-tail-miss-preserved"
      #[intV 77, .cell dictSlice4Single, .slice (mkSliceFromBits (natToBits 7 4)), intV 4],

    -- [B7] malformed dictionary structure.
    mkCase "oracle/malformed/dict-root-bad-structure" (mkSliceStack (.cell malformedDict) 4 (natToBits 2 4)),
    mkCase "oracle/malformed/nested-key-value-shape" (mkSliceStack (.cell (mkDictSliceRoot! "dict/malformed/value-shape" 4 #[(2, mkSliceFromBits (natToBits 0b1 1))] false) 4 (natToBits 2 4)),

    -- [B9] decode boundary behavior.
    mkCase "oracle/decode/below-boundary" #[] (rawCell16 0xf458),
    mkCase "oracle/decode/above-boundary" #[] (rawCell16 0xf45c),
    mkCase "oracle/decode/truncated" #[] (rawCell8 0xf4),

    -- [B10] gas accounting.
    mkCase "oracle/gas/exact/miss-none-root" (mkSliceStack (.cell dictSlice4Single) 4 (natToBits 8 4)) dictDelSliceCode dictDelGasExact,
    mkCase "oracle/gas/exact-minus-one/miss-none-root" (mkSliceStack (.cell dictSlice4Single) 4 (natToBits 8 4)) dictDelSliceCode dictDelGasExactMinusOne,
    mkCase "oracle/gas/exact/int-signed-hit" (mkIntStack (.cell dictSliceSigned4) 4 (-3)) dictDelIntSignedCode dictDelGasExact,
    mkCase "oracle/gas/exact/int-unsigned-hit" (mkIntStack (.cell dictSliceUnsigned4) 4 9) dictDelIntUnsignedCode dictDelGasExact
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictDelId
      count := 500
      gen := genDICTDEL }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTDEL
