import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.SUBDICTRPGET

/-!
INSTRUCTION: SUBDICTRPGET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch:
   - `execInstrDictExt` handles only `.dictExt (.subdictGet ...)`; all other instructions follow `next`.

2. [B2] Runtime stack underflow:
   - `VM.checkUnderflow 4` is enforced.
   - Valid stack shape is `[keySlice, k:Int, dictRoot:Option Cell, n:Int]` (top is `n`).

3. [B3] `n` parsing:
   - `popNatUpTo 1023` accepts `0..1023`.
   - `n` outside this range, negative, or NaN must fail.

4. [B4] Dictionary root argument validation:
   - `popMaybeCell` accepts `null` or a `Cell`.
   - Non-cell values (e.g. `Int`, `Slice`) produce `typeChk`.

5. [B5] Prefix length `k` parsing:
   - `k` is parsed with `popNatUpTo (min 1023 n)`.
   - Underflow, negative, NaN, and `k > n` cases fail before key extraction.

6. [B6] Key extraction and short-key boundary:
   - Slice keys must provide at least `k` bits.
   - Fewer than `k` bits raises `cellUnd`.

7. [B7] `k = 0` fast path:
   - For `k = 0`, `dictExtractPrefixSubdictWithCells` returns unchanged `dictRoot`.
   - No root-load precharge is performed.

8. [B8] Prefix extraction traversal:
   - `k > 0` and `k ≤ n` performs root-load precharge before lookup.
   - Prefix mismatch returns `null` dictionary.
   - Prefix match with `rp=true` returns rebuilt subtree with prefix removed.

9. [B9] Dictionary-shape failures:
   - Malformed dictionary structures propagate `cellUnd` or `dictErr` depending on `parse/lookup` shape.

10. [B10] Assembler encoding:
    - `.dictExt (.subdictGet false false true)` is encodable by CP0 (`0xf4b5`).
    - Assembly roundtrips through `decodeCp0WithBits` with 16-bit encoding.

11. [B11] Decoder behavior:
   - `0xf4b5` decodes to `.dictExt (.subdictGet false false true)`.
   - `0xf4b1..0xf4b3` and `0xf4b5..0xf4b7` are neighboring encodings with different `intKey/unsigned/rp` flags.
   - `0xf4b4` and `0xf4b8` are invalid in this region and must decode as `invOpcode`.
   - Truncated bitstreams (e.g., `0xf4`) are also `invOpcode`.

12. [B12] Gas accounting:
   - Base instruction gas is `instrGas (.dictExt (.subdictGet false false true)) 16`.
   - Exact-gas and exact-minus-one limits are tested as success/failure boundaries.
   - Dynamic `created` surcharge exists (`consumeCreatedGas`) in successful prefix-match/rewrite branches; fuzz keeps this path probabilistically covered.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it exercises.
Any branch not covered by oracle tests is covered by the fuzz generator.
-/

private def subdictRpGetId : InstrId := { name := "SUBDICTRPGET" }

private def subdictRpGetInstr : Instr :=
  .dictExt (.subdictGet false false true)

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawOpcode : Cell := raw16 0xf4b5

private def rawOpcodeLower : Cell := raw16 0xf4b3

private def rawOpcodeUpper : Cell := raw16 0xf4b8

private def rawOpcodeSlice : Cell := raw16 0xf4b0

private def rawOpcodeInt : Cell := raw16 0xf4b6

private def rawOpcodeUInt : Cell := raw16 0xf4b7

private def rawOpcodeTrunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def dispatchSentinel : Int := 9090

private def keyBits0 : BitString := #[]

private def keyBits1 : BitString := natToBits 1 1

private def keyBits4 (v : Nat) : BitString :=
  natToBits v 4

private def keyBits8 (v : Nat) : BitString :=
  natToBits v 8

private def keyBits1023 : BitString :=
  Array.replicate 1023 true

private def keyA4 : BitString := keyBits4 0

private def keyB4 : BitString := keyBits4 15

private def keyC4 : BitString := keyBits4 3

private def keyA8 : BitString := keyBits8 170

private def valueCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def valueCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x3C 8) #[]

private def valueCellC : Cell :=
  Cell.mkOrdinary (natToBits 0x77 8) #[]

private def valueSliceA : Slice := Slice.ofCell valueCellA

private def valueSliceB : Slice := Slice.ofCell valueCellB

private def valueSliceC : Slice := Slice.ofCell valueCellC

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictSliceRoot! (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for p in pairs do
      let (k, v) := p
      match dictSetSliceWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: dictionary insertion produced no root for key {k}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {e}"
    match root with
    | some d => d
    | none => panic! s!"{label}: empty dictionary after construction"

private def dict4Single : Cell :=
  mkDictSliceRoot! "dict4/single" #[(keyA4, valueSliceA)]

private def dict4Pair : Cell :=
  mkDictSliceRoot! "dict4/pair" #[(keyA4, valueSliceA), (keyB4, valueSliceB)]

private def dict4Triple : Cell :=
  mkDictSliceRoot! "dict4/triple" #[(keyA4, valueSliceA), (keyC4, valueSliceB), (keyB4, valueSliceC)]

private def dict8Single : Cell :=
  mkDictSliceRoot! "dict8/single" #[(keyA8, valueSliceA)]

private def dict0Single : Cell :=
  mkDictSliceRoot! "dict0/single" #[(keyBits0, valueSliceC)]

private def stack4
    (key : BitString)
    (dictVal : Value)
    (k : Int)
    (n : Int) : Array Value :=
  #[.slice (mkSliceFromBits key), dictVal, intV k, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := rawOpcode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := subdictRpGetId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasProgram (gasLimit : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gasLimit), .tonEnvOp .setGasLimit ] with
  | .ok p =>
      Cell.mkOrdinary (p.bits ++ rawOpcode.bits) #[]
  | .error e =>
      panic! s!"SUBDICTRPGET gas program assembly failed: {reprStr e}"

private def subdictRpGetBaseGas : Int :=
  instrGas subdictRpGetInstr 16

private def subdictRpGetBaseGasMinusOne : Int :=
  if subdictRpGetBaseGas > 0 then subdictRpGetBaseGas - 1 else 0

private def subdictRpGetGasExact : OracleGasLimits :=
  { gasLimit := subdictRpGetBaseGas
    gasMax := subdictRpGetBaseGas
    gasCredit := 0 }

private def subdictRpGetGasExactMinusOne : OracleGasLimits :=
  { gasLimit := subdictRpGetBaseGasMinusOne
    gasMax := subdictRpGetBaseGasMinusOne
    gasCredit := 0 }

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, rest) =>
      if instr != expected || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: unexpected decode result {reprStr instr}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembly error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleExact
    (label : String)
    (instr : Instr)
    (w16 : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble ok, got {e}")
  | .ok c =>
      if c.bits != natToBits w16 16 then
        throw (IO.userError s!"{label}: expected bits {reprStr (natToBits w16 16)}, got {reprStr c.bits}")
      expectDecodeOk label c instr

private def runDispatchFallback (instr : Instr) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dispatchSentinel)) #[
    .slice (mkSliceFromBits keyA4),
    .cell dict4Single,
    intV 2,
    intV 4
  ]

private def genSUBDICTRPGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (tag, rng2) := randNat rng1 0 999_999
  let (tagName, case0, rng3) :=
    if shape = 0 then
      (s!"fuzz/ok/null/k0/{tag}", mkCase (s!"{tag}/ok/null/k0") (stack4 keyBits0 .null 0 0), rng2)
    else if shape = 1 then
      (s!"fuzz/ok/null/k1/{tag}", mkCase (s!"{tag}/ok/null/k1") (stack4 keyBits1 .null 1 1), rng2)
    else if shape = 2 then
      (s!"fuzz/ok/single/k0/{tag}", mkCase (s!"{tag}/ok/single/k0") (stack4 keyA4 (.cell dict4Single) 0 4), rng2)
    else if shape = 3 then
      (s!"fuzz/ok/single/k4/{tag}", mkCase (s!"{tag}/ok/single/k4") (stack4 keyA4 (.cell dict4Single) 4 4), rng2)
    else if shape = 4 then
      (s!"fuzz/ok/prefix-match/{tag}", mkCase (s!"{tag}/ok/prefix-match") (stack4 keyA4 (.cell dict4Pair) 2 4), rng2)
    else if shape = 5 then
      (s!"fuzz/ok/prefix-miss/{tag}", mkCase (s!"{tag}/ok/prefix-miss") (stack4 (natToBits 4 4) (.cell dict4Pair) 2 4), rng2)
    else if shape = 6 then
      (s!"fuzz/ok/triple/{tag}", mkCase (s!"{tag}/ok/triple") (stack4 keyC4 (.cell dict4Triple) 1 4), rng2)
    else if shape = 7 then
      (s!"fuzz/ok/eight/{tag}", mkCase (s!"{tag}/ok/eight") (stack4 keyA8 (.cell dict8Single) 4 8), rng2)
    else if shape = 8 then
      (s!"fuzz/ok/zero-key/{tag}", mkCase (s!"{tag}/ok/zero-key") (stack4 keyBits0 (.cell dict0Single) 0 0), rng2)
    else if shape = 9 then
      let (k, rng3') := randNat rng2 0 4
      let n : Int := Int.ofNat (max 1 k)
      let k' : Int := k
      (s!"fuzz/ok/key-short/{tag}", mkCase (s!"{tag}/fuzz/key-short/{k}/{n}") (stack4 keyBits1 (.cell dict4Single) k' n), rng3')
    else if shape = 10 then
      (s!"fuzz/err/underflow/0/{tag}", mkCase (s!"{tag}/err/underflow/0") #[], rng2)
    else if shape = 11 then
      (s!"fuzz/err/underflow/1/{tag}", mkCase (s!"{tag}/err/underflow/1") #[intV 0], rng2)
    else if shape = 12 then
      (s!"fuzz/err/underflow/2/{tag}", mkCase (s!"{tag}/err/underflow/2") #[.slice (mkSliceFromBits keyA4), intV 0], rng2)
    else if shape = 13 then
      (s!"fuzz/err/n-too-large/{tag}", mkCase (s!"{tag}/err/n-too-large") (stack4 keyA4 (.cell dict4Single) 1 1024), rng2)
    else if shape = 14 then
      (s!"fuzz/err/n-negative/{tag}", mkCase (s!"{tag}/err/n-negative") (stack4 keyA4 (.cell dict4Single) 1 (-1)), rng2)
    else if shape = 15 then
      (s!"fuzz/err/n-nan/{tag}", mkCase (s!"{tag}/err/n-nan") #[.slice (mkSliceFromBits keyA4), .cell dict4Single, intV 1, .int .nan], rng2)
    else if shape = 16 then
      (s!"fuzz/err/k-over-n/{tag}", mkCase (s!"{tag}/err/k-over-n") (stack4 keyA4 (.cell dict4Single) 1 0), rng2)
    else if shape = 17 then
      (s!"fuzz/err/k-negative/{tag}", mkCase (s!"{tag}/err/k-negative") (stack4 keyA4 (.cell dict4Single) (-1) 4), rng2)
    else if shape = 18 then
      (s!"fuzz/err/k-nan/{tag}", mkCase (s!"{tag}/err/k-nan") #[.slice (mkSliceFromBits keyA4), .cell dict4Single, .int .nan, intV 4], rng2)
    else if shape = 19 then
      (s!"fuzz/err/dict-type/{tag}", mkCase (s!"{tag}/err/dict-type") #[.slice (mkSliceFromBits keyA4), .int (.num 5), intV 1, intV 4], rng2)
    else if shape = 20 then
      (s!"fuzz/err/key-type/{tag}", mkCase (s!"{tag}/err/key-type") #[.int (.num 5), .cell dict4Single, intV 1, intV 4], rng2)
    else if shape = 21 then
      (s!"fuzz/err/key-type-null/{tag}", mkCase (s!"{tag}/err/key-type-null") #[.null, .cell dict4Single, intV 1, intV 4], rng2)
    else if shape = 22 then
      (s!"fuzz/err/key-type-slice-0/{tag}", mkCase (s!"{tag}/err/key-type-slice-0") #[.slice (mkSliceFromBits keyA4), .cell dict4Single, intV 0, .int .nan], rng2)
    else if shape = 23 then
      (s!"fuzz/err/malformed/{tag}", mkCase (s!"{tag}/err/malformed") (stack4 keyA4 (.cell malformedDict) 1 1), rng2)
    else if shape = 24 then
      (s!"fuzz/gas/exact/{tag}", mkCase (s!"{tag}/fuzz/gas/exact") (stack4 keyBits0 .null 0 0) (mkGasProgram subdictRpGetBaseGas) subdictRpGetGasExact, rng2)
    else if shape = 25 then
      (s!"fuzz/gas/exact-minus-one/{tag}", mkCase (s!"{tag}/fuzz/gas/exact-minus-one") (stack4 keyBits0 .null 0 0) (mkGasProgram subdictRpGetBaseGasMinusOne) subdictRpGetGasExactMinusOne, rng2)
    else if shape = 26 then
      (s!"fuzz/gas/exact-k1023/{tag}", mkCase (s!"{tag}/fuzz/gas/exact-k1023") (stack4 keyBits1023 .null 1023 1023) (mkGasProgram subdictRpGetBaseGas) subdictRpGetGasExact, rng2)
    else if shape = 27 then
      (s!"fuzz/gas/exact-minus-one-k1023/{tag}", mkCase (s!"{tag}/fuzz/gas/exact-minus-one-k1023") (stack4 keyBits1023 .null 1023 1023) (mkGasProgram subdictRpGetBaseGasMinusOne) subdictRpGetGasExactMinusOne, rng2)
    else if shape = 28 then
      let (k, rng3') := randNat rng2 0 4
      let (n, rng3'') := randNat rng3' 1 1023
      let (idx, rng4) := randNat rng3'' 0 3
      let d :=
        if idx = 0 then
          dict4Single
        else if idx = 1 then
          dict4Pair
        else if idx = 2 then
          dict4Triple
        else
          dict8Single
      (s!"fuzz/extra/{tag}", mkCase (s!"{tag}/fuzz/extra") (stack4 keyA4 (.cell d) (Int.ofNat k) (Int.ofNat n)), rng4)
    else
      (s!"fuzz/random/{tag}", mkCase (s!"{tag}/fuzz/random") (stack4 keyBits1023 (.cell dict4Pair) 2 10) (mkGasProgram subdictRpGetBaseGas), rng2)
  ({ case0 with name := tagName }, rng3)

def suite : InstrSuite where
  id := subdictRpGetId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        let out := runDispatchFallback .add
        let expected : Array Value := #[
          .slice (mkSliceFromBits keyA4),
          .cell dict4Single,
          intV 2,
          intV 4,
          intV dispatchSentinel
        ]
        expectOkStack "unit/dispatch/fallback" out expected },
    { name := "unit/decode/self-op"
      run := do
        expectDecodeOk "unit/decode/self" rawOpcode
          (.dictExt (.subdictGet false false true)) },
    { name := "unit/decode/lower-neighbor"
      run := do
        expectDecodeOk "unit/decode/lower-neighbor" rawOpcodeLower (.dictExt (.subdictGet true true false)) },
    { name := "unit/decode/int-neighbor"
      run := do
        expectDecodeOk "unit/decode/int-neighbor" rawOpcodeInt (.dictExt (.subdictGet true false true)) },
    { name := "unit/decode/uint-neighbor"
      run := do
        expectDecodeOk "unit/decode/uint-neighbor" rawOpcodeUInt (.dictExt (.subdictGet true true true)) },
    { name := "unit/decode/upper-gap"
      run := do
        expectDecodeErr "unit/decode/upper-gap" rawOpcodeUpper .invOpcode },
    { name := "unit/decode/truncated-16"
      run := do
        expectDecodeErr "unit/decode/truncated-16" rawOpcodeTrunc8 .invOpcode },
    { name := "unit/decode/slice-lower-gap"
      run := do
        expectDecodeErr "unit/decode/slice-lower-gap" rawOpcodeSlice .invOpcode },
    { name := "unit/assemble/invOpcode"
      run := do
        expectAssembleExact "unit/assemble/roundtrip" subdictRpGetInstr 0xf4b5 }
  ]
  oracle := #[
    mkCase "ok/null/k0" (stack4 keyBits0 .null 0 0), -- [B7]
    mkCase "ok/null/k1" (stack4 keyBits1 .null 1 1), -- [B7][B8]
    mkCase "ok/null/k1023" (stack4 keyBits1023 .null 1023 1023), -- [B7][B8][B3]
    mkCase "ok/single/k0" (stack4 keyA4 (.cell dict4Single) 0 4), -- [B7]
    mkCase "ok/single/k4" (stack4 keyA4 (.cell dict4Single) 4 4), -- [B8]
    mkCase "ok/pair/k2" (stack4 keyA4 (.cell dict4Pair) 2 4), -- [B8]
    mkCase "ok/pair/mismatch/k2" (stack4 (natToBits 4 4) (.cell dict4Pair) 2 4), -- [B8]
    mkCase "ok/triple/k1" (stack4 keyB4 (.cell dict4Triple) 1 4), -- [B8]
    mkCase "ok/eight/slice" (stack4 keyA8 (.cell dict8Single) 4 8), -- [B8]
    mkCase "ok/zero-key" (stack4 keyBits0 (.cell dict0Single) 0 0), -- [B7]
    mkCase "err/underflow-0" #[], -- [B2]
    mkCase "err/underflow-1" #[intV 1], -- [B2]
    mkCase "err/underflow-2" #[.slice (mkSliceFromBits keyA4), intV 1], -- [B2]
    mkCase "err/underflow-3" #[.slice (mkSliceFromBits keyA4), .cell dict4Single, intV 1], -- [B2]
    mkCase "err/n-too-large" (stack4 keyA4 (.cell dict4Single) 1 1024), -- [B3]
    mkCase "err/n-negative" (stack4 keyA4 (.cell dict4Single) 1 (-1)), -- [B3]
    mkCase "err/n-nan" #[.slice (mkSliceFromBits keyA4), .cell dict4Single, intV 1, .int .nan], -- [B3]
    mkCase "err/k-over-n" (stack4 keyA4 (.cell dict4Single) 1 0), -- [B5]
    mkCase "err/k-negative" (stack4 keyA4 (.cell dict4Single) (-1) 4), -- [B5]
    mkCase "err/k-nan" #[.slice (mkSliceFromBits keyA4), .cell dict4Single, .int .nan, intV 4], -- [B5][B6]
    mkCase "err/dict-type-int" #[.slice (mkSliceFromBits keyA4), .int (.num 7), intV 1, intV 4], -- [B4]
    mkCase "err/dict-type-slice" #[.slice (mkSliceFromBits keyA4), .slice (mkSliceFromBits keyC4), intV 1, intV 4], -- [B4]
    mkCase "err/key-type-int" #[.int (.num 5), .cell dict4Single, intV 1, intV 4], -- [B5][B6]
    mkCase "err/key-type-null" #[.null, .cell dict4Single, intV 1, intV 4], -- [B5][B6]
    mkCase "err/key-short" (stack4 keyBits1 (.cell dict4Single) 4 4), -- [B6]
    mkCase "err/key-short-zero" (stack4 keyBits0 (.cell dict4Single) 4 4), -- [B6]
    mkCase "err/malformed" (stack4 keyA4 (.cell malformedDict) 1 1), -- [B9]
    mkCase "gas/exact-null-k0" (stack4 keyBits0 .null 0 0) (mkGasProgram subdictRpGetBaseGas) subdictRpGetGasExact, -- [B12]
    mkCase "gas/exact-minus-one-null-k0" (stack4 keyBits0 .null 0 0) (mkGasProgram subdictRpGetBaseGasMinusOne) subdictRpGetGasExactMinusOne, -- [B12]
    mkCase "gas/exact-null-k1023" (stack4 keyBits1023 .null 1023 1023) (mkGasProgram subdictRpGetBaseGas) subdictRpGetGasExact, -- [B12]
    mkCase "gas/exact-minus-one-null-k1023" (stack4 keyBits1023 .null 1023 1023) (mkGasProgram subdictRpGetBaseGasMinusOne) subdictRpGetGasExactMinusOne -- [B12]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr subdictRpGetId
      count := 500
      gen := genSUBDICTRPGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTRPGET
