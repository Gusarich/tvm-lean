import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTREPLACEB

/-!
INSTRUCTION: DICTREPLACEB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Encoder-valid branch: `.dictReplaceB false false` encodes to opcode `0xF449`.
2. [B2] Encoder-invalid branch: `.dictReplaceB false true` must fail with `.invOpcode`.
3. [B3] Decoder-valid branch:
   - `0xf449` decodes to `.dictReplaceB false false`.
   - `0xf44a` / `0xf44b` decode to integer-key variants via the shared `0xf449..0xf44b` range.
4. [B4] Decoder-boundary branch:
   - adjacent opcodes `0xf448` and `0xf44c` are decoding errors (`invOpcode`).
5. [B5] Runtime normal-success branch (slice-key hit):
   - `n` popped via `popNatUpTo 1023` (all valid n),
   - `dict` popped as maybe-cell,
   - `key` popped as slice with at least `n` bits,
   - `value` popped as builder,
   - `dictSetBuilderWithCells` returns `ok ... true`.
   VM pushes updated dictionary (`.cell`) and `-1`.
6. [B6] Runtime miss branch (slice-key miss):
   - key is valid slice and not in dictionary.
   - `dictSetBuilderWithCells` returns `ok ... false`.
   VM pushes `null` and `0`.
7. [B7] Runtime underflow branch: stack underflow at any of the 4 required items triggers VM underflow.
8. [B8] Range-check branches on `n` from `popNatUpTo 1023`:
   - negative `n`,
   - `n > 1023`,
   - `.nan` => `.rangeChk`.
9. [B9] Slice-key decoding branch:
   - key slice shorter than `n` bits triggers `.cellUnd`.
10. [B10] Type-check branches:
    - non-slice key,
    - non-maybe-cell dict argument,
    - non-builder new value,
    - non-integer `n`.
11. [B11] Malformed-dictionary branch:
    - valid-looking argument types but malformed dictionary payload causes dictionary operation error (`.dictErr`) through the shared loader/error-propagation path.
12. [B12] Builder-size/ref-count overflow branch:
    - key hit + builder >1023 bits or >4 refs causes `.cellOv` from `dictReplaceBuilderWithCells`.
13. [B13] Gas exactness branch:
    - success/fail under exact gas = `computeExactGasBudget`,
    - failure under exact-minus-one gas (`computeExactGasBudgetMinusOne`).
14. [B14] Variable gas penalty branch:
    - hit path with `created > 0` adds `created * cellCreateGasPrice`; miss path has no created-cell charge.

TOTAL BRANCHES: 14

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/
private def dictReplaceBSlice : Instr := .dictReplaceB false false
private def dictReplaceBId : InstrId := { name := "DICTREPLACEB" }

private def rawF449 : Cell := Cell.mkOrdinary (natToBits 0xf449 16) #[]
private def rawF44A : Cell := Cell.mkOrdinary (natToBits 0xf44a 16) #[]
private def rawF44B : Cell := Cell.mkOrdinary (natToBits 0xf44b 16) #[]
private def rawF448 : Cell := Cell.mkOrdinary (natToBits 0xf448 16) #[]
private def rawF44C : Cell := Cell.mkOrdinary (natToBits 0xf44c 16) #[]

private def sampleValueA : Builder := Builder.empty.storeBits (natToBits 0xAA 8)
private def sampleValueB : Builder := Builder.empty.storeBits (natToBits 0xBB 8)
private def sampleValueC : Builder := Builder.empty.storeBits (natToBits 0xCC 8)
private def sampleValueD : Builder := Builder.empty.storeBits (natToBits 0xDD 8)
private def sampleValueE : Builder := Builder.empty.storeBits (natToBits 0xEE 8)
private def oversizedValue : Builder := Builder.empty.storeBits (Array.replicate 1024 false)

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkDictBits! (label : String) (pairs : Array (BitString × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in pairs do
      let (k, v) := entry
      match dictSetBuilderWithCells root k v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"DICTREPLACEB: {label}: unexpected empty root after set"
      | .error e =>
          panic! s!"DICTREPLACEB: {label}: dict build failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTREPLACEB: {label}: empty dict after construction"

private def dictSlice0 : Cell :=
  mkDictBits! "dictSlice0" #[(#[], sampleValueA)]

private def dictSlice4 : Cell :=
  mkDictBits! "dictSlice4" #[
    (natToBits 1 4, sampleValueA),
    (natToBits 7 4, sampleValueB),
    (natToBits 15 4, sampleValueC)
  ]

private def dictSlice8 : Cell :=
  mkDictBits! "dictSlice8" #[
    (natToBits 0 8, sampleValueA),
    (natToBits 85 8, sampleValueB),
    (natToBits 255 8, sampleValueC),
    (natToBits 170 8, sampleValueD)
  ]

private def key1023 : BitString := Array.replicate 1023 true
private def dictSlice1023 : Cell :=
  mkDictBits! "dictSlice1023" #[ (key1023, sampleValueE) ]

private def dictSignedDecodeRoot : Cell :=
  mkDictBits! "dictSignedDecodeRoot" #[
    (natToBits 7 8, sampleValueA)
  ]

private def dictUnsignedDecodeRoot : Cell :=
  mkDictBits! "dictUnsignedDecodeRoot" #[
    (natToBits 255 8, sampleValueB)
  ]

private def slice0Exact : Slice := mkSliceFromBits (#[])
private def slice4ExactA : Slice := mkSliceFromBits (natToBits 1 4)
private def slice4ExactC : Slice := mkSliceFromBits (natToBits 7 4)
private def slice4Miss : Slice := mkSliceFromBits (natToBits 3 4)
private def slice8ExactA : Slice := mkSliceFromBits (natToBits 0 8)
private def slice8ExactD : Slice := mkSliceFromBits (natToBits 255 8)
private def slice8Miss : Slice := mkSliceFromBits (natToBits 170 8)
private def sliceTooShortFor4 : Slice := mkSliceFromBits (natToBits 1 1)
private def sliceTooShortFor8 : Slice := mkSliceFromBits (natToBits 5 3)
private def slice1023Exact : Slice := mkSliceFromBits key1023
private def sliceTooShortFor1023 : Slice := mkSliceFromBits (Array.replicate 1022 false)

private def mkSliceStack
    (n : Int)
    (key : Slice)
    (dict : Value := .null)
    (value : Builder := sampleValueA) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

private def mkIntStack
    (n : Int)
    (key : Int)
    (dict : Value := .null)
    (value : Builder := sampleValueA) : Array Value :=
  #[.builder value, intV key, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictReplaceBSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictReplaceBId
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
    instr := dictReplaceBId
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
  mkCase name stack
    (#[] ++ #[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr])
    gasLimits
    fuel

private def expectAssembleErr
    (label : String)
    (expected : Excno)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler failure {expected}, got success")

private def expectDecodeInv (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr} with {bits} bits")

private def replaceCreated (root : Cell) (key : BitString) : Nat :=
  match dictSetBuilderWithCells (some root) key sampleValueA .replace with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def replaceBaseGas : Int := computeExactGasBudget dictReplaceBSlice
private def replaceMissGas : Int := replaceBaseGas
private def replaceMissGasMinusOne : Int := computeExactGasBudgetMinusOne dictReplaceBSlice

private def replaceHitCreated : Nat := replaceCreated dictSlice8 (natToBits 255 8)
private def replaceHitGas : Int := replaceBaseGas + Int.ofNat replaceHitCreated * cellCreateGasPrice
private def replaceHitGasMinusOne : Int := if replaceHitGas > 0 then replaceHitGas - 1 else 0

private def fuzzSeed : UInt64 := fuzzSeedForInstr { name := "DICTREPLACEB" }

private def genDICTREPLACEBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 14 then
    -- [B7] underflow
    let (idx, rng2) := randNat rng1 0 3
    let c : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/underflow/empty" #[]
      else if idx = 1 then
        mkCase "fuzz/underflow/one" #[.builder sampleValueA]
      else if idx = 2 then
        mkCase "fuzz/underflow/two" (#[] ++ #[.builder sampleValueA, .slice slice8ExactA])
      else
        mkCase "fuzz/underflow/three" (#[] ++ #[.builder sampleValueA, .slice slice8ExactA, .cell dictSlice8])
    (c, rng2)
  else if shape < 34 then
    -- [B5/B6] hit/miss with slice keys
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/slice-hit/0" (mkSliceStack 0 slice0Exact (.cell dictSlice0) sampleValueA)
      else if sel = 1 then
        mkCase "fuzz/slice-hit/4" (mkSliceStack 4 slice4ExactA (.cell dictSlice4) sampleValueB)
      else if sel = 2 then
        mkCase "fuzz/slice-hit/8" (mkSliceStack 8 slice8ExactD (.cell dictSlice8) sampleValueC)
      else if sel = 3 then
        mkCase "fuzz/slice-miss/8" (mkSliceStack 8 slice8Miss .null sampleValueA)
      else if sel = 4 then
        mkCase "fuzz/slice-miss/4" (mkSliceStack 4 slice4Miss .null sampleValueA)
      else
        mkCase "fuzz/slice-hit/1023" (mkSliceStack 1023 slice1023Exact (.cell dictSlice1023) sampleValueE)
    (c, rng2)
  else if shape < 52 then
    -- [B8] n-boundary errors
    let (sel, rng2) := randNat rng1 0 2
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/range/n-negative" (mkSliceStack (-1) slice8ExactA (.cell dictSlice8) sampleValueA)
      else if sel = 1 then
        mkCase "fuzz/range/n-too-large" (mkSliceStack 1024 slice8ExactA (.cell dictSlice8) sampleValueA)
      else
        mkCase "fuzz/range/n-nan" (#[.builder sampleValueA, .slice slice8ExactA, .cell dictSlice8, .int .nan])
    (c, rng2)
  else if shape < 68 then
    -- [B9] cell_und
    let (sel, rng2) := randNat rng1 0 2
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/cellund/8" (mkSliceStack 8 sliceTooShortFor8 (.cell dictSlice8) sampleValueA)
      else if sel = 1 then
        mkCase "fuzz/cellund/4" (mkSliceStack 4 sliceTooShortFor4 (.cell dictSlice4) sampleValueA)
      else
        mkCase "fuzz/cellund/1023" (mkSliceStack 1023 sliceTooShortFor1023 (.cell dictSlice1023) sampleValueA)
    (c, rng2)
  else if shape < 84 then
    -- [B10/B11/B12] type/malformed/error branches
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/type/key-not-slice" (#[] ++ #[.builder sampleValueA, intV 3, .cell dictSlice8, intV 8])
      else if sel = 1 then
        mkCase "fuzz/type/value-not-builder" (#[] ++ #[.int (.num 7), .slice slice8ExactA, .cell dictSlice8, intV 8])
      else if sel = 2 then
        mkCase "fuzz/type/dict-not-maybe-cell" (mkSliceStack 8 slice8ExactA (.int (.num 7)) sampleValueA)
      else if sel = 3 then
        mkCase "fuzz/type/n-not-int" (#[] ++ #[.builder sampleValueA, .slice slice8ExactA, .cell dictSlice8, .slice slice8ExactA])
        else if sel = 4 then
        mkCase "fuzz/malformed-dict" (mkSliceStack 8 slice8ExactA (.cell malformedDict) sampleValueA)
      else
        mkCase "fuzz/builder/cellov" (mkSliceStack 8 slice8ExactA (.cell dictSlice8) oversizedValue)
    (c, rng2)
  else
    -- [B13/B14] gas branches
    let (sel, rng2) := randNat rng1 0 3
    let c : OracleCase :=
      if sel = 0 then
        mkGasCase "fuzz/gas/miss-exact" (mkSliceStack 0 slice0Exact .null sampleValueA) dictReplaceBSlice replaceMissGas (oracleGasLimitsExact replaceMissGas)
      else if sel = 1 then
        mkGasCase "fuzz/gas/miss-exact-minus-one" (mkSliceStack 0 slice0Exact .null sampleValueA) dictReplaceBSlice replaceMissGasMinusOne (oracleGasLimitsExactMinusOne replaceMissGas)
      else if sel = 2 then
        mkGasCase "fuzz/gas/hit-exact" (mkSliceStack 8 slice8ExactD (.cell dictSlice8) sampleValueC) dictReplaceBSlice replaceHitGas (oracleGasLimitsExact replaceHitGas)
      else
        mkGasCase "fuzz/gas/hit-exact-minus-one" (mkSliceStack 8 slice8ExactD (.cell dictSlice8) sampleValueC) dictReplaceBSlice replaceHitGasMinusOne (oracleGasLimitsExactMinusOne replaceHitGas)
    (c, rng2)

def suite : InstrSuite where
  id := dictReplaceBId
  unit := #[
    { name := "unit/asm/valid-opcodes"
      run := do
        match assembleCp0 [dictReplaceBSlice] with
        | .ok _ => pure ()
        | .error e =>
            throw (IO.userError s!"unit/asm/valid: expected success, got {e}")
    },
    { name := "unit/asm/invalid-unsigned-slice"
      run := do
        expectAssembleErr "slice-unsigned-flag" .invOpcode (.dictReplaceB false true)
    },
    { name := "unit/decode/valid-opcodes"
      run := do
        let _ ← expectDecodeStep "decode/f449" (Slice.ofCell rawF449) (.dictReplaceB false false) 16
    },
    { name := "unit/decode/valid-aliases"
      run := do
        let _ ← expectDecodeStep "decode/f44a" (Slice.ofCell rawF44A) (.dictReplaceB true false) 16
        let _ ← expectDecodeStep "decode/f44b" (Slice.ofCell rawF44B) (.dictReplaceB true true) 16
    },
    { name := "unit/decode/invalid-adjacent-opcodes"
      run := do
        expectDecodeInv "decode/0xf448-invalid" rawF448
        expectDecodeInv "decode/0xf44c-invalid" rawF44C
    }
  ]
  oracle := #[
    -- [B5] hit path: replace existing key (n=8).
    mkCase "ok/hit/8/replace-ff" (mkSliceStack 8 slice8ExactD (.cell dictSlice8) sampleValueB),
    -- [B5] hit path: replace key at mid-range bit pattern (n=4).
    mkCase "ok/hit/4/replace-07" (mkSliceStack 4 slice4ExactC (.cell dictSlice4) sampleValueC),
    -- [B5] hit path with n=0 boundary.
    mkCase "ok/hit/0/replace-empty" (mkSliceStack 0 slice0Exact (.cell dictSlice0) sampleValueD),
    -- [B5,B13] replace at max-width boundary n=1023.
    mkCase "ok/hit/1023/replace-boundary" (mkSliceStack 1023 slice1023Exact (.cell dictSlice1023) sampleValueE),

    -- [B6] miss path: key absent in non-empty dictionary.
    mkCase "ok/miss/8/not-present" (mkSliceStack 8 slice8Miss (.cell dictSlice8) sampleValueA),
    -- [B6] miss path: key absent in non-empty dictionary.
    mkCase "ok/miss/4/not-present" (mkSliceStack 4 slice4Miss (.cell dictSlice4) sampleValueB),
    -- [B6] miss path: nil dictionary at n=8.
    mkCase "ok/miss/8/null-dict" (mkSliceStack 8 slice8ExactA .null sampleValueA),

    -- [B8] range errors on `n`.
    mkCase "err/range/n-negative" (mkSliceStack (-1) slice8ExactA (.cell dictSlice8) sampleValueA),
    mkCase "err/range/n-too-large" (mkSliceStack 1024 slice8ExactA (.cell dictSlice8) sampleValueA),
    mkCase "err/range/n-nan" (#[.builder sampleValueA, .slice slice8ExactA, .cell dictSlice8, .int .nan]),

    -- [B9] cell_und from short slice key.
    mkCase "err/cellund/too-few-bits-8" (mkSliceStack 8 sliceTooShortFor8 (.cell dictSlice8) sampleValueA),
    mkCase "err/cellund/too-few-bits-4" (mkSliceStack 4 sliceTooShortFor4 (.cell dictSlice4) sampleValueA),
    mkCase "err/cellund/shorter-than-1023" (mkSliceStack 1023 sliceTooShortFor1023 (.cell dictSlice1023) sampleValueA),

    -- [B7] stack underflow.
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/one" (#[] ++ #[.builder sampleValueA]),
    mkCase "err/underflow/two" (#[] ++ #[.builder sampleValueA, .slice slice8ExactA]),
    mkCase "err/underflow/three" (#[] ++ #[.builder sampleValueA, .slice slice8ExactA, .cell dictSlice8]),

    -- [B10] type errors in popped operand order.
    mkCase "err/type/key-not-slice" (#[] ++ #[.builder sampleValueA, intV 3, .cell dictSlice8, intV 8]),
    mkCase "err/type/value-not-builder" (#[] ++ #[.int (.num 7), .slice slice8ExactA, .cell dictSlice8, intV 8]),
    mkCase "err/type/dict-not-maybe-cell" (mkSliceStack 8 slice8ExactA (.int (.num 7)) sampleValueA),
    mkCase "err/type/n-not-int" (#[] ++ #[.builder sampleValueA, .slice slice8ExactA, .cell dictSlice8, .slice slice8ExactA]),

    -- [B11] malformed dictionary errors propagated from dictionary primitives.
    mkCase "err/dict/malformed-slice" (mkSliceStack 8 slice8ExactA (.cell malformedDict) sampleValueA),

    -- [B12] builder overflow into dictSetBuilderWithCells.
    mkCase "err/builder/cellov" (mkSliceStack 8 slice8ExactA (.cell dictSlice8) oversizedValue),

    -- [B13] gas exactness branch.
    mkGasCase "gas/miss/exact" (mkSliceStack 0 slice0Exact .null sampleValueA) dictReplaceBSlice replaceMissGas (oracleGasLimitsExact replaceMissGas),
    mkGasCase "gas/miss/exact-minus-one" (mkSliceStack 0 slice0Exact .null sampleValueA) dictReplaceBSlice replaceMissGasMinusOne (oracleGasLimitsExactMinusOne replaceMissGas),
    mkGasCase "gas/hit/exact" (mkSliceStack 8 slice8ExactD (.cell dictSlice8) sampleValueB) dictReplaceBSlice replaceHitGas (oracleGasLimitsExact replaceHitGas),
    mkGasCase "gas/hit/exact-minus-one" (mkSliceStack 8 slice8ExactD (.cell dictSlice8) sampleValueB) dictReplaceBSlice replaceHitGasMinusOne (oracleGasLimitsExactMinusOne replaceHitGas),

    -- [B14] explicit variable-gas path: verify hit path carries created-cell surcharge vs miss path.
    mkCase "gas/hit/created-positive" (mkSliceStack 8 slice8ExactD (.cell dictSlice8) sampleValueB),
    mkCase "gas/miss/created-zero" (mkSliceStack 8 slice8Miss .null sampleValueA),

    -- [B3] decode-roundtrip via raw opcodes for aliases in the same range.
    mkCodeCase "ok/code/0xf449" (mkSliceStack 8 slice8ExactA (.cell dictSlice8) sampleValueA) rawF449,
    mkCodeCase "ok/code/0xf44a" (mkIntStack 8 7 (.cell dictSignedDecodeRoot) sampleValueC) rawF44A,
    mkCodeCase "ok/code/0xf44b" (mkIntStack 8 255 (.cell dictUnsignedDecodeRoot) sampleValueD) rawF44B
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTREPLACEBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREPLACEB
