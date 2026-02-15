import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUREPLACEB

/-!
INSTRUCTION: DICTUREPLACEB

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime underflow branch: `execInstrDictDictSet` requires exactly 4 stack items
   (`value`, `key`, `dict`, `n`) and fails with `.stkUnd` when missing.
2. [B2] `n` validation branch:
   - `n` is read by `popNatUpTo 1023`; negative, `>1023`, or NaN yields `.rangeChk`.
3. [B3] Unsigned integer key conversion branch (`dictKeyBits?`):
   - `n = 0` requires key `0` exactly.
   - `key < 0` is rejected.
   - `key >= 2^n` is rejected.
4. [B4] Runtime hit branch (`ok = true`): dictionary has existing key and `mode == .replace`
   pushes updated dictionary and `-1`.
5. [B5] Runtime miss branch (`ok = false`): key not present or empty dictionary pushes `null` and `0`.
6. [B6] Stack/type error branch:
   - integer key must be integer, value must be builder, and `dict` must be maybe-cell.
7. [B7] Dictionary structure branch:
   - malformed dictionary root errors (`.dictErr`) are propagated from `dictSetBuilderWithCells`.
8. [B8] Builder size/ref-count overflow branch:
   - oversized builder values propagate as `.cellOv` via `dictSetBuilderWithCells`.
9. [B9] Assembler branch:
   - `.dictReplaceB true true` encodes to `0xf44b`.
   - `.dictReplaceB false true` is invalid and throws `.invOpcode`.
10. [B10] Decoder branch:
    - `0xf44b` decodes to `.dictReplaceB true true`.
    - `0xf449` and `0xf44a` decode to sibling variants
      (`.dictReplaceB false false`, `.dictReplaceB true false`) sharing the same decode slot.
    - `0xf448` / `0xf44c` are invalid (`.invOpcode`).
11. [B11] Gas boundary branch:
    - exact gas budget succeeds, exact-minus-one fails.
12. [B12] Variable gas penalty branch:
    - hit path can add `created * cellCreateGasPrice`.

Assembler validation for slice-mode for this opcode has no additional valid/invalid
branches beyond the above and invalid-bit combinations above.
No slice-key runtime branch exists in this opcode variant, so there is no
`key.haveBits n -> cellUnd` branch in DICTUREPLACEB.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/
private def dictReplaceBId : InstrId :=
  { name := "DICTUREPLACEB" }

private def dictReplaceBUnsigned : Instr := .dictReplaceB true true

private def rawF449 : Cell := Cell.mkOrdinary (natToBits 0xf449 16) #[]
private def rawF44A : Cell := Cell.mkOrdinary (natToBits 0xf44a 16) #[]
private def rawF44B : Cell := Cell.mkOrdinary (natToBits 0xf44b 16) #[]
private def rawF448 : Cell := Cell.mkOrdinary (natToBits 0xf448 16) #[]
private def rawF44C : Cell := Cell.mkOrdinary (natToBits 0xf44c 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def sampleValueA : Builder := Builder.empty.storeBits (natToBits 0xA0 8)
private def sampleValueB : Builder := Builder.empty.storeBits (natToBits 0xB0 8)
private def sampleValueC : Builder := Builder.empty.storeBits (natToBits 0xC0 8)
private def sampleValueD : Builder := Builder.empty.storeBits (natToBits 0xD0 8)
private def sampleValueE : Builder := Builder.empty.storeBits (natToBits 0xE0 8)
private def oversizedValue : Builder := Builder.empty.storeBits (Array.replicate 1024 false)

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def mkSliceKey (n : Nat) (value : Nat) : Slice := mkSliceFromBits (natToBits value n)
private def keySlice8Max : Slice := mkSliceKey 8 255

private def mkDictInt! (label : String) (n : Nat) (pairs : Array (Int × Builder)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let (k, v) := pair
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"DICTUREPLACEB: {label}: out-of-range key k={k}, n={n}"
      match dictSetBuilderWithCells root keyBits v .set with
      | .ok (some r, _ok, _created, _loaded) =>
          root := some r
      | .ok (none, _, _, _) =>
          panic! s!"DICTUREPLACEB: {label}: unexpected empty root after set"
      | .error e =>
          panic! s!"DICTUREPLACEB: {label}: dict build failed ({reprStr e})"
    match root with
    | some d => d
    | none => panic! s!"DICTUREPLACEB: {label}: empty dict after construction"

private def mkDictIntReplaceHit! (label : String) (root : Cell) (n : Nat) (key : Int) (value : Builder) : Cell :=
  match dictKeyBits? key n true with
  | none =>
      panic! s!"DICTUREPLACEB: {label}: out-of-range key k={key}, n={n}"
  | some keyBits =>
      match dictSetBuilderWithCells (some root) keyBits value .replace with
      | .ok (some r, _ok, _created, _loaded) => r
      | .ok (none, _, _, _) => panic! s!"DICTUREPLACEB: {label}: expected new root after replace"
      | .error e => panic! s!"DICTUREPLACEB: {label}: dict replace failed ({reprStr e})"

private def dictUnsigned0 : Cell :=
  mkDictInt! "dictUnsigned0" 0 #[(0, sampleValueA)]

private def dictUnsigned4 : Cell :=
  mkDictInt! "dictUnsigned4" 4 #[(0, sampleValueA), (7, sampleValueB)]

private def dictUnsigned8 : Cell :=
  mkDictInt! "dictUnsigned8" 8 #[(0, sampleValueA), (64, sampleValueB), (128, sampleValueC), (255, sampleValueD)]

private def dictUnsigned1023 : Cell :=
  mkDictInt! "dictUnsigned1023" 1023 #[(0, sampleValueE)]

private def dictUnsigned8Replace255 : Cell :=
  mkDictIntReplaceHit! "dictUnsigned8Replace255" dictUnsigned8 8 255 sampleValueE

private def dictUnsigned0Replace0 : Cell :=
  mkDictIntReplaceHit! "dictUnsigned0Replace0" dictUnsigned0 0 0 sampleValueC

private def dictUnsigned4MissKey : Int := 12

private def replaceCreated (root : Cell) (n : Nat) (key : Int) : Nat :=
  match dictKeyBits? key n true with
  | none => 0
  | some bs =>
      match dictSetBuilderWithCells (some root) bs sampleValueA .replace with
      | .ok (_, _, created, _) => created
      | .error _ => 0

private def replaceBaseGas : Int := computeExactGasBudget dictReplaceBUnsigned
private def replaceMissGas : Int := replaceBaseGas
private def replaceMissGasMinusOne : Int := computeExactGasBudgetMinusOne dictReplaceBUnsigned

private def replaceHitCreated : Nat := replaceCreated dictUnsigned8 8 255
private def replaceHitGas : Int := replaceBaseGas + Int.ofNat replaceHitCreated * cellCreateGasPrice
private def replaceHitGasMinusOne : Int := if replaceHitGas > 0 then replaceHitGas - 1 else 0

private def fuzzSeed : UInt64 := fuzzSeedForInstr dictReplaceBId

private def mkIntStack
    (n : Int)
    (key : Int)
    (dict : Value := .null)
    (value : Builder := sampleValueA) : Array Value :=
  #[.builder value, intV key, dict, intV n]

private def mkSliceStack
    (n : Int)
    (key : Slice)
    (dict : Value := .null)
    (value : Builder := sampleValueA) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictReplaceBUnsigned])
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
    (#[.pushInt (.num gas), .tonEnvOp .setGasLimit, instr])
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
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i} with {bits} bits")

private def runDICTUREPLACEBDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictReplaceB instr stack

private def genDICTUREPLACEBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 14 then
    let (idx, rng2) := randNat rng1 0 3
    let c : OracleCase :=
      if idx = 0 then
        mkCase "fuzz/underflow/empty" #[]
      else if idx = 1 then
        mkCase "fuzz/underflow/one" #[.builder sampleValueA]
      else if idx = 2 then
        mkCase "fuzz/underflow/two" #[.builder sampleValueA, intV 7]
      else
        mkCase "fuzz/underflow/three" #[.builder sampleValueA, intV 7, .cell dictUnsigned8]
    (c, rng2)
  else if shape < 32 then
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/hit/zero" (mkIntStack 0 0 (.cell dictUnsigned0) sampleValueB)
      else if sel = 1 then
        mkCase "fuzz/hit/4" (mkIntStack 4 0 (.cell dictUnsigned4) sampleValueC)
      else if sel = 2 then
        mkCase "fuzz/hit/8" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueD)
      else if sel = 3 then
        mkCase "fuzz/miss/empty" (mkIntStack 8 12 .null sampleValueA)
      else if sel = 4 then
        mkCase "fuzz/miss/nonempty" (mkIntStack 8 dictUnsigned4MissKey (.cell dictUnsigned8) sampleValueB)
      else
        mkCase "fuzz/hit/1023" (mkIntStack 1023 0 (.cell dictUnsigned1023) sampleValueE)
    (c, rng2)
  else if shape < 48 then
    let (sel, rng2) := randNat rng1 0 2
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/range/n-negative" (mkIntStack (-1) 0 .null)
      else if sel = 1 then
        mkCase "fuzz/range/n-too-large" (mkIntStack 1024 0 .null)
      else
        mkCase "fuzz/range/n-nan" (#[.builder sampleValueA, intV 7, .null, .int .nan])
    (c, rng2)
  else if shape < 64 then
    let (sel, rng2) := randNat rng1 0 2
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/key/unsigned-negative" (mkIntStack 8 (-1) (.cell dictUnsigned8) sampleValueA)
      else if sel = 1 then
        mkCase "fuzz/key/unsigned-high" (mkIntStack 8 256 (.cell dictUnsigned8) sampleValueA)
      else
        mkCase "fuzz/key/nzero-nonzero" (mkIntStack 0 1 (.cell dictUnsigned0) sampleValueA)
    (c, rng2)
  else if shape < 80 then
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkCase "fuzz/type/value-not-builder" (#[] ++ #[ .int (.num 7), intV 5, .cell dictUnsigned8, intV 8])
      else if sel = 1 then
        mkCase "fuzz/type/key-not-int" (#[] ++ #[ .builder sampleValueA, .slice keySlice8Max, .cell dictUnsigned8, intV 8])
      else if sel = 2 then
        mkCase "fuzz/type/dict-not-maybe-cell" (mkIntStack 8 7 (.int (.num 9)) sampleValueA)
      else if sel = 3 then
        mkCase "fuzz/type/n-not-int" (#[] ++ #[ .builder sampleValueA, intV 7, .cell dictUnsigned8, .builder sampleValueA])
      else if sel = 4 then
        mkCase "fuzz/malformed-dict" (mkIntStack 8 7 (.cell malformedDict) sampleValueA)
      else
        mkCase "fuzz/overflow/builder-cellov" (mkIntStack 8 7 (.cell dictUnsigned8) oversizedValue)
    (c, rng2)
  else
    let (sel, rng2) := randNat rng1 0 5
    let c : OracleCase :=
      if sel = 0 then
        mkGasCase "fuzz/gas/miss-exact" (mkIntStack 0 5 .null sampleValueA) dictReplaceBUnsigned replaceMissGas (oracleGasLimitsExact replaceMissGas)
      else if sel = 1 then
        mkGasCase "fuzz/gas/miss-exact-minus-one" (mkIntStack 0 5 .null sampleValueA) dictReplaceBUnsigned replaceMissGasMinusOne (oracleGasLimitsExactMinusOne replaceMissGas)
      else if sel = 2 then
        mkGasCase "fuzz/gas/hit-exact" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueB) dictReplaceBUnsigned replaceHitGas (oracleGasLimitsExact replaceHitGas)
      else if sel = 3 then
        mkGasCase "fuzz/gas/hit-exact-minus-one" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueB) dictReplaceBUnsigned replaceHitGasMinusOne (oracleGasLimitsExactMinusOne replaceHitGas)
      else if sel = 4 then
        mkGasCase "fuzz/gas/hit-zero-boundary" (mkIntStack 0 0 (.cell dictUnsigned0) sampleValueC) dictReplaceBUnsigned (replaceBaseGas + Int.ofNat (replaceCreated dictUnsigned0 0 0) * cellCreateGasPrice)
          (oracleGasLimitsExact (replaceBaseGas + Int.ofNat (replaceCreated dictUnsigned0 0 0) * cellCreateGasPrice))
      else
        mkGasCase "fuzz/gas/hit-zero-boundary-minus-one" (mkIntStack 0 0 (.cell dictUnsigned0) sampleValueC) dictReplaceBUnsigned
          (let base := replaceBaseGas + Int.ofNat (replaceCreated dictUnsigned0 0 0) * cellCreateGasPrice
           if base > 0 then base - 1 else 0)
          (oracleGasLimitsExactMinusOne (replaceBaseGas + Int.ofNat (replaceCreated dictUnsigned0 0 0) * cellCreateGasPrice))
    (c, rng2)

def suite : InstrSuite where
  id := dictReplaceBId
  unit := #[
    { name := "unit/asm/valid/opcode"
      run := do
        match assembleCp0 [dictReplaceBUnsigned] with
        | .ok _ => pure ()
        | .error e =>
            throw (IO.userError s!"unit/asm/valid: expected success, got {e}") },

    { name := "unit/asm/invalid/unsigned-slice"
      run := do
        expectAssembleErr "unit/asm/invalid" .invOpcode (.dictReplaceB false true) },

    { name := "unit/decode/valid-opcodes"
      run := do
        let _ ← expectDecodeStep "decode/f44b" (Slice.ofCell rawF44B) (.dictReplaceB true true) 16
        let _ ← expectDecodeStep "decode/f44a" (Slice.ofCell rawF44A) (.dictReplaceB true false) 16
        let _ ← expectDecodeStep "decode/f449" (Slice.ofCell rawF449) (.dictReplaceB false false) 16
        pure () },

    { name := "unit/decode/invalid-adjacent-opcodes"
      run := do
        expectDecodeInv "decode/f448" rawF448
        expectDecodeInv "decode/f44c" rawF44C
        expectDecodeInv "decode/truncated" rawF4 },

    { name := "unit/runtime/hit"
      run := do
        let st := mkIntStack 8 255 (.cell dictUnsigned8) sampleValueE
        expectOkStack
          "unit/runtime/hit"
          (runDICTUREPLACEBDirect dictReplaceBUnsigned st)
          #[.cell dictUnsigned8Replace255, intV (-1)] },

    { name := "unit/runtime/miss-null"
      run := do
        let st := mkIntStack 8 12 .null sampleValueA
        expectOkStack
          "unit/runtime/miss-null"
          (runDICTUREPLACEBDirect dictReplaceBUnsigned st)
          #[.null, intV 0] },

    { name := "unit/runtime/miss-nonempty"
      run := do
        let st := mkIntStack 8 dictUnsigned4MissKey (.cell dictUnsigned8) sampleValueB
        expectOkStack
          "unit/runtime/miss-nonempty"
          (runDICTUREPLACEBDirect dictReplaceBUnsigned st)
          #[.cell dictUnsigned8, intV 0] },

    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "unit/runtime/underflow-empty" (runDICTUREPLACEBDirect dictReplaceBUnsigned #[]) .stkUnd }
  ]
  oracle := #[
    -- [B1] Underflow
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one" #[.builder sampleValueA],
    mkCase "oracle/underflow/two" #[.builder sampleValueA, intV 1],
    mkCase "oracle/underflow/three" #[.builder sampleValueA, intV 1, .cell dictUnsigned4],

    -- [B2] Range on `n`
    mkCase "oracle/range/n-negative" (mkIntStack (-1) 1 (.cell dictUnsigned4) sampleValueA),
    mkCase "oracle/range/n-too-large" (mkIntStack 1024 1 (.cell dictUnsigned8) sampleValueB),
    mkCase "oracle/range/n-nan" (#[.builder sampleValueA, intV 1, .cell dictUnsigned8, .int .nan]),

    -- [B3] Unsigned key conversion
    mkCase "oracle/key/negative" (mkIntStack 8 (-1) (.cell dictUnsigned8) sampleValueA),
    mkCase "oracle/key/too-large" (mkIntStack 8 256 (.cell dictUnsigned8) sampleValueA),
    mkCase "oracle/key/n0-nonzero" (mkIntStack 0 1 (.cell dictUnsigned0) sampleValueA),

    -- [B4] Hit path
    mkCase "oracle/hit/zero" (mkIntStack 0 0 (.cell dictUnsigned0) sampleValueB),
    mkCase "oracle/hit/n4" (mkIntStack 4 0 (.cell dictUnsigned4) sampleValueC),
    mkCase "oracle/hit/n8" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueD),
    mkCase "oracle/hit/n1023" (mkIntStack 1023 0 (.cell dictUnsigned1023) sampleValueE),

    -- [B5] Miss path
    mkCase "oracle/miss/null" (mkIntStack 8 12 .null sampleValueA),
    mkCase "oracle/miss/nonempty" (mkIntStack 8 dictUnsigned4MissKey (.cell dictUnsigned8) sampleValueA),
    mkCase "oracle/miss/zero-width" (mkIntStack 0 0 .null sampleValueC),

    -- [B6] Type checks
    mkCase "oracle/type/value-not-builder" (#[] ++ #[ .int (.num 7), intV 5, .cell dictUnsigned8, intV 8]),
    mkCase "oracle/type/key-not-int" (#[] ++ #[ .builder sampleValueA, .slice keySlice8Max, .cell dictUnsigned8, intV 8]),
    mkCase "oracle/type/dict-not-maybe-cell" (mkIntStack 8 7 (.tuple #[]) sampleValueA),
    mkCase "oracle/type/n-not-int" (#[] ++ #[ .builder sampleValueA, intV 7, .cell dictUnsigned8, .builder sampleValueA]),

    -- [B7] Malformed dictionary
    mkCase "oracle/malformed-dict" (mkIntStack 8 7 (.cell malformedDict) sampleValueA),
    mkCase "oracle/malformed-dict-with-key" (mkSliceStack 8 keySlice8Max (.cell malformedDict) sampleValueB),

    -- [B8] Builder overflow
    mkCase "oracle/overflow/builder" (mkIntStack 8 7 (.cell dictUnsigned8) oversizedValue),

    -- [B11] Gas exact/edge cases
    mkGasCase "oracle/gas/miss-exact" (mkIntStack 0 5 .null sampleValueA) dictReplaceBUnsigned replaceMissGas (oracleGasLimitsExact replaceMissGas),
    mkGasCase "oracle/gas/miss-exact-minus-one" (mkIntStack 0 5 .null sampleValueA) dictReplaceBUnsigned replaceMissGasMinusOne (oracleGasLimitsExactMinusOne replaceMissGas),
    mkGasCase "oracle/gas/hit-exact" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueB) dictReplaceBUnsigned replaceHitGas (oracleGasLimitsExact replaceHitGas),
    mkGasCase "oracle/gas/hit-exact-minus-one" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueB) dictReplaceBUnsigned replaceHitGasMinusOne (oracleGasLimitsExactMinusOne replaceHitGas),

    -- [B12] Variable gas surcharge branch (created > 0) versus zero-created miss
    mkCase "oracle/gas/hit-created" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueB),
    mkCase "oracle/gas/miss-created-zero" (mkIntStack 8 12 (.cell dictUnsigned8) sampleValueA),

    -- [B10] Decode aliases and roundtrip coverage
    mkCodeCase "oracle/code/0xf44b" (mkIntStack 8 255 (.cell dictUnsigned8) sampleValueE) rawF44B,
    mkCodeCase "oracle/code/0xf44a" (mkIntStack 8 7 (.cell dictUnsigned8) sampleValueA) rawF44A,
    mkCodeCase "oracle/code/0xf449" (mkSliceStack 8 keySlice8Max (.cell dictUnsigned8) sampleValueA) rawF449
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTUREPLACEBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUREPLACEB
