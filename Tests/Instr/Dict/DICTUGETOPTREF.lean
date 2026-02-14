import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETOPTREF

/-
INSTRUCTION: DICTUGETOPTREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - Instruction is handled in `execInstrDictExt` only when opcode decodes to
     `.dictExt (.getOptRef true true)`; all other instructions are delegated to `next`.

2. [B2] Runtime arity check (`checkUnderflow 3`).
   - Any stack with fewer than three items must fail with `.stkUnd` before key parsing.

3. [B3] `n` operand parsing/range (`popNatUpTo 1023`).
   - `n` must be an integer value.
   - `.nan` is rejected.
   - Negative values and values larger than 1023 are `.rangeChk`.

4. [B4] Dictionary operand parsing (`popMaybeCell`).
   - `.null` is accepted as an empty dictionary root.
   - Non-cell, non-null values are `.typeChk`.

5. [B5] Integer-key parsing (`intKey = true`, unsigned=true).
   - Key must be finite integer (`popIntFinite`), so non-integer is `.typeChk`, `.nan` is `.intOv`.
   - For keys outside representable unsigned range, lookup is skipped and `.null` is pushed.

6. [B6] Missing-dict/miss-key behavior.
   - Valid key but empty root / absent key yields `.null`.

7. [B7] Dictionary hit behavior.
   - Valid root and present key returns the referenced value cell after validating
     that the stored value is exactly one ref with no trailing bits.

8. [B8] Dictionary value format validation.
   - Hit value with wrong bit/ref layout triggers `.dictErr` (`extractRefOrThrow`).

9. [B9] Dictionary structural validation.
   - Malformed dictionary layout errors are propagated as `.dictErr` before returning a value.

10. [B10] Assembler behavior.
    - `.dictExt` instructions are not assembled by `assembleCp0`, so raw raw instruction forms must yield `.invOpcode`.

11. [B11] Decoder behavior and opcode boundaries.
    - Raw `0xF469..0xF46B` decode to the three `getOptRef` forms.
    - `0xF46C` and truncated forms decode to error.

12. [B12] Gas accounting.
    - Gas is exact/fixed by `computeExactGasBudget`; test exact success and exact-minus-one.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def dictUGETOPTREFId : InstrId :=
  { name := "DICTUGETOPTREF" }

private def dictUGETOPTREF : Instr :=
  .dictExt (.getOptRef true true)

private def rawUGETOPTREFSlice : Cell := Cell.mkOrdinary (natToBits 0xF469 16) #[]
private def rawUGETOPTREFInt : Cell := Cell.mkOrdinary (natToBits 0xF46A 16) #[]
private def rawUGETOPTREF : Cell := Cell.mkOrdinary (natToBits 0xF46B 16) #[]
private def rawSetGetOPTREF : Cell := Cell.mkOrdinary (natToBits 0xF46D 16) #[]
private def rawSetGetOPTREFInt : Cell := Cell.mkOrdinary (natToBits 0xF46E 16) #[]
private def rawSetGetOPTREFUInt : Cell := Cell.mkOrdinary (natToBits 0xF46F 16) #[]
private def rawUGETOPTREFFollowing : Cell := Cell.mkOrdinary (natToBits 0xF46C 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def mkGasPrefix (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok c => c
  | .error e => panic! s!"failed to assemble gas prefix for DICTUGETOPTREF: {reprStr e}"

private def gasCode (gas : Int) (opcode : Cell) : Cell := by
  exact Cell.mkOrdinary ((mkGasPrefix gas).bits ++ opcode.bits) ((mkGasPrefix gas).refs ++ opcode.refs)

private def assembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr c}")
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {reprStr e}")

private def mkDictSetRefRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n unsigned with
        | some b => b
        | none => panic! s!"{label}: out-of-range key for dict set ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while building dictionary"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed with {e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits : BitString :=
        dictKeyBits? k n true |>.getD (panic! s!"{label}: malformed key ({k}, n={n})")
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while building dictionary"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary construction"

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC 8) #[]

private def badValueSliceBits : Slice := mkSliceFromBits (natToBits 0xF0 8)
private def badValueSliceBitsAndRef : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[valueA])

private def dictUnsigned8 : Cell :=
  mkDictSetRefRoot! "DICTUGETOPTREF dictUnsigned8" 8 true #[(0, valueA), (7, valueB), (255, valueC)]

private def dictUnsigned1 : Cell :=
  mkDictSetRefRoot! "DICTUGETOPTREF dictUnsigned1" 1 true #[(0, valueA), (1, valueB)]

private def dictUnsigned0 : Cell :=
  mkDictSetRefRoot! "DICTUGETOPTREF dictUnsigned0" 0 true #[(0, valueA)]

private def dictSliceValueBad : Cell :=
  mkDictSetSliceRoot! "DICTUGETOPTREF dictSliceValueBad" 8 #[(1, badValueSliceBits)]

private def dictSliceValueBad2 : Cell :=
  mkDictSetSliceRoot! "DICTUGETOPTREF dictSliceValueBad2" 8 #[(2, badValueSliceBitsAndRef)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0xF 4) #[]

private def dictUGETOPTREFGas : Int :=
  computeExactGasBudget dictUGETOPTREF

private def dictUGETOPTREFGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictUGETOPTREFGas

private def dictUGETOPTREFGasMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictUGETOPTREFGas

private def stackUIntKey (key : Int) (dictValue : Value) (n : Int) : Array Value :=
  #[intV key, dictValue, intV n]

private def underflowOneStack : Array Value :=
  #[] |>.push (.slice (mkSliceFromBits (natToBits 1 8)))

private def underflowTwoStack : Array Value :=
  #[] |>.push (.slice (mkSliceFromBits (natToBits 1 8))) |>.push (.cell dictUnsigned8)

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictUGETOPTREFId
    program := #[]
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDICTUGETOPTREF (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) : OracleCase × StdGen :=
    if shape = 0 then
      (mkCase "fuzz/hit/n8-key0" (stackUIntKey 0 (.cell dictUnsigned8) 8) rawUGETOPTREF, rng1)
    else if shape = 1 then
      (mkCase "fuzz/hit/n8-key7" (stackUIntKey 7 (.cell dictUnsigned8) 8) rawUGETOPTREF, rng1)
    else if shape = 2 then
      (mkCase "fuzz/hit/n8-key255" (stackUIntKey 255 (.cell dictUnsigned8) 8) rawUGETOPTREF, rng1)
    else if shape = 3 then
      (mkCase "fuzz/hit/n1-key0" (stackUIntKey 0 (.cell dictUnsigned1) 1) rawUGETOPTREF, rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/n1-key1" (stackUIntKey 1 (.cell dictUnsigned1) 1) rawUGETOPTREF, rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/n0-key0" (stackUIntKey 0 (.cell dictUnsigned0) 0) rawUGETOPTREF, rng1)
    else if shape = 6 then
      (mkCase "fuzz/miss/n0-key1" (stackUIntKey 1 (.cell dictUnsigned0) 0) rawUGETOPTREF, rng1)
    else if shape = 7 then
      (mkCase "fuzz/miss/n8-neg-key" (stackUIntKey (-1) (.cell dictUnsigned8) 8) rawUGETOPTREF, rng1)
    else if shape = 8 then
      (mkCase "fuzz/miss/n8-too-large-key" (stackUIntKey 256 (.cell dictUnsigned8) 8) rawUGETOPTREF, rng1)
    else if shape = 9 then
      (mkCase "fuzz/miss/n1-key2" (stackUIntKey 2 (.cell dictUnsigned1) 1) rawUGETOPTREF, rng1)
    else if shape = 10 then
      (mkCase "fuzz/miss/null-dict" (stackUIntKey 7 (.null) 8) rawUGETOPTREF, rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/type-dict-non-cell" (stackUIntKey 7 (.tuple #[]) 8) rawUGETOPTREF, rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-key-non-int" (#[.slice (mkSliceFromBits (natToBits 5 8)), .cell dictUnsigned8, intV 8]) rawUGETOPTREF, rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/type-key-nan" (#[.int .nan, .cell dictUnsigned8, intV 8]) rawUGETOPTREF, rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/nan-n" (#[.cell dictUnsigned8, intV 1, .int .nan]) rawUGETOPTREF, rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/n-negative" (stackUIntKey 0 (.cell dictUnsigned8) (-1)) rawUGETOPTREF, rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/n-over" (stackUIntKey 0 (.cell dictUnsigned8) 1024) rawUGETOPTREF, rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/bad-value-bits" (stackUIntKey 0 (.cell dictSliceValueBad) 8) rawUGETOPTREF, rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/bad-value-bits-ref" (stackUIntKey 1 (.cell dictSliceValueBad2) 8) rawUGETOPTREF, rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/malformed-dict" (stackUIntKey 1 (.cell malformedDict) 8) rawUGETOPTREF, rng1)
    else if shape = 20 then
      let (g, rng') := randBool rng1
      if g then
        (mkCase "fuzz/err/underflow" #[] rawUGETOPTREF, rng')
      else
        (mkCase "fuzz/err/underflow-alt" underflowTwoStack rawUGETOPTREF, rng')
    else if shape = 21 then
      (mkCase "fuzz/gas/exact-hit" (stackUIntKey 0 (.cell dictUnsigned8) 8) (gasCode dictUGETOPTREFGas rawUGETOPTREF) dictUGETOPTREFGasExact, rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/exact-minus-one-hit" (stackUIntKey 0 (.cell dictUnsigned8) 8) (gasCode (dictUGETOPTREFGas - 1) rawUGETOPTREF) dictUGETOPTREFGasMinusOne, rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/exact-zero-width" (stackUIntKey 0 (.cell dictUnsigned0) 0) (gasCode dictUGETOPTREFGas rawUGETOPTREF) dictUGETOPTREFGasExact, rng1)
    else if shape = 24 then
      (mkCase "fuzz/decode-adjacent/raw-setget" (stackUIntKey 255 (.cell dictUnsigned8) 8) rawSetGetOPTREFUInt, rng1)
    else
      (mkCase "fuzz/bounds-truncated" (stackUIntKey 0 (.cell dictUnsigned8) 8) rawTruncated8, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := dictUGETOPTREFId
  unit := #[
    { name := "unit/assembler/reject-raw-getoptref"
      run := do
        assembleInvOpcode "dictgetoptref/uint" dictUGETOPTREF
    },
    { name := "unit/decode/raw-family"
      run := do
        let stream : Slice :=
          Slice.ofCell <|
            Cell.mkOrdinary
              (rawUGETOPTREFSlice.bits ++ rawUGETOPTREFInt.bits ++ rawUGETOPTREF.bits ++
                rawSetGetOPTREF.bits ++ rawSetGetOPTREFInt.bits ++ rawSetGetOPTREFUInt.bits)
              (rawUGETOPTREFSlice.refs ++ rawUGETOPTREFInt.refs ++ rawUGETOPTREF.refs ++
                rawSetGetOPTREF.refs ++ rawSetGetOPTREFInt.refs ++ rawSetGetOPTREFUInt.refs)
        let s1 ← expectDecodeStep "decode/f469" stream (.dictExt (.getOptRef false false)) 16
        let s2 ← expectDecodeStep "decode/f46a" s1 (.dictExt (.getOptRef true false)) 16
        let _ ← expectDecodeStep "decode/f46b" s2 (.dictExt (.getOptRef true true)) 16
        pure ()
    },
    { name := "unit/decode/bounds-and-truncation"
      run := do
        match decodeCp0WithBits (Slice.ofCell rawUGETOPTREFFollowing) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/f46c expected failure")
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated-8 expected failure")
    }
  ]
  oracle := #[
    -- [B1][B3][B4][B5][B6][B7]
    mkCase "ok/hit/n8-key0" (stackUIntKey 0 (.cell dictUnsigned8) 8) rawUGETOPTREF,
    -- [B1][B3][B4][B5][B6][B7]
    mkCase "ok/hit/n8-key7" (stackUIntKey 7 (.cell dictUnsigned8) 8) rawUGETOPTREF,
    -- [B1][B3][B4][B5][B6][B7]
    mkCase "ok/hit/n8-key255" (stackUIntKey 255 (.cell dictUnsigned8) 8) rawUGETOPTREF,
    -- [B1][B3][B4][B5][B6][B7]
    mkCase "ok/hit/n1-key0" (stackUIntKey 0 (.cell dictUnsigned1) 1) rawUGETOPTREF,
    -- [B1][B3][B4][B5][B6][B7]
    mkCase "ok/hit/n1-key1" (stackUIntKey 1 (.cell dictUnsigned1) 1) rawUGETOPTREF,
    -- [B1][B3][B4][B5][B6][B7]
    mkCase "ok/hit/n0-key0" (stackUIntKey 0 (.cell dictUnsigned0) 0) rawUGETOPTREF,
    -- [B1][B3][B6][B7]
    mkCase "ok/miss/n0-key1" (stackUIntKey 1 (.cell dictUnsigned0) 0) rawUGETOPTREF,
    -- [B1][B3][B5][B6][B7]
    mkCase "ok/miss/n8-neg-key" (stackUIntKey (-1) (.cell dictUnsigned8) 8) rawUGETOPTREF,
    -- [B1][B3][B5][B6][B7]
    mkCase "ok/miss/n8-too-large-key" (stackUIntKey 256 (.cell dictUnsigned8) 8) rawUGETOPTREF,
    -- [B1][B3][B5][B6][B7]
    mkCase "ok/miss/n1-key2" (stackUIntKey 2 (.cell dictUnsigned1) 1) rawUGETOPTREF,
    -- [B1][B3][B5][B6][B7]
    mkCase "ok/miss/null-dict" (stackUIntKey 7 (.null) 8) rawUGETOPTREF,
    -- [B1][B2][B10]
    mkCase "err/underflow-empty" #[] rawUGETOPTREF,
    -- [B1][B2][B10]
    mkCase "err/underflow-one" underflowOneStack rawUGETOPTREF,
    -- [B1][B2][B10]
    mkCase "err/underflow-two" underflowTwoStack rawUGETOPTREF,
    -- [B1][B4][B10]
    mkCase "err/type-dict-non-cell" (stackUIntKey 7 (.tuple #[]) 8) rawUGETOPTREF,
    -- [B1][B5][B10]
    mkCase "err/type-key-non-int" (#[.slice (mkSliceFromBits (natToBits 5 8)), .cell dictUnsigned8, intV 8]) rawUGETOPTREF,
    -- [B1][B5][B10]
    mkCase "err/type-key-nan" (#[.int .nan, .cell dictUnsigned8, intV 8]) rawUGETOPTREF,
    -- [B1][B5][B10]
    mkCase "err/nan-n" (#[.cell dictUnsigned8, intV 1, .int .nan]) rawUGETOPTREF,
    -- [B1][B3][B10]
    mkCase "err/type-n-non-int" (#[.cell dictUnsigned8, .slice (mkSliceFromBits (natToBits 1 8)), intV 8]) rawUGETOPTREF,
    -- [B1][B3][B10]
    mkCase "err/range-n-negative" (stackUIntKey 0 (.cell dictUnsigned8) (-1)) rawUGETOPTREF,
    -- [B1][B3][B10]
    mkCase "err/range-n-over" (stackUIntKey 0 (.cell dictUnsigned8) 1024) rawUGETOPTREF,
    -- [B1][B8]
    mkCase "err/dict-value-bad-bits" (stackUIntKey 0 (.cell dictSliceValueBad) 8) rawUGETOPTREF,
    -- [B1][B8]
    mkCase "err/dict-value-bad-ref" (stackUIntKey 1 (.cell dictSliceValueBad2) 8) rawUGETOPTREF,
    -- [B1][B9]
    mkCase "err/dict-malformed" (stackUIntKey 1 (.cell malformedDict) 8) rawUGETOPTREF,
    -- [B1][B11]
    mkCase "err/decode/f46c" (stackUIntKey 0 (.cell dictUnsigned8) 8) rawUGETOPTREFFollowing,
    -- [B1][B11]
    mkCase "err/decode/truncated-8" (stackUIntKey 0 (.cell dictUnsigned8) 8) rawTruncated8,
    -- [B12]
    mkCase "gas/exact-hit" (stackUIntKey 0 (.cell dictUnsigned8) 8) (gasCode dictUGETOPTREFGas rawUGETOPTREF) dictUGETOPTREFGasExact,
    -- [B12]
    mkCase "gas/exact-minus-one" (stackUIntKey 0 (.cell dictUnsigned8) 8)
      (gasCode (dictUGETOPTREFGas - 1) rawUGETOPTREF) dictUGETOPTREFGasMinusOne,
    -- [B12]
    mkCase "gas/exact-hit-zero-width" (stackUIntKey 0 (.cell dictUnsigned0) 0)
      (gasCode dictUGETOPTREFGas rawUGETOPTREF) dictUGETOPTREFGasExact,
    -- [B12]
    mkCase "gas/exact-minus-one-zero-width" (stackUIntKey 0 (.cell dictUnsigned0) 0)
      (gasCode (dictUGETOPTREFGas - 1) rawUGETOPTREF) dictUGETOPTREFGasMinusOne,
    -- [B11]
    mkCase "err/raw/adjacent-slice" (stackUIntKey 255 (.cell dictUnsigned8) 8) rawUGETOPTREFSlice,
    -- [B11]
    mkCase "err/raw/adjacent-int" (stackUIntKey 255 (.cell dictUnsigned8) 8) rawUGETOPTREFInt,
    -- [B10]
    mkCase "err/raw/adjacent-setget" (stackUIntKey 255 (.cell dictUnsigned8) 8) rawSetGetOPTREF,
    -- [B10]
    mkCase "err/raw/adjacent-setget-uint" (stackUIntKey 255 (.cell dictUnsigned8) 8) rawSetGetOPTREFUInt
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictUGETOPTREFId
      count := 500
      gen := genDICTUGETOPTREF
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETOPTREF
