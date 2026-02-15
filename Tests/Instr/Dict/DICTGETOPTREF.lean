import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTGETOPTREF

/-
INSTRUCTION: DICTGETOPTREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `.dictExt` branch dispatch in `execInstrDictExt` handles `.getOptRef`; all other
     instructions continue via `next`.

2. [B2] Runtime arity check (`checkUnderflow 3`).
   - Missing at least one of `n`, `D`, or key/`i` must throw `.stkUnd` before any
     typed/numeric branch checks.

3. [B3] `n`-validation branch (`popNatUpTo 1023`).
   - `n = .nan` => `.rangeChk` via `popInt`/`popNatUpTo`.
   - `n < 0` => `.rangeChk` via `popNatUpTo`.
   - `n > 1023` => `.rangeChk` via `popNatUpTo`.
   - `n = 0` is allowed.

4. [B4] Dictionary argument parsing (`popMaybeCell`).
   - `.null` is accepted as no root.
   - non-null values that are not `.cell` or `.null` throw `.typeChk`.

5. [B5] Key encoding path: `intKey = false`.
   - key argument must be `.slice`; insufficient bits for width `n` => `.cellUnd`.
   - slice key present with enough bits extracts `n` bits.

6. [B6] Key encoding path: `intKey = true` (signed/unsigned).
   - `popIntFinite` on invalid integer value throws `.intOv`.
   - `dictKeyBits?` invalid => treated as "not found" and returns `.null`.
   - unsigned and signed bounds differ (`signed`: [-2^(n-1), 2^(n-1)-1],
     `unsigned`: [0, 2^n-1]).

7. [B7] Dictionary lookup branch after key materialization.
   - no root or missing key => pushes `.null`.
   - hit with malformed value representation (`bitsRemaining != 0` or `refsRemaining != 1`)
     => throws `.dictErr`.
   - hit with value slice exactly one ref and no remaining bits => pushes that ref.

8. [B8] Dictionary traversal structural errors.
   - malformed dict payload in root/traversal path throws `.dictErr` before value handling.

9. [B9] Assembler encoding behavior.
   - `.dictExt (.getOptRef ...)` is supported by assembler; `assembleCp0` should succeed.

10. [B10] Decoder behavior.
   - raw opcodes `0xF469`, `0xF46A`, `0xF46B` decode to
     `.dictExt (.getOptRef false false)`, `.dictExt (.getOptRef true false)`, and
     `.dictExt (.getOptRef true true)` respectively.
   - truncated 8-bit sequence must fail with `.invOpcode`.

11. [B11] Gas accounting.
   - Gas is fixed budget for this opcode path in this model (`computeExactGasBudget`
     via the fixed instruction gas model for this opcode family.
   - No variable gas adjustments are observable in this instruction body.
   - Need exact-gas success and exact-1 fail via explicit `PUSHINT; SETGASLIMIT` wrappers.

TOTAL BRANCHES: 11

Assembler/gas notes:
- No variable gas penalty per runtime branch is modeled for this suite.
- Assembler coverage should include encode+decode roundtrip, plus decoder checks for
  raw opcode boundaries.
-/

private def suiteId : InstrId :=
  { name := "DICTGETOPTREF" }

private def dictGetOptRef : Instr :=
  .dictExt (.getOptRef false false)

private def dictGetOptRefInt : Instr :=
  .dictExt (.getOptRef true false)

private def dictGetOptRefUInt : Instr :=
  .dictExt (.getOptRef true true)

private def rawGetOptRef : Cell := Cell.mkOrdinary (natToBits 0xF469 16) #[]
private def rawGetOptRefInt : Cell := Cell.mkOrdinary (natToBits 0xF46A 16) #[]
private def rawGetOptRefUInt : Cell := Cell.mkOrdinary (natToBits 0xF46B 16) #[]

private def rawSetGetOptRef : Cell := Cell.mkOrdinary (natToBits 0xF46D 16) #[]
private def rawSetGetOptRefInt : Cell := Cell.mkOrdinary (natToBits 0xF46E 16) #[]
private def rawSetGetOptRefUInt : Cell := Cell.mkOrdinary (natToBits 0xF46F 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def mkGasPrefix (gas : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gas), .tonEnvOp .setGasLimit ] with
  | .ok c => c
  | .error e => panic! s!"failed to assemble gas prefix for DICTGETOPTREF: {reprStr e}"

private def gasCode (gas : Int) (opcode : Cell) : Cell :=
  Cell.mkOrdinary ((mkGasPrefix gas).bits ++ opcode.bits) ((mkGasPrefix gas).refs ++ opcode.refs)

private def assembleOk16 (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c => do
      let rest ← expectDecodeStep label (Slice.ofCell c) instr 16
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected no trailing bits")
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {reprStr e}")

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

private def mkDictSetSliceRoot! (label : String) (n : Nat) (unsigned : Bool) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n unsigned with
        | some b => b
        | none => panic! s!"{label}: out-of-range key for dict set ({k}, n={n})"
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
private def badValueSliceBitsAndRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[valueA])

private def dictSigned8 : Cell :=
  mkDictSetRefRoot! "DICTGETOPTREF dictSigned8" 8 false #[(0, valueA), (-1, valueB), (7, valueC)]

private def dictUnsigned8 : Cell :=
  mkDictSetRefRoot! "DICTGETOPTREF dictUnsigned8" 8 true #[(0, valueA), (7, valueB), (255, valueC)]

private def dictZero : Cell :=
  mkDictSetRefRoot! "DICTGETOPTREF dictZero" 0 false #[(0, valueA)]

private def dictSlice : Cell :=
  mkDictSetRefRoot! "DICTGETOPTREF dictSlice" 8 false #[(1, valueA), (2, valueB)]

private def dictSliceValueBad : Cell :=
  mkDictSetSliceRoot! "DICTGETOPTREF dictSliceValueBad" 8 false #[(1, badValueSliceBits)]

private def dictSliceValueBad2 : Cell :=
  mkDictSetSliceRoot! "DICTGETOPTREF dictSliceValueBad2" 8 false #[(2, badValueSliceBitsAndRef)]

private def malformedDict : Cell :=
  Cell.mkOrdinary (natToBits 0xF 4) #[]

private def getOptRefGas : Int :=
  computeExactGasBudget dictGetOptRef

private def getOptRefGasExact : OracleGasLimits :=
  oracleGasLimitsExact getOptRefGas

private def getOptRefGasMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne getOptRefGas

private def stackIntKey (key : Int) (dictValue : Value) (n : Int) : Array Value :=
  #[intV key, dictValue, intV n]

private def stackSliceKey (keyBits : BitString) (dictValue : Value) (n : Int) : Array Value :=
  #[.slice (mkSliceFromBits keyBits), dictValue, intV n]

private def underflowOneStack : Array Value :=
  #[] |>.push (.slice (mkSliceFromBits (natToBits 1 8)))

private def underflowTwoStack : Array Value :=
  #[] |>.push (.slice (mkSliceFromBits (natToBits 1 8)) ) |>.push (.cell dictSigned8)

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := #[]
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDictGetOptRefFuzz (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/slice/hit/one" (stackSliceKey (natToBits 1 8) (.cell dictSlice) 8) rawGetOptRef, rng1)
    else if shape = 1 then
      (mkCase "fuzz/slice/hit/two" (stackSliceKey (natToBits 2 8) (.cell dictSlice) 8) rawGetOptRef, rng1)
    else if shape = 2 then
      (mkCase "fuzz/int/signed/hit-0" (stackIntKey 0 (.cell dictSigned8) 8) rawGetOptRefInt, rng1)
    else if shape = 3 then
      (mkCase "fuzz/int/signed/hit-neg-1" (stackIntKey (-1) (.cell dictSigned8) 8) rawGetOptRefInt, rng1)
    else if shape = 4 then
      (mkCase "fuzz/int/signed/hit-7" (stackIntKey 7 (.cell dictSigned8) 8) rawGetOptRefInt, rng1)
    else if shape = 5 then
      (mkCase "fuzz/int/unsigned/hit-0" (stackIntKey 0 (.cell dictUnsigned8) 8) rawGetOptRefUInt, rng1)
    else if shape = 6 then
      (mkCase "fuzz/int/unsigned/hit-255" (stackIntKey 255 (.cell dictUnsigned8) 8) rawGetOptRefUInt, rng1)
    else if shape = 7 then
      (mkCase "fuzz/int/signed/n0-hit" (stackIntKey 0 (.cell dictZero) 0) rawGetOptRefInt, rng1)
    else if shape = 8 then
      (mkCase "fuzz/int/unsigned/n0-hit" (stackIntKey 0 (.cell dictZero) 0) rawGetOptRefUInt, rng1)
    else if shape = 9 then
      (mkCase "fuzz/miss/int/signed-oob-neg" (stackIntKey 7 (.cell dictSigned8) 8) rawGetOptRefInt, rng1)
    else if shape = 10 then
      (mkCase "fuzz/miss/int/unsigned-neg-key" (stackIntKey (-1) (.cell dictUnsigned8) 8) rawGetOptRefUInt, rng1)
    else if shape = 11 then
      (mkCase "fuzz/miss/int/zero-width-mismatch" (stackIntKey 1 (.cell dictZero) 0) rawGetOptRefInt, rng1)
    else if shape = 12 then
      (mkCase "fuzz/miss/slice-width-mismatch" (stackSliceKey (natToBits 1 4) (.cell dictSlice) 8) rawGetOptRef, rng1)
    else if shape = 13 then
      (mkCase "fuzz/miss/null-dict" (stackSliceKey (natToBits 8 8) .null 8) rawGetOptRef, rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/type-dict" (stackIntKey 0 (.int (.num 7)) 8) rawGetOptRefInt, rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/type-key" (#[.int (.num 1), .cell dictSigned8, intV 8]) rawGetOptRef, rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-key-int" (#[.slice (mkSliceFromBits (natToBits 1 8)), .cell dictSigned8, intV 8]) rawGetOptRefInt, rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/intkey-nan" (#[(.int .nan), .cell dictSigned8, intV 8]) rawGetOptRefInt, rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/key-too-short" (stackSliceKey (natToBits 1 4) (.cell dictSigned8) 8) rawGetOptRef, rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/bad-value-bits" (stackSliceKey (natToBits 1 8) (.cell dictSliceValueBad) 8) rawGetOptRef, rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/bad-value-bits-ref" (stackSliceKey (natToBits 2 8) (.cell dictSliceValueBad2) 8) rawGetOptRef, rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/malformed-dict" (stackSliceKey (natToBits 1 8) (.cell malformedDict) 8) rawGetOptRef, rng1)
    else
      (mkCase "fuzz/err/underflow" (stackSliceKey (natToBits 1 8) (.cell dictSigned8) 8) rawGetOptRef, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def genDICTGETOPTREF (rng0 : StdGen) : OracleCase × StdGen :=
  let (mode, rng1) := randNat rng0 0 7
  let (case0, rng2) :=
    if mode = 0 then
      genDictGetOptRefFuzz rng1
    else if mode = 1 then
      let (g, rng) := randBool rng1
      if g then
        (mkCase "fuzz/gas/exact" (stackSliceKey (natToBits 1 8) (.cell dictSlice) 8) (gasCode getOptRefGas rawGetOptRef)
          getOptRefGasExact, rng)
      else
        (mkCase "fuzz/gas/exact-minus-one" (stackSliceKey (natToBits 1 8) (.cell dictSlice) 8) (gasCode (getOptRefGas - 1) rawGetOptRef)
          getOptRefGasMinusOne, rng)
    else if mode = 2 then
      (mkCase "fuzz/type/intkey-unsigned-nan" (#[.int .nan, .cell dictUnsigned8, intV 8]) rawGetOptRefUInt, rng1)
    else if mode = 3 then
      (mkCase "fuzz/type/nan-n" (#[.int (.num 7), .cell dictSigned8, .int .nan]) rawGetOptRefInt, rng1)
    else if mode = 4 then
      (mkCase "fuzz/err/range-n-negative" (stackIntKey 0 (.cell dictUnsigned8) (-1)) rawGetOptRefUInt, rng1)
    else if mode = 5 then
      (mkCase "fuzz/err/range-n-large" (stackIntKey 0 (.cell dictUnsigned8) 1024) rawGetOptRefUInt, rng1)
    else if mode = 6 then
      (mkCase "fuzz/gas/int-decoder" (stackIntKey (-1) (.cell dictZero) 0) (gasCode getOptRefGas rawGetOptRefInt)
        getOptRefGasExact, rng1)
    else
      (mkCase "fuzz/gas/setgetref-raw-compat" (stackIntKey 0 (.cell dictSlice) 8) rawSetGetOptRef, rng1)
  (case0, rng2)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/assembler/encode-getoptref" 
      run := do
        assembleOk16 "dictgetoptref/nokey" dictGetOptRef
    },
    { name := "unit/assembler/encode-getoptref-int" 
      run := do
        assembleOk16 "dictgetoptref/int" dictGetOptRefInt
    },
    { name := "unit/assembler/encode-getoptref-uint" 
      run := do
        assembleOk16 "dictgetoptref/uint" dictGetOptRefUInt
    },
    { name := "unit/decode/raw-family" 
      run := do
        let stream : Slice :=
          Slice.ofCell <|
            Cell.mkOrdinary
              (rawGetOptRef.bits ++ rawGetOptRefInt.bits ++ rawGetOptRefUInt.bits ++
                rawSetGetOptRef.bits ++ rawSetGetOptRefInt.bits ++ rawSetGetOptRefUInt.bits)
              (rawGetOptRef.refs ++ rawGetOptRefInt.refs ++ rawGetOptRefUInt.refs ++
                rawSetGetOptRef.refs ++ rawSetGetOptRefInt.refs ++ rawSetGetOptRefUInt.refs)
        let s1 ← expectDecodeStep "decode/f469" stream (.dictExt (.getOptRef false false)) 16
        let s2 ← expectDecodeStep "decode/f46a" s1 (.dictExt (.getOptRef true false)) 16
        let s3 ← expectDecodeStep "decode/f46b" s2 (.dictExt (.getOptRef true true)) 16
        let s4 ← expectDecodeStep "decode/f46d" s3 (.dictExt (.setGetOptRef false false)) 16
        let s5 ← expectDecodeStep "decode/f46e" s4 (.dictExt (.setGetOptRef true false)) 16
        let _ ← expectDecodeStep "decode/f46f" s5 (.dictExt (.setGetOptRef true true)) 16
        pure ()
    },
    { name := "unit/decode/truncated-8-bit" 
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated expected failure")
    }
  ]
  oracle := #[
    -- [B1][B3][B6]
    mkCase "ok/slice-key-hit/one" (stackSliceKey (natToBits 1 8) (.cell dictSlice) 8) rawGetOptRef,
    -- [B1][B3]
    mkCase "ok/slice-key-hit/two" (stackSliceKey (natToBits 2 8) (.cell dictSlice) 8) rawGetOptRef,
    -- [B1][B3][B4]
    mkCase "ok/intkey-signed-hit-0" (stackIntKey 0 (.cell dictSigned8) 8) rawGetOptRefInt,
    -- [B1][B3][B4]
    mkCase "ok/intkey-signed-hit-minus1" (stackIntKey (-1) (.cell dictSigned8) 8) rawGetOptRefInt,
    -- [B1][B3][B4]
    mkCase "ok/intkey-signed-hit-7" (stackIntKey 7 (.cell dictSigned8) 8) rawGetOptRefInt,
    -- [B1][B6]
    mkCase "ok/intkey-unsigned-hit-0" (stackIntKey 0 (.cell dictUnsigned8) 8) rawGetOptRefUInt,
    -- [B1][B6]
    mkCase "ok/intkey-unsigned-hit-255" (stackIntKey 255 (.cell dictUnsigned8) 8) rawGetOptRefUInt,
    -- [B4][B7]
    mkCase "ok/intkey-signed-bool-hit-n0" (stackIntKey 0 (.cell dictZero) 0) rawGetOptRefInt,
    -- [B4][B7]
    mkCase "ok/intkey-unsigned-hit-n0" (stackIntKey 0 (.cell dictZero) 0) rawGetOptRefUInt,
    -- [B2][B3]
    mkCase "ok/intkey-signed-miss-too-large-positive" (stackIntKey 8 (.cell dictSigned8) 8) rawGetOptRefInt,
    -- [B2][B4]
    mkCase "ok/intkey-unsigned-miss-negative" (stackIntKey (-1) (.cell dictUnsigned8) 8) rawGetOptRefUInt,
    -- [B2][B4]
    mkCase "ok/intkey-unsigned-miss-overwidth" (stackIntKey 256 (.cell dictUnsigned8) 8) rawGetOptRefUInt,
    -- [B2]
    mkCase "ok/slice-key-miss-width-mismatch" (stackSliceKey (natToBits 9 4) (.cell dictSlice) 8) rawGetOptRef,
    -- [B2][B3]
    mkCase "ok/slice-key-miss-null" (stackSliceKey (natToBits 1 8) .null 8) rawGetOptRef,
    -- [B2]
    mkCase "ok/intkey-non-representable-n1" (stackIntKey 1 (.cell dictZero) 1) rawGetOptRefInt,
    -- [B2]
    mkCase "ok/intkey-unsigned-non-representable-n0" (stackIntKey 1 (.cell dictZero) 0) rawGetOptRefUInt,
    -- [B8]
    mkCase "ok/raw-uint-hit-alias-check" (stackIntKey 255 (.cell dictUnsigned8) 8) rawGetOptRefUInt,
    -- [B5][B8]
    mkCase "ok/raw-int-hit-narrow" (stackIntKey 0 (.cell dictZero) 0) rawGetOptRefInt,
    -- [B2][B4]
    mkCase "ok/miss/raw-setget-ref" (stackIntKey 7 (.cell dictSlice) 8) rawSetGetOptRef,
    -- [B5][B10]
    mkCase "err/underflow-empty" #[] rawGetOptRef,
    -- [B5][B10]
    mkCase "err/underflow-one" underflowOneStack rawGetOptRef,
    -- [B5][B10]
    mkCase "err/underflow-two" underflowTwoStack rawGetOptRef,
    -- [B10]
    mkCase "err/type-non-int-n" (#[.cell dictSigned8, .cell dictSigned8, .tuple #[]]) rawGetOptRefInt,
    -- [B4][B10]
    mkCase "err/type-dict-non-cell" (#[.slice (mkSliceFromBits (natToBits 1 8)), .tuple #[], intV 8]) rawGetOptRef,
    -- [B4][B10]
    mkCase "err/type-key-non-slice" (#[.int (.num 1), .cell dictSigned8, intV 8]) rawGetOptRef,
    -- [B4][B10]
    mkCase "err/type-key-nan" (#[.int .nan, .cell dictUnsigned8, intV 8]) rawGetOptRefInt,
    -- [B3][B10]
    mkCase "err/range-n-negative" (stackIntKey 0 (.cell dictSigned8) (-1)) rawGetOptRefInt,
    -- [B3][B10]
    mkCase "err/range-n-over" (stackIntKey 0 (.cell dictSigned8) 2048) rawGetOptRefUInt,
    -- [B5]
    mkCase "err/key-too-short" (stackSliceKey (natToBits 1 4) (.cell dictSigned8) 8) rawGetOptRef,
    -- [B6]
    mkCase "err/dicterr-malformed-dict" (stackIntKey 1 (.cell malformedDict) 8) rawGetOptRef,
    -- [B6]
    mkCase "err/dicterr-bad-value-bits" (stackSliceKey (natToBits 1 8) (.cell dictSliceValueBad) 8) rawGetOptRef,
    -- [B6]
    mkCase "err/dicterr-bad-value-bits-with-ref" (stackSliceKey (natToBits 2 8) (.cell dictSliceValueBad2) 8) rawGetOptRef,
    -- [B11]
    mkCase "gas/exact/success-slice" (stackSliceKey (natToBits 1 8) (.cell dictSlice) 8) (gasCode getOptRefGas rawGetOptRef) getOptRefGasExact,
    -- [B11]
    mkCase "gas/exact-minus-one-slice" (stackSliceKey (natToBits 1 8) (.cell dictSlice) 8) (gasCode (getOptRefGas - 1) rawGetOptRef) getOptRefGasMinusOne,
    -- [B11]
    mkCase "gas/exact/intkey" (stackIntKey (-1) (.cell dictSigned8) 8) (gasCode getOptRefGas rawGetOptRefInt) getOptRefGasExact,
    -- [B11]
    mkCase "gas/exact-minus-one/intkey" (stackIntKey (-1) (.cell dictSigned8) 8) (gasCode (getOptRefGas - 1) rawGetOptRefInt) getOptRefGasMinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTGETOPTREF }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTGETOPTREF
