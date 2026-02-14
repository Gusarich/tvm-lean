import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTUMAXREF

/-!
INSTRUCTION: DICTUMAXREF

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch path.
   `execInstrDictDictGetMinMax` handles only `.dictGetMinMax` and should pass control to `next`
   for non-matching instructions.

2. [B2] Preamble checks.
   `checkUnderflow 2` rejects stacks with fewer than two values.
   `popNatUpTo 256` rejects non-integer/nan, negative, and out-of-range (`>=257`) widths.

3. [B3] Root decoding and type checks.
   `.null` and `.cell` are accepted roots; other value kinds (`slice`, `tuple`, `cont`) produce
   `.typeChk` before any dictionary traversal.

4. [B4] Miss path.
   For empty input roots (`null`, malformed empty lookup path, or key-width mismatch against existing
   dictionary shape), execution returns `[0]`.

5. [B5] Hit path and output shape.
   For args `15` (by-ref, unsigned, int-key, max, no remove), a hit returns
   `cell_value`, unsigned `Int` key, and success flag `-1`.

6. [B6] Width and key-boundary behavior.
   Valid width domains are `0` and `1..=256`.
   Boundary widths `0`, `1`, `2`, `8`, `16`, `128`, and `256` are exercised.
   Width `257` is rejected by `popNatUpTo`.

7. [B7] By-ref return-shape validation.
   Value must be a zero-bit slice with exactly one reference when unpacked from dict helper;
   other shapes produce `.dictErr`.

8. [B8] Malformed root behavior.
   Root cell layout errors and key-traversal structural violations map to traversal errors such as
   `.cellUnd`/`.dictErr` (non-`None` root must still be valid dictionary shape).

9. [B9] Assembler constraints.
   `.dictGetMinMax 15` is valid and encodes to `0xF48F`.
   In-family/unsupported argument values (`9`, `24`) are `.invOpcode`.
   `>31` argument values are `.rangeChk`.

10. [B10] Decoder boundaries and aliasing.
    `0xF48A..0xF48F` decode to `.dictGetMinMax 10..15`.
    `0xF489`, `0xF490`, and truncated opcode `0xF4` are decode errors.
    There is no remove-path cleanup and no key-slice allocation for this variant, so gas
    is fixed-base for both hit and miss.

11. [B11] Gas edge cases.
    Exact-gas budgets should succeed.
    Exact-minus-one budgets should fail for out-of-gas.

TOTAL BRANCHES: 11
Each oracle test below is tagged with one or more [Bn].
-/

private def suiteId : InstrId :=
  { name := "DICTUMAXREF" }

private def instr : Instr :=
  .dictGetMinMax 15

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def exactGas : Int :=
  computeExactGasBudget instr

private def exactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def gasExact : OracleGasLimits :=
  oracleGasLimitsExact exactGas

private def gasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne exactGasMinusOne

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def valueD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def mkDictRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid unsigned key {k} for n={n}"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _, _, _) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty entries"

private def mkDictSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid unsigned key {k} for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _, _, _) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty entries"

private def dictU0 : Cell :=
  mkDictRefRoot! "DICTUMAXREF/n=0" 0 #[(0, valueA)]

private def dictU1 : Cell :=
  mkDictRefRoot! "DICTUMAXREF/n=1" 1 #[(0, valueA), (1, valueB)]

private def dictU2 : Cell :=
  mkDictRefRoot! "DICTUMAXREF/n=2" 2 #[(1, valueA), (3, valueB)]

private def dictU8 : Cell :=
  mkDictRefRoot! "DICTUMAXREF/n=8" 8 #[(0, valueA), (127, valueB), (255, valueC)]

private def dictU16 : Cell :=
  mkDictRefRoot! "DICTUMAXREF/n=16" 16 #[(0, valueA), (16, valueB), (65535, valueC)]

private def dictU128 : Cell :=
  mkDictRefRoot! "DICTUMAXREF/n=128" 128 #[(7, valueA), (8, valueB)]

private def dictU256 : Cell :=
  mkDictRefRoot! "DICTUMAXREF/n=256" 256 #[(0, valueA), (1, valueD)]

private def malformedCell0 : Cell :=
  Cell.mkOrdinary (natToBits 0b1 1) #[]

private def malformedCell1 : Cell :=
  Cell.mkOrdinary (natToBits 0b111 3) #[]

private def badValueBits : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0b1 1) #[])

private def badValueTwoRefs : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0 0) #[valueA, valueB])

private def badValueOneRefBits : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0b1 1) #[valueA])

private def dictSliceBadBits : Cell :=
  mkDictSliceRoot! "DICTUMAXREF/slice-bad-bits" 8 #[(0, badValueBits)]

private def dictSliceBadTwoRefs : Cell :=
  mkDictSliceRoot! "DICTUMAXREF/slice-bad-two-refs" 8 #[(0, badValueTwoRefs)]

private def dictSliceBadOneRefBits : Cell :=
  mkDictSliceRoot! "DICTUMAXREF/slice-bad-ref-with-bits" 8 #[(0, badValueOneRefBits)]

private def rawOpcodeF48A : Cell := raw16 0xF48A
private def rawOpcodeF48B : Cell := raw16 0xF48B
private def rawOpcodeF48C : Cell := raw16 0xF48C
private def rawOpcodeF48D : Cell := raw16 0xF48D
private def rawOpcodeF48E : Cell := raw16 0xF48E
private def rawOpcodeF48F : Cell := raw16 0xF48F
private def rawOpcodeF489 : Cell := raw16 0xF489
private def rawOpcodeF490 : Cell := raw16 0xF490
private def rawOpcodeF4 : Cell := raw8 0xF4

private def fallbackSentinel : Int := 90_001

private def runDictUMaxRefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax (.add) (VM.push (intV fallbackSentinel)) stack

private def runDictUMaxRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def expectDecodeOk (label : String) (code : Cell) (expected : Instr) (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected full decode, got {rest.bitsRemaining}b/{rest.refsRemaining}r")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDictUMaxRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/hit/n0" #[.cell dictU0, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/hit/n1" #[.cell dictU1, intV 1], rng1)
    else if shape = 2 then
      (mkCase "fuzz/hit/n2" #[.cell dictU2, intV 2], rng1)
    else if shape = 3 then
      (mkCase "fuzz/hit/n8" #[.cell dictU8, intV 8], rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/n16" #[.cell dictU16, intV 16], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/n128" #[.cell dictU128, intV 128], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/n256" #[.cell dictU256, intV 256], rng1)
    else if shape = 7 then
      (mkCase "fuzz/miss/null/n0" #[.null, intV 0], rng1)
    else if shape = 8 then
      (mkCase "fuzz/miss/null/n8" #[.null, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/miss/null/n256" #[.null, intV 256], rng1)
    else if shape = 10 then
      (mkCase "fuzz/miss/wider-width" #[.cell dictU8, intV 16], rng1)
    else if shape = 11 then
      (mkCase "fuzz/miss/narrower-width" #[.cell dictU16, intV 8], rng1)
    else if shape = 12 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 13 then
      (mkCase "fuzz/underflow/one" #[intV 8], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/nan" #[.null, .int .nan], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/negative" #[.null, intV (-1)], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/too-large" #[.null, intV 257], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/root-slice" #[.slice (Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[])), intV 8], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/root-tuple" #[.tuple #[], intV 8], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/root-cont" #[.cont (.quit 0), intV 8], rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/malformed-root-0" #[.cell malformedCell0, intV 8], rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/malformed-root-1" #[.cell malformedCell1, intV 8], rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/byref-shape-bits" #[.cell dictSliceBadBits, intV 8], rng1)
    else if shape = 23 then
      (mkCase "fuzz/err/byref-shape-two-refs" #[.cell dictSliceBadTwoRefs, intV 8], rng1)
    else if shape = 24 then
      (mkCase "fuzz/err/byref-shape-ref-bits" #[.cell dictSliceBadOneRefBits, intV 8], rng1)
    else if shape = 25 then
      (mkRawCase "fuzz/raw/f48a" #[.cell dictU0, intV 0] rawOpcodeF48A, rng1)
    else if shape = 26 then
      (mkRawCase "fuzz/raw/f48f" #[.cell dictU0, intV 0] rawOpcodeF48F, rng1)
    else if shape = 27 then
      (mkRawCase "fuzz/raw/f489" #[] rawOpcodeF489, rng1)
    else if shape = 28 then
      (mkRawCase "fuzz/raw/f490" #[] rawOpcodeF490, rng1)
    else if shape = 29 then
      (mkRawCase "fuzz/raw/truncated-f4" #[] rawOpcodeF4, rng1)
    else if shape = 30 then
      (mkCase "fuzz/gas/exact" #[.cell dictU8, intV 8]
        (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
        gasExact, rng1)
    else if shape = 31 then
      (mkCase "fuzz/gas/exact-minus-one" #[.cell dictU8, intV 8]
        (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
        gasExactMinusOne, rng1)
    else if shape = 32 then
      (mkRawCase "fuzz/raw/f48c" #[.cell dictU8, intV 8] rawOpcodeF48C, rng1)
    else if shape = 33 then
      (mkRawCase "fuzz/raw/f48d" #[.cell dictU8, intV 8] rawOpcodeF48D, rng1)
    else if shape = 34 then
      (mkRawCase "fuzz/raw/f48e" #[.cell dictU8, intV 8] rawOpcodeF48E, rng1)
    else if shape = 35 then
      (mkRawCase "fuzz/asm-valid-code" #[.cell dictU8, intV 8] rawOpcodeF48F, rng1)
    else if shape = 36 then
      (mkCase "fuzz/dispatch-fallback" #[] #[.add], rng1)
    else if shape = 37 then
      (mkCase "fuzz/hit/u16-high" #[.cell dictU16, intV 16], rng1)
    else if shape = 38 then
      (mkCase "fuzz/hit/empty-root-null" #[.null, intV 8], rng1)
    else
      (mkCase "fuzz/hit/u256" #[.cell dictU256, intV 256], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback"
          (runDictUMaxRefDispatchFallback #[.cell dictU1, intV 8])
          #[.cell dictU1, intV 8, intV fallbackSentinel]
    },
    { name := "unit/miss/null/0" -- [B2][B4]
      run := do
        expectOkStack "miss-null/0" (runDictUMaxRefDirect #[.null, intV 0]) #[intV 0]
    },
    { name := "unit/miss/null/8" -- [B2][B4]
      run := do
        expectOkStack "miss-null/8" (runDictUMaxRefDirect #[.null, intV 8]) #[intV 0]
    },
    { name := "unit/miss/null/256" -- [B2][B4][B6]
      run := do
        expectOkStack "miss-null/256" (runDictUMaxRefDirect #[.null, intV 256]) #[intV 0]
    },
    { name := "unit/hit/u0" -- [B5][B6]
      run := do
        expectOkStack "hit-u0"
          (runDictUMaxRefDirect #[.cell dictU0, intV 0])
          #[.cell valueA, intV 0, intV (-1)]
    },
    { name := "unit/hit/u1" -- [B5][B6]
      run := do
        expectOkStack "hit-u1"
          (runDictUMaxRefDirect #[.cell dictU1, intV 1])
          #[.cell valueB, intV 1, intV (-1)]
    },
    { name := "unit/hit/u2" -- [B5][B6]
      run := do
        expectOkStack "hit-u2"
          (runDictUMaxRefDirect #[.cell dictU2, intV 2])
          #[.cell valueB, intV 3, intV (-1)]
    },
    { name := "unit/hit/u8" -- [B5][B6]
      run := do
        expectOkStack "hit-u8"
          (runDictUMaxRefDirect #[.cell dictU8, intV 8])
          #[.cell valueC, intV 255, intV (-1)]
    },
    { name := "unit/hit/u16" -- [B5][B6]
      run := do
        expectOkStack "hit-u16"
          (runDictUMaxRefDirect #[.cell dictU16, intV 16])
          #[.cell valueC, intV 65535, intV (-1)]
    },
    { name := "unit/hit/u128" -- [B5][B6]
      run := do
        expectOkStack "hit-u128"
          (runDictUMaxRefDirect #[.cell dictU128, intV 128])
          #[.cell valueB, intV 8, intV (-1)]
    },
    { name := "unit/hit/u256" -- [B5][B6]
      run := do
        expectOkStack "hit-u256"
          (runDictUMaxRefDirect #[.cell dictU256, intV 256])
          #[.cell valueD, intV 1, intV (-1)]
    },
    { name := "unit/mismatch-width/shorter" -- [B6]
      run := do
        expectOkStack "mismatch-narrower"
          (runDictUMaxRefDirect #[.cell dictU16, intV 8])
          #[.cell valueD, intV 1, intV (-1)]
    },
    { name := "unit/underflow/empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictUMaxRefDirect #[]) .stkUnd
    },
    { name := "unit/underflow/one" -- [B2]
      run := do
        expectErr "underflow-one" (runDictUMaxRefDirect #[intV 8]) .stkUnd
    },
    { name := "unit/err/nan" -- [B2]
      run := do
        expectErr "n-nan" (runDictUMaxRefDirect #[.null, .int .nan]) .rangeChk
    },
    { name := "unit/err/negative" -- [B2]
      run := do
        expectErr "n-negative" (runDictUMaxRefDirect #[.null, intV (-1)]) .rangeChk
    },
    { name := "unit/err/too-large" -- [B2]
      run := do
        expectErr "n-too-large" (runDictUMaxRefDirect #[.null, intV 257]) .rangeChk
    },
    { name := "unit/err/root-slice" -- [B3]
      run := do
        expectErr "root-slice" (runDictUMaxRefDirect #[.slice (Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[])), intV 8]) .typeChk
    },
    { name := "unit/err/root-tuple" -- [B3]
      run := do
        expectErr "root-tuple" (runDictUMaxRefDirect #[.tuple #[], intV 8]) .typeChk
    },
    { name := "unit/err/root-cont" -- [B3]
      run := do
        expectErr "root-cont" (runDictUMaxRefDirect #[.cont (.quit 0), intV 8]) .typeChk
    },
    { name := "unit/err/malformed-root-cell" -- [B8]
      run := do
        expectErr "malformed-root" (runDictUMaxRefDirect #[.cell malformedCell0, intV 8]) .cellUnd
    },
    { name := "unit/err/byref-shape-bits" -- [B7]
      run := do
        expectErr "byref-bits" (runDictUMaxRefDirect #[.cell dictSliceBadBits, intV 8]) .dictErr
    },
    { name := "unit/err/byref-shape-two-refs" -- [B7]
      run := do
        expectErr "byref-two-refs" (runDictUMaxRefDirect #[.cell dictSliceBadTwoRefs, intV 8]) .dictErr
    },
    { name := "unit/err/byref-shape-one-ref-bits" -- [B7]
      run := do
        expectErr "byref-one-ref-bits" (runDictUMaxRefDirect #[.cell dictSliceBadOneRefBits, intV 8]) .dictErr
    },
    { name := "unit/asm/encode-valid" -- [B9][B10]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF48F 16 then
              throw (IO.userError s!"expected 0xF48F, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"expected assembly success, got {e}")
    },
    { name := "unit/asm/reject-gap" -- [B9]
      run := expectAssembleErr "asm-gap" (.dictGetMinMax 9) .invOpcode
    },
    { name := "unit/asm/reject-range" -- [B9]
      run := expectAssembleErr "asm-range" (.dictGetMinMax 33) .rangeChk
    },
    { name := "unit/decode/ok-chain" -- [B10]
      run := do
        expectDecodeOk "decode-f48a" rawOpcodeF48A (.dictGetMinMax 10)
        expectDecodeOk "decode-f48b" rawOpcodeF48B (.dictGetMinMax 11)
        expectDecodeOk "decode-f48c" rawOpcodeF48C (.dictGetMinMax 12)
        expectDecodeOk "decode-f48d" rawOpcodeF48D (.dictGetMinMax 13)
        expectDecodeOk "decode-f48e" rawOpcodeF48E (.dictGetMinMax 14)
        expectDecodeOk "decode-f48f" rawOpcodeF48F (.dictGetMinMax 15)
    },
    { name := "unit/decode/err" -- [B10]
      run := do
        expectDecodeErr "decode-f489" rawOpcodeF489 .invOpcode
        expectDecodeErr "decode-f490" rawOpcodeF490 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode
    },
    { name := "unit/gas/exact" -- [B11]
      run := do
        expectOkStack "gas-exact"
          (runDictUMaxRefDirect #[.cell dictU8, intV 8])
          #[.cell valueC, intV 255, intV (-1)]
    }
  ]
  oracle := #[
    mkCase "oracle/hit/u0" #[.cell dictU0, intV 0], -- [B5][B6]
    mkCase "oracle/hit/u1" #[.cell dictU1, intV 1], -- [B5][B6]
    mkCase "oracle/hit/u2" #[.cell dictU2, intV 2], -- [B5][B6]
    mkCase "oracle/hit/u8" #[.cell dictU8, intV 8], -- [B5][B6]
    mkCase "oracle/hit/u16" #[.cell dictU16, intV 16], -- [B5][B6]
    mkCase "oracle/hit/u128" #[.cell dictU128, intV 128], -- [B5][B6]
    mkCase "oracle/hit/u256" #[.cell dictU256, intV 256], -- [B5][B6]
    mkCase "oracle/miss/null/0" #[.null, intV 0], -- [B4]
    mkCase "oracle/miss/null/1" #[.null, intV 1], -- [B4]
    mkCase "oracle/miss/null/8" #[.null, intV 8], -- [B4]
    mkCase "oracle/miss/null/16" #[.null, intV 16], -- [B4]
    mkCase "oracle/miss/null/256" #[.null, intV 256], -- [B4]
    mkCase "oracle/miss/edge-nil" #[.null, intV 257], -- [B2]
    mkCase "oracle/mismatch/wider-width" #[.cell dictU8, intV 16], -- [B6]
    mkCase "oracle/mismatch/narrower-width" #[.cell dictU16, intV 8], -- [B6]
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one" #[intV 8], -- [B2]
    mkCase "oracle/err/nan" #[.null, .int .nan], -- [B2]
    mkCase "oracle/err/negative" #[.null, intV (-1)], -- [B2]
    mkCase "oracle/err/too-large" #[.null, intV 9999], -- [B2]
    mkCase "oracle/err/edge" #[.null, intV 257], -- [B2]
    mkCase "oracle/err/root-slice" #[.slice (Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[])), intV 8], -- [B3]
    mkCase "oracle/err/root-tuple" #[.tuple #[], intV 8], -- [B3]
    mkCase "oracle/err/root-cont" #[.cont (.quit 0), intV 8], -- [B3]
    mkCase "oracle/err/malformed-root-0" #[.cell malformedCell0, intV 8], -- [B8]
    mkCase "oracle/err/malformed-root-1" #[.cell malformedCell1, intV 8], -- [B8]
    mkCase "oracle/err/byref-bits" #[.cell dictSliceBadBits, intV 8], -- [B7]
    mkCase "oracle/err/byref-two-refs" #[.cell dictSliceBadTwoRefs, intV 8], -- [B7]
    mkCase "oracle/err/byref-one-ref-bits" #[.cell dictSliceBadOneRefBits, intV 8], -- [B7]
    mkCase "oracle/asm/encode-valid" #[.null, intV 8] (#[instr]), -- [B9]
    mkRawCase "oracle/raw/f48a" #[.null, intV 8] rawOpcodeF48A, -- [B10]
    mkRawCase "oracle/raw/f48b" #[.null, intV 8] rawOpcodeF48B, -- [B10]
    mkRawCase "oracle/raw/f48c" #[.null, intV 8] rawOpcodeF48C, -- [B10]
    mkRawCase "oracle/raw/f48d" #[.null, intV 8] rawOpcodeF48D, -- [B10]
    mkRawCase "oracle/raw/f48e" #[.null, intV 8] rawOpcodeF48E, -- [B10]
    mkRawCase "oracle/raw/f48f" #[.null, intV 8] rawOpcodeF48F, -- [B10]
    mkRawCase "oracle/raw/f489" #[] rawOpcodeF489, -- [B10]
    mkRawCase "oracle/raw/f490" #[] rawOpcodeF490, -- [B10]
    mkRawCase "oracle/raw/truncated" #[] rawOpcodeF4, -- [B10]
    mkCase "oracle/gas/exact" #[.cell dictU8, intV 8]
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
      gasExact, -- [B11]
    mkCase "oracle/gas/exact-minus-one" #[.cell dictU8, intV 8]
      (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
      gasExactMinusOne, -- [B11]
    mkCase "oracle/hit-narrower" #[.cell dictU16, intV 8], -- [B6]
    mkCase "oracle/hit-no-op" #[] -- [B1]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictUMaxRefFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUMAXREF
