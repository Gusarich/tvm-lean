import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTMAXREF

/-!
INSTRUCTION: DICTMAXREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path.
   `execInstrDict` forwards only `.dictGetMinMax` into this handler; all other opcodes fall through to `next`.

2. [B2] Runtime preamble / type checks.
   `checkUnderflow 2` and `popNatUpTo 1023` require a dictionary reference and width `n` in bounds.
   `NaN`, negative width and `1024` must raise `rangeChk` before any dictionary traversal.

3. [B3] Dictionary miss path.
   `null` root or non-matching key space returns no value and pushes only false (`0`).

4. [B4] Hit path and output typing.
   On hit, the handler pushes `(ref cell, key slice, -1)` in that order.
   Key output is produced as a `Slice` for non-`I`/non-`U` mode (DICTMAXREF) and must match dictionary key bits.

5. [B5] Key payload ordering and boundary widths.
   Max selection is taken with max-mode (`args&8`) and uses ordering consistent with `invertFirst = true` for this variant.
   Valid boundary widths include `0`, `1`, `8` and `16`; width `1023` is valid and `0`/`1` are meaningful edge widths.

6. [B6] By-ref shape and structural dictionary errors.
   `byRef` hit succeeds only for a value slice with `bitsRemaining = 0` and `refsRemaining = 1`.
   Malformed value shapes (`0` refs, non-empty bits, or >1 ref) and malformed dictionary roots raise `.dictErr`.

7. [B7] Assembler validation.
   `ExecInstr.dictGetMinMax 11` is valid and encodes to `0xF48B`.
   `dictGetMinMax 9` is validly typed but in the gap (`.invOpcode`).
   `dictGetMinMax 33` is outside opcode range (`.rangeChk`).

8. [B8] Decoder boundaries and aliasing.
   Decoding accepts opcodes in `0xF48A..0xF48F` (max-family slice and i/u variants, ref/non-ref).
   Neighbors in adjacent families are tested via successful decode assertions around `F48A..F48F`.
   `0xF489`, `0xF490`, and truncated opcode `0xF4` must fail decode.

9. [B9] Gas accounting.
   There is no extra size-dependent penalty path for this variant: exact base-budget execution succeeds and exact-minus-one fails.
   (If there were no-variable-gas behavior, this branch explicitly documents that there is none.)

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to its branch coverage.
-/

private def suiteId : InstrId := { name := "DICTMAXREF" }

private def instr : Instr := .dictGetMinMax 11

private def raw16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]
private def raw8 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 8) #[]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def gasExact : OracleGasLimits := oracleGasLimitsExact baseGas
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne

private def mkDictRefRoot! (label : String) (n : Nat) (entries : Array (Nat × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits : BitString := natToBits k n
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some r, _, _, _) =>
          root := some r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root while building ref-dict"
      | .error e =>
          panic! s!"{label}: dictSetRefWithCells failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary input"

private def mkDictSliceRoot! (label : String) (n : Nat) (entries : Array (Nat × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits : BitString := natToBits k n
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _, _, _) =>
          root := some r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root while building slice-dict"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary input"

private def keySlice (n : Nat) (k : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits k n) #[])

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def badSliceBits : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0b1 1) #[])
private def badSliceBitsAndOneRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0 0) #[valueA])
private def badSliceTwoRefs : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0 0) #[valueA, valueB])

private def dictNull : Value := .null

private def dictSingle0 : Cell := mkDictRefRoot! "dict-single-0" 0 #[(0, valueA)]
private def dictSingle1 : Cell := mkDictRefRoot! "dict-single-1" 1 #[(1, valueA)]
private def dictSingle8 : Cell := mkDictRefRoot! "dict-single-8" 8 #[(0x7A, valueA)]
private def dictTwo8 : Cell := mkDictRefRoot! "dict-two-8" 8 #[(0x10, valueB), (0xF0, valueA)]
private def dictThree8 : Cell := mkDictRefRoot! "dict-three-8" 8 #[(0x00, valueC), (0x80, valueA), (0xFF, valueB)]
private def dictSingle16 : Cell := mkDictRefRoot! "dict-single-16" 16 #[(0x1234, valueB)]
private def dictTwo16 : Cell := mkDictRefRoot! "dict-two-16" 16 #[(0x0100, valueA), (0xFF00, valueC)]
private def dictSingle1023 : Cell := mkDictRefRoot! "dict-single-1023" 1023 #[(0x0, valueA)]
private def dictSliceSingle8 : Cell :=
  mkDictSliceRoot! "dict-slice-single-8" 8 #[(0x55, badSliceBits)]
private def dictSliceSingle8TwoRefs : Cell :=
  mkDictSliceRoot! "dict-slice-single-8-two-refs" 8 #[(0x66, badSliceTwoRefs)]
private def dictSliceSingle8OneRefWithBits : Cell :=
  mkDictSliceRoot! "dict-slice-single-8-one-ref" 8 #[(0x77, badSliceBitsAndOneRef)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def rawOpcodeF48A : Cell := raw16 0xF48A
private def rawOpcodeF48B : Cell := raw16 0xF48B
private def rawOpcodeF48C : Cell := raw16 0xF48C
private def rawOpcodeF48D : Cell := raw16 0xF48D
private def rawOpcodeF48E : Cell := raw16 0xF48E
private def rawOpcodeF48F : Cell := raw16 0xF48F
private def rawOpcodeF489 : Cell := raw16 0xF489
private def rawOpcodeF490 : Cell := raw16 0xF490
private def rawOpcodeF4 : Cell := raw8 0xF4

private def fallbackSentinel : Int := 12_345

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

private def runDictMaxRefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV fallbackSentinel)) stack

private def runDictMaxRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat := 16) : IO Unit := do
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

private def genDictMaxRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/miss/null/0" #[dictNull, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/miss/null/1" #[dictNull, intV 1], rng1)
    else if shape = 2 then
      (mkCase "fuzz/miss/null/8" #[dictNull, intV 8], rng1)
    else if shape = 3 then
      (mkCase "fuzz/miss/null/16" #[dictNull, intV 16], rng1)
    else if shape = 4 then
      (mkCase "fuzz/miss/null/1023" #[dictNull, intV 1023], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/single-0" #[.cell dictSingle0, intV 0], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/single-1" #[.cell dictSingle1, intV 1], rng1)
    else if shape = 7 then
      (mkCase "fuzz/hit/single-8" #[.cell dictSingle8, intV 8], rng1)
    else if shape = 8 then
      (mkCase "fuzz/hit/two-8" #[.cell dictTwo8, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/hit/three-8" #[.cell dictThree8, intV 8], rng1)
    else if shape = 10 then
      (mkCase "fuzz/hit/single-16" #[.cell dictSingle16, intV 16], rng1)
    else if shape = 11 then
      (mkCase "fuzz/hit/two-16" #[.cell dictTwo16, intV 16], rng1)
    else if shape = 12 then
      (mkCase "fuzz/hit/mismatch-n16" #[.cell dictSingle8, intV 16], rng1)
    else if shape = 13 then
      (mkCase "fuzz/hit/smaller-width" #[.cell dictSingle16, intV 8], rng1)
    else if shape = 14 then
      (mkCase "fuzz/hit/wider-width" #[.cell dictSingle8, intV 64], rng1)
    else if shape = 15 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 16 then
      (mkCase "fuzz/underflow/one" #[.null], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/n-nan" #[dictNull, .int .nan], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/n-negative" #[dictNull, intV (-1)], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/n-overflow" #[dictNull, intV 1024], rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/root-type" #[.tuple #[], intV 8], rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/root-type-cont" #[.cont (.quit 0), intV 8], rng1)
    else if shape = 22 then
      (mkCase "fuzz/err/malformed-root" #[.cell malformedDict, intV 8], rng1)
    else if shape = 23 then
      (mkCase "fuzz/err/byref-bad-bits" #[.cell dictSliceSingle8, intV 8], rng1)
    else if shape = 24 then
      (mkCase "fuzz/err/byref-bad-refs" #[.cell dictSliceSingle8TwoRefs, intV 8], rng1)
    else if shape = 25 then
      (mkCase "fuzz/err/byref-one-ref-with-bits" #[.cell dictSliceSingle8OneRefWithBits, intV 8], rng1)
    else if shape = 26 then
      (mkRawCase "fuzz/raw/f48a" #[.cell dictSingle0, intV 0] rawOpcodeF48A, rng1)
    else if shape = 27 then
      (mkRawCase "fuzz/raw/f48b" #[.cell dictSingle8, intV 8] rawOpcodeF48B, rng1)
    else if shape = 28 then
      (mkRawCase "fuzz/raw/f48c" #[.cell dictSingle8, intV 8] rawOpcodeF48C, rng1)
    else if shape = 29 then
      (mkRawCase "fuzz/raw/f48f" #[.cell dictSingle8, intV 8] rawOpcodeF48F, rng1)
    else if shape = 30 then
      (mkRawCase "fuzz/raw/f489" #[.cell dictSingle8, intV 8] rawOpcodeF489, rng1)
    else if shape = 31 then
      (mkRawCase "fuzz/raw/f490" #[] rawOpcodeF490, rng1)
    else if shape = 32 then
      (mkRawCase "fuzz/raw/truncated" #[] rawOpcodeF4, rng1)
    else if shape = 33 then
      (mkCase "fuzz/gas/exact"
        #[dictNull, intV 8]
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact baseGas),
        rng1)
    else if shape = 34 then
      (mkCase "fuzz/gas/exact-minus-one"
        #[dictNull, intV 8]
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else
      (mkRawCase "fuzz/raw/f4a" #[.cell dictSingle8, intV 8] rawOpcodeF48A, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDictMaxRefDispatchFallback #[.cell dictSingle8, intV 8] with
        | .ok st =>
            if st == #[.cell dictSingle8, intV 8, intV fallbackSentinel] then
              pure ()
            else
              throw (IO.userError s!"fallback failed: expected {reprStr #[.cell dictSingle8, intV 8, intV fallbackSentinel]}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"fallback failed: {e}")
    },
    { name := "unit/miss/null/0" -- [B3]
      run := do
        expectOkStack "miss-null-0" (runDictMaxRefDirect #[dictNull, intV 0]) #[intV 0]
    },
    { name := "unit/miss/null/8" -- [B3][B6]
      run := do
        expectOkStack "miss-null-8" (runDictMaxRefDirect #[dictNull, intV 8]) #[intV 0]
    },
    { name := "unit/miss/null/1023" -- [B2][B6][B3]
      run := do
        expectOkStack "miss-null-1023" (runDictMaxRefDirect #[dictNull, intV 1023]) #[intV 0]
    },
    { name := "unit/hit/single0" -- [B4]
      run := do
        expectOkStack "hit-single0"
          (runDictMaxRefDirect #[.cell dictSingle0, intV 0])
          #[.cell valueA, .slice (keySlice 0 0), intV (-1)]
    },
    { name := "unit/hit/single8" -- [B4]
      run := do
        expectOkStack "hit-single8"
          (runDictMaxRefDirect #[.cell dictSingle8, intV 8])
          #[.cell valueA, .slice (keySlice 8 0x7A), intV (-1)]
    },
    { name := "unit/hit/two8" -- [B4]
      run := do
        expectOkStack "hit-two8"
          (runDictMaxRefDirect #[.cell dictTwo8, intV 8])
          #[.cell valueA, .slice (keySlice 8 0xF0), intV (-1)]
    },
    { name := "unit/hit/three8" -- [B4]
      run := do
        expectOkStack "hit-three8"
          (runDictMaxRefDirect #[.cell dictThree8, intV 8])
          #[.cell valueB, .slice (keySlice 8 0xFF), intV (-1)]
    },
    { name := "unit/hit/single16" -- [B4][B6]
      run := do
        expectOkStack "hit-single16"
          (runDictMaxRefDirect #[.cell dictSingle16, intV 16])
          #[.cell valueB, .slice (keySlice 16 0x1234), intV (-1)]
    },
    { name := "unit/underflow/empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictMaxRefDirect #[]) .stkUnd
    },
    { name := "unit/underflow/one" -- [B2]
      run := do
        expectErr "underflow-one" (runDictMaxRefDirect #[intV 8]) .stkUnd
    },
    { name := "unit/err/n-nan" -- [B2]
      run := do
        expectErr "n-nan" (runDictMaxRefDirect #[dictNull, .int .nan]) .rangeChk
    },
    { name := "unit/err/n-negative" -- [B2]
      run := do
        expectErr "n-negative" (runDictMaxRefDirect #[dictNull, intV (-1)]) .rangeChk
    },
    { name := "unit/err/n-overflow" -- [B2]
      run := do
        expectErr "n-overflow" (runDictMaxRefDirect #[dictNull, intV 1024]) .rangeChk
    },
    { name := "unit/err/root-type-tuple" -- [B6]
      run := do
        expectErr "root-type-tuple" (runDictMaxRefDirect #[.tuple #[], intV 8]) .typeChk
    },
    { name := "unit/err/root-type-cont" -- [B6]
      run := do
        expectErr "root-type-cont" (runDictMaxRefDirect #[.cont (.quit 0), intV 8]) .typeChk
    },
    { name := "unit/err/malformed-root" -- [B6]
      run := do
        expectErr "malformed-root" (runDictMaxRefDirect #[.cell malformedDict, intV 8]) .cellUnd
    },
    { name := "unit/err/byref-shape-zero" -- [B5]
      run := do
        expectErr "byref-shape-zero" (runDictMaxRefDirect #[.cell dictSliceSingle8, intV 8]) .dictErr
    },
    { name := "unit/err/byref-shape-two-ref" -- [B5]
      run := do
        expectErr "byref-shape-two-ref" (runDictMaxRefDirect #[.cell dictSliceSingle8TwoRefs, intV 8]) .dictErr
    },
    { name := "unit/err/byref-shape-one-ref-bits" -- [B5]
      run := do
        expectOkStack "byref-shape-one-ref-bits"
          (runDictMaxRefDirect #[.cell dictSliceSingle8OneRefWithBits, intV 8])
          #[.cell valueA, .slice (keySlice 8 0x77), intV (-1)]
    },
    { name := "unit/asm/encode-valid" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok cell =>
            if cell.bits != natToBits 0xF48B 16 then
              throw (IO.userError s!"expected 0xF48B, got {cell.bits}")
        | .error e =>
            throw (IO.userError s!"expected assemble success, got {e}")
    },
    { name := "unit/asm/reject-gap" -- [B7]
      run := expectAssembleErr "asm-reject-gap" (.dictGetMinMax 9) .invOpcode
    },
    { name := "unit/asm/reject-range" -- [B7]
      run := expectAssembleErr "asm-reject-range" (.dictGetMinMax 33) .rangeChk
    },
    { name := "unit/decode/valid" -- [B8]
      run := do
        expectDecodeOk "decode-f48a" rawOpcodeF48A (.dictGetMinMax 10)
        expectDecodeOk "decode-f48b" rawOpcodeF48B (.dictGetMinMax 11)
        expectDecodeOk "decode-f48c" rawOpcodeF48C (.dictGetMinMax 12)
        expectDecodeOk "decode-f48d" rawOpcodeF48D (.dictGetMinMax 13)
        expectDecodeOk "decode-f48e" rawOpcodeF48E (.dictGetMinMax 14)
        expectDecodeOk "decode-f48f" rawOpcodeF48F (.dictGetMinMax 15)
    },
    { name := "unit/decode/errors" -- [B8]
      run := do
        expectDecodeErr "decode-invalid-gap" rawOpcodeF489 .invOpcode
        expectDecodeErr "decode-invalid-next" rawOpcodeF490 .invOpcode
        expectDecodeErr "decode-truncated" rawOpcodeF4 .invOpcode
    }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" #[dictNull, intV 0], -- [B3]
    mkCase "oracle/miss/null/1" #[dictNull, intV 1], -- [B3]
    mkCase "oracle/miss/null/8" #[dictNull, intV 8], -- [B3]
    mkCase "oracle/miss/null/16" #[dictNull, intV 16], -- [B3]
    mkCase "oracle/miss/null/1023" #[dictNull, intV 1023], -- [B3]
    mkCase "oracle/miss/null/1024" #[dictNull, intV 1024], -- [B2]
    mkCase "oracle/hit/single0" #[.cell dictSingle0, intV 0], -- [B4]
    mkCase "oracle/hit/single1" #[.cell dictSingle1, intV 1], -- [B4]
    mkCase "oracle/hit/single8" #[.cell dictSingle8, intV 8], -- [B4]
    mkCase "oracle/hit/two8" #[.cell dictTwo8, intV 8], -- [B4]
    mkCase "oracle/hit/three8" #[.cell dictThree8, intV 8], -- [B4]
    mkCase "oracle/hit/single16" #[.cell dictSingle16, intV 16], -- [B4]
    mkCase "oracle/hit/two16" #[.cell dictTwo16, intV 16], -- [B4]
    mkCase "oracle/hit/narrower-width" #[.cell dictTwo16, intV 8], -- [B6]
    mkCase "oracle/hit/wider-width" #[.cell dictSingle8, intV 64], -- [B6]
    mkCase "oracle/hit/single1023" #[.cell dictSingle1023, intV 1023], -- [B4][B6]
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one" #[intV 8], -- [B2]
    mkCase "oracle/err/n-nan" #[dictNull, .int .nan], -- [B2]
    mkCase "oracle/err/n-negative" #[dictNull, intV (-1)], -- [B2]
    mkCase "oracle/err/n-overflow" #[dictNull, intV 1024], -- [B2]
    mkCase "oracle/err/root-tuple" #[.tuple #[], intV 8], -- [B6]
    mkCase "oracle/err/root-cont" #[.cont (.quit 0), intV 8], -- [B6]
    mkCase "oracle/err/malformed-root" #[.cell malformedDict, intV 8], -- [B6]
    mkCase "oracle/err/byref-shape-zero" #[.cell dictSliceSingle8, intV 8], -- [B5]
    mkCase "oracle/err/byref-shape-two-ref" #[.cell dictSliceSingle8TwoRefs, intV 8], -- [B5]
    mkCase "oracle/err/byref-shape-one-ref-bits" #[.cell dictSliceSingle8OneRefWithBits, intV 8], -- [B5]
    mkCase "oracle/asm/encode-valid" #[dictNull, intV 8], -- [B7]
    mkRawCase "oracle/raw/f48a" #[.cell dictSingle0, intV 0] rawOpcodeF48A, -- [B8]
    mkRawCase "oracle/raw/f48b" #[.cell dictSingle8, intV 8] rawOpcodeF48B, -- [B8]
    mkRawCase "oracle/raw/f48c" #[.cell dictSingle16, intV 16] rawOpcodeF48C, -- [B8]
    mkRawCase "oracle/raw/f48d" #[.cell dictSingle16, intV 16] rawOpcodeF48D, -- [B8]
    mkRawCase "oracle/raw/f48e" #[.cell dictSingle16, intV 16] rawOpcodeF48E, -- [B8]
    mkRawCase "oracle/raw/f48f" #[.cell dictSingle16, intV 16] rawOpcodeF48F, -- [B8]
    mkRawCase "oracle/raw/f489" #[.cell dictSingle8, intV 8] rawOpcodeF489, -- [B8]
    mkRawCase "oracle/raw/f490" #[.cell dictSingle8, intV 8] rawOpcodeF490, -- [B8]
    mkRawCase "oracle/raw/truncated-f4" #[] rawOpcodeF4, -- [B8]
    mkCase "oracle/gas/exact" #[dictNull, intV 8]
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (gasExact), -- [B9]
    mkCase "oracle/gas/exact-minus-one" #[dictNull, intV 8]
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (gasExactMinusOne) -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictMaxRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTMAXREF
