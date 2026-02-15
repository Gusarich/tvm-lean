import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTUMAX

/-!
INSTRUCTION: DICTUMAX

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch path.
   `execInstrDictDictGetMinMax` handles only `.dictGetMinMax`; unrelated opcodes follow `next`.

2. [B2] Preamble checks.
   `checkUnderflow 2` requires both dictionary root and `n`.
   `popNatUpTo 256` rejects NaN, negatives, and values above 256 as `.rangeChk`.

3. [B3] Dictionary root decoding.
   `.null` and `.cell` are accepted by `popMaybeCell`.
   Any other top-of-stack type for root rejects with `.typeChk`.

4. [B4] Miss path.
   `.null` root or non-existent key returns exactly `[0]`.

5. [B5] Hit path.
   For DICTUMAX (`.dictGetMinMax 14`) execution decodes unsigned key and returns
   value slice, unsigned key (`Int`), and success flag `-1`.

6. [B6] Unsigned key widths and boundaries.
   Valid widths include `0`, `1`, `2`, `8`, `16`, `64`, `128`, and `256`.
   Boundary keys are tested for each family.

7. [B7] Malformed dictionary roots.
   Invalid roots can raise dictionary traversal errors (`.cellUnd` in current fixtures).

8. [B8] Assembler constraints.
   `ExecInstr.dictGetMinMax` accepts disjoint args in families:
   `2..7`, `10..15`, `18..23`, `26..31`.
   In-family gaps and `>31` are rejected (`.invOpcode` / `.rangeChk`).

9. [B9] Decoder behavior.
   - `0xF48A..0xF48F` decode to `.dictGetMinMax 10..15`.
   - `0xF488`, `0xF489`, `0xF490`, and truncated streams are `.invOpcode`.

10. [B10] Gas.
    DICTUMAX uses fixed base gas in these paths (no remove/ref cleanup penalty).
    Exact budget should succeed; exact-minus-one budget should fail.

TOTAL BRANCHES: 10
Each oracle test below is tagged [Bn] to branches it exercises.
-/

private def suiteId : InstrId :=
  { name := "DICTUMAX" }

private def dictUMaxInstr : Instr := .dictGetMinMax 14

private def dictUMaxExactGas : Int := computeExactGasBudget dictUMaxInstr

private def dictUMaxExactMinusOneGas : Int :=
  computeExactGasBudgetMinusOne dictUMaxInstr

private def dictUMaxGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictUMaxExactGas

private def dictUMaxGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictUMaxExactMinusOneGas

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def sampleValueA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xA5 8) #[])

private def sampleValueB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x5A 8) #[])

private def sampleValueC : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x77 8) #[])

private def sampleValueD : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xCC 8) #[])

private def sampleSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[Cell.empty])

private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 0 0) #[]

private def malformedDictCell2 : Cell := Cell.mkOrdinary (natToBits 0b111 3) #[]

private def emptyDictCell : Cell := Cell.mkOrdinary (natToBits 0 1) #[]

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid unsigned key={k} for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _, _, _) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root for key={k}, n={n}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed for key={k}, n={n}: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: dictionary construction unexpectedly empty"

private def dictN0 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=0" 0 #[(0, sampleValueA)]

private def dictN1 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=1" 1 #[(0, sampleValueA), (1, sampleValueB)]

private def dictN2 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=2" 2 #[(1, sampleValueA), (2, sampleValueB)]

private def dictN8 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=8" 8 #[(0, sampleValueA), (255, sampleValueB), (127, sampleValueC)]

private def dictN16 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=16" 16 #[(0, sampleValueA), (12345, sampleValueB), (65535, sampleValueC)]

private def dictN64 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=64" 64 #[(1, sampleValueA), (2, sampleValueB), (3, sampleValueC)]

private def dictN128 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=128" 128 #[(7, sampleValueA), (8, sampleValueB)]

private def dictN256 : Cell :=
  mkDictSetSliceRoot! "DICTUMAX/n=256" 256 #[(0, sampleValueA), (255, sampleValueB)]

private def fallbackSentinel : Int := 70_001

private def runDictUMaxDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax (.add) (VM.push (intV fallbackSentinel)) stack

private def runDictUMaxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictUMaxInstr stack

private def expectDecodeOk
    (label : String)
    (cell : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decoder did not consume full cell")
  | .error e =>
      throw (IO.userError s!"{label}: decode expected success, got {e}")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectHitShape (label : String) (res : Except Excno (Array Value)) (expectedKey : Int) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.size != 3 then
        throw (IO.userError s!"{label}: expected 3 stack items, got {st.size}")
      match st[0]?, st[1]?, st[2]? with
      | some (Value.slice _), some (Value.int (IntVal.num k)), some (Value.int (IntVal.num flag)) =>
          if k != expectedKey then
            throw (IO.userError s!"{label}: expected key {expectedKey}, got {k}")
          if flag != -1 then
            throw (IO.userError s!"{label}: expected success flag -1, got {flag}")
      | _, _, _ =>
          throw (IO.userError s!"{label}: unexpected stack shape {reprStr st}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictUMaxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDictUMaxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 30
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/hit/n0" #[.cell dictN0, intV 0]
    else if shape = 1 then
      mkCase "fuzz/hit/n1" #[.cell dictN1, intV 1]
    else if shape = 2 then
      mkCase "fuzz/hit/n2" #[.cell dictN2, intV 2]
    else if shape = 3 then
      mkCase "fuzz/hit/n8" #[.cell dictN8, intV 8]
    else if shape = 4 then
      mkCase "fuzz/hit/n16" #[.cell dictN16, intV 16]
    else if shape = 5 then
      mkCase "fuzz/hit/n64" #[.cell dictN64, intV 64]
    else if shape = 6 then
      mkCase "fuzz/hit/n128" #[.cell dictN128, intV 128]
    else if shape = 7 then
      mkCase "fuzz/hit/n256" #[.cell dictN256, intV 256]
    else if shape = 8 then
      mkCase "fuzz/hit/empty-dict-cell" #[.cell emptyDictCell, intV 8]
    else if shape = 9 then
      mkCase "fuzz/miss/null-n8" #[.null, intV 8]
    else if shape = 10 then
      mkCase "fuzz/miss/empty-dict-root" #[.cell emptyDictCell, intV 16]
    else if shape = 11 then
      mkCase "fuzz/underflow/empty" #[]
    else if shape = 12 then
      mkCase "fuzz/underflow/one" #[intV 8]
    else if shape = 13 then
      mkCase "fuzz/err/nan" #[.null, .int .nan]
    else if shape = 14 then
      mkCase "fuzz/err/negative-n" #[.null, intV (-1)]
    else if shape = 15 then
      mkCase "fuzz/err/too-large-n" #[.null, intV 999]
    else if shape = 16 then
      mkCase "fuzz/err/edge-n" #[.null, intV 257]
    else if shape = 17 then
      mkCase "fuzz/err/root-type-slice" #[.slice sampleSlice, intV 8]
    else if shape = 18 then
      mkCase "fuzz/err/root-type-tuple" #[.tuple #[], intV 8]
    else if shape = 19 then
      mkCase "fuzz/err/root-malformed-1" #[.cell malformedDictCell, intV 8]
    else if shape = 20 then
      mkCase "fuzz/err/root-malformed-2" #[.cell malformedDictCell2, intV 8]
    else if shape = 21 then
      mkCaseCode "fuzz/raw/decode-valid-f48f" #[.null, intV 8] (raw16 0xF48F)
    else if shape = 22 then
      mkCaseCode "fuzz/raw/decode-gap-f488" #[.null, intV 8] (raw16 0xF488)
    else if shape = 23 then
      mkCaseCode "fuzz/raw/decode-gap-f489" #[.null, intV 8] (raw16 0xF489)
    else if shape = 24 then
      mkCaseCode "fuzz/raw/decode-invalid-f4" #[.null, intV 8] (raw8 0xF4)
    else if shape = 25 then
      mkCaseCode "fuzz/raw/decode-invalid-f490" #[.null, intV 8] (raw16 0xF490)
    else if shape = 26 then
      mkCase "fuzz/gas/exact" #[.cell dictN8, intV 8]
        #[.pushInt (.num dictUMaxExactGas), .tonEnvOp .setGasLimit, dictUMaxInstr]
        dictUMaxGasExact
    else if shape = 27 then
      mkCase "fuzz/gas/exact-minus-one" #[.cell dictN8, intV 8]
        #[.pushInt (.num dictUMaxExactMinusOneGas), .tonEnvOp .setGasLimit, dictUMaxInstr]
        dictUMaxGasExactMinusOne
    else if shape = 28 then
      mkCase "fuzz/err/mismatch-n-wide" #[.cell dictN8, intV 16]
    else if shape = 29 then
      mkCase "fuzz/err/mismatch-n-narrow" #[.cell dictN16, intV 8]
    else
      mkCase "fuzz/err/underflow-with-filler" #[]
  ({ name := s!"{case0.name}/{tag}", instr := case0.instr, program := case0.program, codeCell? := case0.codeCell?, initStack := case0.initStack, gasLimits := case0.gasLimits, fuel := case0.fuel }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback"
          (runDictUMaxDispatchFallback #[.cell dictN8, intV 8])
          #[.cell dictN8, intV 8, intV fallbackSentinel]
    },
    { name := "unit/exec/hit/n0" -- [B2][B3][B5]
      run := do
        expectHitShape "hit/n0" (runDictUMaxDirect #[.cell dictN0, intV 0]) 0
    },
    { name := "unit/exec/hit/n1" -- [B2][B3][B5][B6]
      run := do
        expectHitShape "hit/n1" (runDictUMaxDirect #[.cell dictN1, intV 1]) 1
    },
    { name := "unit/exec/hit/n2" -- [B5][B6]
      run := do
        expectHitShape "hit/n2" (runDictUMaxDirect #[.cell dictN2, intV 2]) 2
    },
    { name := "unit/exec/hit/n8" -- [B5][B6]
      run := do
        expectHitShape "hit/n8" (runDictUMaxDirect #[.cell dictN8, intV 8]) 255
    },
    { name := "unit/exec/hit/n16" -- [B6]
      run := do
        expectHitShape "hit/n16" (runDictUMaxDirect #[.cell dictN16, intV 16]) 65535
    },
    { name := "unit/exec/hit/n256" -- [B6]
      run := do
        expectHitShape "hit/n256" (runDictUMaxDirect #[.cell dictN256, intV 256]) 255
    },
    { name := "unit/exec/miss/null" -- [B4]
      run := do
        expectOkStack "miss-null" (runDictUMaxDirect #[.null, intV 8])
          #[intV 0]
    },
    { name := "unit/exec/miss/empty-dict" -- [B4]
      run := do
        expectErr "miss-empty-dict-cell" (runDictUMaxDirect #[.cell emptyDictCell, intV 8]) .cellUnd
    },
    { name := "unit/exec/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictUMaxDirect #[]) .stkUnd
        expectErr "underflow-one" (runDictUMaxDirect #[intV 8]) .stkUnd
    },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "nan" (runDictUMaxDirect #[.null, .int .nan]) .rangeChk
        expectErr "negative" (runDictUMaxDirect #[.null, intV (-1)]) .rangeChk
        expectErr "too-large" (runDictUMaxDirect #[.null, intV 9999]) .rangeChk
        expectErr "edge" (runDictUMaxDirect #[.null, intV 257]) .rangeChk
    },
    { name := "unit/exec/root-type-errors" -- [B3]
      run := do
        expectErr "root-slice" (runDictUMaxDirect #[.slice sampleSlice, intV 8]) .typeChk
        expectErr "root-tuple" (runDictUMaxDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDictUMaxDirect #[.cont (.quit 0), intV 8]) .typeChk
    },
    { name := "unit/exec/malformed-root" -- [B7]
      run := do
        expectErr "malformed-cell" (runDictUMaxDirect #[.cell malformedDictCell, intV 8]) .cellUnd
        expectErr "malformed-cell-2" (runDictUMaxDirect #[.cell malformedDictCell2, intV 8]) .cellUnd
    },
    { name := "unit/asm/ok" -- [B8]
      run := do
        match assembleCp0 [dictUMaxInstr] with
        | .ok c =>
            if c.bits != natToBits 0xF48E 16 then
              throw (IO.userError "assemble encoded wrong opcode for DICTUMAX")
        | .error e =>
            throw (IO.userError s!"assemble failed: {e}")
    },
    { name := "unit/asm/reject-gapped" -- [B8]
      run := do
        expectAssembleErr "assemble-gap-8" (.dictGetMinMax 8) .invOpcode
        expectAssembleErr "assemble-gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "assemble-too-large" (.dictGetMinMax 33) .rangeChk
    },
    { name := "unit/decoder/valid-and-neighbor" -- [B9]
      run := do
        expectDecodeOk "decode-f48a" (raw16 0xF48A) (.dictGetMinMax 10)
        expectDecodeOk "decode-f48e" (raw16 0xF48E) (.dictGetMinMax 14)
        expectDecodeOk "decode-f48f" (raw16 0xF48F) (.dictGetMinMax 15)
    },
    { name := "unit/decoder/errors" -- [B9]
      run := do
        expectDecodeErr "decode-f488" (raw16 0xF488) .invOpcode
        expectDecodeErr "decode-f489" (raw16 0xF489) .invOpcode
        expectDecodeErr "decode-f490" (raw16 0xF490) .invOpcode
        expectDecodeErr "decode-truncated" (raw8 0xF4) .invOpcode
    },
    { name := "unit/exec/gas/exact" -- [B10]
      run := do
        expectHitShape "exact" (runDictUMaxDirect #[.cell dictN8, intV 8]) 255
    }
  ]
  oracle := #[
    mkCase "oracle/hit/n0" #[.cell dictN0, intV 0], -- [B4][B5]
    mkCase "oracle/hit/n1" #[.cell dictN1, intV 1], -- [B4][B5]
    mkCase "oracle/hit/n2" #[.cell dictN2, intV 2], -- [B4][B5]
    mkCase "oracle/hit/n8" #[.cell dictN8, intV 8], -- [B5][B6]
    mkCase "oracle/hit/n16" #[.cell dictN16, intV 16], -- [B5][B6]
    mkCase "oracle/hit/n64" #[.cell dictN64, intV 64], -- [B5][B6]
    mkCase "oracle/hit/n128" #[.cell dictN128, intV 128], -- [B5][B6]
    mkCase "oracle/hit/n256" #[.cell dictN256, intV 256], -- [B5][B6]
    mkCase "oracle/miss/null/n0" #[.null, intV 0], -- [B4]
    mkCase "oracle/miss/null/n1" #[.null, intV 1], -- [B4]
    mkCase "oracle/miss/null/n8" #[.null, intV 8], -- [B4]
    mkCase "oracle/miss/empty-dict-cell" #[.cell emptyDictCell, intV 8], -- [B4]
    mkCase "oracle/miss/empty-dict-diff-n" #[.cell emptyDictCell, intV 16], -- [B4]
    mkCase "oracle/mismatch-key-width-short" #[.cell dictN1, intV 16], -- [B4]
    mkCase "oracle/mismatch-key-width-long" #[.cell dictN8, intV 256], -- [B4]
    mkCase "oracle/underflow-empty" #[], -- [B2]
    mkCase "oracle/underflow-one-item" #[.null], -- [B2]
    mkCase "oracle/err/nan" #[.null, .int .nan], -- [B2]
    mkCase "oracle/err/negative" #[.null, intV (-1)], -- [B2]
    mkCase "oracle/err/too-large" #[.null, intV 999], -- [B2]
    mkCase "oracle/err/edge" #[.null, intV 257], -- [B2]
    mkCase "oracle/root-type-slice" #[.slice sampleSlice, intV 8], -- [B3]
    mkCase "oracle/root-type-tuple" #[.tuple #[], intV 8], -- [B3]
    mkCase "oracle/root-type-cont" #[.cont (.quit 0), intV 8], -- [B3]
    mkCase "oracle/malformed-root-cell" #[.cell malformedDictCell, intV 8], -- [B7]
    mkCase "oracle/malformed-root-cell-2" #[.cell malformedDictCell2, intV 8], -- [B7]
    mkCaseCode "oracle/raw/f48a" #[] (raw16 0xF48A), -- [B9]
    mkCaseCode "oracle/raw/f48e" #[] (raw16 0xF48E), -- [B9]
    mkCaseCode "oracle/raw/f48f" #[] (raw16 0xF48F), -- [B9]
    mkCaseCode "oracle/raw/f488" #[] (raw16 0xF488), -- [B9]
    mkCaseCode "oracle/raw/f489" #[] (raw16 0xF489), -- [B9]
    mkCaseCode "oracle/raw/f4" #[] (raw8 0xF4), -- [B9]
    mkCaseCode "oracle/raw/f490" #[] (raw16 0xF490), -- [B9]
    mkCase "oracle/gas/exact" #[.cell dictN8, intV 8]
      (#[.pushInt (.num dictUMaxExactGas), .tonEnvOp .setGasLimit, dictUMaxInstr])
      dictUMaxGasExact, -- [B10]
    mkCase "oracle/gas/exact-minus-one" #[.cell dictN8, intV 8]
      (#[.pushInt (.num dictUMaxExactMinusOneGas), .tonEnvOp .setGasLimit, dictUMaxInstr])
      dictUMaxGasExactMinusOne -- [B10]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictUMaxFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUMAX
