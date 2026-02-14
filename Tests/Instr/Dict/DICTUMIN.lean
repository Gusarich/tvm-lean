import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTUMIN

/-!
INSTRUCTION: DICTUMIN

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch path.
   `execInstrDictDictGetMinMax` executes for `.dictGetMinMax`; anything else must fall through
   through `next`.

2. [B2] Runtime precondition checks.
   - `checkUnderflow 2` requires both dictionary root and width `n`.
   - `popNatUpTo 256` enforces unsigned-key width constraints and rejects non-int, NaN, negative,
     and too-large values.

3. [B3] Dictionary root handling.
   - `popMaybeCell` accepts `.null` and `.cell` only.
   - Any other top-of-stack value raises `.typeChk`.

4. [B4] Miss behavior.
   - Empty and missing-key dictionary traversals push `[0]` and do not mutate gas beyond base.

5. [B5] Hit behavior.
   - Valid roots and widths push value slice, unsigned key integer, and success flag `-1`.

6. [B6] Unsigned boundary widths and key decoding.
   - Boundary widths include `0`, `1`, `2`, `8`, `16`, `128`, and `256`.
   - Returned key is `bitsToNat` reconstruction and should preserve unsigned identity.

7. [B7] Width mismatch / malformed-key-depth behavior.
   - Asking for a different `n` than dictionary encoding width is a miss and pushes `0`.
   - Malformed roots can produce traversal errors (`.cellUnd` or `.dictErr`).

8. [B8] Assembler encoding and argument validity.
   - `.dictGetMinMax 6` must assemble to `0xF486`.
   - In-family gaps (`1`, `8`, `24`, etc.) are `.invOpcode`.
   - Out-of-range `args > 31` is `.rangeChk`.

9. [B9] Decoder behavior.
   - `0xF486` and `0xF487` decode to `.dictGetMinMax 6` and `7`.
   - `0xF488`, `0xF489`, `0xF490`, and truncated `0xF4` are decode errors (`.invOpcode`).

10. [B10] Gas accounting.
    This variant has no remove/ref cleanup and no key-slice reconstruction gas.
    Exact budget from `computeExactGasBudget` succeeds; exact-minus-one fails in execution.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it exercises.
-/

private def suiteId : InstrId :=
  { name := "DICTUMIN" }

private def instr : Instr :=
  .dictGetMinMax 6

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none => panic! s!"{label}: invalid unsigned key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _, _, _) =>
          root := r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: empty root after insertion ({k}), n={n}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty input dictionary"

private def valueA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xA5 8) #[])

private def valueB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x5A 8) #[])

private def valueC : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x77 8) #[])

private def valueD : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xC3 8) #[])

private def dict0Root : Cell :=
  mkDictSetSliceRoot! "dict0Root" 0 #[(0, valueA)]

private def dict1Root : Cell :=
  mkDictSetSliceRoot! "dict1Root" 1 #[(0, valueA), (1, valueB)]

private def dict2Root : Cell :=
  mkDictSetSliceRoot! "dict2Root" 2 #[(1, valueA), (2, valueB), (3, valueC)]

private def dict8Root : Cell :=
  mkDictSetSliceRoot! "dict8Root" 8 #[(1, valueA), (5, valueB), (255, valueC)]

private def dict16Root : Cell :=
  mkDictSetSliceRoot! "dict16Root" 16 #[(0x0017, valueA), (0xFFFE, valueD)]

private def dict128Root : Cell :=
  mkDictSetSliceRoot! "dict128Root" 128 #[(2, valueA), (127, valueC)]

private def dict256Root : Cell :=
  mkDictSetSliceRoot! "dict256Root" 256 #[(255, valueD), (1, valueB)]

private def emptyDictCell : Cell :=
  Cell.mkOrdinary (natToBits 0 1) #[]

private def malformedDictCell : Cell :=
  Cell.mkOrdinary (natToBits 0 3) #[]

private def malformedDictCellRefs : Cell :=
  Cell.mkOrdinary (natToBits 0 2) #[Cell.empty]

private def dictUMinGas : Int :=
  computeExactGasBudget instr

private def dictUMinGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def dictUMinGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictUMinGas

private def dictUMinGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictUMinGasMinusOne

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def rawF486 : Cell := raw16 0xF486
private def rawF487 : Cell := raw16 0xF487
private def rawF488 : Cell := raw16 0xF488
private def rawF489 : Cell := raw16 0xF489
private def rawF490 : Cell := raw16 0xF490
private def rawF4 : Cell := raw8 0xF4

private def fallbackSentinel : Int := 99_001

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

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

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
        throw (IO.userError s!"{label}: expected full decode, got {rest.bitsRemaining}b/{rest.refsRemaining}r")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got success {actual}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (ins : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [ins] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def runDictUMinDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax (.add) (VM.push (intV fallbackSentinel)) stack

private def runDictUMinDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def genDictUMINFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 33
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/hit/n0" #[.cell dict0Root, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/hit/n1" #[.cell dict1Root, intV 1], rng1)
    else if shape = 2 then
      (mkCase "fuzz/hit/n2" #[.cell dict2Root, intV 2], rng1)
    else if shape = 3 then
      (mkCase "fuzz/hit/n8" #[.cell dict8Root, intV 8], rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/n16" #[.cell dict16Root, intV 16], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/n128" #[.cell dict128Root, intV 128], rng1)
    else if shape = 6 then
      (mkCase "fuzz/hit/n256" #[.cell dict256Root, intV 256], rng1)
    else if shape = 7 then
      (mkCase "fuzz/miss/null/n0" #[.null, intV 0], rng1)
    else if shape = 8 then
      (mkCase "fuzz/miss/null/n8" #[.null, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/miss/null/n256" #[.null, intV 256], rng1)
    else if shape = 10 then
      (mkCase "fuzz/miss/empty-dict" #[.cell emptyDictCell, intV 8], rng1)
    else if shape = 11 then
      (mkCase "fuzz/preserve-prefix" #[intV 77, .cell dict8Root, intV 8], rng1)
    else if shape = 12 then
      (mkCase "fuzz/miss/underflow/empty" #[], rng1)
    else if shape = 13 then
      (mkCase "fuzz/miss/underflow/one" #[.null], rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/nan" #[.cell dict8Root, .int .nan], rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/negative-n" #[.cell dict8Root, intV (-1)], rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/too-large-n" #[.cell dict8Root, intV 999], rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/root-builder" #[.builder Builder.empty, intV 8], rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/root-tuple" #[.tuple #[], intV 8], rng1)
    else if shape = 19 then
      (mkCase "fuzz/err/root-cont" #[.cont (.quit 0), intV 8], rng1)
    else if shape = 20 then
      (mkCase "fuzz/err/root-malformed-cell" #[.cell malformedDictCell, intV 8], rng1)
    else if shape = 21 then
      (mkCase "fuzz/err/root-malformed-cell-refs" #[.cell malformedDictCellRefs, intV 8], rng1)
    else if shape = 22 then
      (mkCaseCode "fuzz/raw/decode-valid-f486" #[.null, intV 8] rawF486, rng1)
    else if shape = 23 then
      (mkCaseCode "fuzz/raw/decode-valid-f487" #[.null, intV 8] rawF487, rng1)
    else if shape = 24 then
      (mkCaseCode "fuzz/raw/decode-gap-f488" #[.null, intV 8] rawF488, rng1)
    else if shape = 25 then
      (mkCaseCode "fuzz/raw/decode-gap-f489" #[.null, intV 8] rawF489, rng1)
    else if shape = 26 then
      (mkCaseCode "fuzz/raw/decode-gap-f490" #[.null, intV 8] rawF490, rng1)
    else if shape = 27 then
      (mkCaseCode "fuzz/raw/decode-truncated" #[] rawF4, rng1)
    else if shape = 28 then
      (mkCase "fuzz/gas/exact" #[.cell dict8Root, intV 8]
        (#[.pushInt (.num dictUMinGas), .tonEnvOp .setGasLimit, instr])
        dictUMinGasExact, rng1)
    else if shape = 29 then
      (mkCase "fuzz/gas/exact-minus-one" #[.cell dict8Root, intV 8]
        (#[.pushInt (.num dictUMinGasMinusOne), .tonEnvOp .setGasLimit, instr])
        dictUMinGasExactMinusOne, rng1)
    else if shape = 30 then
      (mkCase "fuzz/mismatch-narrow" #[.cell dict8Root, intV 16], rng1)
    else if shape = 31 then
      (mkCase "fuzz/mismatch-wide" #[.cell dict16Root, intV 8], rng1)
    else
      (mkCase "fuzz/error/preserve-prefix" #[.int (.num 99), .cell dict2Root, intV 16], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback-empty"
          (runDictUMinDispatchFallback #[])
          #[.int (.num fallbackSentinel)]
        expectOkStack "fallback-preserve-prefix"
          (runDictUMinDispatchFallback #[.int (.num 77), .cell dict8Root, intV 8])
          #[.int (.num 77), .cell dict8Root, .int (.num fallbackSentinel)] },
    { name := "unit/exec/underflow-and-n-checks" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictUMinDirect #[]) .stkUnd
        expectErr "underflow-one" (runDictUMinDirect #[.null]) .stkUnd
        expectErr "n-non-int" (runDictUMinDirect #[.cell dict8Root, .null]) .typeChk
        expectErr "n-nan" (runDictUMinDirect #[.cell dict8Root, .int .nan]) .rangeChk
        expectErr "n-negative" (runDictUMinDirect #[.cell dict8Root, intV (-1)]) .rangeChk
        expectErr "n-overflow" (runDictUMinDirect #[.cell dict8Root, intV 257]) .rangeChk },
    { name := "unit/exec/root-type" -- [B3]
      run := do
        expectErr "root-builder" (runDictUMinDirect #[.builder Builder.empty, intV 8]) .typeChk
        expectErr "root-tuple" (runDictUMinDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDictUMinDirect #[.cont (.quit 0), intV 8]) .typeChk },
    { name := "unit/exec/hit-and-miss" -- [B4][B5][B6][B7]
      run := do
        expectOkStack "hit/n0" (runDictUMinDirect #[.cell dict0Root, intV 0])
          #[.slice valueA, intV 0, intV (-1)]
        expectOkStack "hit/n1" (runDictUMinDirect #[.cell dict1Root, intV 1])
          #[.slice valueA, intV 0, intV (-1)]
        expectOkStack "hit/n2" (runDictUMinDirect #[.cell dict2Root, intV 2])
          #[.slice valueA, intV 1, intV (-1)]
        expectOkStack "hit/n8" (runDictUMinDirect #[.cell dict8Root, intV 8])
          #[.slice valueA, intV 1, intV (-1)]
        expectOkStack "hit/n16" (runDictUMinDirect #[.cell dict16Root, intV 16])
          #[.slice valueA, intV 0x17, intV (-1)]
        expectOkStack "hit/n128" (runDictUMinDirect #[.cell dict128Root, intV 128])
          #[.slice valueA, intV 2, intV (-1)]
        expectOkStack "hit/n256" (runDictUMinDirect #[.cell dict256Root, intV 256])
          #[.slice valueB, intV 1, intV (-1)]
        expectOkStack "miss/null" (runDictUMinDirect #[.null, intV 8]) #[intV 0]
        expectOkStack "miss-empty" (runDictUMinDirect #[.cell emptyDictCell, intV 8]) #[intV 0]
        expectOkStack "miss/mismatch-wide" (runDictUMinDirect #[.cell dict16Root, intV 8]) #[intV 0]
        expectOkStack "preserve-prefix" (runDictUMinDirect #[.int (.num 77), .cell dict8Root, intV 8])
          #[.int (.num 77), .slice valueA, intV 1, intV (-1)] },
    { name := "unit/exec/malformed" -- [B7]
      run := do
        expectErr "malformed-cell" (runDictUMinDirect #[.cell malformedDictCell, intV 8]) .cellUnd
        expectErr "malformed-cell-refs" (runDictUMinDirect #[.cell malformedDictCellRefs, intV 8]) .cellUnd },
    { name := "unit/asm-decode-valid" -- [B8][B9]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF486 16 then
              throw (IO.userError "DICTUMIN assemble wrong opcode")
        | .error e =>
            throw (IO.userError s!"DICTUMIN assemble failed: {e}")
        expectDecodeOk "decode/f486" rawF486 (.dictGetMinMax 6)
        expectDecodeOk "decode/f487" rawF487 (.dictGetMinMax 7)
        expectDecodeErr "decode/f488" rawF488 .invOpcode
        expectDecodeErr "decode/f489" rawF489 .invOpcode
        expectDecodeErr "decode/f490" rawF490 .invOpcode
        expectDecodeErr "decode-truncated" rawF4 .invOpcode },
    { name := "unit/asm-reject" -- [B8]
      run := do
        expectAssembleErr "assemble-gap-1" (.dictGetMinMax 1) .invOpcode
        expectAssembleErr "assemble-gap-8" (.dictGetMinMax 8) .invOpcode
        expectAssembleErr "assemble-gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "assemble-too-large" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/gas/exact" -- [B10]
      run := do
        expectOkStack "exact" (runDictUMinDirect #[.cell dict8Root, intV 8])
          #[.slice valueA, intV 1, intV (-1)] }
  ]
  oracle := #[
    mkCase "oracle/hit/n0" (#[(.cell dict0Root), intV 0]), -- [B5][B6]
    mkCase "oracle/hit/n1" (#[(.cell dict1Root), intV 1]), -- [B5][B6]
    mkCase "oracle/hit/n2" (#[(.cell dict2Root), intV 2]), -- [B5][B6]
    mkCase "oracle/hit/n8" (#[(.cell dict8Root), intV 8]), -- [B5][B6]
    mkCase "oracle/hit/n16" (#[(.cell dict16Root), intV 16]), -- [B5][B6]
    mkCase "oracle/hit/n128" (#[(.cell dict128Root), intV 128]), -- [B5][B6]
    mkCase "oracle/hit/n256" (#[(.cell dict256Root), intV 256]), -- [B5][B6]
    mkCase "oracle/miss/null/0" (#[(.null), intV 0]), -- [B4]
    mkCase "oracle/miss/null/1" (#[(.null), intV 1]), -- [B4]
    mkCase "oracle/miss/null/8" (#[(.null), intV 8]), -- [B4]
    mkCase "oracle/miss/null/16" (#[(.null), intV 16]), -- [B4]
    mkCase "oracle/miss/null/256" (#[(.null), intV 256]), -- [B4]
    mkCase "oracle/miss/empty" (#[(.cell emptyDictCell), intV 8]), -- [B4]
    mkCase "oracle/miss/mismatch-wide" (#[(.cell dict16Root), intV 8]), -- [B4][B7]
    mkCase "oracle/miss/mismatch-narrow" (#[(.cell dict8Root), intV 16]), -- [B4][B7]
    mkCase "oracle/preserve-prefix-hit" #[intV 77, .cell dict8Root, intV 8], -- [B5]
    mkCase "oracle/preserve-prefix-miss" #[intV 77, .null, intV 8], -- [B4]

    mkCase "oracle/underflow-empty" #[], -- [B2]
    mkCase "oracle/underflow-one" #[(.null)], -- [B2]
    mkCase "oracle/err/type-root" #[.builder Builder.empty, intV 8], -- [B3]
    mkCase "oracle/err/type-non-int" #[.cell dict8Root, .null], -- [B2]
    mkCase "oracle/err/nan" #[.cell dict8Root, .int .nan], -- [B2]
    mkCase "oracle/err/negative-n" #[.cell dict8Root, intV (-1)], -- [B2]
    mkCase "oracle/err/overflow" #[.cell dict8Root, intV 999], -- [B2]
    mkCase "oracle/err/edge-257" #[.cell dict8Root, intV 257], -- [B2]
    mkCase "oracle/err/root-type-slice" #[.slice valueA, intV 8], -- [B3]
    mkCase "oracle/err/root-type-tuple" #[.tuple #[], intV 8], -- [B3]
    mkCase "oracle/err/root-type-cont" #[.cont (.quit 0), intV 8], -- [B3]

    mkCaseCode "oracle/raw/f486" (#[(.null), intV 8] ) rawF486, -- [B9]
    mkCaseCode "oracle/raw/f487" (#[(.null), intV 8] ) rawF487, -- [B9]
    mkCaseCode "oracle/raw/f488-gap" #[] rawF488, -- [B9]
    mkCaseCode "oracle/raw/f489-gap" #[] rawF489, -- [B9]
    mkCaseCode "oracle/raw/f490-gap" #[] rawF490, -- [B9]
    mkCaseCode "oracle/raw/truncated" #[] rawF4, -- [B9]

    mkCase "oracle/malformed-cell" (#[(.cell malformedDictCell), intV 8]), -- [B7]
    mkCase "oracle/malformed-cell-refs" (#[(.cell malformedDictCellRefs), intV 8]), -- [B7]

    mkCase "oracle/asm/valid/f486" (#[(.cell dict8Root), intV 8])
      (#[.pushInt (.num dictUMinGas), .tonEnvOp .setGasLimit, instr])
      dictUMinGasExact, -- [B10]
    mkCase "oracle/gas/exact-minus-one" (#[(.cell dict8Root), intV 8])
      (#[.pushInt (.num dictUMinGasMinusOne), .tonEnvOp .setGasLimit, instr])
      dictUMinGasExactMinusOne -- [B10]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictUMINFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUMIN
