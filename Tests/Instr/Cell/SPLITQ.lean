import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SPLITQ

/-
SPLITQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Split.lean` (`.split quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SPLIT=0xd736`, `SPLITQ=0xd737`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode of `0xd736/0xd737`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_split(st, quiet)`).

Branch map for `SPLITQ`:
- `checkUnderflow 3` before all pops;
- pop order is `refs` (top, `0..4`) then `bits` (`0..1023`) then `slice`;
- split guard is `haveBits(bits) && haveRefs(refs)`;
- quiet success: push `[prefix, rest, -1]`;
- quiet failure: preserve original slice and push status `0`;
- non-quiet contrast (`SPLIT`): same pop/split logic but failure throws `.cellUnd`.
-/

private def splitqId : InstrId := { name := "SPLITQ" }

private def splitInstr (quiet : Bool) : Instr :=
  .cellOp (.split quiet)

private def splitqInstr : Instr :=
  splitInstr true

private def splitInstrNonQuiet : Instr :=
  splitInstr false

private def splitWord : Nat := 0xd736
private def splitqWord : Nat := 0xd737

private def dispatchSentinel : Int := 638

private def natV (n : Nat) : Value :=
  intV (Int.ofNat n)

private def mkSplitqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[splitqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := splitqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSplitqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkSplitqCase name stack program gasLimits fuel

private def execCellOpSplitInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpSplit op next
  | _ => next

private def runSplitDirect (quiet : Bool) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpSplitInstr (splitInstr quiet) stack

private def runSplitqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runSplitDirect true stack

private def runSplitDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpSplitInstr instr (VM.push (intV dispatchSentinel)) stack

private def splitqSetGasExact : Int :=
  computeExactGasBudget splitqInstr

private def splitqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne splitqInstr

private def patternedBits (n : Nat) : BitString :=
  Array.ofFn (n := n) fun i => (i.1 % 2 = 0) || (i.1 % 5 = 1)

private def refLeafA : Cell :=
  Cell.mkOrdinary (patternedBits 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (patternedBits 5) #[Cell.empty]

private def refLeafC : Cell :=
  Cell.mkOrdinary (patternedBits 2) #[Cell.ofUInt 6 3]

private def refLeafD : Cell :=
  Cell.mkOrdinary #[] #[refLeafA, refLeafB]

private def mkRefPack : Nat → Array Cell
  | 0 => #[]
  | 1 => #[refLeafA]
  | 2 => #[refLeafA, refLeafB]
  | 3 => #[refLeafA, refLeafB, refLeafC]
  | _ => #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkPatternSlice (bits : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternedBits bits) #[])

private def mkPatternSliceWithRefs (bits refs : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternedBits bits) (mkRefPack refs))

private def splitStop (s : Slice) (bits refs : Nat) : Slice :=
  { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }

private def expectedPrefixSlice (s : Slice) (bits refs : Nat) : Slice :=
  Slice.ofCell (Slice.prefixCell s (splitStop s bits refs))

private def expectedRestSlice (s : Slice) (bits refs : Nat) : Slice :=
  splitStop s bits refs

private def expectedSplitqSuccessStack
    (below : Array Value)
    (s : Slice)
    (bits refs : Nat) : Array Value :=
  below ++ #[.slice (expectedPrefixSlice s bits refs), .slice (expectedRestSlice s bits refs), intV (-1)]

private def expectedSplitqFailureStack (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[.slice s, intV 0]

private def expectedSplitSuccessStack
    (below : Array Value)
    (s : Slice)
    (bits refs : Nat) : Array Value :=
  below ++ #[.slice (expectedPrefixSlice s bits refs), .slice (expectedRestSlice s bits refs)]

private def oracleSliceEmpty : Slice := mkPatternSlice 0
private def oracleSlice6 : Slice := mkPatternSlice 6
private def oracleSlice12 : Slice := mkPatternSlice 12
private def oracleSlice24 : Slice := mkPatternSlice 24
private def oracleSlice128 : Slice := mkPatternSlice 128
private def oracleSlice1022 : Slice := mkPatternSlice 1022
private def oracleSlice1023 : Slice := mkPatternSlice 1023
private def oracleSliceRefs1 : Slice := mkPatternSliceWithRefs 4 1
private def oracleSliceRefs2 : Slice := mkPatternSliceWithRefs 8 2
private def oracleSliceRefs3 : Slice := mkPatternSliceWithRefs 9 3
private def oracleSliceRefs4 : Slice := mkPatternSliceWithRefs 6 4

private def partialBaseCell : Cell :=
  Cell.mkOrdinary (patternedBits 21) (mkRefPack 3)

private def partialSlice : Slice :=
  { cell := partialBaseCell, bitPos := 4, refPos := 1 }

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def refsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def pickBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (bitsBoundaryPool.size - 1)
  (bitsBoundaryPool[idx]!, rng')

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickRefsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (refsBoundaryPool.size - 1)
  (refsBoundaryPool[idx]!, rng')

private def pickRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickRefsBoundary rng1
  else
    randNat rng1 0 4

private def pickAvailBitsAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickAvailBitsBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickAvailRefsAtLeast (refs : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := 4 - refs
  let (extra, rng1) := randNat rng0 0 maxExtra
  (refs + extra, rng1)

private def pickAvailRefsBelow (refs : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if refs = 0 then
    (0, rng0)
  else
    randNat rng0 0 (refs - 1)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 37
    else .cell refLeafA
  (noise, rng1)

private def genSplitqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (bits0, rng2) := pickBitsMixed rng1
  let (refs0, rng3) := pickRefsMixed rng2
  if shape = 0 then
    let (availBits, rng4) := pickAvailBitsAtLeast bits0 rng3
    let (availRefs, rng5) := pickAvailRefsAtLeast refs0 rng4
    let s := mkPatternSliceWithRefs availBits availRefs
    (mkSplitqCase s!"fuzz/ok/exact-or-extra/b-{bits0}-r-{refs0}"
      #[.slice s, natV bits0, natV refs0], rng5)
  else if shape = 1 then
    let (availBits, rng4) := pickAvailBitsAtLeast bits0 rng3
    let s := mkPatternSliceWithRefs availBits refs0
    (mkSplitqCase s!"fuzz/ok/extra-bits/b-{bits0}-a-{availBits}-r-{refs0}"
      #[.slice s, natV bits0, natV refs0], rng4)
  else if shape = 2 then
    let (availRefs, rng4) := pickAvailRefsAtLeast refs0 rng3
    let s := mkPatternSliceWithRefs bits0 availRefs
    (mkSplitqCase s!"fuzz/ok/extra-refs/b-{bits0}-r-{refs0}-a-{availRefs}"
      #[.slice s, natV bits0, natV refs0], rng4)
  else if shape = 3 then
    let (availBits, rng4) := pickAvailBitsAtLeast bits0 rng3
    let (availRefs, rng5) := pickAvailRefsAtLeast refs0 rng4
    let (noise, rng6) := pickNoiseValue rng5
    let s := mkPatternSliceWithRefs availBits availRefs
    (mkSplitqCase s!"fuzz/ok/deep-stack/b-{bits0}-r-{refs0}"
      #[noise, .slice s, natV bits0, natV refs0], rng6)
  else if shape = 4 then
    let bits := if bits0 = 0 then 1 else bits0
    let (availBits, rng4) := pickAvailBitsBelow bits rng3
    let s := mkPatternSliceWithRefs availBits refs0
    (mkSplitqCase s!"fuzz/fail/bits-short/b-{bits}-a-{availBits}-r-{refs0}"
      #[.slice s, natV bits, natV refs0], rng4)
  else if shape = 5 then
    let refs := if refs0 = 0 then 1 else refs0
    let (availRefs, rng4) := pickAvailRefsBelow refs rng3
    let s := mkPatternSliceWithRefs bits0 availRefs
    (mkSplitqCase s!"fuzz/fail/refs-short/b-{bits0}-r-{refs}-a-{availRefs}"
      #[.slice s, natV bits0, natV refs], rng4)
  else if shape = 6 then
    let bits := if bits0 = 0 then 1 else bits0
    let refs := if refs0 = 0 then 1 else refs0
    let (availBits, rng4) := pickAvailBitsBelow bits rng3
    let (availRefs, rng5) := pickAvailRefsBelow refs rng4
    let s := mkPatternSliceWithRefs availBits availRefs
    (mkSplitqCase s!"fuzz/fail/bits-refs-short/b-{bits}-r-{refs}-a-{availBits}-{availRefs}"
      #[.slice s, natV bits, natV refs], rng5)
  else if shape = 7 then
    (mkSplitqCase "fuzz/fail/empty-plus-1" #[.slice oracleSliceEmpty, natV 1, natV 0], rng3)
  else if shape = 8 then
    (mkSplitqCase "fuzz/underflow/empty" #[], rng3)
  else if shape = 9 then
    (mkSplitqCase "fuzz/underflow/two-items" #[.slice oracleSlice6, natV 1], rng3)
  else if shape = 10 then
    (mkSplitqCase "fuzz/type/refs-not-int" #[.slice oracleSlice6, natV 1, .null], rng3)
  else if shape = 11 then
    (mkSplitqCase "fuzz/range/refs-gt4" #[.slice oracleSlice6, natV 1, natV 5], rng3)
  else if shape = 12 then
    (mkSplitqCase "fuzz/type/bits-not-int" #[.slice oracleSlice6, .null, natV 0], rng3)
  else if shape = 13 then
    (mkSplitqCase "fuzz/range/bits-gt1023" #[.slice oracleSlice6, natV 1024, natV 0], rng3)
  else if shape = 14 then
    (mkSplitqCase "fuzz/type/slice-not-slice" #[.null, natV 0, natV 0], rng3)
  else if shape = 15 then
    (mkSplitqCase "fuzz/order/refs-range-before-bits-type" #[.null, .null, natV 5], rng3)
  else if shape = 16 then
    (mkSplitqProgramCase "fuzz/gas/exact"
      #[.slice oracleSlice12, natV 3, natV 1]
      #[.pushInt (.num splitqSetGasExact), .tonEnvOp .setGasLimit, splitqInstr], rng3)
  else
    (mkSplitqProgramCase "fuzz/gas/exact-minus-one"
      #[.slice oracleSlice12, natV 3, natV 1]
      #[.pushInt (.num splitqSetGasExactMinusOne), .tonEnvOp .setGasLimit, splitqInstr], rng3)

def suite : InstrSuite where
  id := { name := "SPLITQ" }
  unit := #[
    { name := "unit/direct/quiet-success-stack-order-and-status-minus1"
      run := do
        expectOkStack "ok/zero-zero-on-nonempty"
          (runSplitqDirect #[.slice oracleSlice12, natV 0, natV 0])
          (expectedSplitqSuccessStack #[] oracleSlice12 0 0)
        expectOkStack "ok/bits-only"
          (runSplitqDirect #[.slice oracleSlice24, natV 5, natV 0])
          (expectedSplitqSuccessStack #[] oracleSlice24 5 0)
        expectOkStack "ok/refs-only"
          (runSplitqDirect #[.slice oracleSliceRefs3, natV 0, natV 2])
          (expectedSplitqSuccessStack #[] oracleSliceRefs3 0 2)
        expectOkStack "ok/mixed-bits-refs"
          (runSplitqDirect #[.slice oracleSliceRefs4, natV 4, natV 3])
          (expectedSplitqSuccessStack #[] oracleSliceRefs4 4 3)
        expectOkStack "ok/max-boundary"
          (runSplitqDirect #[.slice oracleSlice1023, natV 1023, natV 0])
          (expectedSplitqSuccessStack #[] oracleSlice1023 1023 0)
        expectOkStack "ok/partial-cursor"
          (runSplitqDirect #[.slice partialSlice, natV 7, natV 1])
          (expectedSplitqSuccessStack #[] partialSlice 7 1)
        expectOkStack "ok/deep-stack-preserve-below"
          (runSplitqDirect #[.null, intV 44, .slice oracleSliceRefs3, natV 3, natV 2])
          (expectedSplitqSuccessStack #[.null, intV 44] oracleSliceRefs3 3 2) }
    ,
    { name := "unit/direct/quiet-failure-preserves-original-and-status0"
      run := do
        expectOkStack "fail/bits-short-by-one"
          (runSplitqDirect #[.slice oracleSlice6, natV 7, natV 0])
          (expectedSplitqFailureStack #[] oracleSlice6)
        expectOkStack "fail/refs-short-by-one"
          (runSplitqDirect #[.slice oracleSliceRefs2, natV 2, natV 3])
          (expectedSplitqFailureStack #[] oracleSliceRefs2)
        expectOkStack "fail/bits-and-refs-short"
          (runSplitqDirect #[.slice oracleSliceRefs1, natV 5, natV 2])
          (expectedSplitqFailureStack #[] oracleSliceRefs1)
        expectOkStack "fail/partial-slice-short"
          (runSplitqDirect #[.slice partialSlice, natV 18, natV 0])
          (expectedSplitqFailureStack #[] partialSlice)
        expectOkStack "fail/deep-stack-preserve-below"
          (runSplitqDirect #[intV 91, .slice oracleSlice6, natV 8, natV 0])
          (expectedSplitqFailureStack #[intV 91] oracleSlice6) }
    ,
    { name := "unit/direct/underflow-type-range-and-pop-order"
      run := do
        expectErr "underflow/empty" (runSplitqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runSplitqDirect #[.slice oracleSlice6]) .stkUnd
        expectErr "underflow/two-items" (runSplitqDirect #[.slice oracleSlice6, natV 1]) .stkUnd

        expectErr "type/refs-top-null"
          (runSplitqDirect #[.slice oracleSlice6, natV 1, .null]) .typeChk
        expectErr "range/refs-negative"
          (runSplitqDirect #[.slice oracleSlice6, natV 1, intV (-1)]) .rangeChk
        expectErr "range/refs-gt4"
          (runSplitqDirect #[.slice oracleSlice6, natV 1, natV 5]) .rangeChk
        expectErr "range/refs-nan"
          (runSplitqDirect #[.slice oracleSlice6, natV 1, .int .nan]) .rangeChk

        expectErr "type/bits-not-int-after-valid-refs"
          (runSplitqDirect #[.slice oracleSlice6, .null, natV 0]) .typeChk
        expectErr "range/bits-negative-after-valid-refs"
          (runSplitqDirect #[.slice oracleSlice6, intV (-1), natV 0]) .rangeChk
        expectErr "range/bits-gt1023-after-valid-refs"
          (runSplitqDirect #[.slice oracleSlice6, natV 1024, natV 0]) .rangeChk
        expectErr "range/bits-nan-after-valid-refs"
          (runSplitqDirect #[.slice oracleSlice6, .int .nan, natV 0]) .rangeChk

        expectErr "type/slice-not-slice-after-valid-ints"
          (runSplitqDirect #[.null, natV 0, natV 0]) .typeChk
        expectErr "order/refs-range-before-bits-type"
          (runSplitqDirect #[.null, .null, natV 5]) .rangeChk
        expectErr "order/bits-range-before-slice-type"
          (runSplitqDirect #[.null, natV 2048, natV 0]) .rangeChk }
    ,
    { name := "unit/direct/non-quiet-split-contrast"
      run := do
        expectOkStack "split/non-quiet-success-no-status"
          (runSplitDirect false #[.slice oracleSliceRefs3, natV 3, natV 2])
          (expectedSplitSuccessStack #[] oracleSliceRefs3 3 2)
        expectOkStack "split/non-quiet-success-deep-stack"
          (runSplitDirect false #[.null, .slice oracleSlice24, natV 5, natV 0])
          (expectedSplitSuccessStack #[.null] oracleSlice24 5 0)
        expectErr "split/non-quiet-failure-bits-short"
          (runSplitDirect false #[.slice oracleSlice6, natV 7, natV 0]) .cellUnd
        expectErr "split/non-quiet-failure-refs-short"
          (runSplitDirect false #[.slice oracleSliceRefs1, natV 1, natV 2]) .cellUnd }
    ,
    { name := "unit/opcode/decode-assembler-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[.cellOp .subslice, splitInstrNonQuiet, splitqInstr, .cellOp (.schkBits false), .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-subslice" s0 (.cellOp .subslice) 16
        let s2 ← expectDecodeStep "decode/asm-split" s1 splitInstrNonQuiet 16
        let s3 ← expectDecodeStep "decode/asm-splitq" s2 splitqInstr 16
        let s4 ← expectDecodeStep "decode/asm-schkbits" s3 (.cellOp (.schkBits false)) 16
        let s5 ← expectDecodeStep "decode/asm-tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits (natToBits splitWord 16 ++ natToBits splitqWord 16 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-split" raw splitInstrNonQuiet 16
        let raw2 ← expectDecodeStep "decode/raw-splitq" raw1 splitqInstr 16
        let raw3 ← expectDecodeStep "decode/raw-tail-add" raw2 .add 8
        if raw3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {raw3.bitsRemaining} bits remaining")

        let splitqCode ←
          match assembleCp0 [splitqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/splitq failed: {e}")
        if splitqCode.bits == natToBits splitqWord 16 && splitqCode.refs.isEmpty then
          pure ()
        else
          throw (IO.userError s!"assemble/splitq word mismatch: bits={reprStr splitqCode.bits}, refs={splitqCode.refs.size}")

        let splitCode ←
          match assembleCp0 [splitInstrNonQuiet] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/split failed: {e}")
        if splitCode.bits == natToBits splitWord 16 && splitCode.refs.isEmpty then
          pure ()
        else
          throw (IO.userError s!"assemble/split word mismatch: bits={reprStr splitCode.bits}, refs={splitCode.refs.size}") }
    ,
    { name := "unit/dispatch/non-split-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runSplitDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop"
          (runSplitDispatchFallback (.cellOp .subslice) #[intV 12])
          #[intV 12, intV dispatchSentinel] }
  ]
  oracle := #[
    -- Success branches
    mkSplitqCase "ok/zero-zero-empty"
      #[.slice oracleSliceEmpty, natV 0, natV 0],
    mkSplitqCase "ok/bits-only"
      #[.slice oracleSlice24, natV 5, natV 0],
    mkSplitqCase "ok/refs-only"
      #[.slice oracleSliceRefs1, natV 0, natV 1],
    mkSplitqCase "ok/mixed-small"
      #[.slice oracleSliceRefs2, natV 3, natV 2],
    mkSplitqCase "ok/mixed-large"
      #[.slice oracleSlice128, natV 64, natV 0],
    mkSplitqCase "ok/max-bits-1023"
      #[.slice oracleSlice1023, natV 1023, natV 0],
    mkSplitqCase "ok/max-refs-4"
      #[.slice oracleSliceRefs4, natV 2, natV 4],
    mkSplitqCase "ok/deep-stack"
      #[.null, intV 7, .slice oracleSliceRefs3, natV 4, natV 1],

    -- Quiet failure branches
    mkSplitqCase "fail/bits-short-by-one"
      #[.slice oracleSlice6, natV 7, natV 0],
    mkSplitqCase "fail/refs-short-by-one"
      #[.slice oracleSliceRefs2, natV 2, natV 3],
    mkSplitqCase "fail/bits-and-refs-short"
      #[.slice oracleSliceRefs1, natV 5, natV 2],
    mkSplitqCase "fail/empty-plus-required"
      #[.slice oracleSliceEmpty, natV 1, natV 0],
    mkSplitqCase "fail/max-bits-over"
      #[.slice oracleSlice1022, natV 1023, natV 0],
    mkSplitqCase "fail/deep-stack"
      #[intV 41, .slice oracleSliceRefs1, natV 4, natV 2],

    -- Underflow / type / range
    mkSplitqCase "underflow/empty" #[],
    mkSplitqCase "underflow/two-items" #[.slice oracleSlice6, natV 1],
    mkSplitqCase "type/refs-top-null" #[.slice oracleSlice6, natV 1, .null],
    mkSplitqCase "range/refs-negative" #[.slice oracleSlice6, natV 1, intV (-1)],
    mkSplitqCase "range/refs-gt4" #[.slice oracleSlice6, natV 1, natV 5],
    mkSplitqCase "type/bits-not-int" #[.slice oracleSlice6, .null, natV 0],
    mkSplitqCase "range/bits-gt1023" #[.slice oracleSlice6, natV 1024, natV 0],
    mkSplitqCase "type/slice-not-slice" #[.null, natV 0, natV 0],

    -- Gas edge behavior
    mkSplitqCase "gas/exact-cost-succeeds"
      #[.slice oracleSlice12, natV 3, natV 1]
      #[.pushInt (.num splitqSetGasExact), .tonEnvOp .setGasLimit, splitqInstr],
    mkSplitqCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSlice12, natV 3, natV 1]
      #[.pushInt (.num splitqSetGasExactMinusOne), .tonEnvOp .setGasLimit, splitqInstr]
  ]
  fuzz := #[
    { seed := 2026021019
      count := 240
      gen := genSplitqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SPLITQ
