import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SPLIT

/-
SPLIT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Split.lean` (`.split quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SPLIT`/`SPLITQ` encode as `0xd736`/`0xd737`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode neighborhood around `0xd734..0xd741`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_split`).

Branch map targeted by this suite (`quiet=false`, i.e. SPLIT):
- `checkUnderflow 3` before any pops;
- pop order is `refs` (`0..4`) then `bits` (`0..1023`) then `slice`;
- non-quiet failure (`!haveBits || !haveRefs`) throws `cellUnd`;
- success pushes two slices: prefix first, remainder second;
- handler fallthrough for non-`.split` cell-op variants;
- opcode/decode boundaries around `SUBSLICE (0xd734)`, `SPLIT (0xd736)`,
  `SPLITQ (0xd737)`, `XCTOS (0xd739)`, `SCHKBITS (0xd741)`.

Key risk areas:
- range/type ordering from pop sequence (`refs` range errors win first);
- exact boundary behavior at `(bits, refs) = (0,0), (0,4), (1023,0), (1023,4)`;
- prefix/remainder construction for partial-cursor slices (`bitPos/refPos` offsets);
- explicit contrast with quiet behavior (`SPLITQ`) to guard non-quiet `cellUnd`.
-/

private def splitId : InstrId := { name := "SPLIT" }

private def splitInstr : Instr :=
  .cellOp (.split false)

private def splitQInstr : Instr :=
  .cellOp (.split true)

private def dispatchSentinel : Int := 53736

private def splitSetGasExact : Int :=
  computeExactGasBudget splitInstr

private def splitSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne splitInstr

private def execCellOpSplitInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpSplit op next
  | _ => next

private def mkSplitCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[splitInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := splitId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSplitDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpSplitInstr splitInstr stack

private def runSplitQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpSplitInstr splitQInstr stack

private def runSplitDispatch (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpSplitInstr instr (VM.push (intV dispatchSentinel)) stack

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0b0110 4) #[Cell.empty]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0b11001 5) #[]

private def refLeafD : Cell :=
  Cell.mkOrdinary (natToBits 0b111000 6) #[Cell.empty]

private def refPool : Array Cell :=
  #[refLeafA, refLeafB, refLeafC, refLeafD]

private def takeRefs (n : Nat) : Array Cell :=
  refPool.extract 0 (Nat.min n refPool.size)

private def mkSplitSlice (availBits availRefs : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stripeBits availBits phase) (takeRefs availRefs))

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 40 1) (takeRefs 4)

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 7, refPos := 1 }

private def splitStack (s : Slice) (bits refs : Int) : Array Value :=
  #[.slice s, intV bits, intV refs]

private def splitStackNat (s : Slice) (bits refs : Nat) : Array Value :=
  splitStack s (Int.ofNat bits) (Int.ofNat refs)

private def splitPrefixSlice (s : Slice) (bits refs : Nat) : Slice :=
  let stop : Slice := { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }
  Slice.ofCell (Slice.prefixCell s stop)

private def splitRestSlice (s : Slice) (bits refs : Nat) : Slice :=
  { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }

private def splitSuccessStack (s : Slice) (bits refs : Nat) : Array Value :=
  #[.slice (splitPrefixSlice s bits refs), .slice (splitRestSlice s bits refs)]

private def splitQSuccessStack (s : Slice) (bits refs : Nat) : Array Value :=
  splitSuccessStack s bits refs ++ #[intV (-1)]

private def splitBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def splitRefsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def pickSplitBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (splitBitsBoundaryPool.size - 1)
  (splitBitsBoundaryPool[idx]!, rng')

private def pickSplitRefsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (splitRefsBoundaryPool.size - 1)
  (splitRefsBoundaryPool[idx]!, rng')

private def pickSplitBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickSplitBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickSplitRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 5 then
    pickSplitRefsBoundary rng1
  else
    randNat rng1 0 4

private def pickSplitAvailBitsAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickSplitAvailRefsAtLeast (refs : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let (extra, rng1) := randNat rng0 0 (4 - refs)
  (refs + extra, rng1)

private def pickSplitAvailBitsBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickSplitAvailRefsBelow (refs : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if refs = 0 then
    (0, rng0)
  else
    randNat rng0 0 (refs - 1)

private def pickSplitNoise (rng0 : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng0 0 3
  let v : Value :=
    if k = 0 then .null
    else if k = 1 then intV 91
    else if k = 2 then .cell Cell.empty
    else .builder Builder.empty
  (v, rng1)

private def genSplitFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (bits, rng2) := pickSplitBitsMixed rng1
  let (refs, rng3) := pickSplitRefsMixed rng2
  let (phase, rng4) := randNat rng3 0 1
  if shape = 0 then
    let (availBits, rng5) := pickSplitAvailBitsAtLeast bits rng4
    let (availRefs, rng6) := pickSplitAvailRefsAtLeast refs rng5
    (mkSplitCase s!"fuzz/ok/exact-or-extra/bits-{bits}/refs-{refs}"
      (splitStackNat (mkSplitSlice availBits availRefs phase) bits refs), rng6)
  else if shape = 1 then
    let (availBits, rng5) := pickSplitAvailBitsAtLeast bits rng4
    let (availRefs, rng6) := pickSplitAvailRefsAtLeast refs rng5
    let (noise, rng7) := pickSplitNoise rng6
    (mkSplitCase s!"fuzz/ok/deep-stack/bits-{bits}/refs-{refs}"
      (#[noise] ++ splitStackNat (mkSplitSlice availBits availRefs phase) bits refs), rng7)
  else if shape = 2 then
    let (useMax, rng5) := randBool rng4
    if useMax then
      (mkSplitCase "fuzz/ok/boundary-max"
        (splitStackNat (mkSplitSlice 1023 4 phase) 1023 4), rng5)
    else
      (mkSplitCase "fuzz/ok/boundary-min"
        (splitStackNat (mkSplitSlice 0 0 phase) 0 0), rng5)
  else if shape = 3 then
    let bitsNeed := if bits = 0 then 1 else bits
    let (availBits, rng5) := pickSplitAvailBitsBelow bitsNeed rng4
    let (availRefs, rng6) := pickSplitAvailRefsAtLeast refs rng5
    (mkSplitCase s!"fuzz/cellund/bits-short/bits-{bitsNeed}/refs-{refs}"
      (splitStackNat (mkSplitSlice availBits availRefs phase) bitsNeed refs), rng6)
  else if shape = 4 then
    let refsNeed := if refs = 0 then 1 else refs
    let (availBits, rng5) := pickSplitAvailBitsAtLeast bits rng4
    let (availRefs, rng6) := pickSplitAvailRefsBelow refsNeed rng5
    (mkSplitCase s!"fuzz/cellund/refs-short/bits-{bits}/refs-{refsNeed}"
      (splitStackNat (mkSplitSlice availBits availRefs phase) bits refsNeed), rng6)
  else if shape = 5 then
    let bitsNeed := if bits = 0 then 1 else bits
    let refsNeed := if refs = 0 then 1 else refs
    let (availBits, rng5) := pickSplitAvailBitsBelow bitsNeed rng4
    let (availRefs, rng6) := pickSplitAvailRefsBelow refsNeed rng5
    (mkSplitCase s!"fuzz/cellund/both-short/bits-{bitsNeed}/refs-{refsNeed}"
      (splitStackNat (mkSplitSlice availBits availRefs phase) bitsNeed refsNeed), rng6)
  else if shape = 6 then
    (mkSplitCase "fuzz/underflow/empty" #[], rng4)
  else if shape = 7 then
    (mkSplitCase s!"fuzz/underflow/two-items/bits-{bits}" #[.slice (mkSplitSlice 8 1), intV bits], rng4)
  else if shape = 8 then
    (mkSplitCase s!"fuzz/type/refs-top-not-int/bits-{bits}" #[.slice (mkSplitSlice 8 1), intV bits, .null], rng4)
  else if shape = 9 then
    (mkSplitCase s!"fuzz/type/bits-second-not-int/refs-{refs}" #[.slice (mkSplitSlice 8 1), .null, intV refs], rng4)
  else if shape = 10 then
    (mkSplitCase s!"fuzz/type/slice-third-not-slice/bits-{bits}/refs-{refs}" #[.null, intV bits, intV refs], rng4)
  else if shape = 11 then
    (mkSplitCase s!"fuzz/range/refs-too-large/bits-{bits}" #[.slice (mkSplitSlice 16 4), intV bits, intV 5], rng4)
  else if shape = 12 then
    (mkSplitCase s!"fuzz/range/refs-negative/bits-{bits}" #[.slice (mkSplitSlice 16 4), intV bits, intV (-1)], rng4)
  else if shape = 13 then
    (mkSplitCase s!"fuzz/range/bits-too-large/refs-{refs}" #[.slice (mkSplitSlice 16 4), intV 1024, intV refs], rng4)
  else if shape = 14 then
    (mkSplitCase s!"fuzz/range/bits-negative/refs-{refs}" #[.slice (mkSplitSlice 16 4), intV (-1), intV refs], rng4)
  else if shape = 15 then
    (mkSplitCase "fuzz/gas/exact"
      (splitStackNat (mkSplitSlice 20 3 1) 8 1)
      #[.pushInt (.num splitSetGasExact), .tonEnvOp .setGasLimit, splitInstr], rng4)
  else if shape = 16 then
    (mkSplitCase "fuzz/gas/exact-minus-one"
      (splitStackNat (mkSplitSlice 20 3 1) 8 1)
      #[.pushInt (.num splitSetGasExactMinusOne), .tonEnvOp .setGasLimit, splitInstr], rng4)
  else if shape = 17 then
    (mkSplitCase "fuzz/boundary/max-bits-max-refs"
      (splitStackNat (mkSplitSlice 1023 4 phase) 1023 4), rng4)
  else
    (mkSplitCase "fuzz/boundary/min-bits-min-refs"
      (splitStackNat (mkSplitSlice 0 0 phase) 0 0), rng4)

private structure SplitDirectCheck where
  bits : Nat
  refs : Nat
  input : Slice

def suite : InstrSuite where
  id := splitId
  unit := #[
    { name := "unit/direct/success-boundaries-and-prefix-remainder"
      run := do
        let checks : Array SplitDirectCheck :=
          #[
            { bits := 0, refs := 0, input := mkSplitSlice 0 0 },
            { bits := 1, refs := 0, input := mkSplitSlice 3 0 },
            { bits := 8, refs := 1, input := mkSplitSlice 13 2 },
            { bits := 64, refs := 2, input := mkSplitSlice 80 3 },
            { bits := 255, refs := 3, input := mkSplitSlice 260 4 },
            { bits := 1023, refs := 0, input := mkSplitSlice 1023 1 },
            { bits := 0, refs := 4, input := mkSplitSlice 12 4 },
            { bits := 1023, refs := 4, input := mkSplitSlice 1023 4 }
          ]
        for c in checks do
          expectOkStack s!"ok/bits-{c.bits}/refs-{c.refs}/avail-bits-{c.input.bitsRemaining}/avail-refs-{c.input.refsRemaining}"
            (runSplitDirect (splitStackNat c.input c.bits c.refs))
            (splitSuccessStack c.input c.bits c.refs)

        expectOkStack "ok/partial-cursor/bits-12/refs-2"
          (runSplitDirect (splitStackNat partialCursorSlice 12 2))
          (splitSuccessStack partialCursorSlice 12 2)

        let deep := mkSplitSlice 20 3 1
        let deepExpected := #[.null, intV 44] ++ splitSuccessStack deep 9 2
        expectOkStack "ok/deep-stack-preserve"
          (runSplitDirect #[.null, intV 44, .slice deep, intV 9, intV 2])
          deepExpected }
    ,
    { name := "unit/direct/cellund-for-short-bits-or-refs"
      run := do
        expectErr "cellund/bits-short-only"
          (runSplitDirect (splitStackNat (mkSplitSlice 7 2 0) 8 2)) .cellUnd
        expectErr "cellund/refs-short-only"
          (runSplitDirect (splitStackNat (mkSplitSlice 8 1 1) 8 2)) .cellUnd
        expectErr "cellund/both-short"
          (runSplitDirect (splitStackNat (mkSplitSlice 7 1 0) 8 2)) .cellUnd
        expectErr "cellund/empty-slice-needs-bit"
          (runSplitDirect (splitStackNat (mkSplitSlice 0 0) 1 0)) .cellUnd
        expectErr "cellund/refs-only-needs-bit"
          (runSplitDirect (splitStackNat (mkSplitSlice 0 4 1) 1 1)) .cellUnd
        expectErr "cellund/bits-only-needs-ref"
          (runSplitDirect (splitStackNat (mkSplitSlice 32 0 1) 32 1)) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-pop-order"
      run := do
        expectErr "underflow/empty" (runSplitDirect #[]) .stkUnd
        expectErr "underflow/one-item"
          (runSplitDirect #[.slice (mkSplitSlice 8 1)]) .stkUnd
        expectErr "underflow/two-items"
          (runSplitDirect #[.slice (mkSplitSlice 8 1), intV 1]) .stkUnd

        expectErr "type/refs-top-not-int"
          (runSplitDirect #[.slice (mkSplitSlice 8 1), intV 4, .null]) .typeChk
        expectErr "type/bits-second-not-int"
          (runSplitDirect #[.slice (mkSplitSlice 8 1), .null, intV 1]) .typeChk
        expectErr "type/slice-third-not-slice"
          (runSplitDirect #[.null, intV 4, intV 1]) .typeChk

        expectErr "range/refs-too-large-before-bits-range-and-slice-type"
          (runSplitDirect #[.null, intV 2048, intV 5]) .rangeChk
        expectErr "range/refs-negative-before-bits-type"
          (runSplitDirect #[.slice (mkSplitSlice 8 1), .null, intV (-1)]) .rangeChk
        expectErr "range/bits-too-large-before-slice-type"
          (runSplitDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-negative-before-slice-type"
          (runSplitDirect #[.null, intV (-1), intV 0]) .rangeChk }
    ,
    { name := "unit/direct/nonquiet-vs-quiet-outcomes"
      run := do
        let okInput := mkSplitSlice 20 3 1
        expectOkStack "split/nonquiet-success"
          (runSplitDirect (splitStackNat okInput 9 2))
          (splitSuccessStack okInput 9 2)
        expectOkStack "splitq/quiet-success-minus1"
          (runSplitQDirect (splitStackNat okInput 9 2))
          (splitQSuccessStack okInput 9 2)

        let failInput := mkSplitSlice 8 1 0
        expectErr "split/nonquiet-fail-cellund"
          (runSplitDirect (splitStackNat failInput 9 2)) .cellUnd
        expectOkStack "splitq/quiet-fail-status0"
          (runSplitQDirect (splitStackNat failInput 9 2))
          #[.slice failInput, intV 0]
        expectOkStack "splitq/quiet-fail-deep-stack-preserve"
          (runSplitQDirect #[.null, .slice failInput, intV 9, intV 2])
          #[.null, .slice failInput, intV 0] }
    ,
    { name := "unit/opcode/decode-family-boundaries-and-assembler"
      run := do
        let splitCode ←
          match assembleCp0 [splitInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/split failed: {e}")
        if splitCode.bits = natToBits 0xd736 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/split: expected 0xd736, got {splitCode.bits}")
        if splitCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/split: expected 16 bits, got {splitCode.bits.size}")

        let program : Array Instr :=
          #[.cellOp .subslice, splitInstr, splitQInstr, .xctos, .cellOp (.schkBits false), .add]
        let asmCode ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-subslice-left-neighbor" a0 (.cellOp .subslice) 16
        let a2 ← expectDecodeStep "decode/asm-split" a1 splitInstr 16
        let a3 ← expectDecodeStep "decode/asm-splitq-right-neighbor" a2 splitQInstr 16
        let a4 ← expectDecodeStep "decode/asm-xctos-neighbor" a3 .xctos 16
        let a5 ← expectDecodeStep "decode/asm-schkbits-boundary" a4 (.cellOp (.schkBits false)) 16
        let a6 ← expectDecodeStep "decode/asm-tail-add" a5 .add 8
        if a6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a6.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits
          (natToBits 0xd734 16 ++
           natToBits 0xd736 16 ++
           natToBits 0xd737 16 ++
           natToBits 0xd739 16 ++
           natToBits 0xd741 16 ++
           natToBits 0xa0 8)
        let r1 ← expectDecodeStep "decode/raw-subslice" raw (.cellOp .subslice) 16
        let r2 ← expectDecodeStep "decode/raw-split" r1 splitInstr 16
        let r3 ← expectDecodeStep "decode/raw-splitq" r2 splitQInstr 16
        let r4 ← expectDecodeStep "decode/raw-xctos" r3 .xctos 16
        let r5 ← expectDecodeStep "decode/raw-schkbits" r4 (.cellOp (.schkBits false)) 16
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-split-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runSplitDispatch .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-split-cellop"
          (runSplitDispatch (.cellOp .subslice) #[intV 7])
          #[intV 7, intV dispatchSentinel]

        let s := mkSplitSlice 10 2
        expectOkStack "dispatch/splitq-handled-not-fallback"
          (runSplitDispatch splitQInstr (splitStackNat s 6 1))
          (splitQSuccessStack s 6 1) }
  ]
  oracle := #[
    mkSplitCase "ok/bits0-refs0-empty"
      (splitStackNat (mkSplitSlice 0 0) 0 0),
    mkSplitCase "ok/bits1-refs0"
      (splitStackNat (mkSplitSlice 1 0 1) 1 0),
    mkSplitCase "ok/bits8-refs1"
      (splitStackNat (mkSplitSlice 12 2 0) 8 1),
    mkSplitCase "ok/bits16-refs2"
      (splitStackNat (mkSplitSlice 20 2 1) 16 2),
    mkSplitCase "ok/bits64-refs2"
      (splitStackNat (mkSplitSlice 96 3 1) 64 2),
    mkSplitCase "ok/bits255-refs4"
      (splitStackNat (mkSplitSlice 260 4 0) 255 4),
    mkSplitCase "ok/bits1023-refs0"
      (splitStackNat (mkSplitSlice 1023 1 0) 1023 0),
    mkSplitCase "ok/bits0-refs4"
      (splitStackNat (mkSplitSlice 12 4 1) 0 4),
    mkSplitCase "ok/deep-stack-preserve"
      #[.null, intV 11, .slice (mkSplitSlice 32 3 1), intV 9, intV 2],

    mkSplitCase "cellund/bits-short"
      (splitStackNat (mkSplitSlice 7 2 0) 8 2),
    mkSplitCase "cellund/refs-short"
      (splitStackNat (mkSplitSlice 8 1 1) 8 2),
    mkSplitCase "cellund/both-short"
      (splitStackNat (mkSplitSlice 7 1 0) 8 2),
    mkSplitCase "cellund/need-refs4-have3-bits0"
      (splitStackNat (mkSplitSlice 0 3 0) 0 4),
    mkSplitCase "cellund/need-bits256-have255-refs4"
      (splitStackNat (mkSplitSlice 255 4 1) 256 4),

    mkSplitCase "underflow/empty" #[],
    mkSplitCase "underflow/two-items" #[.slice (mkSplitSlice 8 1), intV 1],
    mkSplitCase "type/refs-top-not-int" #[.slice (mkSplitSlice 8 1), intV 4, .null],
    mkSplitCase "type/bits-second-not-int" #[.slice (mkSplitSlice 8 1), .null, intV 1],
    mkSplitCase "type/slice-third-not-slice" #[.null, intV 4, intV 1],
    mkSplitCase "range/refs-too-large" #[.slice (mkSplitSlice 16 4), intV 8, intV 5],
    mkSplitCase "range/refs-negative" #[.slice (mkSplitSlice 16 4), intV 8, intV (-1)],
    mkSplitCase "range/bits-too-large" #[.slice (mkSplitSlice 16 4), intV 1024, intV 0],
    mkSplitCase "range/bits-negative" #[.slice (mkSplitSlice 16 4), intV (-1), intV 0],

    mkSplitCase "gas/exact-cost-succeeds"
      (splitStackNat (mkSplitSlice 20 3 1) 8 1)
      #[.pushInt (.num splitSetGasExact), .tonEnvOp .setGasLimit, splitInstr],
    mkSplitCase "gas/exact-minus-one-out-of-gas"
      (splitStackNat (mkSplitSlice 20 3 1) 8 1)
      #[.pushInt (.num splitSetGasExactMinusOne), .tonEnvOp .setGasLimit, splitInstr]
  ]
  fuzz := #[
    { seed := 2026021011
      count := 320
      gen := genSplitFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SPLIT
