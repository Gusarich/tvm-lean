import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCUTFIRST

/-
SCUTFIRST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.scutfirst`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd730` decode to `.cellOp .scutfirst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.cellOp .scutfirst` encode as `0xd730`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_op_args2(..., "SCUTFIRST", 1023, 4, &CellSlice::cut_first)` at `0xd730`).

Branch map used in this suite:
- dispatch guard in instruction-local handler (`.cellOp .scutfirst` vs fallback);
- stack arity check (`checkUnderflow 3`);
- pop-order/error precedence: `refs` (0..4) -> `bits` (0..1023) -> `slice`;
- success branch builds a new ordinary cell from the current cursor prefix;
- failure branch throws `cellUnd` when either `haveBits bits` or `haveRefs refs` fails;
- opcode/decode boundary at exact word `0xd730`, with nearby `0xd724` and `0xd731..0xd734`.
-/

private def scutfirstId : InstrId := { name := "SCUTFIRST" }

private def scutfirstInstr : Instr :=
  .cellOp .scutfirst

private def sskipfirstInstr : Instr :=
  .cellOp .sskipfirst

private def scutlastInstr : Instr :=
  .cellOp .scutlast

private def sskiplastInstr : Instr :=
  .cellOp .sskiplast

private def sdsubstrInstr : Instr :=
  .cellOp .sdSubstr

private def subsliceInstr : Instr :=
  .cellOp .subslice

private def scutfirstWord : Nat := 0xd730

private def dispatchSentinel : Int := 3730

private def execInstrCellOpScutfirstOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .scutfirst => execCellOpExt .scutfirst next
  | _ => next

private def mkScutfirstCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[scutfirstInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := scutfirstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runScutfirstDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpScutfirstOnly scutfirstInstr stack

private def runScutfirstDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpScutfirstOnly instr (VM.push (intV dispatchSentinel)) stack

private def valueToNatUpTo (v : Value) (max : Nat) : Except Excno Nat := do
  match v with
  | .int .nan =>
      throw .rangeChk
  | .int (.num n) =>
      if n < 0 then
        throw .rangeChk
      else
        let u := n.toNat
        if u > max then
          throw .rangeChk
        else
          pure u
  | _ =>
      throw .typeChk

private def cutFirstSlice (s : Slice) (bits refs : Nat) : Slice :=
  let newCell : Cell :=
    Cell.mkOrdinary
      (s.cell.bits.extract s.bitPos (s.bitPos + bits))
      (s.cell.refs.extract s.refPos (s.refPos + refs))
  Slice.ofCell newCell

private def runScutfirstModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 3 then
    throw .stkUnd
  let refsV := stack[stack.size - 1]!
  let bitsV := stack[stack.size - 2]!
  let sliceV := stack[stack.size - 3]!
  let below := stack.extract 0 (stack.size - 3)
  let refs ← valueToNatUpTo refsV 4
  let bits ← valueToNatUpTo bitsV 1023
  let s ←
    match sliceV with
    | .slice s => pure s
    | _ => throw .typeChk
  if s.haveBits bits && s.haveRefs refs then
    pure (below.push (.slice (cutFirstSlice s bits refs)))
  else
    throw .cellUnd

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkFullSlice (bits refs : Nat) (phase : Nat := 0) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase) (refsByCount refs)

private def mkScutfirstStackNat
    (s : Slice)
    (bits refs : Nat)
    (below : Array Value := #[]) : Array Value :=
  below ++ #[.slice s, intV (Int.ofNat bits), intV (Int.ofNat refs)]

private def sliceBits0Refs0 : Slice := mkFullSlice 0 0
private def sliceBits0Refs4 : Slice := mkFullSlice 0 4
private def sliceBits7Refs1 : Slice := mkFullSlice 7 1
private def sliceBits8Refs0 : Slice := mkFullSlice 8 0
private def sliceBits8Refs1 : Slice := mkFullSlice 8 1
private def sliceBits8Refs3 : Slice := mkFullSlice 8 3
private def sliceBits16Refs2 : Slice := mkFullSlice 16 2
private def sliceBits16Refs4 : Slice := mkFullSlice 16 4
private def sliceBits32Refs1 : Slice := mkFullSlice 32 1
private def sliceBits64Refs4 : Slice := mkFullSlice 64 4
private def sliceBits1023Refs4 : Slice := mkFullSlice 1023 4

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 12 0) (refsByCount 4)

private def partialSliceMid : Slice :=
  { cell := partialCursorCell, bitPos := 3, refPos := 1 }

private def partialSliceBitsExhausted : Slice :=
  { cell := partialCursorCell, bitPos := partialCursorCell.bits.size, refPos := 2 }

private def partialSliceRefsExhausted : Slice :=
  { cell := partialCursorCell, bitPos := 4, refPos := partialCursorCell.refs.size }

private def scutfirstSetGasExact : Int :=
  computeExactGasBudget scutfirstInstr

private def scutfirstSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne scutfirstInstr

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    let (idx, rng2) := randNat rng1 0 (bitsBoundaryPool.size - 1)
    (((bitsBoundaryPool[idx]?).getD 0), rng2)
  else
    randNat rng1 0 1023

private def pickRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (4, rng1)
  else
    randNat rng1 0 4

private def fuzzNoisePool : Array Value :=
  #[.null, intV 0, intV 7, intV (-9), .cell refLeafB, .builder Builder.empty, .tuple #[], .cont (.quit 0)]

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (fuzzNoisePool.size - 1)
  (((fuzzNoisePool[idx]?).getD .null), rng1)

private def genScutfirstFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (totalRefs, rng3) := pickRefsMixed rng2
    let (wantBits, rng4) := randNat rng3 0 totalBits
    let (wantRefs, rng5) := randNat rng4 0 totalRefs
    let (phase, rng6) := randNat rng5 0 3
    let s := mkFullSlice totalBits totalRefs phase
    (mkScutfirstCase s!"fuzz/ok/full/bits{wantBits}/refs{wantRefs}/tot{totalBits}-{totalRefs}"
      (mkScutfirstStackNat s wantBits wantRefs), rng6)
  else if shape = 1 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (totalRefs, rng3) := pickRefsMixed rng2
    let (wantBits, rng4) := randNat rng3 0 totalBits
    let (wantRefs, rng5) := randNat rng4 0 totalRefs
    let (phase, rng6) := randNat rng5 0 3
    let (noise, rng7) := pickNoiseValue rng6
    let s := mkFullSlice totalBits totalRefs phase
    (mkScutfirstCase s!"fuzz/ok/deep/bits{wantBits}/refs{wantRefs}"
      (mkScutfirstStackNat s wantBits wantRefs #[noise]), rng7)
  else if shape = 2 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (totalRefs, rng3) := pickRefsMixed rng2
    let (skipBits, rng4) := randNat rng3 0 totalBits
    let (skipRefs, rng5) := randNat rng4 0 totalRefs
    let remBits := totalBits - skipBits
    let remRefs := totalRefs - skipRefs
    let (wantBits, rng6) := randNat rng5 0 remBits
    let (wantRefs, rng7) := randNat rng6 0 remRefs
    let (phase, rng8) := randNat rng7 0 3
    let s := mkFullSlice totalBits totalRefs phase
    let stack : Array Value := #[.slice s, intV (Int.ofNat skipBits), intV (Int.ofNat skipRefs)]
    let program : Array Instr :=
      #[sskipfirstInstr, .pushInt (.num wantBits), .pushInt (.num wantRefs), scutfirstInstr]
    (mkScutfirstCase s!"fuzz/ok/cursor/skip{skipBits}-{skipRefs}/want{wantBits}-{wantRefs}" stack program, rng8)
  else if shape = 3 then
    let (mode, rng2) := randNat rng1 0 1
    if mode = 0 then
      let (totalBits0, rng3) := randNat rng2 0 1022
      let (totalRefs, rng4) := pickRefsMixed rng3
      let (wantRefs, rng5) := randNat rng4 0 totalRefs
      let (phase, rng6) := randNat rng5 0 3
      let s := mkFullSlice totalBits0 totalRefs phase
      (mkScutfirstCase "fuzz/cellund/bits+1"
        (mkScutfirstStackNat s (totalBits0 + 1) wantRefs), rng6)
    else
      let (totalBits, rng3) := pickBitsMixed rng2
      let (totalRefs0, rng4) := randNat rng3 0 3
      let (wantBits, rng5) := randNat rng4 0 totalBits
      let (phase, rng6) := randNat rng5 0 3
      let s := mkFullSlice totalBits totalRefs0 phase
      (mkScutfirstCase "fuzz/cellund/refs+1"
        (mkScutfirstStackNat s wantBits (totalRefs0 + 1)), rng6)
  else if shape = 4 then
    let (n, rng2) := randNat rng1 0 2
    if n = 0 then
      (mkScutfirstCase "fuzz/underflow/empty" #[], rng2)
    else if n = 1 then
      (mkScutfirstCase "fuzz/underflow/one" #[.slice sliceBits8Refs0], rng2)
    else
      (mkScutfirstCase "fuzz/underflow/two" #[.slice sliceBits8Refs0, intV 1], rng2)
  else if shape = 5 then
    let (mode, rng2) := randNat rng1 0 3
    let badRefs : Value :=
      if mode = 0 then .null
      else if mode = 1 then intV (-1)
      else if mode = 2 then intV 5
      else .int .nan
    (mkScutfirstCase "fuzz/bad-refs"
      #[.slice sliceBits8Refs0, intV 1, badRefs], rng2)
  else if shape = 6 then
    let (mode, rng2) := randNat rng1 0 3
    let badBits : Value :=
      if mode = 0 then .null
      else if mode = 1 then intV (-1)
      else if mode = 2 then intV 1024
      else .int .nan
    (mkScutfirstCase "fuzz/bad-bits"
      #[.slice sliceBits8Refs0, badBits, intV 0], rng2)
  else
    (mkScutfirstCase "fuzz/bad-slice"
      #[.null, intV 1, intV 0], rng1)

def suite : InstrSuite where
  id := { name := "SCUTFIRST" }
  unit := #[
    { name := "unit/direct/success-boundaries-and-deep-stack"
      run := do
        let checks : Array (String × Slice × Nat × Nat) :=
          #[
            ("empty/0-0", sliceBits0Refs0, 0, 0),
            ("bits0-refs2", sliceBits0Refs4, 0, 2),
            ("bits5-refs0", sliceBits8Refs0, 5, 0),
            ("bits5-refs2", sliceBits8Refs3, 5, 2),
            ("bits8-refs4", sliceBits16Refs4, 8, 4),
            ("full-consume-16-2", sliceBits16Refs2, 16, 2),
            ("max-1023-refs4", sliceBits1023Refs4, 1023, 4)
          ]
        for (name, s, bits, refs) in checks do
          expectOkStack s!"ok/{name}"
            (runScutfirstDirect (mkScutfirstStackNat s bits refs))
            #[.slice (cutFirstSlice s bits refs)]

        expectOkStack "ok/deep-stack-preserve-below"
          (runScutfirstDirect
            (mkScutfirstStackNat sliceBits64Refs4 9 3 #[.null, intV 77, .cell refLeafD]))
          #[.null, intV 77, .cell refLeafD, .slice (cutFirstSlice sliceBits64Refs4 9 3)] }
    ,
    { name := "unit/direct/partial-cursor-respects-bitpos-refpos"
      run := do
        let checks : Array (String × Slice × Nat × Nat) :=
          #[
            ("mid/4-1", partialSliceMid, 4, 1),
            ("mid/0-2", partialSliceMid, 0, 2),
            ("mid/full-remaining", partialSliceMid, partialSliceMid.bitsRemaining, partialSliceMid.refsRemaining),
            ("bits-exhausted/0-2", partialSliceBitsExhausted, 0, 2),
            ("refs-exhausted/3-0", partialSliceRefsExhausted, 3, 0)
          ]
        for (name, s, bits, refs) in checks do
          expectOkStack s!"partial/{name}"
            (runScutfirstDirect (mkScutfirstStackNat s bits refs))
            #[.slice (cutFirstSlice s bits refs)] }
    ,
    { name := "unit/direct/cellund-insufficient-bits-or-refs"
      run := do
        expectErr "cellund/bits-insufficient-by1"
          (runScutfirstDirect (mkScutfirstStackNat sliceBits7Refs1 8 1)) .cellUnd
        expectErr "cellund/refs-insufficient-by1"
          (runScutfirstDirect (mkScutfirstStackNat sliceBits8Refs1 8 2)) .cellUnd
        expectErr "cellund/bits-and-refs-insufficient"
          (runScutfirstDirect (mkScutfirstStackNat sliceBits7Refs1 8 2)) .cellUnd
        expectErr "cellund/empty-slice-nonzero-bits"
          (runScutfirstDirect (mkScutfirstStackNat sliceBits0Refs0 1 0)) .cellUnd
        expectErr "cellund/refs-only-missing-bits"
          (runScutfirstDirect (mkScutfirstStackNat sliceBits0Refs4 1 2)) .cellUnd
        expectErr "cellund/bits-only-missing-refs"
          (runScutfirstDirect (mkScutfirstStackNat sliceBits8Refs0 0 1)) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty" (runScutfirstDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runScutfirstDirect #[.slice sliceBits8Refs0]) .stkUnd
        expectErr "underflow/two-items" (runScutfirstDirect #[.slice sliceBits8Refs0, intV 1]) .stkUnd

        expectErr "type/refs-top-null"
          (runScutfirstDirect #[.slice sliceBits8Refs0, intV 1, .null]) .typeChk
        expectErr "range/refs-over4"
          (runScutfirstDirect #[.slice sliceBits8Refs0, intV 1, intV 5]) .rangeChk
        expectErr "range/refs-negative"
          (runScutfirstDirect #[.slice sliceBits8Refs0, intV 1, intV (-1)]) .rangeChk
        expectErr "range/refs-nan"
          (runScutfirstDirect #[.slice sliceBits8Refs0, intV 1, .int .nan]) .rangeChk

        expectErr "type/bits-not-int-after-valid-refs"
          (runScutfirstDirect #[.slice sliceBits8Refs0, .null, intV 0]) .typeChk
        expectErr "range/bits-over1023"
          (runScutfirstDirect #[.slice sliceBits8Refs0, intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-negative"
          (runScutfirstDirect #[.slice sliceBits8Refs0, intV (-1), intV 0]) .rangeChk
        expectErr "range/bits-nan"
          (runScutfirstDirect #[.slice sliceBits8Refs0, .int .nan, intV 0]) .rangeChk

        expectErr "type/slice-not-slice"
          (runScutfirstDirect #[.null, intV 1, intV 0]) .typeChk

        expectErr "order/refs-range-before-bits-type"
          (runScutfirstDirect #[.null, .null, intV 5]) .rangeChk
        expectErr "order/bits-range-before-slice-type"
          (runScutfirstDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "order/bits-type-before-slice-type"
          (runScutfirstDirect #[.null, .null, intV 0]) .typeChk }
    ,
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-0-0", mkScutfirstStackNat sliceBits0Refs0 0 0),
            ("ok/refs-only-0-2", mkScutfirstStackNat sliceBits0Refs4 0 2),
            ("ok/full-16-2", mkScutfirstStackNat sliceBits16Refs2 16 2),
            ("ok/partial-mid-4-1", mkScutfirstStackNat partialSliceMid 4 1),
            ("ok/deep", mkScutfirstStackNat sliceBits32Refs1 7 1 #[.null, intV 9]),
            ("err/cellund-bits", mkScutfirstStackNat sliceBits7Refs1 8 1),
            ("err/cellund-refs", mkScutfirstStackNat sliceBits8Refs1 8 2),
            ("err/underflow", #[]),
            ("err/type-refs", #[.slice sliceBits8Refs0, intV 1, .null]),
            ("err/range-refs", #[.slice sliceBits8Refs0, intV 1, intV 5]),
            ("err/type-bits", #[.slice sliceBits8Refs0, .null, intV 0]),
            ("err/range-bits", #[.slice sliceBits8Refs0, intV 1024, intV 0]),
            ("err/type-slice", #[.null, intV 1, intV 0])
          ]
        for (name, stack) in samples do
          expectSameOutcome s!"model/{name}"
            (runScutfirstDirect stack)
            (runScutfirstModel stack) }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let canonical ←
          match assembleCp0 [scutfirstInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/canonical failed: {e}")
        if canonical.bits = natToBits scutfirstWord 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/canonical: expected opcode 0xd730, got bits {canonical.bits}")

        let program : Array Instr :=
          #[.sdcutlast, sdsubstrInstr, scutfirstInstr, sskipfirstInstr, scutlastInstr, sskiplastInstr, subsliceInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdcutlast-neighbor" s0 .sdcutlast 16
        let s2 ← expectDecodeStep "decode/sdsubstr-neighbor" s1 sdsubstrInstr 16
        let s3 ← expectDecodeStep "decode/scutfirst" s2 scutfirstInstr 16
        let s4 ← expectDecodeStep "decode/sskipfirst-neighbor" s3 sskipfirstInstr 16
        let s5 ← expectDecodeStep "decode/scutlast-neighbor" s4 scutlastInstr 16
        let s6 ← expectDecodeStep "decode/sskiplast-neighbor" s5 sskiplastInstr 16
        let s7 ← expectDecodeStep "decode/subslice-neighbor" s6 subsliceInstr 16
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/sequence-end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd724 16
            ++ natToBits scutfirstWord 16
            ++ natToBits 0xd731 16
            ++ natToBits 0xd732 16
            ++ natToBits 0xd733 16
            ++ natToBits 0xd734 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdsubstr" r0 sdsubstrInstr 16
        let r2 ← expectDecodeStep "decode/raw-scutfirst" r1 scutfirstInstr 16
        let r3 ← expectDecodeStep "decode/raw-sskipfirst" r2 sskipfirstInstr 16
        let r4 ← expectDecodeStep "decode/raw-scutlast" r3 scutlastInstr 16
        let r5 ← expectDecodeStep "decode/raw-sskiplast" r4 sskiplastInstr 16
        let r6 ← expectDecodeStep "decode/raw-subslice" r5 subsliceInstr 16
        let r7 ← expectDecodeStep "decode/raw-tail-add" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-scutfirst-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runScutfirstDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-sskipfirst"
          (runScutfirstDispatchFallback sskipfirstInstr #[intV 7])
          #[intV 7, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-sdcutfirst"
          (runScutfirstDispatchFallback .sdcutfirst #[])
          #[intV dispatchSentinel] }
  ]
  oracle := #[
    mkScutfirstCase "ok/empty-0-0" (mkScutfirstStackNat sliceBits0Refs0 0 0),
    mkScutfirstCase "ok/refs-only-0-2" (mkScutfirstStackNat sliceBits0Refs4 0 2),
    mkScutfirstCase "ok/bits5-refs0" (mkScutfirstStackNat sliceBits8Refs0 5 0),
    mkScutfirstCase "ok/bits5-refs2" (mkScutfirstStackNat sliceBits8Refs3 5 2),
    mkScutfirstCase "ok/bits8-refs4" (mkScutfirstStackNat sliceBits16Refs4 8 4),
    mkScutfirstCase "ok/full-consume-16-2" (mkScutfirstStackNat sliceBits16Refs2 16 2),
    mkScutfirstCase "ok/max-1023-refs4" (mkScutfirstStackNat sliceBits1023Refs4 1023 4),
    mkScutfirstCase "ok/deep-stack-preserve" (mkScutfirstStackNat sliceBits64Refs4 9 3 #[.null, .cell refLeafA]),

    mkScutfirstCase "cellund/bits-insufficient-by1" (mkScutfirstStackNat sliceBits7Refs1 8 1),
    mkScutfirstCase "cellund/refs-insufficient-by1" (mkScutfirstStackNat sliceBits8Refs1 8 2),
    mkScutfirstCase "cellund/bits-and-refs-insufficient" (mkScutfirstStackNat sliceBits7Refs1 8 2),
    mkScutfirstCase "cellund/empty-slice-nonzero-bits" (mkScutfirstStackNat sliceBits0Refs0 1 0),
    mkScutfirstCase "cellund/bits-only-missing-refs" (mkScutfirstStackNat sliceBits8Refs0 0 1),

    mkScutfirstCase "underflow/empty" #[],
    mkScutfirstCase "underflow/two-items" #[.slice sliceBits8Refs0, intV 1],
    mkScutfirstCase "type/refs-top-null" #[.slice sliceBits8Refs0, intV 1, .null],
    mkScutfirstCase "range/refs-over4" #[.slice sliceBits8Refs0, intV 1, intV 5],
    mkScutfirstCase "type/bits-not-int" #[.slice sliceBits8Refs0, .null, intV 0],
    mkScutfirstCase "range/bits-over1023" #[.slice sliceBits8Refs0, intV 1024, intV 0],
    mkScutfirstCase "type/slice-not-slice" #[.null, intV 1, intV 0],
    mkScutfirstCase "order/refs-range-before-bits-type" #[.null, .null, intV 5],
    mkScutfirstCase "order/bits-range-before-slice-type" #[.null, intV 1024, intV 0],

    mkScutfirstCase "gas/exact-cost-succeeds"
      (mkScutfirstStackNat sliceBits16Refs2 8 2)
      #[.pushInt (.num scutfirstSetGasExact), .tonEnvOp .setGasLimit, scutfirstInstr],
    mkScutfirstCase "gas/exact-minus-one-out-of-gas"
      (mkScutfirstStackNat sliceBits16Refs2 8 2)
      #[.pushInt (.num scutfirstSetGasExactMinusOne), .tonEnvOp .setGasLimit, scutfirstInstr]
  ]
  fuzz := #[
    { seed := 2026021111
      count := 500
      gen := genScutfirstFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCUTFIRST
