import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SUBSLICE

/-
SUBSLICE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Subslice.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xd734` encode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd734` decode)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_subslice`)

Branch map covered by this suite:
- dispatch guard: `.cellOp .subslice` vs fallthrough to `next`;
- mandatory `checkUnderflow 5` before pop/type/range checks;
- pop order and validation: `r2`, `l2`, `r1`, `l1`, `slice`;
- success path: skip (`l1`,`r1`) then take (`l2`,`r2`), push only extracted subslice;
- failure split: first-stage vs second-stage `cellUnd`;
- opcode/decode boundaries around `0xd734` and adjacent opcodes.
-/

private def subsliceId : InstrId := { name := "SUBSLICE" }

private def subsliceInstr : Instr := .cellOp .subslice

private def sskiplastOpcode : Nat := 0xd733
private def subsliceOpcode : Nat := 0xd734
private def splitOpcode : Nat := 0xd736
private def splitQOpcode : Nat := 0xd737
private def xctosOpcode : Nat := 0xd739

private def dispatchSentinel : Int := 734

private def execInstrCellOpSubsliceOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpSubslice op next
  | _ => next

private def mkSubsliceCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[subsliceInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := subsliceId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSubsliceDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSubsliceOnly subsliceInstr stack

private def runSubsliceDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSubsliceOnly instr (VM.push (intV dispatchSentinel)) stack

private def natV (n : Nat) : Value :=
  intV (Int.ofNat n)

private def patternBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 0) || ((i.1 + phase) % 5 = 1)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b10101 5) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2d 6) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0b1100101 7) #[refLeafA]

private def refLeafD : Cell :=
  Cell.mkOrdinary (natToBits 0x5a 8) #[refLeafB]

private def refPool : Array Cell :=
  #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkRefs (count : Nat) : Array Cell := Id.run do
  let mut refs : Array Cell := #[]
  for i in [0:count] do
    refs := refs.push (refPool[i % refPool.size]!)
  return refs

private def mkPatternSlice (bitCount refCount : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternBits bitCount phase) (mkRefs refCount))

private def mkSubsliceNatStack
    (below : Array Value := #[])
    (s : Slice)
    (l1 r1 l2 r2 : Nat) : Array Value :=
  below ++ #[.slice s, natV l1, natV r1, natV l2, natV r2]

private def mkSubsliceNatCase
    (name : String)
    (s : Slice)
    (l1 r1 l2 r2 : Nat)
    (below : Array Value := #[]) : OracleCase :=
  mkSubsliceCase name (mkSubsliceNatStack below s l1 r1 l2 r2)

private def expectedSubslice? (s : Slice) (l1 r1 l2 r2 : Nat) : Option Slice :=
  if !s.haveBits l1 || !s.haveRefs r1 then
    none
  else
    let s1 : Slice := { s with bitPos := s.bitPos + l1, refPos := s.refPos + r1 }
    if !s1.haveBits l2 || !s1.haveRefs r2 then
      none
    else
      let stop : Slice := { s1 with bitPos := s1.bitPos + l2, refPos := s1.refPos + r2 }
      let outCell : Cell := Slice.prefixCell s1 stop
      some (Slice.ofCell outCell)

private def expectSubsliceSuccess
    (label : String)
    (below : Array Value)
    (s : Slice)
    (l1 r1 l2 r2 : Nat) : IO Unit := do
  match expectedSubslice? s l1 r1 l2 r2 with
  | none =>
      throw (IO.userError s!"{label}: invalid success fixture")
  | some expected =>
      expectOkStack label
        (runSubsliceDirect (mkSubsliceNatStack below s l1 r1 l2 r2))
        (below ++ #[.slice expected])

private def sliceEmpty : Slice :=
  mkPatternSlice 0 0

private def sliceBits8Refs2 : Slice :=
  mkPatternSlice 8 2

private def sliceBits16Refs1 : Slice :=
  mkPatternSlice 16 1

private def sliceBits24Refs2 : Slice :=
  mkPatternSlice 24 2 1

private def sliceBits40Refs4 : Slice :=
  mkPatternSlice 40 4 2

private def sliceBits1023Refs4 : Slice :=
  mkPatternSlice 1023 4 3

private def partialBaseCell : Cell :=
  Cell.mkOrdinary (patternBits 37 1) (mkRefs 4)

private def partialSliceA : Slice :=
  { cell := partialBaseCell, bitPos := 5, refPos := 1 }

private def partialSliceB : Slice :=
  { cell := partialBaseCell, bitPos := 12, refPos := 0 }

private def subsliceSetGasExact : Int :=
  computeExactGasBudget subsliceInstr

private def subsliceSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne subsliceInstr

def suite : InstrSuite where
  id := { name := "SUBSLICE" }
  unit := #[
    { name := "unit/direct/success-full-and-boundary-cases"
      run := do
        let cases : Array (String × Slice × Nat × Nat × Nat × Nat) :=
          #[
            ("empty->empty", sliceEmpty, 0, 0, 0, 0),
            ("full-copy-16b-1r", sliceBits16Refs1, 0, 0, 16, 1),
            ("bits-only-mid", sliceBits24Refs2, 5, 0, 7, 0),
            ("refs-only-mid", sliceBits24Refs2, 0, 1, 0, 1),
            ("mixed-mid", sliceBits40Refs4, 6, 1, 10, 2),
            ("postskip-empty", sliceBits40Refs4, 9, 2, 0, 0),
            ("max-bits-1023", sliceBits1023Refs4, 0, 0, 1023, 0),
            ("max-bits-and-refs", sliceBits1023Refs4, 0, 0, 1023, 4)
          ]
        for c in cases do
          expectSubsliceSuccess s!"ok/{c.1}" #[] c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2 }
    ,
    { name := "unit/direct/partial-cursor-and-deep-stack"
      run := do
        expectSubsliceSuccess "ok/partial-a" #[] partialSliceA 3 1 7 1
        expectSubsliceSuccess "ok/partial-b" #[] partialSliceB 4 0 8 2
        expectSubsliceSuccess "ok/deep-stack-preserved"
          #[.null, intV 91, .cell refLeafA] partialSliceA 2 1 6 1

        let stack := mkSubsliceNatStack #[] partialSliceA 3 1 7 1
        match runSubsliceDirect stack with
        | .ok #[.slice out] =>
            if out.bitPos = 0 && out.refPos = 0 then
              pure ()
            else
              throw (IO.userError s!"ok/partial-output-normalized: expected (0,0), got ({out.bitPos},{out.refPos})")
        | .ok st =>
            throw (IO.userError s!"ok/partial-output-normalized: unexpected stack {reprStr st}")
        | .error e =>
            throw (IO.userError s!"ok/partial-output-normalized: expected success, got {e}") }
    ,
    { name := "unit/direct/underflow-and-type-per-pop-position"
      run := do
        expectErr "underflow/empty" (runSubsliceDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runSubsliceDirect #[.slice sliceBits16Refs1]) .stkUnd
        expectErr "underflow/four-items"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0]) .stkUnd

        expectErr "type/r2-not-int"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0, .null]) .typeChk
        expectErr "type/l2-not-int"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, .null, natV 0]) .typeChk
        expectErr "type/r1-not-int"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, .null, natV 0, natV 0]) .typeChk
        expectErr "type/l1-not-int"
          (runSubsliceDirect #[.slice sliceBits16Refs1, .null, natV 0, natV 0, natV 0]) .typeChk
        expectErr "type/slice-not-slice"
          (runSubsliceDirect #[.null, natV 0, natV 0, natV 0, natV 0]) .typeChk }
    ,
    { name := "unit/direct/range-and-error-order"
      run := do
        expectErr "range/r2-negative"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0, intV (-1)]) .rangeChk
        expectErr "range/r2-too-large"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0, intV 5]) .rangeChk
        expectErr "range/l2-negative"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, intV (-1), natV 0]) .rangeChk
        expectErr "range/l2-too-large"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, intV 1024, natV 0]) .rangeChk
        expectErr "range/r1-negative"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, intV (-1), natV 0, natV 0]) .rangeChk
        expectErr "range/r1-too-large"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, intV 5, natV 0, natV 0]) .rangeChk
        expectErr "range/l1-negative"
          (runSubsliceDirect #[.slice sliceBits16Refs1, intV (-1), natV 0, natV 0, natV 0]) .rangeChk
        expectErr "range/l1-too-large"
          (runSubsliceDirect #[.slice sliceBits16Refs1, intV 1024, natV 0, natV 0, natV 0]) .rangeChk
        expectErr "range/r2-nan"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0, .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-type"
          (runSubsliceDirect #[.null, natV 0, natV 0, natV 0, intV 5]) .rangeChk
        expectErr "error-order/type-before-l2-range"
          (runSubsliceDirect #[.slice sliceBits16Refs1, natV 0, natV 0, intV 4096, .null]) .typeChk }
    ,
    { name := "unit/direct/cellund-first-stage-vs-second-stage"
      run := do
        expectErr "cellund/first-stage-bits"
          (runSubsliceDirect (mkSubsliceNatStack #[] sliceBits8Refs2 9 0 0 0)) .cellUnd
        expectErr "cellund/first-stage-refs"
          (runSubsliceDirect (mkSubsliceNatStack #[] sliceBits16Refs1 0 2 0 0)) .cellUnd
        expectErr "cellund/second-stage-bits"
          (runSubsliceDirect (mkSubsliceNatStack #[] sliceBits24Refs2 10 1 15 0)) .cellUnd
        expectErr "cellund/second-stage-refs"
          (runSubsliceDirect (mkSubsliceNatStack #[] sliceBits40Refs4 5 3 4 2)) .cellUnd
        expectErr "cellund/first-stage-before-second"
          (runSubsliceDirect (mkSubsliceNatStack #[] sliceBits16Refs1 20 2 999 4)) .cellUnd }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [subsliceInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/subslice failed: {reprStr e}")
        if assembled.bits = natToBits subsliceOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/subslice: expected 0xd734, got bits {assembled.bits}")

        let s0 := Slice.ofCell assembled
        let s1 ← expectDecodeStep "decode/assembled-subslice" s0 subsliceInstr 16
        if s1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/assembled-subslice: expected exhausted slice, got {s1.bitsRemaining} bits")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {reprStr e}")
        let rawBits : BitString :=
          natToBits sskiplastOpcode 16 ++
          natToBits subsliceOpcode 16 ++
          natToBits splitOpcode 16 ++
          natToBits splitQOpcode 16 ++
          natToBits xctosOpcode 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sskiplast" r0 (.cellOp .sskiplast) 16
        let r2 ← expectDecodeStep "decode/raw-subslice" r1 subsliceInstr 16
        let r3 ← expectDecodeStep "decode/raw-split" r2 (.cellOp (.split false)) 16
        let r4 ← expectDecodeStep "decode/raw-splitq" r3 (.cellOp (.split true)) 16
        let r5 ← expectDecodeStep "decode/raw-xctos" r4 .xctos 16
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining} bits")

        match decodeCp0WithBits (mkSliceFromBits (natToBits subsliceOpcode 7)) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/truncated: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-subslice-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-op"
          (runSubsliceDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cell-neighbor-skiplast"
          (runSubsliceDispatchFallback (.cellOp .sskiplast) #[.slice sliceBits16Refs1])
          #[.slice sliceBits16Refs1, intV dispatchSentinel]
        expectOkStack "dispatch/cell-neighbor-split"
          (runSubsliceDispatchFallback (.cellOp (.split false)) #[intV 11])
          #[intV 11, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSubsliceNatCase "ok/empty/l0-r0-l0-r0" sliceEmpty 0 0 0 0,
    mkSubsliceNatCase "ok/full-copy/16-1" sliceBits16Refs1 0 0 16 1,
    mkSubsliceNatCase "ok/full-copy/40-4" sliceBits40Refs4 0 0 40 4,
    mkSubsliceNatCase "ok/skip-bits/take-bits" sliceBits24Refs2 5 0 7 0,
    mkSubsliceNatCase "ok/skip-refs/take-refs" sliceBits24Refs2 0 1 0 1,
    mkSubsliceNatCase "ok/middle/bits-and-refs" sliceBits40Refs4 6 1 10 2,
    mkSubsliceNatCase "ok/postskip/empty" sliceBits40Refs4 9 2 0 0,
    mkSubsliceNatCase "ok/postskip/refs-only" sliceBits40Refs4 4 1 0 2,
    mkSubsliceNatCase "ok/postskip/bits-only" sliceBits40Refs4 8 2 9 0,
    mkSubsliceNatCase "ok/max-bits/1023" sliceBits1023Refs4 0 0 1023 0,
    mkSubsliceNatCase "ok/max-bits-and-refs/1023-4" sliceBits1023Refs4 0 0 1023 4,
    mkSubsliceNatCase "ok/deep-stack-preserve" sliceBits24Refs2 3 1 8 1 #[.null, intV 42],

    mkSubsliceNatCase "cellund/first-stage-bits" sliceBits8Refs2 9 0 0 0,
    mkSubsliceNatCase "cellund/first-stage-refs" sliceBits16Refs1 0 2 0 0,
    mkSubsliceNatCase "cellund/second-stage-bits" sliceBits24Refs2 10 1 15 0,
    mkSubsliceNatCase "cellund/second-stage-refs" sliceBits40Refs4 5 3 4 2,
    mkSubsliceNatCase "cellund/first-stage-before-second" sliceBits16Refs1 20 2 999 4,

    mkSubsliceCase "range/r2-negative" #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0, intV (-1)],
    mkSubsliceCase "range/r2-too-large" #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0, intV 5],
    mkSubsliceCase "range/l2-too-large" #[.slice sliceBits16Refs1, natV 0, natV 0, intV 1024, natV 0],
    mkSubsliceCase "range/r1-too-large" #[.slice sliceBits16Refs1, natV 0, intV 5, natV 0, natV 0],
    mkSubsliceCase "range/l1-too-large" #[.slice sliceBits16Refs1, intV 1024, natV 0, natV 0, natV 0],

    mkSubsliceCase "underflow/empty" #[],
    mkSubsliceCase "underflow/four-items" #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0],
    mkSubsliceCase "type/r2-not-int" #[.slice sliceBits16Refs1, natV 0, natV 0, natV 0, .null],
    mkSubsliceCase "type/slice-not-slice" #[.null, natV 0, natV 0, natV 0, natV 0],

    mkSubsliceCase "error-order/range-before-slice-type"
      #[.null, natV 0, natV 0, natV 0, intV 5],
    mkSubsliceCase "error-order/type-before-l2-range"
      #[.slice sliceBits16Refs1, natV 0, natV 0, intV 4096, .null],

    mkSubsliceCase "gas/exact-cost-succeeds"
      (mkSubsliceNatStack #[] sliceBits24Refs2 3 1 8 1)
      #[.pushInt (.num subsliceSetGasExact), .tonEnvOp .setGasLimit, subsliceInstr],
    mkSubsliceCase "gas/exact-minus-one-out-of-gas"
      (mkSubsliceNatStack #[] sliceBits24Refs2 3 1 8 1)
      #[.pushInt (.num subsliceSetGasExactMinusOne), .tonEnvOp .setGasLimit, subsliceInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SUBSLICE
