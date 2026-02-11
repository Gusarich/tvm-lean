import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SEMPTY

/-
SEMPTY branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sempty.lean` (`execInstrCellSempty`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc700` decodes to `.sempty`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sempty` encodes to `0xc700`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`reg_un_cs_cmp(... "SEMPTY", [](cs) { return cs->empty() && !cs->size_refs(); })`,
     shared unary path `exec_un_cs_cmp`).

Branch map used for this suite:
- dispatch guard: non-`.sempty` must fall through to `next`;
- top pop via `VM.popSlice`: `stkUnd` and `typeChk` branches;
- predicate result on remaining cursor state:
  `bitsRemaining = 0 && refsRemaining = 0` -> `-1`, otherwise `0`;
- cp0 encode/decode exact opcode `0xc700` with adjacent decode neighbors.
-/

private def semptyId : InstrId := { name := "SEMPTY" }

private def semptyInstr : Instr := .sempty

private def semptyOpcode : Nat := 0xc700
private def sdemptyOpcode : Nat := 0xc701
private def sremptyOpcode : Nat := 0xc702
private def sdfirstOpcode : Nat := 0xc703

private def dispatchSentinel : Int := 577

private def mkSemptyCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[semptyInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := semptyId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSemptyDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSempty semptyInstr stack

private def runSemptyDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSempty instr (VM.push (intV dispatchSentinel)) stack

private def semptyExpectedInt (s : Slice) : Int :=
  if s.bitsRemaining == 0 && s.refsRemaining == 0 then -1 else 0

private def semptyExpectedStack (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[intV (semptyExpectedInt s)]

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x1f 5) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0xa3 8) #[refLeafA]

private def sliceEmpty : Slice :=
  mkSliceWithBitsRefs #[] #[]

private def sliceBits1 : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[]

private def sliceBits31 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x5aa5abcd 31) #[]

private def sliceRefs1 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA]

private def sliceRefs4 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA, refLeafB, refLeafC, Cell.empty]

private def sliceBitsRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0b101101 6) #[refLeafA]

private def sliceBitsRefsLarge : Slice :=
  mkSliceWithBitsRefs (natToBits 0x1345 13) #[refLeafA, refLeafB]

private def cursorBaseCell : Cell :=
  Cell.mkOrdinary (natToBits 0b110011 6) #[refLeafA, refLeafB]

private def sliceCursorAllConsumed : Slice :=
  { cell := cursorBaseCell, bitPos := 6, refPos := 2 }

private def sliceCursorBitsConsumedOnly : Slice :=
  { cell := cursorBaseCell, bitPos := 6, refPos := 1 }

private def sliceCursorRefsConsumedOnly : Slice :=
  { cell := cursorBaseCell, bitPos := 2, refPos := 2 }

private def sliceCursorShiftedNonEmpty : Slice :=
  { cell := cursorBaseCell, bitPos := 2, refPos := 1 }

private def semptySetGasExact : Int :=
  computeExactGasBudget semptyInstr

private def semptySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne semptyInstr

def suite : InstrSuite where
  id := { name := "SEMPTY" }
  unit := #[
    { name := "unit/direct/result-matrix/full-slices"
      run := do
        let cases : Array Slice :=
          #[sliceEmpty, sliceBits1, sliceBits31, sliceRefs1, sliceRefs4, sliceBitsRefs, sliceBitsRefsLarge]
        for s in cases do
          expectOkStack s!"direct/full/bits-{s.bitsRemaining}/refs-{s.refsRemaining}"
            (runSemptyDirect #[.slice s])
            #[intV (semptyExpectedInt s)] }
    ,
    { name := "unit/direct/result-matrix/partial-cursors"
      run := do
        let cases : Array Slice :=
          #[sliceCursorAllConsumed, sliceCursorBitsConsumedOnly, sliceCursorRefsConsumedOnly, sliceCursorShiftedNonEmpty]
        for s in cases do
          expectOkStack s!"direct/cursor/bits-{s.bitsRemaining}/refs-{s.refsRemaining}"
            (runSemptyDirect #[.slice s])
            #[intV (semptyExpectedInt s)] }
    ,
    { name := "unit/direct/pop-order/deep-stack-preserved"
      run := do
        expectOkStack "deep/null-preserved-empty"
          (runSemptyDirect #[.null, .slice sliceEmpty])
          (semptyExpectedStack #[.null] sliceEmpty)
        expectOkStack "deep/int-preserved-bits"
          (runSemptyDirect #[intV 77, .slice sliceBits31])
          (semptyExpectedStack #[intV 77] sliceBits31)
        expectOkStack "deep/cell-preserved-refs"
          (runSemptyDirect #[.cell refLeafC, .slice sliceRefs1])
          (semptyExpectedStack #[.cell refLeafC] sliceRefs1)
        expectOkStack "deep/builder-preserved-cursor"
          (runSemptyDirect #[.builder Builder.empty, .slice sliceCursorAllConsumed])
          (semptyExpectedStack #[.builder Builder.empty] sliceCursorAllConsumed) }
    ,
    { name := "unit/direct/errors/underflow-and-type"
      run := do
        expectErr "underflow/empty" (runSemptyDirect #[]) .stkUnd
        expectErr "type/top-null" (runSemptyDirect #[.null]) .typeChk
        expectErr "type/top-int" (runSemptyDirect #[intV 7]) .typeChk
        expectErr "type/top-cell" (runSemptyDirect #[.cell refLeafA]) .typeChk
        expectErr "type/top-builder" (runSemptyDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty" (runSemptyDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont-quit0" (runSemptyDirect #[.cont (.quit 0)]) .typeChk }
    ,
    { name := "unit/direct/error-order/top-not-slice-before-below-slice"
      run := do
        expectErr "type/top-null-before-below-slice"
          (runSemptyDirect #[.slice sliceEmpty, .null]) .typeChk
        expectErr "type/top-int-before-below-slice"
          (runSemptyDirect #[.slice sliceEmpty, intV 11]) .typeChk
        expectErr "type/top-builder-before-below-slice"
          (runSemptyDirect #[.slice sliceEmpty, .builder Builder.empty]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let program : Array Instr := #[.sempty, .sdempty, .srempty, .cellOp .sdFirst, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sempty" s0 .sempty 16
        let s2 ← expectDecodeStep "decode/sdempty-neighbor" s1 .sdempty 16
        let s3 ← expectDecodeStep "decode/srempty-neighbor" s2 .srempty 16
        let s4 ← expectDecodeStep "decode/sdfirst-neighbor" s3 (.cellOp .sdFirst) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits")

        let single ←
          match assembleCp0 [.sempty] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sempty failed: {reprStr e}")
        if single.bits = natToBits semptyOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"opcode/sempty: expected {semptyOpcode}, got bits {reprStr single.bits}")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {reprStr e}")
        let rawBits : BitString :=
          natToBits semptyOpcode 16 ++
          natToBits sdemptyOpcode 16 ++
          natToBits sremptyOpcode 16 ++
          natToBits sdfirstOpcode 16 ++
          addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sempty" r0 .sempty 16
        let r2 ← expectDecodeStep "decode/raw-sdempty" r1 .sdempty 16
        let r3 ← expectDecodeStep "decode/raw-srempty" r2 .srempty 16
        let r4 ← expectDecodeStep "decode/raw-sdfirst" r3 (.cellOp .sdFirst) 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits") }
    ,
    { name := "unit/dispatch/non-sempty-falls-through"
      run := do
        expectOkStack "dispatch/sdempty"
          (runSemptyDispatchFallback .sdempty #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/srempty"
          (runSemptyDispatchFallback .srempty #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/add"
          (runSemptyDispatchFallback .add #[.cell refLeafA])
          #[.cell refLeafA, intV dispatchSentinel] }
    ,
    { name := "unit/direct/no-extra-exceptions"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok-empty", runSemptyDirect #[.slice sliceEmpty]),
            ("ok-bits", runSemptyDirect #[.slice sliceBits1]),
            ("underflow", runSemptyDirect #[]),
            ("type", runSemptyDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for SEMPTY")
          | .error .cellUnd =>
              throw (IO.userError s!"{p.1}: unexpected cellUnd for SEMPTY")
          | .error .intOv =>
              throw (IO.userError s!"{p.1}: unexpected intOv for SEMPTY")
          | _ => pure () }
  ]
  oracle := #[
    mkSemptyCase "ok/empty/full-empty" #[.slice sliceEmpty],
    mkSemptyCase "ok/nonempty/bits-1" #[.slice sliceBits1],
    mkSemptyCase "ok/nonempty/bits-31" #[.slice sliceBits31],
    mkSemptyCase "ok/nonempty/refs-1" #[.slice sliceRefs1],
    mkSemptyCase "ok/nonempty/refs-4" #[.slice sliceRefs4],
    mkSemptyCase "ok/nonempty/bits-and-refs" #[.slice sliceBitsRefs],
    mkSemptyCase "ok/nonempty/bits-and-refs-large" #[.slice sliceBitsRefsLarge],

    mkSemptyCase "ok/deep/null-preserved-empty" #[.null, .slice sliceEmpty],
    mkSemptyCase "ok/deep/int-preserved-bits" #[intV (-7), .slice sliceBits31],
    mkSemptyCase "ok/deep/cell-preserved-refs" #[.cell refLeafC, .slice sliceRefs1],
    mkSemptyCase "ok/deep/builder-empty-preserved" #[.builder Builder.empty, .slice sliceBits1],
    mkSemptyCase "ok/deep/tuple-empty-preserved" #[.tuple #[], .slice sliceRefs4],
    mkSemptyCase "ok/deep/cont-quit0-preserved" #[.cont (.quit 0), .slice sliceBitsRefs],

    mkSemptyCase "underflow/empty" #[],

    mkSemptyCase "type/top-null" #[.null],
    mkSemptyCase "type/top-int" #[intV 99],
    mkSemptyCase "type/top-cell" #[.cell refLeafA],
    mkSemptyCase "type/top-builder" #[.builder Builder.empty],
    mkSemptyCase "type/top-tuple-empty" #[.tuple #[]],
    mkSemptyCase "type/top-cont-quit0" #[.cont (.quit 0)],

    mkSemptyCase "error-order/top-null-before-below-slice"
      #[.slice sliceEmpty, .null],

    mkSemptyCase "gas/exact-cost-succeeds" #[.slice sliceBits1]
      #[.pushInt (.num semptySetGasExact), .tonEnvOp .setGasLimit, .sempty],

    mkSemptyCase "gas/exact-minus-one-out-of-gas" #[.slice sliceBits1]
      #[.pushInt (.num semptySetGasExactMinusOne), .tonEnvOp .setGasLimit, .sempty]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SEMPTY
