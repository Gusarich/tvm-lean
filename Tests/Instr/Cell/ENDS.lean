import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.ENDS

/-
ENDS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ends.lean` (`execInstrCellEnds`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd1` decodes to `.ends`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ends` assembles as `0xd1`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_chk_empty`, opcode table entry `0xd1` "ENDS")

Branch map used for this suite:
- dispatch guard: only `.ends` executes, all others fall through to `next`;
- `popSlice` on stack top: `stkUnd` / `typeChk` / success;
- cursor-emptiness split:
  `bitsRemaining = 0 && refsRemaining = 0` -> success (no push),
  otherwise throw `cellUnd`.

Key risk areas:
- ENDS must consume exactly one slice and push nothing;
- success must be based on cursor remainder (not backing cell totals);
- partial cursors with all remaining data consumed must succeed;
- opcode boundary around `0xd0/0xd1/0xd2` must decode with correct widths.
-/

private def endsId : InstrId := { name := "ENDS" }

private def endsInstr : Instr := .ends
private def ctosInstr : Instr := .ctos
private def ldi1Instr : Instr := .loadInt false false false 1

private def ctosOpcode : Nat := 0xd0
private def endsOpcode : Nat := 0xd1
private def ldiOpcode : Nat := 0xd2

private def dispatchSentinel : Int := 1709

private def mkEndsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[endsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := endsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runEndsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellEnds endsInstr stack

private def runEndsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellEnds instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

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

private def sliceBits1023 : Slice :=
  mkSliceWithBitsRefs (stripeBits 1023 1) #[]

private def sliceRefs1 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA]

private def sliceRefs4 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA, refLeafB, refLeafC, Cell.empty]

private def sliceBitsRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0x35 6) #[refLeafA]

private def cursorBaseCell : Cell :=
  Cell.mkOrdinary (natToBits 0x2d 6) #[refLeafA, refLeafB]

private def sliceCursorAllConsumed : Slice :=
  { cell := cursorBaseCell, bitPos := 6, refPos := 2 }

private def sliceCursorBitsRemain : Slice :=
  { cell := cursorBaseCell, bitPos := 5, refPos := 2 }

private def sliceCursorRefsRemain : Slice :=
  { cell := cursorBaseCell, bitPos := 6, refPos := 1 }

private def sliceCursorBothRemain : Slice :=
  { cell := cursorBaseCell, bitPos := 2, refPos := 1 }

private def endsSetGasExact : Int :=
  computeExactGasBudget endsInstr

private def endsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne endsInstr

def suite : InstrSuite where
  id := { name := "ENDS" }
  unit := #[
    { name := "unit/direct/success-when-cursor-fully-consumed"
      run := do
        let checks : Array (String × Slice) :=
          #[
            ("full/empty", sliceEmpty),
            ("cursor/all-consumed", sliceCursorAllConsumed)
          ]
        for c in checks do
          expectOkStack c.1 (runEndsDirect #[.slice c.2]) #[] }
    ,
    { name := "unit/direct/cellund-when-any-data-remains"
      run := do
        let checks : Array (String × Slice) :=
          #[
            ("full/bits-1", sliceBits1),
            ("full/bits-31", sliceBits31),
            ("full/bits-1023", sliceBits1023),
            ("full/refs-1", sliceRefs1),
            ("full/refs-4", sliceRefs4),
            ("full/bits-and-refs", sliceBitsRefs),
            ("cursor/bits-remain", sliceCursorBitsRemain),
            ("cursor/refs-remain", sliceCursorRefsRemain),
            ("cursor/bits-and-refs-remain", sliceCursorBothRemain)
          ]
        for c in checks do
          expectErr c.1 (runEndsDirect #[.slice c.2]) .cellUnd }
    ,
    { name := "unit/direct/deep-stack-preserved-on-success"
      run := do
        expectOkStack "deep/null-below-empty"
          (runEndsDirect #[.null, .slice sliceEmpty])
          #[.null]
        expectOkStack "deep/int-cell-below-cursor-consumed"
          (runEndsDirect #[intV 42, .cell refLeafC, .slice sliceCursorAllConsumed])
          #[intV 42, .cell refLeafC]
        expectOkStack "deep/builder-tuple-below-empty"
          (runEndsDirect #[.builder Builder.empty, .tuple #[], .slice sliceEmpty])
          #[.builder Builder.empty, .tuple #[]] }
    ,
    { name := "unit/direct/underflow-type-and-error-order"
      run := do
        expectErr "underflow/empty" (runEndsDirect #[]) .stkUnd

        let badTopVals : Array (String × Value) :=
          #[
            ("null", .null),
            ("int", intV 7),
            ("cell", .cell refLeafA),
            ("builder", .builder Builder.empty),
            ("tuple-empty", .tuple #[]),
            ("cont-quit0", .cont (.quit 0))
          ]
        for bad in badTopVals do
          expectErr s!"type/top-{bad.1}" (runEndsDirect #[bad.2]) .typeChk

        expectErr "type/order-top-first-null"
          (runEndsDirect #[.slice sliceEmpty, .null]) .typeChk
        expectErr "type/order-top-first-int"
          (runEndsDirect #[.slice sliceEmpty, intV 11]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let canonical ←
          match assembleCp0 [endsInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/ends failed: {e}")
        if canonical.bits = natToBits endsOpcode 8 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/ends: expected opcode 0xd1, got bits {reprStr canonical.bits}")

        let program : Array Instr := #[ctosInstr, endsInstr, .ldref, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ctos-d0" s0 ctosInstr 8
        let s2 ← expectDecodeStep "decode/ends-d1" s1 endsInstr 8
        let s3 ← expectDecodeStep "decode/ldref-d4" s2 .ldref 8
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/sequence-end: expected exhausted slice, got {s4.bitsRemaining} bits")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits ctosOpcode 8
            ++ natToBits endsOpcode 8
            ++ natToBits ldiOpcode 8
            ++ natToBits 0x00 8
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-ctos" r0 ctosInstr 8
        let r2 ← expectDecodeStep "decode/raw-ends" r1 endsInstr 8
        let r3 ← expectDecodeStep "decode/raw-ldi1" r2 ldi1Instr 16
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted slice, got {r4.bitsRemaining} bits") }
    ,
    { name := "unit/dispatch/non-ends-falls-through"
      run := do
        expectOkStack "dispatch/ctos"
          (runEndsDispatchFallback .ctos #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/add"
          (runEndsDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/sdempty"
          (runEndsDispatchFallback .sdempty #[.cell refLeafA])
          #[.cell refLeafA, intV dispatchSentinel] }
    ,
    { name := "unit/direct/no-unexpected-exception-kinds"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok/empty", runEndsDirect #[.slice sliceEmpty]),
            ("err/cellund", runEndsDirect #[.slice sliceBits1]),
            ("err/underflow", runEndsDirect #[]),
            ("err/type", runEndsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for ENDS")
          | .error .intOv =>
              throw (IO.userError s!"{p.1}: unexpected intOv for ENDS")
          | .error .cellOv =>
              throw (IO.userError s!"{p.1}: unexpected cellOv for ENDS")
          | _ => pure () }
  ]
  oracle := #[
    mkEndsCase "ok/empty/top-only" #[.slice sliceEmpty],
    mkEndsCase "ok/empty/deep-null" #[.null, .slice sliceEmpty],
    mkEndsCase "ok/empty/deep-int" #[intV (-7), .slice sliceEmpty],
    mkEndsCase "ok/empty/deep-cell" #[.cell refLeafC, .slice sliceEmpty],
    mkEndsCase "ok/empty/deep-builder" #[.builder Builder.empty, .slice sliceEmpty],
    mkEndsCase "ok/empty/deep-two-values" #[intV 8, .null, .slice sliceEmpty],

    mkEndsCase "cellund/bits-1" #[.slice sliceBits1],
    mkEndsCase "cellund/bits-31" #[.slice sliceBits31],
    mkEndsCase "cellund/bits-1023" #[.slice sliceBits1023],
    mkEndsCase "cellund/refs-1" #[.slice sliceRefs1],
    mkEndsCase "cellund/refs-4" #[.slice sliceRefs4],
    mkEndsCase "cellund/bits-and-refs" #[.slice sliceBitsRefs],
    mkEndsCase "cellund/deep-nonempty-slice" #[.null, .slice sliceBitsRefs],

    mkEndsCase "underflow/empty-stack" #[],

    mkEndsCase "type/top-null" #[.null],
    mkEndsCase "type/top-int" #[intV 0],
    mkEndsCase "type/top-cell" #[.cell refLeafA],
    mkEndsCase "type/top-builder" #[.builder Builder.empty],
    mkEndsCase "type/top-tuple-empty" #[.tuple #[]],
    mkEndsCase "type/top-cont-quit0" #[.cont (.quit 0)],

    mkEndsCase "error-order/top-null-before-below-slice"
      #[.slice sliceEmpty, .null],

    mkEndsCase "gas/exact-succeeds" #[.slice sliceEmpty]
      #[.pushInt (.num endsSetGasExact), .tonEnvOp .setGasLimit, endsInstr],
    mkEndsCase "gas/exact-minus-one-out-of-gas" #[.slice sliceEmpty]
      #[.pushInt (.num endsSetGasExactMinusOne), .tonEnvOp .setGasLimit, endsInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.ENDS
