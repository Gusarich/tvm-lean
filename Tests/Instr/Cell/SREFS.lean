import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SREFS

/-
SREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Srefs.lean` (`execInstrCellSrefs`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.srefs` encodes as `0xd74a`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd74a` decodes to `.srefs`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_bits_refs(..., mode=2)` for opcode `0xd74a`).

Branch map covered by this suite:
- dispatch guard: `.srefs` executes, any other opcode falls through to `next`;
- stack pop path: `popSlice` success / underflow / strict top-type errors;
- success path: pushes exactly `refsRemaining` as small int; bits are ignored;
- cursor sensitivity: partial slices must use current `refPos`, not total refs;
- opcode/decode boundaries around `0xd748..0xd74f` (neighbors + masked family).

Harness note:
- oracle stack tokens can only encode full-cell slices (`bitPos = refPos = 0`);
  partial-cursor coverage is therefore concentrated in unit tests.
-/

private def srefsId : InstrId := { name := "SREFS" }

private def srefsInstr : Instr := .srefs
private def sbitsInstr : Instr := .sbits
private def sbitrefsInstr : Instr := .sbitrefs
private def pldRefVarInstr : Instr := .cellOp .pldRefVar
private def pldRefIdxInstr (idx : Nat) : Instr := .pldRefIdx idx

private def srefsOpcode : Nat := 0xd74a

private def dispatchSentinel : Int := 742

private def mkSrefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[srefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := srefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSrefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSrefs srefsInstr stack

private def runSrefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSrefs instr (VM.push (intV dispatchSentinel)) stack

private def srefsSetGasExact : Int :=
  computeExactGasBudget srefsInstr

private def srefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne srefsInstr

private def expectedSrefsInt (s : Slice) : Int :=
  Int.ofNat s.refsRemaining

private def expectedSrefsOut (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[intV (expectedSrefsInt s)]

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[Cell.empty]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0x1D 5) #[refLeafA]

private def refLeafD : Cell :=
  Cell.empty

private def sEmpty : Slice :=
  mkSliceWithBitsRefs #[] #[]

private def sBitsOnly1 : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[]

private def sBitsOnly31 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x5AA5ABCD 31) #[]

private def sBitsOnly1023 : Slice :=
  mkSliceWithBitsRefs (Array.replicate 1023 false) #[]

private def sRefsOnly1 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA]

private def sRefsOnly2 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]

private def sRefsOnly4 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA, refLeafB, refLeafC, refLeafD]

private def sBitsOnly7 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x4F 7) #[]

private def sBitsRefs1 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x2D 6) #[refLeafB]

private def sBitsRefs2 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x15D 9) #[refLeafA, refLeafB]

private def sBitsRefs4 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x5A3 11) #[refLeafA, refLeafB, refLeafC, refLeafD]

private def cursorCell4 : Cell :=
  Cell.mkOrdinary (natToBits 0x2D5 10) #[refLeafA, refLeafB, refLeafC, refLeafD]

private def sCursorRef0 : Slice :=
  { cell := cursorCell4, bitPos := 0, refPos := 0 }

private def sCursorRef1 : Slice :=
  { cell := cursorCell4, bitPos := 3, refPos := 1 }

private def sCursorRef3 : Slice :=
  { cell := cursorCell4, bitPos := 8, refPos := 3 }

private def sCursorAllRefsConsumed : Slice :=
  { cell := cursorCell4, bitPos := 9, refPos := 4 }

private def srefsSuccessCases : Array (String × Slice) :=
  #[
    ("full/empty", sEmpty),
    ("full/bits-1", sBitsOnly1),
    ("full/bits-31", sBitsOnly31),
    ("full/bits-1023", sBitsOnly1023),
    ("full/refs-1", sRefsOnly1),
    ("full/refs-4", sRefsOnly4),
    ("full/bits-plus-refs-1", sBitsRefs1),
    ("full/bits-plus-refs-4", sBitsRefs4),
    ("cursor/refpos-0", sCursorRef0),
    ("cursor/refpos-1", sCursorRef1),
    ("cursor/refpos-3", sCursorRef3),
    ("cursor/all-refs-consumed", sCursorAllRefsConsumed)
  ]

def suite : InstrSuite where
  id := { name := "SREFS" }
  unit := #[
    { name := "unit/direct/success-matrix-full-and-partial"
      run := do
        for c in srefsSuccessCases do
          let label := c.1
          let s := c.2
          expectOkStack s!"ok/{label}/refs-{s.refsRemaining}"
            (runSrefsDirect #[.slice s])
            #[intV (expectedSrefsInt s)] }
    ,
    { name := "unit/direct/deep-stack-preserved"
      run := do
        expectOkStack "deep/null-below"
          (runSrefsDirect #[.null, .slice sEmpty])
          (expectedSrefsOut #[.null] sEmpty)
        expectOkStack "deep/int-below"
          (runSrefsDirect #[intV (-17), .slice sRefsOnly4])
          (expectedSrefsOut #[intV (-17)] sRefsOnly4)
        expectOkStack "deep/cell-below"
          (runSrefsDirect #[.cell refLeafC, .slice sCursorRef1])
          (expectedSrefsOut #[.cell refLeafC] sCursorRef1)
        expectOkStack "deep/two-values-below"
          (runSrefsDirect #[.builder Builder.empty, .tuple #[], .slice sCursorRef3])
          (expectedSrefsOut #[.builder Builder.empty, .tuple #[]] sCursorRef3) }
    ,
    { name := "unit/direct/pop-order-top-slice-controls-result"
      run := do
        expectOkStack "order/two-slices-top-picked"
          (runSrefsDirect #[.slice sRefsOnly1, .slice sCursorRef3])
          #[.slice sRefsOnly1, intV 1]
        expectOkStack "order/non-slice-below-preserved"
          (runSrefsDirect #[.cell refLeafA, .slice sBitsRefs4])
          #[.cell refLeafA, intV 4] }
    ,
    { name := "unit/direct/errors-underflow-type-and-order"
      run := do
        expectErr "underflow/empty" (runSrefsDirect #[]) .stkUnd
        expectErr "type/top-null" (runSrefsDirect #[.null]) .typeChk
        expectErr "type/top-int" (runSrefsDirect #[intV 3]) .typeChk
        expectErr "type/top-cell" (runSrefsDirect #[.cell refLeafA]) .typeChk
        expectErr "type/top-builder" (runSrefsDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty" (runSrefsDirect #[.tuple #[]]) .typeChk
        expectErr "error-order/top-not-slice-before-below-slice"
          (runSrefsDirect #[.slice sRefsOnly1, .null]) .typeChk }
    ,
    { name := "unit/direct/no-unexpected-exceptions"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok", runSrefsDirect #[.slice sCursorRef1]),
            ("underflow", runSrefsDirect #[]),
            ("type", runSrefsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for SREFS")
          | .error .cellUnd =>
              throw (IO.userError s!"{p.1}: unexpected cellUnd for SREFS")
          | .error .intOv =>
              throw (IO.userError s!"{p.1}: unexpected intOv for SREFS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-assembler-boundaries"
      run := do
        let familyProgram : Array Instr := #[
          pldRefVarInstr,
          sbitsInstr,
          srefsInstr,
          sbitrefsInstr,
          pldRefIdxInstr 0,
          pldRefIdxInstr 3,
          .add
        ]
        let familyCode ←
          match assembleCp0 familyProgram.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/family failed: {e}")
        let f0 := Slice.ofCell familyCode
        let f1 ← expectDecodeStep "decode/pldrefvar-neighbor" f0 pldRefVarInstr 16
        let f2 ← expectDecodeStep "decode/sbits-neighbor" f1 sbitsInstr 16
        let f3 ← expectDecodeStep "decode/srefs-target" f2 srefsInstr 16
        let f4 ← expectDecodeStep "decode/sbitrefs-neighbor" f3 sbitrefsInstr 16
        let f5 ← expectDecodeStep "decode/pldrefidx-0-neighbor" f4 (pldRefIdxInstr 0) 16
        let f6 ← expectDecodeStep "decode/pldrefidx-3-neighbor" f5 (pldRefIdxInstr 3) 16
        let f7 ← expectDecodeStep "decode/tail-add" f6 .add 8
        if f7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/family-end: expected exhausted slice, got {f7.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [srefsInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/srefs failed: {e}")
        if singleCode.bits = natToBits srefsOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"opcode/srefs: expected 0xd74a encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError
            s!"opcode/srefs: expected 16-bit encoding, got {singleCode.bits.size}")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd748 16 ++
          natToBits 0xd749 16 ++
          natToBits srefsOpcode 16 ++
          natToBits 0xd74b 16 ++
          natToBits 0xd74c 16 ++
          natToBits 0xd74f 16 ++
          addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-pldrefvar" r0 pldRefVarInstr 16
        let r2 ← expectDecodeStep "decode/raw-sbits" r1 sbitsInstr 16
        let r3 ← expectDecodeStep "decode/raw-srefs" r2 srefsInstr 16
        let r4 ← expectDecodeStep "decode/raw-sbitrefs" r3 sbitrefsInstr 16
        let r5 ← expectDecodeStep "decode/raw-pldrefidx-0" r4 (pldRefIdxInstr 0) 16
        let r6 ← expectDecodeStep "decode/raw-pldrefidx-3" r5 (pldRefIdxInstr 3) 16
        let r7 ← expectDecodeStep "decode/raw-tail-add" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-srefs-falls-through"
      run := do
        expectOkStack "dispatch/sbits"
          (runSrefsDispatchFallback sbitsInstr #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sbitrefs"
          (runSrefsDispatchFallback sbitrefsInstr #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/pldrefvar"
          (runSrefsDispatchFallback pldRefVarInstr #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel]
        expectOkStack "dispatch/add"
          (runSrefsDispatchFallback .add #[.cell refLeafA])
          #[.cell refLeafA, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSrefsCase "ok/full-empty"
      #[.slice sEmpty],
    mkSrefsCase "ok/full-bits-1"
      #[.slice sBitsOnly1],
    mkSrefsCase "ok/full-bits-31"
      #[.slice sBitsOnly31],
    mkSrefsCase "ok/full-bits-1023"
      #[.slice sBitsOnly1023],
    mkSrefsCase "ok/full-refs-1"
      #[.slice sRefsOnly1],
    mkSrefsCase "ok/full-refs-2"
      #[.slice sRefsOnly2],
    mkSrefsCase "ok/full-refs-4"
      #[.slice sRefsOnly4],
    mkSrefsCase "ok/full-bits-7"
      #[.slice sBitsOnly7],
    mkSrefsCase "ok/full-bits-plus-refs-1"
      #[.slice sBitsRefs1],
    mkSrefsCase "ok/full-bits-plus-refs-2"
      #[.slice sBitsRefs2],
    mkSrefsCase "ok/full-bits-plus-refs-4"
      #[.slice sBitsRefs4],
    mkSrefsCase "ok/cursor-refpos-0"
      #[.slice sCursorRef0],

    mkSrefsCase "ok/deep/null-preserved"
      #[.null, .slice sEmpty],
    mkSrefsCase "ok/deep/int-preserved"
      #[intV (-7), .slice sRefsOnly4],
    mkSrefsCase "ok/deep/cell-preserved"
      #[.cell refLeafC, .slice sRefsOnly2],
    mkSrefsCase "ok/deep/two-values-preserved"
      #[.builder Builder.empty, .tuple #[], .slice sBitsRefs2],

    mkSrefsCase "underflow/empty"
      #[],

    mkSrefsCase "type/top-null"
      #[.null],
    mkSrefsCase "type/top-int"
      #[intV 42],
    mkSrefsCase "type/top-cell"
      #[.cell refLeafA],
    mkSrefsCase "type/top-builder"
      #[.builder Builder.empty],
    mkSrefsCase "error-order/top-null-before-below-slice"
      #[.slice sRefsOnly1, .null],

    mkSrefsCase "gas/exact-cost-succeeds"
      #[.slice sRefsOnly1]
      #[.pushInt (.num srefsSetGasExact), .tonEnvOp .setGasLimit, srefsInstr],
    mkSrefsCase "gas/exact-minus-one-out-of-gas"
      #[.slice sRefsOnly1]
      #[.pushInt (.num srefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, srefsInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SREFS
