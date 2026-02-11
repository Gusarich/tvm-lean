import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDPFX

/-
SDPFX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdPfx.lean` (`.sdPfx`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc708` decode to `.sdPfx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdPfx` encode to `0xc708`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_bin_cs_cmp`, opcode registration for `SDPFX`)

Branch map used for this suite:
- dispatch guard (`.sdPfx` vs fallback-to-`next`);
- stack errors across the two `popSlice` calls (underflow/type ordering);
- core predicate: `prefBits` is a prefix of `sBits` (including equality and empty prefix);
- non-prefix outcomes (length mismatch and bit mismatch);
- opcode encode/decode boundary around neighbors `0xc705/0xc708/0xc709/0xc70a`.

Semantic intent checked here:
- stack order is `... pref s` (top is `s`);
- comparison uses remaining bits only (refs ignored);
- result is pushed as TVM bool smallint (`-1` true, `0` false).
-/

private def sdpfxId : InstrId := { name := "SDPFX" }

private def sdpfxInstr : Instr := .sdPfx

private def sdpfxWord : Nat := 0xc708

private def dispatchSentinel : Int := 708

private def mkSdpfxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdpfxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdpfxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdpfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPfx sdpfxInstr stack

private def runSdpfxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdPfx instr (VM.push (intV dispatchSentinel)) stack

private def mkWordSlice
    (bits : Nat)
    (word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def mkStripedSlice
    (bits : Nat)
    (phase : Nat := 0)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def emptySlice : Slice := mkSliceWithBitsRefs #[]
private def pref5 : Slice := mkWordSlice 5 0x15
private def target8FromPref5 : Slice := mkWordSlice 8 0xad
private def equal8A5 : Slice := mkWordSlice 8 0xa5
private def prefix255 : Slice := mkStripedSlice 255 1
private def target256FromPrefix255 : Slice := mkStripedSlice 255 1 #[true]
private def prefix256 : Slice := mkStripedSlice 256 0
private def target255 : Slice := mkStripedSlice 255 0
private def prefix33 : Slice := mkStripedSlice 33 1
private def target32 : Slice := mkStripedSlice 32 1
private def prefix32 : Slice := mkStripedSlice 32 0
private def target64FromPrefix32 : Slice := mkStripedSlice 32 0 tailBits11

private def pref8WithRefs : Slice := mkWordSlice 8 0xa5 #[] #[refLeafA, refLeafB]
private def target8WithRefs : Slice := mkWordSlice 8 0xa5 #[] #[refLeafC]

private def cursorPrefCell : Cell := Cell.mkOrdinary (tailBits3 ++ stripeBits 11 0) #[refLeafA, refLeafB]
private def cursorTargetCell : Cell := Cell.mkOrdinary (tailBits5 ++ stripeBits 11 0 ++ tailBits7) #[refLeafC]
private def cursorMismatchTargetCell : Cell :=
  Cell.mkOrdinary (tailBits5 ++ stripeBits 11 1 ++ tailBits7) #[refLeafA, refLeafC]

private def cursorPref : Slice :=
  { cell := cursorPrefCell, bitPos := tailBits3.size, refPos := 1 }

private def cursorTarget : Slice :=
  { cell := cursorTargetCell, bitPos := tailBits5.size, refPos := 1 }

private def cursorTargetMismatch : Slice :=
  { cell := cursorMismatchTargetCell, bitPos := tailBits5.size, refPos := 1 }

private def sdpfxSetGasExact : Int :=
  computeExactGasBudget sdpfxInstr

private def sdpfxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdpfxInstr

def suite : InstrSuite where
  id := { name := "SDPFX" }
  unit := #[
    { name := "unit/direct/prefix-truth-table"
      run := do
        let checks : Array (String × Slice × Slice × Int) :=
          #[
            ("ok/empty-vs-empty", emptySlice, emptySlice, -1),
            ("ok/empty-prefix-vs-nonempty", emptySlice, equal8A5, -1),
            ("ok/equal-8bits", equal8A5, equal8A5, -1),
            ("ok/proper-prefix-1-of-8", mkWordSlice 1 1, equal8A5, -1),
            ("ok/proper-prefix-7-of-8", mkWordSlice 7 0x52, equal8A5, -1),
            ("fail/mismatch-first-bit", mkWordSlice 8 0x80, mkWordSlice 8 0x00, 0),
            ("fail/mismatch-middle-bit", mkWordSlice 8 0xac, mkWordSlice 8 0xa4, 0),
            ("fail/mismatch-last-bit", mkWordSlice 8 0xfe, mkWordSlice 8 0xff, 0),
            ("fail/target-shorter-by-1", mkStripedSlice 9 0, mkStripedSlice 8 0, 0),
            ("ok/prefix-255-of-256", prefix255, target256FromPrefix255, -1)
          ]
        for (label, pref, s, expected) in checks do
          expectOkStack label
            (runSdpfxDirect #[.slice pref, .slice s])
            #[intV expected] }
    ,
    { name := "unit/direct/order-refs-cursor-and-deep-stack"
      run := do
        expectOkStack "ok/refs-ignored-equal-bits"
          (runSdpfxDirect #[.slice pref8WithRefs, .slice equal8A5])
          #[intV (-1)]

        expectOkStack "ok/refs-ignored-target-side"
          (runSdpfxDirect #[.slice pref5, .slice (mkWordSlice 8 0xad #[] #[refLeafA, refLeafC])])
          #[intV (-1)]

        expectOkStack "ok/cursor-prefix"
          (runSdpfxDirect #[.slice cursorPref, .slice cursorTarget])
          #[intV (-1)]

        expectOkStack "fail/cursor-prefix-mismatch"
          (runSdpfxDirect #[.slice cursorPref, .slice cursorTargetMismatch])
          #[intV 0]

        expectOkStack "ok/stack-order-pref-then-s"
          (runSdpfxDirect #[.slice pref5, .slice target8FromPref5])
          #[intV (-1)]

        expectOkStack "fail/stack-order-reversed"
          (runSdpfxDirect #[.slice target8FromPref5, .slice pref5])
          #[intV 0]

        expectOkStack "ok/deep-stack-preserved"
          (runSdpfxDirect #[.null, intV 17, .slice pref5, .slice target8FromPref5])
          #[.null, intV 17, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-ordering"
      run := do
        expectErr "underflow/empty"
          (runSdpfxDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdpfxDirect #[.slice equal8A5]) .stkUnd
        expectErr "type/one-non-slice"
          (runSdpfxDirect #[.null]) .typeChk

        expectErr "type/top-null"
          (runSdpfxDirect #[.slice equal8A5, .null]) .typeChk
        expectErr "type/top-int"
          (runSdpfxDirect #[.slice equal8A5, intV 7]) .typeChk
        expectErr "type/top-cell"
          (runSdpfxDirect #[.slice equal8A5, .cell Cell.empty]) .typeChk
        expectErr "type/second-not-slice"
          (runSdpfxDirect #[.null, .slice equal8A5]) .typeChk
        expectErr "type/second-int-not-slice"
          (runSdpfxDirect #[intV (-3), .slice equal8A5]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let singleCode ←
          match assembleCp0 [sdpfxInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdpfx failed: {e}")
        if singleCode.bits = natToBits sdpfxWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdpfx: expected 0xc708, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdpfx: expected 16 bits, got {singleCode.bits.size}")

        let asmProgram : Array Instr := #[.sdEq, sdpfxInstr, .sdPfxRev, .sdPpfx, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-sdeq" a0 .sdEq 16
        let a2 ← expectDecodeStep "decode/asm-sdpfx" a1 sdpfxInstr 16
        let a3 ← expectDecodeStep "decode/asm-sdpfxrev" a2 .sdPfxRev 16
        let a4 ← expectDecodeStep "decode/asm-sdppfx" a3 .sdPpfx 16
        let a5 ← expectDecodeStep "decode/asm-tail-add" a4 .add 8
        if a5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a5.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xc705 16 ++
          natToBits sdpfxWord 16 ++
          natToBits 0xc709 16 ++
          natToBits 0xc70a 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdeq-neighbor" r0 .sdEq 16
        let r2 ← expectDecodeStep "decode/raw-sdpfx" r1 sdpfxInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdpfxrev-neighbor" r2 .sdPfxRev 16
        let r4 ← expectDecodeStep "decode/raw-sdppfx-neighbor" r3 .sdPpfx 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdpfx-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runSdpfxDispatchFallback .add #[.null, intV 1])
          #[.null, intV 1, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdpfxCase "ok/empty-prefix-empty-target"
      #[.slice emptySlice, .slice emptySlice],
    mkSdpfxCase "ok/empty-prefix-nonempty-target"
      #[.slice emptySlice, .slice equal8A5],
    mkSdpfxCase "ok/equal-8bits"
      #[.slice equal8A5, .slice equal8A5],
    mkSdpfxCase "ok/proper-prefix-1-of-8"
      #[.slice (mkWordSlice 1 1), .slice equal8A5],
    mkSdpfxCase "ok/proper-prefix-7-of-8"
      #[.slice (mkWordSlice 7 0x52), .slice equal8A5],
    mkSdpfxCase "ok/prefix-32-of-64"
      #[.slice prefix32, .slice target64FromPrefix32],
    mkSdpfxCase "ok/prefix-255-of-256"
      #[.slice prefix255, .slice target256FromPrefix255],
    mkSdpfxCase "ok/refs-ignored-prefix-side"
      #[.slice pref8WithRefs, .slice equal8A5],
    mkSdpfxCase "ok/refs-ignored-target-side"
      #[.slice equal8A5, .slice target8WithRefs],
    mkSdpfxCase "ok/deep-stack-preserve-null"
      #[.null, .slice pref5, .slice target8FromPref5],
    mkSdpfxCase "ok/deep-stack-preserve-null-int"
      #[.null, intV 77, .slice pref5, .slice target8FromPref5],

    mkSdpfxCase "fail/nonempty-prefix-empty-target"
      #[.slice pref5, .slice emptySlice],
    mkSdpfxCase "fail/mismatch-first-bit"
      #[.slice (mkWordSlice 8 0x80), .slice (mkWordSlice 8 0x00)],
    mkSdpfxCase "fail/mismatch-middle-bit"
      #[.slice (mkWordSlice 8 0xac), .slice (mkWordSlice 8 0xa4)],
    mkSdpfxCase "fail/mismatch-last-bit"
      #[.slice (mkWordSlice 8 0xfe), .slice (mkWordSlice 8 0xff)],
    mkSdpfxCase "fail/target-shorter-by-1"
      #[.slice prefix256, .slice target255],
    mkSdpfxCase "fail/prefix-33-vs-target-32"
      #[.slice prefix33, .slice target32],
    mkSdpfxCase "fail/reversed-order-not-prefix"
      #[.slice target8FromPref5, .slice pref5],

    mkSdpfxCase "underflow/empty"
      #[],
    mkSdpfxCase "underflow/one-slice"
      #[.slice equal8A5],
    mkSdpfxCase "type/top-null"
      #[.slice equal8A5, .null],
    mkSdpfxCase "type/top-int"
      #[.slice equal8A5, intV (-9)],
    mkSdpfxCase "type/second-not-slice"
      #[.null, .slice equal8A5],

    mkSdpfxCase "gas/exact-cost-succeeds"
      #[.slice pref5, .slice target8FromPref5]
      #[.pushInt (.num sdpfxSetGasExact), .tonEnvOp .setGasLimit, sdpfxInstr],
    mkSdpfxCase "gas/exact-minus-one-out-of-gas"
      #[.slice pref5, .slice target8FromPref5]
      #[.pushInt (.num sdpfxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdpfxInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDPFX
