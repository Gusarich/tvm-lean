import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDPPFX

/-
SDPPFX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdPpfx.lean` (`.sdPpfx`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc70a` decode to `.sdPpfx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdPpfx` encodes as `0xc70a`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_bin_cs_cmp`, opcode registration `0xc70a` as `SDPPFX`).

Branch map used for this suite:
- dispatch guard (`.sdPpfx` vs fallthrough to `next`);
- first `popSlice` failure split (`stkUnd`/`typeChk`);
- second `popSlice` failure split after first pop succeeds (`stkUnd`/`typeChk`);
- proper-prefix comparison on remaining bits only:
  `prefBits.size < sBits.size && sBits.take prefBits.size == prefBits`;
- push result is `-1` on true, `0` on false.

Key risk areas covered:
- strictness (`proper` prefix: equal slices must return `0`);
- argument order (`pref` is second-from-top, `s` is top);
- cursor-aware comparisons (`bitPos`/`refPos`) and ref-insensitive behavior;
- opcode boundary around `0xc709/0xc70a/0xc70b`;
- no reachable `rangeChk` path for SDPPFX.
-/

private def sdppfxId : InstrId := { name := "SDPPFX" }

private def sdppfxInstr : Instr := .sdPpfx

private def sdPfxInstr : Instr := .sdPfx
private def sdPfxRevInstr : Instr := .sdPfxRev
private def sdPpfxRevInstr : Instr := .sdPpfxRev

private def dispatchSentinel : Int := 948

private def mkSdppfxCase
    (name : String)
    (pref s : Slice)
    (below : Array Value := #[])
    (program : Array Instr := #[sdppfxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdppfxId
    program := program
    initStack := below ++ #[.slice pref, .slice s]
    gasLimits := gasLimits
    fuel := fuel }

private def mkSdppfxRawCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdppfxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdppfxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdppfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPpfx sdppfxInstr stack

private def runSdPfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPfx sdPfxInstr stack

private def runSdppfxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdPpfx instr (VM.push (intV dispatchSentinel)) stack

private def sdppfxSetGasExact : Int :=
  computeExactGasBudget sdppfxInstr

private def sdppfxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdppfxInstr

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 0b101 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 0b1101 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 0b11 2) #[]

private def prefEmpty : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA]

private def sOneBit : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[]

private def pref1 : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[]

private def s2 : Slice :=
  mkSliceWithBitsRefs (natToBits 0b10 2) #[]

private def pref3 : Slice :=
  mkSliceWithBitsRefs (natToBits 0b101 3) #[]

private def s5 : Slice :=
  mkSliceWithBitsRefs (natToBits 0b10110 5) #[]

private def pref12 : Slice :=
  mkSliceWithBitsRefs (stripeBits 12 0) #[]

private def s17 : Slice :=
  mkSliceWithBitsRefs (stripeBits 17 0) #[]

private def prefRefsHeavy : Slice :=
  mkSliceWithBitsRefs (natToBits 0b1101 4) #[refLeafA, refLeafB, refLeafC]

private def sRefsLight : Slice :=
  mkSliceWithBitsRefs (natToBits 0b110100 6) #[]

private def prefEqBitsRefs1 : Slice :=
  mkSliceWithBitsRefs (stripeBits 12 1) #[refLeafA]

private def sEqBitsRefs2 : Slice :=
  mkSliceWithBitsRefs (stripeBits 12 1) #[refLeafB, refLeafC]

private def prefLonger : Slice :=
  mkSliceWithBitsRefs (natToBits 0b110101 6) #[]

private def sShorter : Slice :=
  mkSliceWithBitsRefs (natToBits 0b1101 4) #[]

private def prefMismatchFirst : Slice :=
  mkSliceWithBitsRefs (natToBits 0b100 3) #[]

private def sMismatchFirst : Slice :=
  mkSliceWithBitsRefs (natToBits 0b01111 5) #[]

private def prefMismatchLater : Slice :=
  mkSliceWithBitsRefs (natToBits 0b1011 4) #[]

private def sMismatchLater : Slice :=
  mkSliceWithBitsRefs (natToBits 0b10101 5) #[]

private def sEmpty : Slice :=
  mkSliceWithBitsRefs #[] #[]

private def cursorPrefBitsCell : Cell :=
  Cell.mkOrdinary (natToBits 0b110101 6) #[refLeafA, refLeafB]

private def cursorPrefBits : Slice :=
  { cell := cursorPrefBitsCell, bitPos := 2, refPos := 1 }

private def cursorSBitsCell : Cell :=
  Cell.mkOrdinary (natToBits 0b11010111 8) #[refLeafC]

private def cursorSBits : Slice :=
  { cell := cursorSBitsCell, bitPos := 2, refPos := 0 }

private def cursorPrefBitsRefsCell : Cell :=
  Cell.mkOrdinary (natToBits 0b00101101 8) #[refLeafA, refLeafB, refLeafC]

private def cursorPrefBitsRefs : Slice :=
  { cell := cursorPrefBitsRefsCell, bitPos := 2, refPos := 1 }

private def cursorSBitsRefsCell : Cell :=
  Cell.mkOrdinary (natToBits 0b0010110101 10) #[refLeafC]

private def cursorSBitsRefs : Slice :=
  { cell := cursorSBitsRefsCell, bitPos := 2, refPos := 0 }

private def cursorEqPrefCell : Cell :=
  Cell.mkOrdinary (natToBits 0b0010101 7) #[refLeafA]

private def cursorEqPref : Slice :=
  { cell := cursorEqPrefCell, bitPos := 2, refPos := 0 }

private def cursorEqSCell : Cell :=
  Cell.mkOrdinary (natToBits 0b1110101 7) #[refLeafB]

private def cursorEqS : Slice :=
  { cell := cursorEqSCell, bitPos := 2, refPos := 0 }

private def oracleCursorPrefBits : Slice :=
  mkSliceWithBitsRefs (natToBits 0b0101 4) #[refLeafA]

private def oracleCursorSBits : Slice :=
  mkSliceWithBitsRefs (natToBits 0b010111 6) #[refLeafC]

private def oracleCursorPrefBitsRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0b101101 6) #[refLeafA, refLeafB]

private def oracleCursorSBitsRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 0b10110101 8) #[refLeafC]

private def oracleCursorEqPref : Slice :=
  mkSliceWithBitsRefs (natToBits 0b10101 5) #[refLeafA]

private def oracleCursorEqS : Slice :=
  mkSliceWithBitsRefs (natToBits 0b10101 5) #[refLeafB]

def suite : InstrSuite where
  id := sdppfxId
  unit := #[
    { name := "unit/direct/proper-prefix-truth-table"
      run := do
        expectOkStack "ok/empty-prefix-vs-one-bit"
          (runSdppfxDirect #[.slice prefEmpty, .slice sOneBit])
          #[intV (-1)]
        expectOkStack "ok/1-to-2"
          (runSdppfxDirect #[.slice pref1, .slice s2])
          #[intV (-1)]
        expectOkStack "ok/3-to-5"
          (runSdppfxDirect #[.slice pref3, .slice s5])
          #[intV (-1)]
        expectOkStack "false/both-empty"
          (runSdppfxDirect #[.slice sEmpty, .slice sEmpty])
          #[intV 0]
        expectOkStack "false/equal-nonempty"
          (runSdppfxDirect #[.slice pref3, .slice pref3])
          #[intV 0]
        expectOkStack "false/pref-longer"
          (runSdppfxDirect #[.slice prefLonger, .slice sShorter])
          #[intV 0]
        expectOkStack "false/mismatch-first"
          (runSdppfxDirect #[.slice prefMismatchFirst, .slice sMismatchFirst])
          #[intV 0]
        expectOkStack "false/mismatch-later"
          (runSdppfxDirect #[.slice prefMismatchLater, .slice sMismatchLater])
          #[intV 0] }
    ,
    { name := "unit/direct/cursors-refs-and-stack-preservation"
      run := do
        expectOkStack "ok/cursor-bits"
          (runSdppfxDirect #[.slice cursorPrefBits, .slice cursorSBits])
          #[intV (-1)]
        expectOkStack "ok/cursor-bits-refs"
          (runSdppfxDirect #[.slice cursorPrefBitsRefs, .slice cursorSBitsRefs])
          #[intV (-1)]
        expectOkStack "false/cursor-equal-remaining"
          (runSdppfxDirect #[.slice cursorEqPref, .slice cursorEqS])
          #[intV 0]
        expectOkStack "ok/refs-ignored"
          (runSdppfxDirect #[.slice prefRefsHeavy, .slice sRefsLight])
          #[intV (-1)]
        expectOkStack "ok/deep-stack-preserved"
          (runSdppfxDirect #[.null, intV 77, .slice pref3, .slice s5])
          #[.null, intV 77, intV (-1)] }
    ,
    { name := "unit/direct/error-ordering"
      run := do
        expectErr "underflow/empty" (runSdppfxDirect #[]) .stkUnd
        expectErr "underflow/one-slice" (runSdppfxDirect #[.slice s5]) .stkUnd
        expectErr "type/top-null" (runSdppfxDirect #[.slice pref3, .null]) .typeChk
        expectErr "type/top-int" (runSdppfxDirect #[.slice pref3, intV 1]) .typeChk
        expectErr "type/top-builder" (runSdppfxDirect #[.slice pref3, .builder Builder.empty]) .typeChk
        expectErr "type/second-pop-after-first-slice"
          (runSdppfxDirect #[.null, .slice s5]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("true", runSdppfxDirect #[.slice pref3, .slice s5]),
            ("false", runSdppfxDirect #[.slice pref3, .slice pref3]),
            ("underflow", runSdppfxDirect #[]),
            ("type", runSdppfxDirect #[.slice pref3, .null]),
            ("type-second-pop", runSdppfxDirect #[.null, .slice s5])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for SDPPFX")
          | _ => pure () }
    ,
    { name := "unit/opcode/encode-decode-and-neighbors"
      run := do
        let encoded ←
          match assembleCp0 [sdppfxInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble sdppfx failed: {e}")
        if encoded.bits = natToBits 0xc70a 16 then
          pure ()
        else
          throw (IO.userError s!"sdppfx encode mismatch: got {encoded.bits}")

        let program : Array Instr := #[sdPfxRevInstr, sdppfxInstr, sdPpfxRevInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble decode sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdpfxrev-0xc709" s0 sdPfxRevInstr 16
        let s2 ← expectDecodeStep "decode/sdppfx-0xc70a" s1 sdppfxInstr 16
        let s3 ← expectDecodeStep "decode/sdppfxrev-0xc70b" s2 sdPpfxRevInstr 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/relations-and-dispatch"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("proper-implies-prefix/ok-3-to-5", pref3, s5),
            ("proper-implies-prefix/ok-12-to-17", pref12, s17),
            ("equal-not-proper-but-prefix", pref3, pref3),
            ("mismatch-neither", prefMismatchLater, sMismatchLater)
          ]
        for c in checks do
          let label := c.1
          let pref := c.2.1
          let s := c.2.2
          let sdppfxRes := runSdppfxDirect #[.slice pref, .slice s]
          let sdpfxRes := runSdPfxDirect #[.slice pref, .slice s]
          match sdppfxRes, sdpfxRes with
          | .ok sdppfxStack, .ok sdpfxStack =>
              let sdppfxV := sdppfxStack.back?
              let sdpfxV := sdpfxStack.back?
              if sdppfxV == some (intV (-1)) && sdpfxV != some (intV (-1)) then
                throw (IO.userError s!"{label}: SDPPFX true must imply SDPFX true")
              else
                pure ()
          | .error e, _ =>
              throw (IO.userError s!"{label}: SDPPFX unexpected error {e}")
          | _, .error e =>
              throw (IO.userError s!"{label}: SDPFX unexpected error {e}")

        expectOkStack "dispatch/fallback"
          (runSdppfxDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdppfxCase "ok/empty-prefix-vs-one-bit"
      prefEmpty sOneBit,
    mkSdppfxCase "ok/1-to-2"
      pref1 s2,
    mkSdppfxCase "ok/3-to-5"
      pref3 s5,
    mkSdppfxCase "ok/12-to-17-pattern"
      pref12 s17,
    mkSdppfxCase "ok/refs-ignored"
      prefRefsHeavy sRefsLight,
    mkSdppfxCase "ok/cursor-bits"
      oracleCursorPrefBits oracleCursorSBits,
    mkSdppfxCase "ok/cursor-bits-refs"
      oracleCursorPrefBitsRefs oracleCursorSBitsRefs,
    mkSdppfxCase "ok/deep-preserve-null"
      pref3 s5 #[.null],
    mkSdppfxCase "ok/deep-preserve-int"
      pref3 s5 #[intV (-7)],
    mkSdppfxCase "ok/deep-preserve-cell"
      pref3 s5 #[.cell refLeafA],
    mkSdppfxCase "ok/deep-preserve-builder-empty"
      pref3 s5 #[.builder Builder.empty],
    mkSdppfxCase "ok/deep-preserve-two-values"
      pref3 s5 #[.null, intV 19],

    mkSdppfxCase "false/both-empty"
      sEmpty sEmpty,
    mkSdppfxCase "false/equal-1bit"
      pref1 pref1,
    mkSdppfxCase "false/equal-12bits-different-refs"
      prefEqBitsRefs1 sEqBitsRefs2,
    mkSdppfxCase "false/pref-longer-than-s"
      prefLonger sShorter,
    mkSdppfxCase "false/mismatch-first-bit"
      prefMismatchFirst sMismatchFirst,
    mkSdppfxCase "false/mismatch-later-bit"
      prefMismatchLater sMismatchLater,
    mkSdppfxCase "false/empty-s-with-nonempty-pref"
      pref1 sEmpty,
    mkSdppfxCase "false/cursor-equal-remaining"
      oracleCursorEqPref oracleCursorEqS,

    mkSdppfxRawCase "underflow/empty"
      #[],
    mkSdppfxRawCase "underflow/one-slice"
      #[.slice s5],
    mkSdppfxRawCase "type/top-null"
      #[.slice pref3, .null],
    mkSdppfxRawCase "type/top-int"
      #[.slice pref3, intV 17],
    mkSdppfxRawCase "type/top-builder-empty"
      #[.slice pref3, .builder Builder.empty],
    mkSdppfxRawCase "type/second-pop-not-slice"
      #[.null, .slice s5],

    mkSdppfxCase "gas/exact-cost-succeeds"
      pref3 s5 #[]
      #[.pushInt (.num sdppfxSetGasExact), .tonEnvOp .setGasLimit, sdppfxInstr],
    mkSdppfxCase "gas/exact-minus-one-out-of-gas"
      pref3 s5 #[]
      #[.pushInt (.num sdppfxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdppfxInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDPPFX
