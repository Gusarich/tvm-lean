import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDPPFXREV

/-
SDPPFXREV branch-mapping notes (Lean + C++ reference):
- Lean execute path:
  - `TvmLean/Semantics/Exec/Cell/SdPpfxRev.lean` (`.sdPpfxRev`)
  - branches: dispatch; `popSlice` x2 (underflow/type); predicate
    `prefBits.size < sBits.size && sBits.extract 0 prefBits.size == prefBits`;
    result pushes `-1` (true) or `0` (false).
- Decode/asm path:
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`: `0xc70b -> .sdPpfxRev`
  - `TvmLean/Model/Instr/Asm/Cp0.lean`: `.sdPpfxRev -> 0xc70b`
- C++ parity:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_bin_cs_cmp`, `register_cell_cmp_ops`):
    `SDPPFXREV` computes `cs2.is_proper_prefix_of(cs1)` after popping
    top as `cs2`, then next as `cs1`.

Coverage focus in this suite:
- strict proper-prefix success/false outcomes (including empty/equal/longer/mismatch);
- remaining-bit cursor behavior and reference-independence;
- underflow/type ordering and dispatch fallthrough;
- opcode boundary checks around `0xc70a/0xc70b/0xc70c`;
- oracle gas edge (`exact` vs `exact - 1`).
-/

private def sdPpfxRevId : InstrId := { name := "SDPPFXREV" }

private def sdPpfxRevInstr : Instr := .sdPpfxRev
private def sdPpfxInstr : Instr := .sdPpfx
private def sdSfxInstr : Instr := .cellOp .sdSfx

private def sdPpfxRevOpcode : Nat := 0xc70b

private def dispatchSentinel : Int := 955

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSliceWord (word width : Nat) (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word width) refs

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def prefixSlice (s : Slice) (prefixLen : Nat) (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (s.readBits prefixLen) refs

private def runSdPpfxRevDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPpfxRev sdPpfxRevInstr stack

private def runSdPpfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPpfx sdPpfxInstr stack

private def runSdPpfxRevDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdPpfxRev instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok ls, .ok rs => ls == rs
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got lhs={reprStr lhs}, rhs={reprStr rhs}")

private def mkSdPpfxRevCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdPpfxRevInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdPpfxRevId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[]

private def emptySlice : Slice := mkSliceWithBitsRefs #[]

private def sBasic : Slice := mkSliceWord 11 4
private def prefBasic : Slice := mkSliceWord 2 2
private def prefEqualBasic : Slice := mkSliceWord 11 4
private def prefLongBasic : Slice := mkSliceWord 44 6
private def prefMismatchFirst : Slice := mkSliceWord 1 2

private def sMismatch : Slice := mkSliceWord 179 8
private def prefMismatchMid : Slice := mkSliceWord 21 5
private def pref7OfMismatch : Slice := prefixSlice sMismatch 7

private def sWithRefs : Slice :=
  mkSliceWithBitsRefs (natToBits 45 6) #[refLeafA, refLeafB]

private def prefWithOwnRefs : Slice :=
  prefixSlice sWithRefs 3 #[refLeafC]

private def prefNoRefs : Slice :=
  prefixSlice sWithRefs 3

private def prefEqualWithRefs : Slice :=
  prefixSlice sWithRefs sWithRefs.bitsRemaining #[refLeafC]

private def s64 : Slice :=
  mkSliceWithBitsRefs (stripeBits 64 0) #[refLeafB]

private def pref31 : Slice :=
  prefixSlice s64 31

private def bits256Phase1 : BitString := stripeBits 256 1

private def s256 : Slice :=
  mkSliceWithBitsRefs bits256Phase1 #[refLeafA]

private def pref255 : Slice :=
  mkSliceWithBitsRefs (bits256Phase1.extract 0 255)

private def pref256Equal : Slice :=
  prefixSlice s256 256

private def cursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 16 0) #[refLeafA, refLeafB]

private def sCursor : Slice :=
  { cell := cursorCell, bitPos := 5, refPos := 1 }

private def prefCursor5 : Slice :=
  prefixSlice sCursor 5 #[refLeafC]

private def prefCursorEq : Slice :=
  prefixSlice sCursor sCursor.bitsRemaining

private def prefCursorMismatch : Slice :=
  mkSliceWithBitsRefs (stripeBits 5 0)

private def sdPpfxRevSetGasExact : Int :=
  computeExactGasBudget sdPpfxRevInstr

private def sdPpfxRevSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdPpfxRevInstr

def suite : InstrSuite where
  id := { name := "SDPPFXREV" }
  unit := #[
    { name := "unit/direct/proper-prefix-core-outcomes"
      run := do
        expectOkStack "ok/basic-proper-prefix"
          (runSdPpfxRevDirect #[.slice sBasic, .slice prefBasic])
          #[intV (-1)]
        expectOkStack "ok/empty-prefix-on-nonempty"
          (runSdPpfxRevDirect #[.slice sBasic, .slice emptySlice])
          #[intV (-1)]

        expectOkStack "false/equal-length-not-proper"
          (runSdPpfxRevDirect #[.slice sBasic, .slice prefEqualBasic])
          #[intV 0]
        expectOkStack "false/prefix-longer-than-source"
          (runSdPpfxRevDirect #[.slice sBasic, .slice prefLongBasic])
          #[intV 0]
        expectOkStack "false/first-bit-mismatch"
          (runSdPpfxRevDirect #[.slice sBasic, .slice prefMismatchFirst])
          #[intV 0]
        expectOkStack "false/middle-bit-mismatch"
          (runSdPpfxRevDirect #[.slice sMismatch, .slice prefMismatchMid])
          #[intV 0]
        expectOkStack "false/empty-vs-empty"
          (runSdPpfxRevDirect #[.slice emptySlice, .slice emptySlice])
          #[intV 0]
        expectOkStack "false/nonempty-prefix-vs-empty-source"
          (runSdPpfxRevDirect #[.slice emptySlice, .slice prefBasic])
          #[intV 0] }
    ,
    { name := "unit/direct/refs-ignored-and-long-boundaries"
      run := do
        expectOkStack "ok/refs-ignored-prefix-has-own-refs"
          (runSdPpfxRevDirect #[.slice sWithRefs, .slice prefWithOwnRefs])
          #[intV (-1)]
        expectOkStack "ok/refs-ignored-prefix-no-refs"
          (runSdPpfxRevDirect #[.slice sWithRefs, .slice prefNoRefs])
          #[intV (-1)]
        expectOkStack "false/equal-length-even-with-different-refs"
          (runSdPpfxRevDirect #[.slice sWithRefs, .slice prefEqualWithRefs])
          #[intV 0]

        expectOkStack "ok/255-of-256-boundary"
          (runSdPpfxRevDirect #[.slice s256, .slice pref255])
          #[intV (-1)]
        expectOkStack "false/256-of-256-equal"
          (runSdPpfxRevDirect #[.slice s256, .slice pref256Equal])
          #[intV 0] }
    ,
    { name := "unit/direct/cursor-based-remaining-bits"
      run := do
        expectOkStack "ok/cursor-prefix-of-remaining-bits"
          (runSdPpfxRevDirect #[.slice sCursor, .slice prefCursor5])
          #[intV (-1)]
        expectOkStack "false/cursor-equal-remaining-bits"
          (runSdPpfxRevDirect #[.slice sCursor, .slice prefCursorEq])
          #[intV 0]
        expectOkStack "false/cursor-mismatch"
          (runSdPpfxRevDirect #[.slice sCursor, .slice prefCursorMismatch])
          #[intV 0]
        expectOkStack "ok/cursor-deep-stack-preserved"
          (runSdPpfxRevDirect #[.null, .cell refLeafA, .slice sCursor, .slice prefCursor5])
          #[.null, .cell refLeafA, intV (-1)] }
    ,
    { name := "unit/direct/underflow-type-and-order"
      run := do
        expectErr "underflow/empty-stack"
          (runSdPpfxRevDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdPpfxRevDirect #[.slice sBasic]) .stkUnd

        expectErr "type/top-null"
          (runSdPpfxRevDirect #[.slice sBasic, .null]) .typeChk
        expectErr "type/top-int"
          (runSdPpfxRevDirect #[.slice sBasic, intV 7]) .typeChk
        expectErr "type/top-cell"
          (runSdPpfxRevDirect #[.slice sBasic, .cell refLeafA]) .typeChk
        expectErr "type/second-not-slice-null"
          (runSdPpfxRevDirect #[.null, .slice prefBasic]) .typeChk
        expectErr "type/second-not-slice-cell"
          (runSdPpfxRevDirect #[.cell refLeafA, .slice prefBasic]) .typeChk
        expectErr "type/one-item-null"
          (runSdPpfxRevDirect #[.null]) .typeChk }
    ,
    { name := "unit/direct/result-shape-consumes-two-slices"
      run := do
        expectOkStack "shape/success"
          (runSdPpfxRevDirect #[intV 7, .null, .slice sBasic, .slice prefBasic])
          #[intV 7, .null, intV (-1)]
        expectOkStack "shape/false"
          (runSdPpfxRevDirect #[.cell refLeafA, .slice sBasic, .slice prefEqualBasic])
          #[.cell refLeafA, intV 0] }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[sdPpfxInstr, sdPpfxRevInstr, sdSfxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")

        let d0 := Slice.ofCell code
        let d1 ← expectDecodeStep "decode/sdppfx-neighbor" d0 sdPpfxInstr 16
        let d2 ← expectDecodeStep "decode/sdppfxrev-target" d1 sdPpfxRevInstr 16
        let d3 ← expectDecodeStep "decode/sdsfx-neighbor" d2 sdSfxInstr 16
        let d4 ← expectDecodeStep "decode/tail-add" d3 .add 8
        if d4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {d4.bitsRemaining} bits remaining")

        let asm ←
          match assembleCp0 [sdPpfxRevInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdppfxrev failed: {e}")
        if asm.bits = natToBits sdPpfxRevOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/sdppfxrev: expected opcode 0x{Nat.toDigits 16 sdPpfxRevOpcode |>.asString}, got bits {asm.bits}")
        if asm.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdppfxrev: expected 16 bits, got {asm.bits.size}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xc70a 16 ++ natToBits 0xc70b 16 ++ natToBits 0xc70c 16 ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdppfx" r0 sdPpfxInstr 16
        let r2 ← expectDecodeStep "decode/raw-sdppfxrev" r1 sdPpfxRevInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdsfx" r2 sdSfxInstr 16
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/reverse-equivalence/with-sdppfx-swapped-stack"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("ok/basic", sBasic, prefBasic),
            ("false/equal", sBasic, prefEqualBasic),
            ("ok/refs", sWithRefs, prefNoRefs),
            ("false/cursor-mismatch", sCursor, prefCursorMismatch),
            ("ok/long-255-256", s256, pref255)
          ]
        for (label, s, pref) in checks do
          expectSameOutcome s!"align/{label}"
            (runSdPpfxRevDirect #[.slice s, .slice pref])
            (runSdPpfxDirect #[.slice pref, .slice s])

        expectSameOutcome "align/underflow-empty"
          (runSdPpfxRevDirect #[])
          (runSdPpfxDirect #[])
        expectSameOutcome "align/type-top-null-vs-swapped"
          (runSdPpfxRevDirect #[.slice sBasic, .null])
          (runSdPpfxDirect #[.null, .slice sBasic])
        expectSameOutcome "align/type-second-null-vs-swapped"
          (runSdPpfxRevDirect #[.null, .slice prefBasic])
          (runSdPpfxDirect #[.slice prefBasic, .null]) }
    ,
    { name := "unit/dispatch/non-sdppfxrev-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runSdPpfxRevDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdppfx-neighbor"
          (runSdPpfxRevDispatchFallback sdPpfxInstr #[.slice sBasic, .slice prefBasic])
          #[.slice sBasic, .slice prefBasic, intV dispatchSentinel]
        expectOkStack "dispatch/sdsfx-neighbor"
          (runSdPpfxRevDispatchFallback sdSfxInstr #[.slice sBasic, .slice prefBasic])
          #[.slice sBasic, .slice prefBasic, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdPpfxRevCase "ok/basic/proper-prefix"
      #[.slice sBasic, .slice prefBasic],
    mkSdPpfxRevCase "ok/basic/empty-prefix-on-nonempty"
      #[.slice sBasic, .slice emptySlice],
    mkSdPpfxRevCase "ok/deep-stack/null-below"
      #[.null, .slice sBasic, .slice prefBasic],
    mkSdPpfxRevCase "ok/deep-stack/int-cell-below"
      #[intV 5, .cell refLeafA, .slice sBasic, .slice prefBasic],
    mkSdPpfxRevCase "ok/refs-ignored/prefix-has-own-refs"
      #[.slice sWithRefs, .slice prefWithOwnRefs],
    mkSdPpfxRevCase "ok/refs-ignored/prefix-no-refs"
      #[.slice sWithRefs, .slice prefNoRefs],
    mkSdPpfxRevCase "ok/boundary/255-of-256"
      #[.slice s256, .slice pref255],
    mkSdPpfxRevCase "ok/long/prefix-31-of-64"
      #[.slice s64, .slice pref31],
    mkSdPpfxRevCase "ok/long/prefix-7-of-8"
      #[.slice sMismatch, .slice pref7OfMismatch],

    mkSdPpfxRevCase "false/equal-basic"
      #[.slice sBasic, .slice prefEqualBasic],
    mkSdPpfxRevCase "false/prefix-longer-than-source"
      #[.slice sBasic, .slice prefLongBasic],
    mkSdPpfxRevCase "false/first-bit-mismatch"
      #[.slice sBasic, .slice prefMismatchFirst],
    mkSdPpfxRevCase "false/middle-bit-mismatch"
      #[.slice sMismatch, .slice prefMismatchMid],
    mkSdPpfxRevCase "false/empty-vs-empty"
      #[.slice emptySlice, .slice emptySlice],
    mkSdPpfxRevCase "false/nonempty-prefix-vs-empty-source"
      #[.slice emptySlice, .slice prefBasic],
    mkSdPpfxRevCase "false/equal-length-different-refs"
      #[.slice sWithRefs, .slice prefEqualWithRefs],
    mkSdPpfxRevCase "false/boundary/256-of-256"
      #[.slice s256, .slice pref256Equal],

    mkSdPpfxRevCase "underflow/empty-stack"
      #[],
    mkSdPpfxRevCase "underflow/one-slice"
      #[.slice sBasic],
    mkSdPpfxRevCase "type/top-null"
      #[.slice sBasic, .null],
    mkSdPpfxRevCase "type/top-int"
      #[.slice sBasic, intV 7],
    mkSdPpfxRevCase "type/second-not-slice-null"
      #[.null, .slice prefBasic],

    mkSdPpfxRevCase "gas/exact-cost-succeeds"
      #[.slice sBasic, .slice prefBasic]
      #[.pushInt (.num sdPpfxRevSetGasExact), .tonEnvOp .setGasLimit, sdPpfxRevInstr],
    mkSdPpfxRevCase "gas/exact-minus-one-out-of-gas"
      #[.slice sBasic, .slice prefBasic]
      #[.pushInt (.num sdPpfxRevSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdPpfxRevInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDPPFXREV
