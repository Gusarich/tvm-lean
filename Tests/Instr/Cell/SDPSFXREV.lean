import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDPSFXREV

/-
SDPSFXREV branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdPsfxRev`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdPsfxRev` encode: `0xc70f`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc70f` decode to `.cellOp .sdPsfxRev`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_bin_cs_cmp`; registration `SDPSFXREV` at opcode `0xc70f`).

Branch map used for this suite:
- dispatch guard in `execCellOpExt`;
- `checkUnderflow 2` before any type/data checks;
- pop order is top-first (`s2` then `s1`), both via `popSlice`;
- success predicate is bits-only proper-suffix:
  `s2.bitsRemaining < s1.bitsRemaining && suffixEq(s2, s1)`;
- terminal push is `-1` (true) or `0` (false), with no extra stack outputs.
-/

private def sdpsfxrevId : InstrId := { name := "SDPSFXREV" }

private def dispatchSentinel : Int := 50959

private def sdpsfxrevInstr : Instr := .cellOp .sdPsfxRev
private def sdpsfxInstr : Instr := .cellOp .sdPsfx
private def sdsfxrevInstr : Instr := .cellOp .sdSfxRev

private def execInstrCellOpExtOnly (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpExt op next
  | _ => next

private def mkSdpsfxrevCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdpsfxrevInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdpsfxrevId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdpsfxrevDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpExtOnly sdpsfxrevInstr stack

private def runSdpsfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpExtOnly sdpsfxInstr stack

private def runSdpsfxrevDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpExtOnly .add (VM.push (intV dispatchSentinel)) stack

private def sdpsfxrevSetGasExact : Int :=
  computeExactGasBudget sdpsfxrevInstr

private def sdpsfxrevSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdpsfxrevInstr

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def flipHeadBit (bs : BitString) : BitString :=
  if bs.isEmpty then
    bs
  else
    bs.set! 0 (!(bs[0]!))

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[]

private def whole6 : Slice :=
  mkSliceFromBits (natToBits 45 6)

private def equal6 : Slice :=
  mkSliceFromBits (natToBits 45 6)

private def suffix4 : Slice :=
  mkSliceFromBits (natToBits 13 4)

private def suffix1 : Slice :=
  mkSliceFromBits (natToBits 1 1)

private def nonSuffix4 : Slice :=
  mkSliceFromBits (natToBits 9 4)

private def longer7 : Slice :=
  mkSliceFromBits (natToBits 109 7)

private def emptySlice : Slice :=
  mkSliceFromBits #[]

private def whole6Refs2 : Slice :=
  mkSliceWithBitsRefs (natToBits 45 6) #[refLeafA, refLeafB]

private def suffix4Refs1 : Slice :=
  mkSliceWithBitsRefs (natToBits 13 4) #[refLeafB]

private def emptyRefs2 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]

private def striped127 : BitString := stripeBits 127 1

private def whole127 : Slice :=
  mkSliceWithBitsRefs striped127

private def suffix126 : Slice :=
  mkSliceWithBitsRefs (striped127.drop 1)

private def prefix126 : Slice :=
  mkSliceWithBitsRefs (striped127.take 126)

private def striped1023 : BitString := stripeBits 1023 0

private def whole1023 : Slice :=
  mkSliceWithBitsRefs striped1023

private def suffix1022 : Slice :=
  mkSliceWithBitsRefs (striped1023.drop 1)

private def cursorBase : Slice :=
  mkSliceFromBits (natToBits 429 9)

private def cursorWhole : Slice :=
  cursorBase.advanceBits 1

private def cursorSuffix : Slice :=
  cursorWhole.advanceBits 3

private def cursorSuffixBits : BitString :=
  cursorSuffix.readBits cursorSuffix.bitsRemaining

private def cursorNonSuffix : Slice :=
  mkSliceFromBits (flipHeadBit cursorSuffixBits)

def suite : InstrSuite where
  id := sdpsfxrevId
  unit := #[
    { name := "unit/direct/truth-table-and-direction"
      run := do
        expectOkStack "ok/proper/basic-6-4"
          (runSdpsfxrevDirect #[.slice whole6, .slice suffix4])
          #[intV (-1)]

        expectOkStack "ok/proper/one-bit"
          (runSdpsfxrevDirect #[.slice whole6, .slice suffix1])
          #[intV (-1)]

        expectOkStack "ok/proper/empty-tail"
          (runSdpsfxrevDirect #[.slice whole6, .slice emptySlice])
          #[intV (-1)]

        expectOkStack "false/equal-bits-not-proper"
          (runSdpsfxrevDirect #[.slice whole6, .slice equal6])
          #[intV 0]

        expectOkStack "false/not-suffix"
          (runSdpsfxrevDirect #[.slice whole6, .slice nonSuffix4])
          #[intV 0]

        expectOkStack "false/candidate-longer"
          (runSdpsfxrevDirect #[.slice whole6, .slice longer7])
          #[intV 0]

        expectOkStack "false/both-empty"
          (runSdpsfxrevDirect #[.slice emptySlice, .slice emptySlice])
          #[intV 0]

        expectOkStack "false/reversed-order"
          (runSdpsfxrevDirect #[.slice suffix4, .slice whole6])
          #[intV 0]

        expectOkStack "ok/deep-stack-order-preserved"
          (runSdpsfxrevDirect #[.null, intV 7, .slice whole6, .slice suffix4])
          #[.null, intV 7, intV (-1)]

        expectOkStack "direction/nonrev-false-on-rev-order"
          (runSdpsfxDirect #[.slice whole6, .slice suffix4])
          #[intV 0]

        expectOkStack "direction/nonrev-true-on-opposite-order"
          (runSdpsfxDirect #[.slice suffix4, .slice whole6])
          #[intV (-1)] }
    ,
    { name := "unit/direct/refs-ignored-and-cursor-slices"
      run := do
        expectOkStack "refs/whole-has-refs"
          (runSdpsfxrevDirect #[.slice whole6Refs2, .slice suffix4])
          #[intV (-1)]

        expectOkStack "refs/suffix-has-refs"
          (runSdpsfxrevDirect #[.slice whole6, .slice suffix4Refs1])
          #[intV (-1)]

        expectOkStack "refs/both-have-refs"
          (runSdpsfxrevDirect #[.slice whole6Refs2, .slice suffix4Refs1])
          #[intV (-1)]

        expectOkStack "refs/empty-bits-can-be-proper"
          (runSdpsfxrevDirect #[.slice whole6Refs2, .slice emptyRefs2])
          #[intV (-1)]

        expectOkStack "refs/empty-vs-empty-not-proper"
          (runSdpsfxrevDirect #[.slice emptyRefs2, .slice emptySlice])
          #[intV 0]

        expectOkStack "cursor/proper-suffix"
          (runSdpsfxrevDirect #[.slice cursorWhole, .slice cursorSuffix])
          #[intV (-1)]

        expectOkStack "cursor/not-suffix-after-flip"
          (runSdpsfxrevDirect #[.slice cursorWhole, .slice cursorNonSuffix])
          #[intV 0] }
    ,
    { name := "unit/direct/underflow-and-type-precedence"
      run := do
        expectErr "underflow/empty"
          (runSdpsfxrevDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdpsfxrevDirect #[.slice whole6]) .stkUnd
        expectErr "underflow/one-null"
          (runSdpsfxrevDirect #[.null]) .stkUnd

        expectErr "type/top-null"
          (runSdpsfxrevDirect #[.slice whole6, .null]) .typeChk
        expectErr "type/top-int"
          (runSdpsfxrevDirect #[.slice whole6, intV 0]) .typeChk
        expectErr "type/top-cell"
          (runSdpsfxrevDirect #[.slice whole6, .cell refLeafA]) .typeChk
        expectErr "type/top-builder"
          (runSdpsfxrevDirect #[.slice whole6, .builder Builder.empty]) .typeChk

        expectErr "type/second-not-slice"
          (runSdpsfxrevDirect #[.null, .slice suffix4]) .typeChk
        expectErr "type/second-nan-not-range"
          (runSdpsfxrevDirect #[.int .nan, .slice suffix4]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[sdsfxrevInstr, sdpsfxInstr, sdpsfxrevInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdsfxrev-neighbor" s0 sdsfxrevInstr 16
        let s2 ← expectDecodeStep "decode/sdpsfx-neighbor" s1 sdpsfxInstr 16
        let s3 ← expectDecodeStep "decode/sdpsfxrev" s2 sdpsfxrevInstr 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdpsfxrev-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runSdpsfxrevDispatchFallback #[.null])
          #[.null, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdpsfxrevCase "ok/proper/basic-6-4"
      #[.slice whole6, .slice suffix4],
    mkSdpsfxrevCase "ok/proper/one-bit-tail"
      #[.slice whole6, .slice suffix1],
    mkSdpsfxrevCase "ok/proper/empty-tail"
      #[.slice whole6, .slice emptySlice],
    mkSdpsfxrevCase "ok/proper/deep-stack-null"
      #[.null, .slice whole6, .slice suffix4],
    mkSdpsfxrevCase "ok/proper/deep-stack-int"
      #[intV 11, .slice whole6, .slice suffix4],
    mkSdpsfxrevCase "ok/proper/refs-whole-ignored"
      #[.slice whole6Refs2, .slice suffix4],
    mkSdpsfxrevCase "ok/proper/refs-suffix-ignored"
      #[.slice whole6, .slice suffix4Refs1],
    mkSdpsfxrevCase "ok/proper/refs-both-ignored"
      #[.slice whole6Refs2, .slice suffix4Refs1],
    mkSdpsfxrevCase "ok/proper/boundary-127-126"
      #[.slice whole127, .slice suffix126],
    mkSdpsfxrevCase "ok/proper/boundary-1023-1022"
      #[.slice whole1023, .slice suffix1022],

    mkSdpsfxrevCase "false/equal-bits-not-proper"
      #[.slice whole6, .slice equal6],
    mkSdpsfxrevCase "false/not-suffix-6-4"
      #[.slice whole6, .slice nonSuffix4],
    mkSdpsfxrevCase "false/candidate-longer"
      #[.slice whole6, .slice longer7],
    mkSdpsfxrevCase "false/both-empty"
      #[.slice emptySlice, .slice emptySlice],
    mkSdpsfxrevCase "false/whole-empty-candidate-nonempty"
      #[.slice emptySlice, .slice suffix1],
    mkSdpsfxrevCase "false/reversed-order"
      #[.slice suffix4, .slice whole6],
    mkSdpsfxrevCase "false/prefix-not-suffix"
      #[.slice whole127, .slice prefix126],

    mkSdpsfxrevCase "underflow/empty"
      #[],
    mkSdpsfxrevCase "underflow/one-slice"
      #[.slice whole6],
    mkSdpsfxrevCase "type/top-null"
      #[.slice whole6, .null],
    mkSdpsfxrevCase "type/top-int"
      #[.slice whole6, intV 0],
    mkSdpsfxrevCase "type/top-cell"
      #[.slice whole6, .cell refLeafA],
    mkSdpsfxrevCase "type/top-builder"
      #[.slice whole6, .builder Builder.empty],
    mkSdpsfxrevCase "type/second-not-slice"
      #[.null, .slice suffix4],

    mkSdpsfxrevCase "gas/exact-cost-succeeds"
      #[.slice whole6, .slice suffix4]
      #[.pushInt (.num sdpsfxrevSetGasExact), .tonEnvOp .setGasLimit, sdpsfxrevInstr],
    mkSdpsfxrevCase "gas/exact-minus-one-out-of-gas"
      #[.slice whole6, .slice suffix4]
      #[.pushInt (.num sdpsfxrevSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdpsfxrevInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDPSFXREV
