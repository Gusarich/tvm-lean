import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SREMPTY

/-
SREMPTY branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Srempty.lean` (`.srempty`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc702` decode to `.srempty`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.srempty` encode as `0xc702`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`reg_un_cs_cmp(... "SREMPTY", [](cs){ return !cs->size_refs(); })`,
     shared unary comparator `exec_un_cs_cmp`).

Branch map used for this suite:
- dispatch guard: `.srempty` executes, any other opcode falls through to `next`;
- `popSlice` on stack top: underflow/type/success;
- success predicate: push `-1` iff `refsRemaining == 0`, else push `0`.

Key risk areas:
- result must depend only on `refsRemaining` (bits are irrelevant);
- partial slices must honor current `refPos` (not total refs in backing cell);
- deep-stack values below top slice must remain untouched;
- opcode boundary around `0xc701/0xc702` must decode correctly;
- no range-checked immediates exist (`rangeChk` must be unreachable).
-/

private def sremptyId : InstrId := { name := "SREMPTY" }

private def sremptyInstr : Instr := .srempty
private def semptyInstr : Instr := .sempty
private def sdemptyInstr : Instr := .sdempty

private def dispatchSentinel : Int := 702

private def mkSremptyCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sremptyInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sremptyId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSremptyDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSrempty sremptyInstr stack

private def runSremptyDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSrempty instr (VM.push (intV dispatchSentinel)) stack

private def sremptySetGasExact : Int :=
  computeExactGasBudget sremptyInstr

private def sremptySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sremptyInstr

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[Cell.empty]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0x1D 5) #[refLeafA, Cell.empty]

private def refLeafD : Cell :=
  Cell.mkOrdinary #[] #[]

private def sEmpty : Slice :=
  mkSliceWithBitsRefs #[] #[]

private def sBitsOnly1 : Slice :=
  mkSliceWithBitsRefs (natToBits 1 1) #[]

private def sBitsOnly17 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x1A2B 17) #[]

private def sBitsOnly7 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x4F 7) #[]

private def sBitsOnly1023 : Slice :=
  mkSliceWithBitsRefs (Array.replicate 1023 false) #[]

private def sRefsOnly1 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA]

private def sRefsOnly2 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]

private def sRefsOnly4 : Slice :=
  mkSliceWithBitsRefs #[] #[refLeafA, refLeafB, refLeafC, refLeafD]

private def sBitsRefs1 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x12 6) #[refLeafB]

private def sBitsRefs2 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x5D 7) #[refLeafA, refLeafB]

private def sBitsRefs4 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x5A3 11) #[refLeafA, refLeafB, refLeafC, refLeafD]

private def partialRefCell : Cell :=
  Cell.mkOrdinary (natToBits 0x5D 7) #[refLeafA, refLeafB]

private def sPartialAllRefsConsumed : Slice :=
  { cell := partialRefCell, bitPos := 2, refPos := 2 }

private def sPartialOneRefLeft : Slice :=
  { cell := partialRefCell, bitPos := 6, refPos := 1 }

private def sPartialNoRefsShifted : Slice :=
  { cell := Cell.mkOrdinary (natToBits 0x4F 7) #[], bitPos := 4, refPos := 0 }

def suite : InstrSuite where
  id := sremptyId
  unit := #[
    { name := "unit/direct/predicate-is-refsremaining-only"
      run := do
        let checks : Array (String × Slice × Int) :=
          #[
            ("empty-slice", sEmpty, -1),
            ("bits-only-1", sBitsOnly1, -1),
            ("bits-only-17", sBitsOnly17, -1),
            ("bits-only-1023", sBitsOnly1023, -1),
            ("refs-only-1", sRefsOnly1, 0),
            ("refs-only-4", sRefsOnly4, 0),
            ("bits-and-refs", sBitsRefs1, 0),
            ("partial/all-refs-consumed", sPartialAllRefsConsumed, -1),
            ("partial/one-ref-left", sPartialOneRefLeft, 0),
            ("partial/no-refs-shifted-bitpos", sPartialNoRefsShifted, -1)
          ]
        for c in checks do
          let label := c.1
          let s := c.2.1
          let expected := c.2.2
          expectOkStack label (runSremptyDirect #[.slice s]) #[intV expected] }
    ,
    { name := "unit/direct/deep-stack-preserved"
      run := do
        expectOkStack "deep/null-below-empty"
          (runSremptyDirect #[.null, .slice sEmpty])
          #[.null, intV (-1)]
        expectOkStack "deep/cell-below-refs"
          (runSremptyDirect #[.cell refLeafA, .slice sRefsOnly1])
          #[.cell refLeafA, intV 0]
        expectOkStack "deep/two-values-below-partial"
          (runSremptyDirect #[intV 9, .builder Builder.empty, .slice sPartialOneRefLeft])
          #[intV 9, .builder Builder.empty, intV 0] }
    ,
    { name := "unit/direct/underflow-and-type"
      run := do
        expectErr "underflow/empty" (runSremptyDirect #[]) .stkUnd
        expectErr "type/top-null" (runSremptyDirect #[.null]) .typeChk
        expectErr "type/top-int" (runSremptyDirect #[intV 7]) .typeChk
        expectErr "type/top-cell" (runSremptyDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runSremptyDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runSremptyDirect #[.tuple #[]]) .typeChk
        expectErr "type/deep-top-not-slice-null"
          (runSremptyDirect #[.slice sRefsOnly1, .null]) .typeChk
        expectErr "type/deep-top-not-slice-int"
          (runSremptyDirect #[.slice sRefsOnly1, intV 3]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success-empty", runSremptyDirect #[.slice sEmpty]),
            ("success-refs", runSremptyDirect #[.slice sRefsOnly1]),
            ("underflow", runSremptyDirect #[]),
            ("type", runSremptyDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for SREMPTY")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let canonical ←
          match assembleCp0 [sremptyInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble srempty failed: {e}")
        if canonical.bits = natToBits 0xc702 16 then
          pure ()
        else
          throw (IO.userError
            s!"srempty canonical encode mismatch: got bits {canonical.bits}")

        let program : Array Instr := #[semptyInstr, sdemptyInstr, sremptyInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sempty-c700" s0 semptyInstr 16
        let s2 ← expectDecodeStep "decode/sdempty-c701" s1 sdemptyInstr 16
        let s3 ← expectDecodeStep "decode/srempty-c702" s2 sremptyInstr 16
        let s4 ← expectDecodeStep "decode/add-tail" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-srempty-falls-through"
      run := do
        expectOkStack "dispatch/fallback/sdempty"
          (runSremptyDispatchFallback sdemptyInstr #[.null])
          #[.null, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSremptyCase "ok/empty-slice"
      #[.slice sEmpty],
    mkSremptyCase "ok/bits-only-1"
      #[.slice sBitsOnly1],
    mkSremptyCase "ok/bits-only-17"
      #[.slice sBitsOnly17],
    mkSremptyCase "ok/bits-only-1023"
      #[.slice sBitsOnly1023],
    mkSremptyCase "ok/refs-only-1"
      #[.slice sRefsOnly1],
    mkSremptyCase "ok/refs-only-4"
      #[.slice sRefsOnly4],
    mkSremptyCase "ok/bits-plus-one-ref"
      #[.slice sBitsRefs1],
    mkSremptyCase "ok/bits-plus-four-refs"
      #[.slice sBitsRefs4],
    mkSremptyCase "ok/bits-only-7"
      #[.slice sBitsOnly7],
    mkSremptyCase "ok/refs-only-2"
      #[.slice sRefsOnly2],
    mkSremptyCase "ok/bits-plus-two-refs"
      #[.slice sBitsRefs2],
    mkSremptyCase "ok/deep/preserve-null"
      #[.null, .slice sEmpty],
    mkSremptyCase "ok/deep/preserve-int"
      #[intV (-7), .slice sBitsOnly17],
    mkSremptyCase "ok/deep/preserve-cell"
      #[.cell refLeafC, .slice sRefsOnly1],
    mkSremptyCase "ok/deep/preserve-builder"
      #[.builder Builder.empty, .slice sBitsRefs4],
    mkSremptyCase "ok/deep/preserve-two-values"
      #[.tuple #[], .cell refLeafA, .slice sBitsRefs2],

    mkSremptyCase "underflow/empty"
      #[],

    mkSremptyCase "type/top-null"
      #[.null],
    mkSremptyCase "type/top-int"
      #[intV 42],
    mkSremptyCase "type/top-cell"
      #[.cell Cell.empty],
    mkSremptyCase "type/top-builder"
      #[.builder Builder.empty],
    mkSremptyCase "type/top-tuple-empty"
      #[.tuple #[]],
    mkSremptyCase "type/deep-top-not-slice-null"
      #[.slice sRefsOnly1, .null],
    mkSremptyCase "type/deep-top-not-slice-int"
      #[.slice sRefsOnly1, intV 5],

    mkSremptyCase "gas/exact-cost-succeeds"
      #[.slice sRefsOnly1]
      #[.pushInt (.num sremptySetGasExact), .tonEnvOp .setGasLimit, sremptyInstr],
    mkSremptyCase "gas/exact-minus-one-out-of-gas"
      #[.slice sRefsOnly1]
      #[.pushInt (.num sremptySetGasExactMinusOne), .tonEnvOp .setGasLimit, sremptyInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SREMPTY
