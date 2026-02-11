import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDCNTLEAD1

/-
SDCNTLEAD1 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdCntLead1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode `0xc711`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (encode `.cellOp .sdCntLead1`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`reg_iun_cs_cmp(..., "SDCNTLEAD1", [](auto cs) { return cs->count_leading(1); })`).

Branch map used for this suite:
- handler dispatch: `.cellOp .sdCntLead1` vs fallthrough to `next`;
- stack pop branch (`VM.popSlice`): `stkUnd` / `typeChk` / valid slice;
- count loop outcomes on remaining bits:
  empty (`rem=0`) -> `0`,
  first bit `0` -> `0`,
  mixed prefix ones -> stop at first `0`,
  all remaining bits `1` -> full `rem`.
-/

private def sdCntLead1Id : InstrId := { name := "SDCNTLEAD1" }

private def sdCntLead1Instr : Instr := .cellOp .sdCntLead1

private def dispatchSentinel : Int := 542

private def sdCntLead0Opcode : Nat := 0xc710
private def sdCntLead1Opcode : Nat := 0xc711
private def sdCntTrail0Opcode : Nat := 0xc712
private def sdCntTrail1Opcode : Nat := 0xc713
private def sdPsfxRevOpcode : Nat := 0xc70f

private def zeros (n : Nat) : BitString :=
  Array.replicate n false

private def ones (n : Nat) : BitString :=
  Array.replicate n true

private def mkPrefixOneSlice (prefixOnes total : Nat) (refs : Array Cell := #[]) : Slice :=
  if prefixOnes < total then
    let tailLen : Nat := total - prefixOnes - 1
    let tail := stripeBits tailLen 0
    mkSliceWithBitsRefs (ones prefixOnes ++ #[false] ++ tail) refs
  else
    mkSliceWithBitsRefs (ones total) refs

private def expectedLead1 (s : Slice) : Int :=
  Int.ofNat (s.countLeading true)

private def execInstrCellOpSdCntLead1Only (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdCntLead1 => execCellOpExt .sdCntLead1 next
  | _ => next

private def runSdCntLead1Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSdCntLead1Only sdCntLead1Instr stack

private def runSdCntLead1DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellOpSdCntLead1Only
    instr
    (VM.push (intV dispatchSentinel))
    stack

private def runSdCntLead1Model (stack : Array Value) : Except Excno (Array Value) := do
  if stack.isEmpty then
    throw .stkUnd
  let top := stack.back!
  let below := stack.extract 0 (stack.size - 1)
  match top with
  | .slice s => pure (below.push (intV (expectedLead1 s)))
  | _ => throw .typeChk

private def mkSdCntLead1Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdCntLead1Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdCntLead1Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def sdCntLead1SetGasExact : Int :=
  computeExactGasBudget sdCntLead1Instr

private def sdCntLead1SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdCntLead1Instr

def suite : InstrSuite where
  id := { name := "SDCNTLEAD1" }
  unit := #[
    { name := "unit/direct/success-full-slices"
      run := do
        let checks : Array (String × Slice) :=
          #[
            ("empty", mkSliceWithBitsRefs #[]),
            ("len1-zero", mkSliceWithBitsRefs #[false]),
            ("len1-one", mkSliceWithBitsRefs #[true]),
            ("len4-prefix2", mkSliceWithBitsRefs #[true, true, false, true]),
            ("len8-stripe0", mkSliceWithBitsRefs (stripeBits 8 0)),
            ("len8-stripe1", mkSliceWithBitsRefs (stripeBits 8 1)),
            ("len32-all-one", mkSliceWithBitsRefs (ones 32)),
            ("len64-all-zero", mkSliceWithBitsRefs (zeros 64))
          ]
        for (label, s) in checks do
          expectOkStack s!"ok/{label}"
            (runSdCntLead1Direct #[.slice s])
            #[intV (expectedLead1 s)] }
    ,
    { name := "unit/direct/manual-prefix-boundaries"
      run := do
        let checks : Array (Nat × Nat) :=
          #[
            (0, 1),
            (1, 2),
            (5, 16),
            (15, 16),
            (255, 256),
            (256, 256)
          ]
        for (prefixOnes, total) in checks do
          let s := mkPrefixOneSlice prefixOnes total
          let expected : Nat := if prefixOnes < total then prefixOnes else total
          expectOkStack s!"ok/prefix-{prefixOnes}/total-{total}"
            (runSdCntLead1Direct #[.slice s])
            #[intV (Int.ofNat expected)] }
    ,
    { name := "unit/direct/partial-cursor-and-refs"
      run := do
        let baseCell : Cell :=
          Cell.mkOrdinary
            #[false, true, true, true, false, true, false, false, true, true, true, false, true, false, true, true]
            #[refLeafA, refLeafB]
        let partialA : Slice := { cell := baseCell, bitPos := 1, refPos := 1 }
        let partialB : Slice := { cell := baseCell, bitPos := 4, refPos := 0 }

        expectOkStack "ok/partial-a"
          (runSdCntLead1Direct #[.slice partialA])
          #[intV (expectedLead1 partialA)]
        expectOkStack "ok/partial-b"
          (runSdCntLead1Direct #[.slice partialB])
          #[intV (expectedLead1 partialB)]

        let tailCell : Cell := Cell.mkOrdinary (stripeBits 24 0 ++ ones 4) #[refLeafA]
        let partialTail : Slice := { cell := tailCell, bitPos := 24, refPos := 0 }
        expectOkStack "ok/partial-tail-all-one"
          (runSdCntLead1Direct #[.slice partialTail])
          #[intV (expectedLead1 partialTail)]

        expectOkStack "ok/deep-stack-preserved"
          (runSdCntLead1Direct #[.null, intV 77, .slice partialA])
          #[.null, intV 77, intV (expectedLead1 partialA)] }
    ,
    { name := "unit/direct/errors-underflow-type"
      run := do
        expectErr "underflow/empty"
          (runSdCntLead1Direct #[]) .stkUnd
        expectErr "type/top-null"
          (runSdCntLead1Direct #[.null]) .typeChk
        expectErr "type/top-int"
          (runSdCntLead1Direct #[intV 0]) .typeChk
        expectErr "type/top-cell"
          (runSdCntLead1Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runSdCntLead1Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runSdCntLead1Direct #[.slice (mkPrefixOneSlice 2 8), .null]) .typeChk }
    ,
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-slice", #[.slice (mkSliceWithBitsRefs #[])]),
            ("ok/single-one", #[.slice (mkSliceWithBitsRefs #[true])]),
            ("ok/single-zero", #[.slice (mkSliceWithBitsRefs #[false])]),
            ("ok/prefix-3-of-8", #[.slice (mkPrefixOneSlice 3 8)]),
            ("ok/all-ones-32", #[.slice (mkPrefixOneSlice 32 32)]),
            ("ok/deep", #[.null, intV 9, .slice (mkPrefixOneSlice 5 16)]),
            ("err/underflow", #[]),
            ("err/type-null", #[.null]),
            ("err/type-order", #[.slice (mkPrefixOneSlice 2 8), .null])
          ]
        for (name, stack) in samples do
          expectSameOutcome s!"model/{name}"
            (runSdCntLead1Direct stack)
            (runSdCntLead1Model stack) }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [sdCntLead1Instr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdcntlead1 failed: {e}")
        if assembled.bits = natToBits sdCntLead1Opcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcntlead1: expected 0xc711, got bits {assembled.bits}")
        if assembled.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcntlead1: expected 16 bits, got {assembled.bits.size}")

        let dec0 := Slice.ofCell assembled
        let dec1 ← expectDecodeStep "decode/assembled-sdcntlead1" dec0 sdCntLead1Instr 16
        if dec1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/assembled-sdcntlead1: expected exhausted slice, got {dec1.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits sdPsfxRevOpcode 16 ++
          natToBits sdCntLead0Opcode 16 ++
          natToBits sdCntLead1Opcode 16 ++
          natToBits sdCntTrail0Opcode 16 ++
          natToBits sdCntTrail1Opcode 16 ++
          addCell.bits
        let s0 := mkSliceFromBits rawBits
        let s1 ← expectDecodeStep "decode/raw-neighbor-sdpsfxrev" s0 (.cellOp .sdPsfxRev) 16
        let s2 ← expectDecodeStep "decode/raw-neighbor-sdcntlead0" s1 .sdCntLead0 16
        let s3 ← expectDecodeStep "decode/raw-sdcntlead1" s2 sdCntLead1Instr 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-sdcnttrail0" s3 .sdCntTrail0 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-sdcnttrail1" s4 (.cellOp .sdCntTrail1) 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        match decodeCp0WithBits (mkSliceFromBits (natToBits sdCntLead1Opcode 15)) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/truncated: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-sdcntlead1-falls-through"
      run := do
        let sNeighbor := mkSliceWithBitsRefs (ones 8)
        expectOkStack "dispatch/non-cell-instr"
          (runSdCntLead1DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdcnttrail0-neighbor"
          (runSdCntLead1DispatchFallback .sdCntTrail0 #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/sdcntlead0-neighbor"
          (runSdCntLead1DispatchFallback .sdCntLead0 #[intV 12])
          #[intV 12, intV dispatchSentinel]
        expectOkStack "dispatch/sdcnttrail1-neighbor"
          (runSdCntLead1DispatchFallback (.cellOp .sdCntTrail1) #[.slice sNeighbor])
          #[.slice sNeighbor, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdCntLead1Case "ok/len0-empty" #[.slice (mkPrefixOneSlice 0 0)],
    mkSdCntLead1Case "ok/len1-one" #[.slice (mkPrefixOneSlice 1 1)],
    mkSdCntLead1Case "ok/len1-zero" #[.slice (mkPrefixOneSlice 0 1)],
    mkSdCntLead1Case "ok/len2-all-one" #[.slice (mkPrefixOneSlice 2 2)],
    mkSdCntLead1Case "ok/len2-prefix1" #[.slice (mkPrefixOneSlice 1 2)],
    mkSdCntLead1Case "ok/len8-all-one" #[.slice (mkPrefixOneSlice 8 8)],
    mkSdCntLead1Case "ok/len8-prefix3" #[.slice (mkPrefixOneSlice 3 8)],
    mkSdCntLead1Case "ok/len8-prefix0" #[.slice (mkPrefixOneSlice 0 8)],
    mkSdCntLead1Case "ok/len16-prefix7" #[.slice (mkPrefixOneSlice 7 16)],
    mkSdCntLead1Case "ok/len32-prefix1" #[.slice (mkPrefixOneSlice 1 32)],
    mkSdCntLead1Case "ok/len64-prefix4-refs2"
      #[.slice (mkPrefixOneSlice 4 64 #[refLeafA, refLeafB])],
    mkSdCntLead1Case "ok/len127-all-one" #[.slice (mkPrefixOneSlice 127 127)],
    mkSdCntLead1Case "ok/len255-all-one" #[.slice (mkPrefixOneSlice 255 255)],
    mkSdCntLead1Case "ok/len256-all-one" #[.slice (mkPrefixOneSlice 256 256)],
    mkSdCntLead1Case "ok/len1023-all-one" #[.slice (mkPrefixOneSlice 1023 1023)],
    mkSdCntLead1Case "ok/deep-stack-preserve"
      #[.null, intV 42, .slice (mkPrefixOneSlice 5 16)],

    mkSdCntLead1Case "underflow/empty" #[],
    mkSdCntLead1Case "type/top-null" #[.null],
    mkSdCntLead1Case "type/top-int" #[intV 0],
    mkSdCntLead1Case "type/top-cell" #[.cell Cell.empty],
    mkSdCntLead1Case "type/top-builder" #[.builder Builder.empty],
    mkSdCntLead1Case "type/deep-top-not-slice" #[.slice (mkPrefixOneSlice 3 8), .null],

    mkSdCntLead1Case "gas/exact-cost-succeeds"
      #[.slice (mkPrefixOneSlice 6 32)]
      #[.pushInt (.num sdCntLead1SetGasExact), .tonEnvOp .setGasLimit, sdCntLead1Instr],
    mkSdCntLead1Case "gas/exact-minus-one-out-of-gas"
      #[.slice (mkPrefixOneSlice 6 32)]
      #[.pushInt (.num sdCntLead1SetGasExactMinusOne), .tonEnvOp .setGasLimit, sdCntLead1Instr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDCNTLEAD1
