import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDCNTTRAIL1

/-
SDCNTTRAIL1 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdCntTrail1`)
  - `TvmLean/Semantics/Exec/CellOp.lean` (dispatch from `.cellOp`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode `0xc713`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (encode `0xc713`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`reg_iun_cs_cmp(..., "SDCNTTRAIL1", [](auto cs) { return cs->count_trailing(1); })`).

Branch map used for this suite:
- handler dispatch: `.cellOp .sdCntTrail1` vs fallthrough to `next`;
- stack checks: `checkUnderflow 1` then `popSlice` (`stkUnd` / `typeChk` / success);
- trailing-scan outcomes: `rem=0 -> 0`, last bit `0 -> 0`,
  mixed suffix ones -> stop on first trailing `0`, all trailing bits `1` -> full `rem`;
- opcode/decode boundary at exact `0xc713` with nearby `0xc710`/`0xc711`/`0xc712`/`0xc70f`.
-/

private def sdCntTrail1Id : InstrId := { name := "SDCNTTRAIL1" }

private def sdCntTrail1Instr : Instr := .cellOp .sdCntTrail1

private def dispatchSentinel : Int := 71351

private def sdCntLead0Opcode : Nat := 0xc710
private def sdCntLead1Opcode : Nat := 0xc711
private def sdCntTrail0Opcode : Nat := 0xc712
private def sdCntTrail1Opcode : Nat := 0xc713
private def sdPsfxRevOpcode : Nat := 0xc70f

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]

private def zeros (n : Nat) : BitString :=
  Array.replicate n false

private def ones (n : Nat) : BitString :=
  Array.replicate n true

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSuffixOneSlice (suffixOnes total : Nat) (refs : Array Cell := #[]) : Slice :=
  if suffixOnes < total then
    let headLen : Nat := total - suffixOnes - 1
    let head := stripeBits headLen 0
    mkSliceWithBitsRefs (head ++ #[false] ++ ones suffixOnes) refs
  else
    mkSliceWithBitsRefs (ones total) refs

private def expectedTrail1Nat (s : Slice) : Nat :=
  Id.run do
    let rem : Nat := s.bitsRemaining
    if rem = 0 then
      return 0
    let mut cnt : Nat := 0
    while cnt < rem && s.cell.bits[s.bitPos + rem - 1 - cnt]! == true do
      cnt := cnt + 1
    return cnt

private def expectedTrail1 (s : Slice) : Int :=
  Int.ofNat (expectedTrail1Nat s)

private def execInstrCellOpSdCntTrail1Only (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdCntTrail1 => execCellOpExt .sdCntTrail1 next
  | _ => next

private def runSdCntTrail1Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSdCntTrail1Only sdCntTrail1Instr stack

private def runSdCntTrail1DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellOpSdCntTrail1Only instr (VM.push (intV dispatchSentinel)) stack

private def runSdCntTrail1Model (stack : Array Value) : Except Excno (Array Value) := do
  if stack.isEmpty then
    throw .stkUnd
  let top := stack.back!
  let below := stack.extract 0 (stack.size - 1)
  match top with
  | .slice s =>
      pure (below.push (intV (expectedTrail1 s)))
  | _ =>
      throw .typeChk

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

private def mkSdCntTrail1Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdCntTrail1Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdCntTrail1Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def sdCntTrail1SetGasExact : Int :=
  computeExactGasBudget sdCntTrail1Instr

private def sdCntTrail1SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdCntTrail1Instr

def suite : InstrSuite where
  id := { name := "SDCNTTRAIL1" }
  unit := #[
    { name := "unit/direct/success-full-slices"
      run := do
        let checks : Array (String × Slice) :=
          #[
            ("empty", mkSliceWithBitsRefs #[]),
            ("len1-zero", mkSliceWithBitsRefs #[false]),
            ("len1-one", mkSliceWithBitsRefs #[true]),
            ("len4-suffix2", mkSliceWithBitsRefs #[false, false, true, true]),
            ("len8-stripe0", mkSliceWithBitsRefs (stripeBits 8 0)),
            ("len8-stripe1", mkSliceWithBitsRefs (stripeBits 8 1)),
            ("len32-all-one", mkSliceWithBitsRefs (ones 32)),
            ("len64-all-zero", mkSliceWithBitsRefs (zeros 64))
          ]
        for (label, s) in checks do
          expectOkStack s!"ok/{label}"
            (runSdCntTrail1Direct #[.slice s])
            #[intV (expectedTrail1 s)] }
    ,
    { name := "unit/direct/manual-suffix-boundaries"
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
        for (suffixOnes, total) in checks do
          let s := mkSuffixOneSlice suffixOnes total
          let expected : Nat := if suffixOnes < total then suffixOnes else total
          expectOkStack s!"ok/suffix-{suffixOnes}/total-{total}"
            (runSdCntTrail1Direct #[.slice s])
            #[intV (Int.ofNat expected)] }
    ,
    { name := "unit/direct/partial-cursor-and-refs"
      run := do
        let baseCell : Cell :=
          Cell.mkOrdinary
            #[true, false, true, false, false, true, true, true, false, true, true, false, true, true, true, false]
            #[refLeafA, refLeafB]
        let partialA : Slice := { cell := baseCell, bitPos := 2, refPos := 1 }
        let partialB : Slice := { cell := baseCell, bitPos := 5, refPos := 0 }

        expectOkStack "ok/partial-a"
          (runSdCntTrail1Direct #[.slice partialA])
          #[intV (expectedTrail1 partialA)]
        expectOkStack "ok/partial-b"
          (runSdCntTrail1Direct #[.slice partialB])
          #[intV (expectedTrail1 partialB)]

        let tailCell : Cell := Cell.mkOrdinary (stripeBits 24 1 ++ ones 4) #[refLeafA]
        let partialTail : Slice := { cell := tailCell, bitPos := 24, refPos := 0 }
        expectOkStack "ok/partial-tail-all-one"
          (runSdCntTrail1Direct #[.slice partialTail])
          #[intV (expectedTrail1 partialTail)]

        expectOkStack "ok/refpos-does-not-affect-count"
          (runSdCntTrail1Direct #[.slice { partialA with refPos := 0 }])
          #[intV (expectedTrail1 partialA)]

        expectOkStack "ok/deep-stack-preserved"
          (runSdCntTrail1Direct #[.null, intV 77, .slice partialA])
          #[.null, intV 77, intV (expectedTrail1 partialA)] }
    ,
    { name := "unit/direct/errors-underflow-type"
      run := do
        expectErr "underflow/empty"
          (runSdCntTrail1Direct #[]) .stkUnd
        expectErr "type/top-null"
          (runSdCntTrail1Direct #[.null]) .typeChk
        expectErr "type/top-int"
          (runSdCntTrail1Direct #[intV 0]) .typeChk
        expectErr "type/top-cell"
          (runSdCntTrail1Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runSdCntTrail1Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runSdCntTrail1Direct #[.slice (mkSuffixOneSlice 3 8), .null]) .typeChk }
    ,
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-slice", #[.slice (mkSliceWithBitsRefs #[])]),
            ("ok/single-one", #[.slice (mkSliceWithBitsRefs #[true])]),
            ("ok/single-zero", #[.slice (mkSliceWithBitsRefs #[false])]),
            ("ok/suffix5-of16", #[.slice (mkSuffixOneSlice 5 16)]),
            ("ok/all-ones-64", #[.slice (mkSuffixOneSlice 64 64)]),
            ("ok/deep", #[.null, intV 9, .slice (mkSuffixOneSlice 7 16)]),
            ("err/underflow", #[]),
            ("err/type-null", #[.null]),
            ("err/type-order", #[.slice (mkSliceWithBitsRefs #[true]), .null])
          ]
        for (name, stack) in samples do
          expectSameOutcome s!"model/{name}"
            (runSdCntTrail1Direct stack)
            (runSdCntTrail1Model stack) }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [sdCntTrail1Instr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdcnttrail1 failed: {e}")
        if assembled.bits = natToBits sdCntTrail1Opcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcnttrail1: expected 0xc713, got bits {assembled.bits}")
        if assembled.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcnttrail1: expected 16 bits, got {assembled.bits.size}")

        let dec0 := Slice.ofCell assembled
        let dec1 ← expectDecodeStep "decode/assembled-sdcnttrail1" dec0 sdCntTrail1Instr 16
        if dec1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/assembled-sdcnttrail1: expected exhausted slice, got {dec1.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits sdPsfxRevOpcode 16 ++
          natToBits sdCntTrail0Opcode 16 ++
          natToBits sdCntTrail1Opcode 16 ++
          natToBits sdCntLead1Opcode 16 ++
          natToBits sdCntLead0Opcode 16 ++
          addCell.bits
        let s0 := mkSliceFromBits rawBits
        let s1 ← expectDecodeStep "decode/raw-neighbor-sdpsfxrev" s0 (.cellOp .sdPsfxRev) 16
        let s2 ← expectDecodeStep "decode/raw-neighbor-sdcnttrail0" s1 .sdCntTrail0 16
        let s3 ← expectDecodeStep "decode/raw-sdcnttrail1" s2 sdCntTrail1Instr 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-sdcntlead1" s3 (.cellOp .sdCntLead1) 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-sdcntlead0" s4 .sdCntLead0 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        match decodeCp0WithBits (mkSliceFromBits (natToBits sdCntTrail1Opcode 15)) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/truncated: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-sdcnttrail1-falls-through"
      run := do
        let sNeighbor := mkSliceWithBitsRefs (ones 8)
        expectOkStack "dispatch/non-cell-instr"
          (runSdCntTrail1DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdcnttrail0-neighbor"
          (runSdCntTrail1DispatchFallback .sdCntTrail0 #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/sdcntlead1-neighbor"
          (runSdCntTrail1DispatchFallback (.cellOp .sdCntLead1) #[.slice sNeighbor])
          #[.slice sNeighbor, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdCntTrail1Case "ok/len0-empty" #[.slice (mkSuffixOneSlice 0 0)],
    mkSdCntTrail1Case "ok/len1-zero" #[.slice (mkSuffixOneSlice 0 1)],
    mkSdCntTrail1Case "ok/len1-one" #[.slice (mkSuffixOneSlice 1 1)],
    mkSdCntTrail1Case "ok/len2-all-one" #[.slice (mkSuffixOneSlice 2 2)],
    mkSdCntTrail1Case "ok/len2-suffix1" #[.slice (mkSuffixOneSlice 1 2)],
    mkSdCntTrail1Case "ok/len8-all-one" #[.slice (mkSuffixOneSlice 8 8)],
    mkSdCntTrail1Case "ok/len8-suffix3" #[.slice (mkSuffixOneSlice 3 8)],
    mkSdCntTrail1Case "ok/len8-suffix0" #[.slice (mkSuffixOneSlice 0 8)],
    mkSdCntTrail1Case "ok/len16-suffix7" #[.slice (mkSuffixOneSlice 7 16)],
    mkSdCntTrail1Case "ok/len64-suffix4-refs2"
      #[.slice (mkSuffixOneSlice 4 64 #[refLeafA, refLeafB])],
    mkSdCntTrail1Case "ok/len127-all-one" #[.slice (mkSuffixOneSlice 127 127)],
    mkSdCntTrail1Case "ok/len255-all-one" #[.slice (mkSuffixOneSlice 255 255)],
    mkSdCntTrail1Case "ok/len256-all-one" #[.slice (mkSuffixOneSlice 256 256)],
    mkSdCntTrail1Case "ok/len1023-all-one" #[.slice (mkSuffixOneSlice 1023 1023)],
    mkSdCntTrail1Case "ok/deep-stack-preserve"
      #[.null, intV 42, .slice (mkSuffixOneSlice 5 16)],

    mkSdCntTrail1Case "underflow/empty" #[],
    mkSdCntTrail1Case "type/top-null" #[.null],
    mkSdCntTrail1Case "type/top-int" #[intV 0],
    mkSdCntTrail1Case "type/top-cell" #[.cell Cell.empty],
    mkSdCntTrail1Case "type/top-builder" #[.builder Builder.empty],
    mkSdCntTrail1Case "type/deep-top-not-slice" #[.slice (mkSuffixOneSlice 3 8), .null],

    mkSdCntTrail1Case "gas/exact-cost-succeeds"
      #[.slice (mkSuffixOneSlice 6 32)]
      #[.pushInt (.num sdCntTrail1SetGasExact), .tonEnvOp .setGasLimit, sdCntTrail1Instr],
    mkSdCntTrail1Case "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSuffixOneSlice 6 32)]
      #[.pushInt (.num sdCntTrail1SetGasExactMinusOne), .tonEnvOp .setGasLimit, sdCntTrail1Instr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDCNTTRAIL1
