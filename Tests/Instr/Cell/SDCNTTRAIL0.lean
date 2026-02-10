import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDCNTTRAIL0

/-
SDCNTTRAIL0 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdCntTrail0.lean` (`.sdCntTrail0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode `0xc712`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (encode `0xc712`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`reg_iun_cs_cmp(..., "SDCNTTRAIL0", [](auto cs) { return cs->count_trailing(0); })`).

Branch map used for this suite:
- handler dispatch: `.sdCntTrail0` vs fallthrough to `next`;
- stack pop branch (`VM.popSlice`): `stkUnd` / `typeChk` / valid slice;
- trailing scan outcomes over remaining bits:
  empty (`rem=0`) -> `0`,
  last bit non-zero -> `0`,
  mixed suffix zeros -> stop at first trailing `1`,
  all remaining bits zero -> full `rem`;
- fixed-width opcode decode/encode boundary at `0xc712` with neighbors
  (`0xc710`, `0xc711`, `0xc713`, `0xc70f`).
-/

private def sdCntTrail0Id : InstrId := { name := "SDCNTTRAIL0" }

private def sdCntTrail0Instr : Instr := .sdCntTrail0

private def dispatchSentinel : Int := 607

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

private def mkSuffixZeroSlice (suffixZeros total : Nat) (refs : Array Cell := #[]) : Slice :=
  if suffixZeros < total then
    let prefixLen : Nat := total - suffixZeros - 1
    let prefixBits := stripeBits prefixLen 1
    mkSliceWithBitsRefs (prefixBits ++ #[true] ++ zeros suffixZeros) refs
  else
    mkSliceWithBitsRefs (zeros total) refs

private def expectedTrail0 (s : Slice) : Int :=
  Id.run do
    let rem : Nat := s.bitsRemaining
    let endPos : Nat := s.cell.bits.size
    let mut cnt : Nat := 0
    while cnt < rem && s.cell.bits[endPos - 1 - cnt]! == false do
      cnt := cnt + 1
    pure (Int.ofNat cnt)

private def runSdCntTrail0Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdCntTrail0 sdCntTrail0Instr stack

private def runSdCntTrail0DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdCntTrail0 instr (VM.push (intV dispatchSentinel)) stack

private def mkSdCntTrail0Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdCntTrail0Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdCntTrail0Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def sdCntTrail0SetGasExact : Int :=
  computeExactGasBudget sdCntTrail0Instr

private def sdCntTrail0SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdCntTrail0Instr

private def cursorCell : Cell :=
  Cell.mkOrdinary
    #[true, true, false, false, false, true, false, false, false, true, false, true, false, false, false, false]
    #[refLeafA, refLeafB]

private def cursorSliceA : Slice := { cell := cursorCell, bitPos := 2, refPos := 1 }
private def cursorSliceB : Slice := { cell := cursorCell, bitPos := 5, refPos := 0 }

def suite : InstrSuite where
  id := { name := "SDCNTTRAIL0" }
  unit := #[
    { name := "unit/direct/success-full-slices"
      run := do
        let checks : Array (String × Slice) :=
          #[
            ("empty", mkSliceWithBitsRefs #[]),
            ("len1-zero", mkSliceWithBitsRefs #[false]),
            ("len1-one", mkSliceWithBitsRefs #[true]),
            ("len4-trail2", mkSliceWithBitsRefs #[true, true, false, false]),
            ("len8-stripe0", mkSliceWithBitsRefs (stripeBits 8 0)),
            ("len8-stripe1", mkSliceWithBitsRefs (stripeBits 8 1)),
            ("len32-all-zero", mkSliceWithBitsRefs (zeros 32)),
            ("len64-all-one", mkSliceWithBitsRefs (ones 64))
          ]
        for (label, s) in checks do
          expectOkStack s!"ok/{label}"
            (runSdCntTrail0Direct #[.slice s])
            #[intV (expectedTrail0 s)] }
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
        for (suffixZeros, total) in checks do
          let s := mkSuffixZeroSlice suffixZeros total
          let expected : Nat := if suffixZeros < total then suffixZeros else total
          expectOkStack s!"ok/suffix-{suffixZeros}/total-{total}"
            (runSdCntTrail0Direct #[.slice s])
            #[intV (Int.ofNat expected)] }
    ,
    { name := "unit/direct/loop-stop-at-first-trailing-one"
      run := do
        let checks : Array (String × Slice × Int) :=
          #[
            ("trail3-stop", mkSliceWithBitsRefs #[false, false, true, false, false, false], 3),
            ("trail1-stop", mkSliceWithBitsRefs #[true, false, true, false, true, false], 1),
            ("trail0-last-is-one", mkSliceWithBitsRefs #[true, false, true, true, true, true], 0)
          ]
        for (label, s, expected) in checks do
          expectOkStack s!"ok/{label}"
            (runSdCntTrail0Direct #[.slice s])
            #[intV expected] }
    ,
    { name := "unit/direct/partial-cursor-and-refs"
      run := do
        expectOkStack "ok/partial-a"
          (runSdCntTrail0Direct #[.slice cursorSliceA])
          #[intV (expectedTrail0 cursorSliceA)]
        expectOkStack "ok/partial-b"
          (runSdCntTrail0Direct #[.slice cursorSliceB])
          #[intV (expectedTrail0 cursorSliceB)]

        let tailCell : Cell := Cell.mkOrdinary (stripeBits 24 1 ++ zeros 4) #[refLeafA]
        let partialTail : Slice := { cell := tailCell, bitPos := 24, refPos := 0 }
        expectOkStack "ok/partial-tail-all-zero"
          (runSdCntTrail0Direct #[.slice partialTail])
          #[intV (expectedTrail0 partialTail)]

        expectOkStack "ok/deep-stack-preserved"
          (runSdCntTrail0Direct #[.null, intV 77, .slice cursorSliceA])
          #[.null, intV 77, intV (expectedTrail0 cursorSliceA)] }
    ,
    { name := "unit/direct/large-bitstrings"
      run := do
        let allZero1023 := mkSuffixZeroSlice 1023 1023
        let suffix511of1023 := mkSuffixZeroSlice 511 1023
        let stripe1023 := mkSliceWithBitsRefs (stripeBits 1023 1)
        expectOkStack "ok/1023-all-zero"
          (runSdCntTrail0Direct #[.slice allZero1023])
          #[intV (expectedTrail0 allZero1023)]
        expectOkStack "ok/1023-suffix511"
          (runSdCntTrail0Direct #[.slice suffix511of1023])
          #[intV (expectedTrail0 suffix511of1023)]
        expectOkStack "ok/1023-stripe-tail"
          (runSdCntTrail0Direct #[.slice stripe1023])
          #[intV (expectedTrail0 stripe1023)] }
    ,
    { name := "unit/direct/errors-underflow-type"
      run := do
        expectErr "underflow/empty"
          (runSdCntTrail0Direct #[]) .stkUnd
        expectErr "type/top-null"
          (runSdCntTrail0Direct #[.null]) .typeChk
        expectErr "type/top-int"
          (runSdCntTrail0Direct #[intV 0]) .typeChk
        expectErr "type/top-cell"
          (runSdCntTrail0Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runSdCntTrail0Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runSdCntTrail0Direct #[.slice (mkSuffixZeroSlice 2 8), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [sdCntTrail0Instr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdcnttrail0 failed: {e}")
        if assembled.bits = natToBits sdCntTrail0Opcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcnttrail0: expected 0xc712, got bits {assembled.bits}")
        if assembled.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcnttrail0: expected 16 bits, got {assembled.bits.size}")

        let dec0 := Slice.ofCell assembled
        let dec1 ← expectDecodeStep "decode/assembled-sdcnttrail0" dec0 sdCntTrail0Instr 16
        if dec1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/assembled-sdcnttrail0: expected exhausted slice, got {dec1.bitsRemaining} bits remaining")

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
        let s3 ← expectDecodeStep "decode/raw-neighbor-sdcntlead1" s2 (.cellOp .sdCntLead1) 16
        let s4 ← expectDecodeStep "decode/raw-sdcnttrail0" s3 sdCntTrail0Instr 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-sdcnttrail1" s4 (.cellOp .sdCntTrail1) 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        match decodeCp0WithBits (mkSliceFromBits (natToBits sdCntTrail0Opcode 15)) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/truncated: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-sdcnttrail0-falls-through"
      run := do
        let sNeighbor := mkSliceWithBitsRefs (zeros 8)
        expectOkStack "dispatch/non-cell-instr"
          (runSdCntTrail0DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdcntlead0-neighbor"
          (runSdCntTrail0DispatchFallback .sdCntLead0 #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/sdcnttrail1-neighbor"
          (runSdCntTrail0DispatchFallback (.cellOp .sdCntTrail1) #[.slice sNeighbor])
          #[.slice sNeighbor, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdCntTrail0Case "ok/len0-empty" #[.slice (mkSuffixZeroSlice 0 0)],
    mkSdCntTrail0Case "ok/len1-zero" #[.slice (mkSuffixZeroSlice 1 1)],
    mkSdCntTrail0Case "ok/len1-one" #[.slice (mkSuffixZeroSlice 0 1)],
    mkSdCntTrail0Case "ok/len2-all-zero" #[.slice (mkSuffixZeroSlice 2 2)],
    mkSdCntTrail0Case "ok/len2-suffix1" #[.slice (mkSuffixZeroSlice 1 2)],
    mkSdCntTrail0Case "ok/len8-all-zero" #[.slice (mkSuffixZeroSlice 8 8)],
    mkSdCntTrail0Case "ok/len8-suffix3" #[.slice (mkSuffixZeroSlice 3 8)],
    mkSdCntTrail0Case "ok/len8-suffix0" #[.slice (mkSuffixZeroSlice 0 8)],
    mkSdCntTrail0Case "ok/len16-suffix7" #[.slice (mkSuffixZeroSlice 7 16)],
    mkSdCntTrail0Case "ok/len64-suffix4-refs2"
      #[.slice (mkSuffixZeroSlice 4 64 #[refLeafA, refLeafB])],
    mkSdCntTrail0Case "ok/len255-all-zero" #[.slice (mkSuffixZeroSlice 255 255)],
    mkSdCntTrail0Case "ok/len1023-all-zero" #[.slice (mkSuffixZeroSlice 1023 1023)],
    mkSdCntTrail0Case "ok/deep-stack-preserve"
      #[.null, intV 42, .slice (mkSuffixZeroSlice 5 16)],
    mkSdCntTrail0Case "ok/len256-all-zero" #[.slice (mkSuffixZeroSlice 256 256)],

    mkSdCntTrail0Case "underflow/empty" #[],
    mkSdCntTrail0Case "type/top-null" #[.null],
    mkSdCntTrail0Case "type/top-int" #[intV 0],
    mkSdCntTrail0Case "type/top-cell" #[.cell Cell.empty],
    mkSdCntTrail0Case "type/top-builder" #[.builder Builder.empty],
    mkSdCntTrail0Case "type/deep-top-not-slice" #[.slice (mkSuffixZeroSlice 3 8), .null],

    mkSdCntTrail0Case "gas/exact-cost-succeeds"
      #[.slice (mkSuffixZeroSlice 6 32)]
      #[.pushInt (.num sdCntTrail0SetGasExact), .tonEnvOp .setGasLimit, sdCntTrail0Instr],
    mkSdCntTrail0Case "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSuffixZeroSlice 6 32)]
      #[.pushInt (.num sdCntTrail0SetGasExactMinusOne), .tonEnvOp .setGasLimit, sdCntTrail0Instr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDCNTTRAIL0
