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

private def zeros (n : Nat) : BitString :=
  Array.replicate n false

private def ones (n : Nat) : BitString :=
  Array.replicate n true

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

private def sdskipfirstInstr : Instr := .sdskipfirst

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    let (idx, rng2) := randNat rng1 0 (bitsBoundaryPool.size - 1)
    (((bitsBoundaryPool[idx]?).getD 0), rng2)
  else
    randNat rng1 0 1023

private def pickRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (4, rng1)
  else
    randNat rng1 0 4

private def fuzzNoisePool : Array Value :=
  #[.null, intV 0, intV 7, intV (-9), .cell Cell.empty, .builder Builder.empty, .tuple #[], .cont (.quit 0)]

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (fuzzNoisePool.size - 1)
  (((fuzzNoisePool[idx]?).getD .null), rng1)

private def genSdCntTrail1FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  if shape = 0 then
    let (total, rng2) := pickBitsMixed rng1
    let (sufOnes, rng3) := randNat rng2 0 total
    let (refs, rng4) := pickRefsMixed rng3
    let s := mkSuffixOneSlice sufOnes total (refsByCount refs)
    (mkSdCntTrail1Case s!"fuzz/ok/suffix{sufOnes}/total{total}/refs{refs}" #[.slice s], rng4)
  else if shape = 1 then
    let (total, rng2) := pickBitsMixed rng1
    let (bits, rng3) := randBitString total rng2
    let (refs, rng4) := pickRefsMixed rng3
    let s := mkSliceWithBitsRefs bits (refsByCount refs)
    (mkSdCntTrail1Case s!"fuzz/ok/random/len{total}/refs{refs}" #[.slice s], rng4)
  else if shape = 2 then
    let (total, rng2) := pickBitsMixed rng1
    let (sufOnes, rng3) := randNat rng2 0 total
    let (skip, rng4) := randNat rng3 0 total
    let (refs, rng5) := pickRefsMixed rng4
    let s := mkSuffixOneSlice sufOnes total (refsByCount refs)
    let stack : Array Value := #[.slice s, intV (Int.ofNat skip)]
    let program : Array Instr := #[sdskipfirstInstr, sdCntTrail1Instr]
    (mkSdCntTrail1Case s!"fuzz/ok/cursor/skip{skip}" stack program, rng5)
  else if shape = 3 then
    let (total, rng2) := pickBitsMixed rng1
    let (sufOnes, rng3) := randNat rng2 0 total
    let (refs, rng4) := pickRefsMixed rng3
    let (noise, rng5) := pickNoiseValue rng4
    let s := mkSuffixOneSlice sufOnes total (refsByCount refs)
    (mkSdCntTrail1Case "fuzz/ok/deep" #[noise, .slice s], rng5)
  else if shape = 4 then
    (mkSdCntTrail1Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    let (mode, rng2) := randNat rng1 0 2
    let bad : Value :=
      if mode = 0 then .null
      else if mode = 1 then intV 0
      else .cell Cell.empty
    (mkSdCntTrail1Case "fuzz/type/top" #[bad], rng2)
  else
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdCntTrail1Case "fuzz/type/deep-top" #[.slice (mkSuffixOneSlice 3 8), bad], rng2)

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
  fuzz := #[
    { seed := 2026021119
      count := 500
      gen := genSdCntTrail1FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDCNTTRAIL1
