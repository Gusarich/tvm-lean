import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDREFIDX

/-!
PLDREFIDX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/PldRefIdx.lean` (`.pldRefIdx idx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.pldRefIdx idx` encodes as `0xd74c + idx`, idx `< 4`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd74c..0xd74f` decode to `.pldRefIdx idx`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_preload_ref_fixed`, opcode registration via `OpcodeInstr::mkfixed(0xd74c >> 2, 14, 2, ...)`).

Branch map covered by this suite:
- dispatch guard for non-`.pldRefIdx` instructions;
- top pop via `VM.popSlice` (underflow/type paths);
- reference availability check `haveRefs (idx + 1)`:
  - success pushes only preloaded referenced cell (no remainder slice in prefetch form),
  - failure throws `cellUnd`;
- decode/dispatch boundary checks around the whole fixed-index family (`0xd74c..0xd74f`)
  and immediate neighbors (`0xd74b`, `0xd750`).
-/

private def pldrefIdxId : InstrId := { name := "PLDREFIDX" }

private def pldrefIdxInstr (idx : Nat) : Instr := .pldRefIdx idx

private def pldrefIdxOpcodeBase : Nat := 0xd74c

private def pldrefIdxOpcode (idx : Nat) : Nat :=
  pldrefIdxOpcodeBase + idx

private def dispatchSentinel : Int := 673

private def mkPldrefIdxProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldrefIdxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPldrefIdxCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkPldrefIdxProgramCase name stack #[pldrefIdxInstr idx] gasLimits fuel

private def runPldrefIdxDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellPldRefIdx (pldrefIdxInstr idx) stack

private def runPldrefIdxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellPldRefIdx instr (VM.push (intV dispatchSentinel)) stack

private def pldrefIdxGasInstr : Instr := .pldRefIdx 2

private def pldrefIdxSetGasExact : Int :=
  computeExactGasBudget pldrefIdxGasInstr

private def pldrefIdxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pldrefIdxGasInstr

private def mkCellWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary bits refs

private def mkSliceWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (mkCellWithBitsAndRefs bits refs)

private def refCellA : Cell :=
  mkCellWithBitsAndRefs (natToBits 0b101 3) #[]

private def refCellB : Cell :=
  mkCellWithBitsAndRefs (natToBits 0xA5 8) #[Cell.empty]

private def refCellC : Cell :=
  mkCellWithBitsAndRefs (natToBits 0x15 5) #[refCellA, Cell.empty]

private def refCellD : Cell :=
  mkCellWithBitsAndRefs (natToBits 0x2A 6) #[refCellB]

private def refCellPool : Array Cell :=
  #[refCellA, refCellB, refCellC, refCellD]

private def sliceRefs1Bits0 : Slice :=
  mkSliceWithBitsAndRefs #[] #[refCellA]

private def sliceRefs2Bits3 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b101 3) #[refCellA, refCellB]

private def sliceRefs3Bits7 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x53 7) #[refCellA, refCellB, refCellC]

private def sliceRefs4Bits11 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x5AB 11) #[refCellA, refCellB, refCellC, refCellD]

private def sliceNoRefsEmpty : Slice :=
  mkSliceWithBitsAndRefs #[] #[]

private def sliceNoRefsBits9 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x12F 9) #[]

private def sliceOneRefBits5 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x1B 5) #[refCellA]

private def sliceTwoRefsBits5 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x12 5) #[refCellA, refCellB]

private def sliceThreeRefsBits5 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x09 5) #[refCellA, refCellB, refCellC]

private def sliceShiftedRefBase : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b110011 6) #[refCellA, refCellB, refCellC, refCellD]

private def sliceShiftedRef : Slice :=
  { sliceShiftedRefBase with refPos := 1 }

private def sliceShiftedBitAndRef : Slice :=
  { (mkSliceWithBitsAndRefs (natToBits 0b111001101 9) #[refCellD, refCellC, refCellB, refCellA]).advanceBits 3 with
      refPos := 1 }

private def sliceShiftedNearEnd : Slice :=
  { sliceShiftedRefBase with refPos := 3 }

private def sliceAllRefsConsumed : Slice :=
  { sliceShiftedRefBase with refPos := sliceShiftedRefBase.cell.refs.size }

private def expectedPldrefIdxOut (below : Array Value) (s : Slice) (idx : Nat) : Array Value :=
  below ++ #[.cell s.cell.refs[s.refPos + idx]!]

private def mkPatternBits (bitCount : Nat) : BitString := Id.run do
  let mut bits : BitString := #[]
  for i in [0:bitCount] do
    let bit := ((i % 2) == 0) || ((i % 5) == 1)
    bits := bits.push bit
  return bits

private def mkPatternSliceWithRefs (bitCount : Nat) (refs : Array Cell) : Slice :=
  mkSliceWithBitsAndRefs (mkPatternBits bitCount) refs

private def bitCountBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127]

private def pickBitCountMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (bitCountBoundaryPool.size - 1)
    (bitCountBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 160

private def pickIdx (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 3

private def pickRefCountSuccess (idx : Nat) (rng : StdGen) : Nat × StdGen :=
  randNat rng (idx + 1) 4

private def pickRefCountInsufficient (idx : Nat) (rng : StdGen) : Nat × StdGen :=
  if idx = 0 then
    (0, rng)
  else
    randNat rng 0 idx

private def randBitString (bitCount : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:bitCount] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def genRefArray (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut refs : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (pick, rng') := randNat rng 0 (refCellPool.size - 1)
    refs := refs.push (refCellPool[pick]!)
    rng := rng'
  return (refs, rng)

private def mkRandomSlice (bitCount refCount : Nat) (rng0 : StdGen) : Slice × StdGen :=
  let (bits, rng1) := randBitString bitCount rng0
  let (refs, rng2) := genRefArray refCount rng1
  (mkSliceWithBitsAndRefs bits refs, rng2)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), rng2)
  else if pick = 2 then
    (.cell refCellB, rng1)
  else if pick = 3 then
    (.builder Builder.empty, rng1)
  else if pick = 4 then
    (.tuple #[], rng1)
  else
    (.cell refCellD, rng1)

private def genPldrefIdxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  if shape = 0 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 1 rng2
    (mkPldrefIdxCase s!"fuzz/ok/idx0/minimal/bits-{bitCount}" 0 #[.slice slice], rng3)
  else if shape = 1 then
    let (idx, rng2) := pickIdx rng1
    let refCount := idx + 1
    let (bitCount, rng3) := pickBitCountMixed rng2
    let (slice, rng4) := mkRandomSlice bitCount refCount rng3
    (mkPldrefIdxCase s!"fuzz/ok/idx-{idx}/refs-{refCount}/exact" idx #[.slice slice], rng4)
  else if shape = 2 then
    let (idx, rng2) := pickIdx rng1
    let (refCount, rng3) := pickRefCountSuccess idx rng2
    let (bitCount, rng4) := pickBitCountMixed rng3
    let (slice, rng5) := mkRandomSlice bitCount refCount rng4
    (mkPldrefIdxCase s!"fuzz/ok/idx-{idx}/refs-{refCount}/wide" idx #[.slice slice], rng5)
  else if shape = 3 then
    let (idx, rng2) := pickIdx rng1
    let (refCount, rng3) := pickRefCountSuccess idx rng2
    let (bitCount, rng4) := pickBitCountMixed rng3
    let (slice, rng5) := mkRandomSlice bitCount refCount rng4
    let (noise, rng6) := pickNoiseValue rng5
    (mkPldrefIdxCase s!"fuzz/ok/deep1/idx-{idx}/refs-{refCount}" idx #[noise, .slice slice], rng6)
  else if shape = 4 then
    let (idx, rng2) := pickIdx rng1
    let (refCount, rng3) := pickRefCountSuccess idx rng2
    let (bitCount, rng4) := pickBitCountMixed rng3
    let (slice, rng5) := mkRandomSlice bitCount refCount rng4
    let (noise1, rng6) := pickNoiseValue rng5
    let (noise2, rng7) := pickNoiseValue rng6
    (mkPldrefIdxCase s!"fuzz/ok/deep2/idx-{idx}/refs-{refCount}" idx #[noise1, noise2, .slice slice], rng7)
  else if shape = 5 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 4 rng2
    (mkPldrefIdxCase s!"fuzz/ok/idx3/refs4/bits-{bitCount}" 3 #[.slice slice], rng3)
  else if shape = 6 then
    let (bitCount, rng2) := randNat rng1 96 256
    let (slice, rng3) := mkRandomSlice bitCount 4 rng2
    (mkPldrefIdxCase s!"fuzz/ok/idx2/long-bits-{bitCount}" 2 #[.slice slice], rng3)
  else if shape = 7 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 0 rng2
    (mkPldrefIdxCase s!"fuzz/cellund/idx0/no-refs/bits-{bitCount}" 0 #[.slice slice], rng3)
  else if shape = 8 then
    let (idx, rng2) := pickIdx rng1
    let (refCount, rng3) := pickRefCountInsufficient idx rng2
    let (bitCount, rng4) := pickBitCountMixed rng3
    let (slice, rng5) := mkRandomSlice bitCount refCount rng4
    (mkPldrefIdxCase s!"fuzz/cellund/idx-{idx}/refs-{refCount}" idx #[.slice slice], rng5)
  else if shape = 9 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 3 rng2
    (mkPldrefIdxCase s!"fuzz/cellund/idx3/refs3/bits-{bitCount}" 3 #[.slice slice], rng3)
  else if shape = 10 then
    (mkPldrefIdxCase "fuzz/underflow/empty" 0 #[], rng1)
  else if shape = 11 then
    (mkPldrefIdxCase "fuzz/type/top-null" 0 #[.null], rng1)
  else if shape = 12 then
    let (n, rng2) := randNat rng1 0 255
    (mkPldrefIdxCase s!"fuzz/type/top-int-{n}" 1 #[intV (Int.ofNat n - 128)], rng2)
  else if shape = 13 then
    (mkPldrefIdxCase "fuzz/type/top-cell" 2 #[.cell refCellC], rng1)
  else if shape = 14 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 4 rng2
    (mkPldrefIdxCase "fuzz/type/deep-top-not-slice-null" 2 #[.slice slice, .null], rng3)
  else if shape = 15 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 4 rng2
    (mkPldrefIdxCase "fuzz/type/deep-top-not-slice-builder" 3 #[.slice slice, .builder Builder.empty], rng3)
  else if shape = 16 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 3 rng2
    (mkPldrefIdxProgramCase "fuzz/gas/exact"
      #[.slice slice]
      #[.pushInt (.num pldrefIdxSetGasExact), .tonEnvOp .setGasLimit, pldrefIdxGasInstr], rng3)
  else if shape = 17 then
    let (bitCount, rng2) := pickBitCountMixed rng1
    let (slice, rng3) := mkRandomSlice bitCount 3 rng2
    (mkPldrefIdxProgramCase "fuzz/gas/exact-minus-one"
      #[.slice slice]
      #[.pushInt (.num pldrefIdxSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldrefIdxGasInstr], rng3)
  else
    let (idx, rng2) := pickIdx rng1
    let (refCount, rng3) := pickRefCountSuccess idx rng2
    let (slice, rng4) := mkRandomSlice 0 refCount rng3
    (mkPldrefIdxCase s!"fuzz/ok/zero-bits/idx-{idx}/refs-{refCount}" idx #[.slice slice], rng4)

private def oracleSliceNoRefs0 : Slice := mkPatternSliceWithRefs 0 #[]

private def oracleSliceNoRefs9 : Slice := mkPatternSliceWithRefs 9 #[]

private def oracleSliceRefs1Bits0 : Slice := mkPatternSliceWithRefs 0 #[refCellA]

private def oracleSliceRefs1Bits9 : Slice := mkPatternSliceWithRefs 9 #[refCellB]

private def oracleSliceRefs2Bits3 : Slice := mkPatternSliceWithRefs 3 #[refCellA, refCellB]

private def oracleSliceRefs2Bits12 : Slice := mkPatternSliceWithRefs 12 #[refCellC, refCellA]

private def oracleSliceRefs3Bits6 : Slice := mkPatternSliceWithRefs 6 #[refCellA, refCellB, refCellC]

private def oracleSliceRefs3Bits19 : Slice := mkPatternSliceWithRefs 19 #[refCellD, refCellB, refCellC]

private def oracleSliceRefs4Bits0 : Slice := mkPatternSliceWithRefs 0 #[refCellA, refCellB, refCellC, refCellD]

private def oracleSliceRefs4Bits11 : Slice := mkPatternSliceWithRefs 11 #[refCellA, refCellB, refCellC, refCellD]

private def oracleSliceRefs4Bits31 : Slice := mkPatternSliceWithRefs 31 #[refCellD, refCellA, refCellC, refCellB]

private def oracleSliceOneRefBits5 : Slice := mkPatternSliceWithRefs 5 #[refCellA]

private def oracleSliceTwoRefsBits5 : Slice := mkPatternSliceWithRefs 5 #[refCellA, refCellB]

private def oracleSliceThreeRefsBits5 : Slice := mkPatternSliceWithRefs 5 #[refCellA, refCellB, refCellC]

def suite : InstrSuite where
  id := pldrefIdxId
  unit := #[
    { name := "unit/direct/success-ordering-and-index-selection"
      run := do
        expectOkStack "ok/idx0/minimal-one-ref"
          (runPldrefIdxDirect 0 #[.slice sliceRefs1Bits0])
          (expectedPldrefIdxOut #[] sliceRefs1Bits0 0)

        for idx in [0:4] do
          expectOkStack s!"ok/idx-{idx}/refs4"
            (runPldrefIdxDirect idx #[.slice sliceRefs4Bits11])
            (expectedPldrefIdxOut #[] sliceRefs4Bits11 idx)

        expectOkStack "ok/idx1/refs2"
          (runPldrefIdxDirect 1 #[.slice sliceRefs2Bits3])
          (expectedPldrefIdxOut #[] sliceRefs2Bits3 1)

        expectOkStack "ok/idx2/refs3"
          (runPldrefIdxDirect 2 #[.slice sliceRefs3Bits7])
          (expectedPldrefIdxOut #[] sliceRefs3Bits7 2)

        expectOkStack "ok/deep-stack-order-preserved"
          (runPldrefIdxDirect 2 #[.null, intV 99, .slice sliceRefs4Bits11])
          (expectedPldrefIdxOut #[.null, intV 99] sliceRefs4Bits11 2)

        expectOkStack "ok/shifted-refpos-idx0"
          (runPldrefIdxDirect 0 #[.slice sliceShiftedRef])
          (expectedPldrefIdxOut #[] sliceShiftedRef 0)

        expectOkStack "ok/shifted-refpos-idx2"
          (runPldrefIdxDirect 2 #[.slice sliceShiftedRef])
          (expectedPldrefIdxOut #[] sliceShiftedRef 2)

        expectOkStack "ok/shifted-bitpos-and-refpos"
          (runPldrefIdxDirect 1 #[.slice sliceShiftedBitAndRef])
          (expectedPldrefIdxOut #[] sliceShiftedBitAndRef 1) }
    ,
    { name := "unit/direct/cellund-branches"
      run := do
        expectErr "cellund/idx0/no-refs-empty"
          (runPldrefIdxDirect 0 #[.slice sliceNoRefsEmpty]) .cellUnd
        expectErr "cellund/idx0/no-refs-bits"
          (runPldrefIdxDirect 0 #[.slice sliceNoRefsBits9]) .cellUnd
        expectErr "cellund/idx1/only-one-ref"
          (runPldrefIdxDirect 1 #[.slice sliceOneRefBits5]) .cellUnd
        expectErr "cellund/idx2/only-two-refs"
          (runPldrefIdxDirect 2 #[.slice sliceTwoRefsBits5]) .cellUnd
        expectErr "cellund/idx3/only-three-refs"
          (runPldrefIdxDirect 3 #[.slice sliceThreeRefsBits5]) .cellUnd
        expectErr "cellund/idx1/shifted-near-end"
          (runPldrefIdxDirect 1 #[.slice sliceShiftedNearEnd]) .cellUnd
        expectErr "cellund/idx0/all-refs-consumed"
          (runPldrefIdxDirect 0 #[.slice sliceAllRefsConsumed]) .cellUnd }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty"
          (runPldrefIdxDirect 0 #[]) .stkUnd

        expectErr "type/top-null"
          (runPldrefIdxDirect 0 #[.null]) .typeChk
        expectErr "type/top-int"
          (runPldrefIdxDirect 1 #[intV 7]) .typeChk
        expectErr "type/top-cell"
          (runPldrefIdxDirect 2 #[.cell refCellA]) .typeChk
        expectErr "type/top-builder"
          (runPldrefIdxDirect 3 #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty"
          (runPldrefIdxDirect 0 #[.tuple #[]]) .typeChk

        expectErr "type/deep-top-not-slice-null"
          (runPldrefIdxDirect 2 #[.slice sliceRefs4Bits11, .null]) .typeChk
        expectErr "type/deep-top-not-slice-cell"
          (runPldrefIdxDirect 2 #[.slice sliceRefs4Bits11, .cell refCellC]) .typeChk
        expectErr "type/deep-top-not-slice-builder"
          (runPldrefIdxDirect 2 #[.slice sliceRefs4Bits11, .builder Builder.empty]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable-for-pldrefidx"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runPldrefIdxDirect 0 #[.slice sliceRefs1Bits0]),
            ("underflow", runPldrefIdxDirect 0 #[]),
            ("type", runPldrefIdxDirect 1 #[.null]),
            ("cellund", runPldrefIdxDirect 3 #[.slice sliceThreeRefsBits5])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for PLDREFIDX")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-dispatch-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[
          .sbitrefs,
          pldrefIdxInstr 0,
          pldrefIdxInstr 1,
          pldrefIdxInstr 2,
          pldrefIdxInstr 3,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sbitrefs-neighbor" s0 .sbitrefs 16
        let s2 ← expectDecodeStep "decode/pldrefidx-0" s1 (pldrefIdxInstr 0) 16
        let s3 ← expectDecodeStep "decode/pldrefidx-1" s2 (pldrefIdxInstr 1) 16
        let s4 ← expectDecodeStep "decode/pldrefidx-2" s3 (pldrefIdxInstr 2) 16
        let s5 ← expectDecodeStep "decode/pldrefidx-3" s4 (pldrefIdxInstr 3) 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        for idx in [0:4] do
          let single ←
            match assembleCp0 [pldrefIdxInstr idx] with
            | .ok c => pure c
            | .error e => throw (IO.userError s!"assemble/pldrefidx-{idx} failed: {e}")
          let expectedBits := natToBits (pldrefIdxOpcode idx) 16
          if single.bits = expectedBits then
            pure ()
          else
            throw (IO.userError s!"opcode/pldrefidx-{idx}: expected {(pldrefIdxOpcode idx)}, got bits {single.bits}")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd74b 16 ++
            natToBits 0xd74c 16 ++
            natToBits 0xd74d 16 ++
            natToBits 0xd74e 16 ++
            natToBits 0xd74f 16 ++
            natToBits 0xd750 16 ++
            addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-0xd74b-sbitrefs" r0 .sbitrefs 16
        let r2 ← expectDecodeStep "decode/raw-0xd74c-idx0" r1 (pldrefIdxInstr 0) 16
        let r3 ← expectDecodeStep "decode/raw-0xd74d-idx1" r2 (pldrefIdxInstr 1) 16
        let r4 ← expectDecodeStep "decode/raw-0xd74e-idx2" r3 (pldrefIdxInstr 2) 16
        let r5 ← expectDecodeStep "decode/raw-0xd74f-idx3" r4 (pldrefIdxInstr 3) 16
        let r6 ← expectDecodeStep "decode/raw-0xd750-loadle4-neighbor" r5 (.cellOp (.loadLeInt false 4 false false)) 16
        let r7 ← expectDecodeStep "decode/raw-tail-add" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining")

        match assembleCp0 [pldrefIdxInstr 4] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/pldrefidx-4: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldrefidx-4: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-pldrefidx-add"
          (runPldrefIdxDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-pldrefidx-ldref"
          (runPldrefIdxDispatchFallback .ldref #[.cell refCellA])
          #[.cell refCellA, intV dispatchSentinel]
        expectOkStack "dispatch/non-pldrefidx-loadslice-neighbor"
          (runPldrefIdxDispatchFallback (.loadSliceX true false) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldrefIdxCase "ok/idx0/minimal-one-ref"
      0
      #[.slice oracleSliceRefs1Bits0],
    mkPldrefIdxCase "ok/idx0/one-ref-with-bits"
      0
      #[.slice oracleSliceRefs1Bits9],
    mkPldrefIdxCase "ok/idx1/two-refs-exact"
      1
      #[.slice oracleSliceRefs2Bits3],
    mkPldrefIdxCase "ok/idx1/three-refs"
      1
      #[.slice oracleSliceRefs3Bits19],
    mkPldrefIdxCase "ok/idx2/three-refs-exact"
      2
      #[.slice oracleSliceRefs3Bits6],
    mkPldrefIdxCase "ok/idx2/four-refs"
      2
      #[.slice oracleSliceRefs4Bits11],
    mkPldrefIdxCase "ok/idx3/four-refs"
      3
      #[.slice oracleSliceRefs4Bits11],
    mkPldrefIdxCase "ok/idx0/zero-bits-four-refs"
      0
      #[.slice oracleSliceRefs4Bits0],
    mkPldrefIdxCase "ok/idx3/long-bits-four-refs"
      3
      #[.slice oracleSliceRefs4Bits31],
    mkPldrefIdxCase "ok/deep-preserve-null"
      0
      #[.null, .slice oracleSliceRefs1Bits9],
    mkPldrefIdxCase "ok/deep-preserve-cell"
      2
      #[.cell refCellD, .slice oracleSliceRefs4Bits11],
    mkPldrefIdxCase "ok/deep-preserve-builder-empty"
      3
      #[.builder Builder.empty, .slice oracleSliceRefs4Bits31],
    mkPldrefIdxCase "ok/deep-preserve-tuple-empty"
      1
      #[.tuple #[], .slice oracleSliceRefs3Bits19],

    mkPldrefIdxCase "cellund/idx0/no-refs-empty"
      0
      #[.slice oracleSliceNoRefs0],
    mkPldrefIdxCase "cellund/idx0/no-refs-bits"
      0
      #[.slice oracleSliceNoRefs9],
    mkPldrefIdxCase "cellund/idx1/only-one-ref"
      1
      #[.slice oracleSliceOneRefBits5],
    mkPldrefIdxCase "cellund/idx2/only-two-refs"
      2
      #[.slice oracleSliceTwoRefsBits5],
    mkPldrefIdxCase "cellund/idx3/only-three-refs"
      3
      #[.slice oracleSliceThreeRefsBits5],
    mkPldrefIdxCase "cellund/idx3/no-refs"
      3
      #[.slice oracleSliceNoRefs9],

    mkPldrefIdxCase "underflow/empty"
      0
      #[],
    mkPldrefIdxCase "type/top-null"
      0
      #[.null],
    mkPldrefIdxCase "type/top-int"
      1
      #[intV 42],
    mkPldrefIdxCase "type/top-cell"
      2
      #[.cell refCellB],
    mkPldrefIdxCase "type/top-builder-empty"
      3
      #[.builder Builder.empty],
    mkPldrefIdxCase "type/top-tuple-empty"
      0
      #[.tuple #[]],
    mkPldrefIdxCase "type/deep-top-not-slice-null"
      1
      #[.slice oracleSliceRefs3Bits6, .null],
    mkPldrefIdxCase "type/deep-top-not-slice-cell"
      1
      #[.slice oracleSliceRefs3Bits6, .cell refCellA],
    mkPldrefIdxCase "type/deep-top-not-slice-builder"
      1
      #[.slice oracleSliceRefs3Bits6, .builder Builder.empty],

    mkPldrefIdxProgramCase "gas/exact-cost-succeeds"
      #[.slice oracleSliceRefs3Bits6]
      #[.pushInt (.num pldrefIdxSetGasExact), .tonEnvOp .setGasLimit, pldrefIdxGasInstr],
    mkPldrefIdxProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSliceRefs3Bits6]
      #[.pushInt (.num pldrefIdxSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldrefIdxGasInstr]
  ]
  fuzz := #[
    { seed := 2026021074
      count := 320
      gen := genPldrefIdxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDREFIDX
