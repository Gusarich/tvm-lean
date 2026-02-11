import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDREF

/-
LDREF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ldref.lean` (`.ldref`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd4` decode to `.ldref`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ldref` encode as `0xd4`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_ref`, opcode registration at `0xd4`).

Branch map used for this suite (non-prefetch, non-quiet LDREF):
- Lean LDREF path: 3 branch sites / 5 terminal outcomes
  (dispatch guard; `popSlice` underflow/type; `haveRefs 1` success or `cellUnd`).
- C++ LDREF path (`mode=0`): 2 branch sites / 4 aligned outcomes
  (`pop_cellslice`; `have_refs` success or `cell_und`).

Key risk areas:
- stack output order must be `... loaded_ref remainder_slice` (remainder on top);
- read position must use current `refPos` (not always zero);
- deep-stack values below the top slice must remain untouched;
- opcode boundary around `0xd4/0xd5` (`LDREF` vs `LDREFRTOS`) must decode correctly;
- LDREF has no immediate/stack range-check branch (`rangeChk` should be unreachable).
-/

private def ldrefId : InstrId := { name := "LDREF" }

private def ldrefInstr : Instr := .ldref

private def ldrefRtosInstr : Instr := .ldrefRtos

private def mkLdrefCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldrefInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldrefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdrefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLdref ldrefInstr stack

private def runLdrefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLdref .add (VM.push (intV 212)) stack

private def ldrefSetGasExact : Int :=
  computeExactGasBudget ldrefInstr

private def ldrefSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldrefInstr

private def mkCellWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary bits refs

private def mkSliceWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (mkCellWithBitsAndRefs bits refs)

private def refCell0 : Cell := Cell.empty

private def refCell1 : Cell :=
  mkCellWithBitsAndRefs (natToBits 0b101 3)

private def refCell2 : Cell :=
  mkCellWithBitsAndRefs (natToBits 0xA5 8) #[Cell.empty]

private def refCell3 : Cell :=
  mkCellWithBitsAndRefs (natToBits 0x15 5) #[refCell1, Cell.empty]

private def sliceOneRef : Slice :=
  mkSliceWithBitsAndRefs #[] #[refCell0]

private def sliceTwoRefsBits3 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b101 3) #[refCell1, refCell2]

private def sliceFourRefsBits11 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x5AB 11) #[refCell0, refCell1, refCell2, refCell3]

private def sliceNoRefsEmpty : Slice :=
  mkSliceWithBitsAndRefs #[] #[]

private def sliceNoRefsBits9 : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0x12F 9) #[]

private def sliceShiftedRefBase : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b110011 6) #[refCell0, refCell2, refCell3]

private def sliceShiftedRef : Slice :=
  { sliceShiftedRefBase with refPos := 1 }

private def sliceAllRefsConsumed : Slice :=
  { sliceShiftedRefBase with refPos := sliceShiftedRefBase.cell.refs.size }

private def sliceShiftedBitAndRef : Slice :=
  (mkSliceWithBitsAndRefs (natToBits 0b1110011 7) #[refCell2, refCell1]).advanceBits 2

private def longTailBits18 : BitString := natToBits 0x2B7A1 18

private def sliceLongTailTwoRefs : Slice :=
  mkSliceWithBitsAndRefs longTailBits18 #[refCell3, refCell0]

private def expectedLdrefOut (s : Slice) : Array Value :=
  #[.cell s.cell.refs[s.refPos]!, .slice { s with refPos := s.refPos + 1 }]

private def refCellPool : Array Cell :=
  #[refCell0, refCell1, refCell2, refCell3]

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 0 20
  if width = 0 then
    (#[], rng1)
  else
    let maxVal : Nat := (1 <<< width) - 1
    let (v, rng2) := randNat rng1 0 maxVal
    (natToBits v width, rng2)

private def genRefArray (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut refs : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (idx, rng1) := randNat rng 0 (refCellPool.size - 1)
    refs := refs.push (refCellPool[idx]!)
    rng := rng1
  return (refs, rng)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), rng2)
  else if pick = 2 then
    (.cell refCell2, rng1)
  else if pick = 3 then
    (.builder Builder.empty, rng1)
  else
    (.tuple #[], rng1)

private def pickNonSliceNoise (rng0 : StdGen) : Value × StdGen :=
  pickNoiseValue rng0

private def genLdrefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    (mkLdrefCase "fuzz/ok/top/minimal-one-ref" #[.slice sliceOneRef], rng1)
  else if shape = 1 then
    let (refCount, rng2) := randNat rng1 1 4
    let (refs, rng3) := genRefArray refCount rng2
    let (tail, rng4) := pickTailBits rng3
    (mkLdrefCase s!"fuzz/ok/top/refs-{refCount}/tail-{tail.size}"
      #[.slice (mkSliceWithBitsAndRefs tail refs)], rng4)
  else if shape = 2 then
    let (refCount, rng2) := randNat rng1 1 4
    let (refs, rng3) := genRefArray refCount rng2
    let (tail, rng4) := pickTailBits rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkLdrefCase s!"fuzz/ok/deep/refs-{refCount}/tail-{tail.size}"
      #[noise, .slice (mkSliceWithBitsAndRefs tail refs)], rng5)
  else if shape = 3 then
    (mkLdrefCase "fuzz/ok/top/refs4-boundary" #[.slice sliceFourRefsBits11], rng1)
  else if shape = 4 then
    (mkLdrefCase "fuzz/ok/top/long-tail-two-refs" #[.slice sliceLongTailTwoRefs], rng1)
  else if shape = 5 then
    (mkLdrefCase "fuzz/cellund/no-refs-empty" #[.slice sliceNoRefsEmpty], rng1)
  else if shape = 6 then
    let (tail, rng2) := pickTailBits rng1
    (mkLdrefCase s!"fuzz/cellund/no-refs/tail-{tail.size}"
      #[.slice (mkSliceWithBitsAndRefs tail #[])], rng2)
  else if shape = 7 then
    (mkLdrefCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 8 then
    (mkLdrefCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 9 then
    let (n, rng2) := randNat rng1 0 255
    (mkLdrefCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
  else if shape = 10 then
    (mkLdrefCase "fuzz/type/top-cell" #[.cell refCell3], rng1)
  else if shape = 11 then
    (mkLdrefCase "fuzz/type/top-builder-empty" #[.builder Builder.empty], rng1)
  else if shape = 12 then
    let (noise, rng2) := pickNonSliceNoise rng1
    (mkLdrefCase "fuzz/type/deep-top-not-slice"
      #[.slice sliceOneRef, noise], rng2)
  else if shape = 13 then
    (mkLdrefCase "fuzz/gas/exact"
      #[.slice sliceOneRef]
      #[.pushInt (.num ldrefSetGasExact), .tonEnvOp .setGasLimit, ldrefInstr], rng1)
  else if shape = 14 then
    (mkLdrefCase "fuzz/gas/exact-minus-one"
      #[.slice sliceOneRef]
      #[.pushInt (.num ldrefSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldrefInstr], rng1)
  else
    let (noise, rng2) := pickNoiseValue rng1
    (mkLdrefCase "fuzz/ok/deep/fixed-boundary"
      #[noise, .slice sliceFourRefsBits11], rng2)

def suite : InstrSuite where
  id := ldrefId
  unit := #[
    { name := "unit/direct/success-order-and-remainder"
      run := do
        expectOkStack "ok/minimal-one-ref"
          (runLdrefDirect #[.slice sliceOneRef])
          (expectedLdrefOut sliceOneRef)

        expectOkStack "ok/two-refs-bits3"
          (runLdrefDirect #[.slice sliceTwoRefsBits3])
          (expectedLdrefOut sliceTwoRefsBits3)

        expectOkStack "ok/four-refs-bits11"
          (runLdrefDirect #[.slice sliceFourRefsBits11])
          (expectedLdrefOut sliceFourRefsBits11)

        expectOkStack "ok/long-tail-two-refs"
          (runLdrefDirect #[.slice sliceLongTailTwoRefs])
          (expectedLdrefOut sliceLongTailTwoRefs)

        expectOkStack "ok/shifted-refpos-starts-at-1"
          (runLdrefDirect #[.slice sliceShiftedRef])
          (expectedLdrefOut sliceShiftedRef)

        expectOkStack "ok/shifted-bitpos-preserved"
          (runLdrefDirect #[.slice sliceShiftedBitAndRef])
          (expectedLdrefOut sliceShiftedBitAndRef)

        expectOkStack "ok/deep-stack-preserve-below"
          (runLdrefDirect #[.null, .slice sliceTwoRefsBits3])
          (#[.null] ++ expectedLdrefOut sliceTwoRefsBits3) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdrefDirect #[]) .stkUnd
        expectErr "type/top-null" (runLdrefDirect #[.null]) .typeChk
        expectErr "type/top-int" (runLdrefDirect #[intV 3]) .typeChk
        expectErr "type/top-cell" (runLdrefDirect #[.cell refCell1]) .typeChk
        expectErr "type/top-builder-empty" (runLdrefDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice-null"
          (runLdrefDirect #[.slice sliceOneRef, .null]) .typeChk
        expectErr "type/deep-top-not-slice-builder"
          (runLdrefDirect #[.slice sliceOneRef, .builder Builder.empty]) .typeChk }
    ,
    { name := "unit/direct/cellund-branches"
      run := do
        expectErr "cellund/no-refs-empty"
          (runLdrefDirect #[.slice sliceNoRefsEmpty]) .cellUnd
        expectErr "cellund/no-refs-bits9"
          (runLdrefDirect #[.slice sliceNoRefsBits9]) .cellUnd
        expectErr "cellund/all-refs-consumed"
          (runLdrefDirect #[.slice sliceAllRefsConsumed]) .cellUnd
        let consumedShifted : Slice := { sliceShiftedBitAndRef with refPos := 2 }
        expectErr "cellund/shifted-bitpos-all-refs-consumed"
          (runLdrefDirect #[.slice consumedShifted]) .cellUnd }
    ,
    { name := "unit/direct/rangechk-unreachable-for-ldref"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runLdrefDirect #[.slice sliceOneRef]),
            ("underflow", runLdrefDirect #[]),
            ("type", runLdrefDirect #[.null]),
            ("cellund", runLdrefDirect #[.slice sliceNoRefsEmpty])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for LDREF")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [ldrefInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble ldref failed: {e}")
        if canonicalOnly.bits = natToBits 0xd4 8 then
          pure ()
        else
          throw (IO.userError s!"ldref canonical encode mismatch: got bits {canonicalOnly.bits}")

        let neighborOnly ←
          match assembleCp0 [ldrefRtosInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble ldrefrtos failed: {e}")
        if neighborOnly.bits = natToBits 0xd5 8 then
          pure ()
        else
          throw (IO.userError s!"ldrefrtos encode mismatch: got bits {neighborOnly.bits}")

        let program : Array Instr := #[ldrefInstr, ldrefRtosInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldref-d4" s0 ldrefInstr 8
        let s2 ← expectDecodeStep "decode/ldrefrtos-d5" s1 ldrefRtosInstr 8
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-ldref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdrefDispatchFallback #[.null])
          #[.null, intV 212] }
  ]
  oracle := #[
    mkLdrefCase "ok/minimal-one-ref"
      #[.slice sliceOneRef],
    mkLdrefCase "ok/two-refs-bits3"
      #[.slice sliceTwoRefsBits3],
    mkLdrefCase "ok/four-refs-bits11"
      #[.slice sliceFourRefsBits11],
    mkLdrefCase "ok/long-tail-two-refs"
      #[.slice sliceLongTailTwoRefs],
    mkLdrefCase "ok/refs4-zero-bits"
      #[.slice (mkSliceWithBitsAndRefs #[] #[refCell0, refCell1, refCell2, refCell3])],
    mkLdrefCase "ok/refs1-bits9"
      #[.slice (mkSliceWithBitsAndRefs (natToBits 0x1A2 9) #[refCell2])],
    mkLdrefCase "ok/deep-preserve-null"
      #[.null, .slice sliceOneRef],
    mkLdrefCase "ok/deep-preserve-int"
      #[intV (-7), .slice sliceTwoRefsBits3],
    mkLdrefCase "ok/deep-preserve-cell"
      #[.cell refCell1, .slice sliceFourRefsBits11],
    mkLdrefCase "ok/deep-preserve-builder-empty"
      #[.builder Builder.empty, .slice sliceLongTailTwoRefs],
    mkLdrefCase "ok/deep-preserve-tuple-empty"
      #[.tuple #[], .slice sliceOneRef],
    mkLdrefCase "ok/deep-preserve-two-values"
      #[.builder Builder.empty, .cell Cell.empty, .slice sliceTwoRefsBits3],

    mkLdrefCase "cellund/no-refs-empty"
      #[.slice sliceNoRefsEmpty],
    mkLdrefCase "cellund/no-refs-bits9"
      #[.slice sliceNoRefsBits9],

    mkLdrefCase "underflow/empty" #[],
    mkLdrefCase "type/top-null" #[.null],
    mkLdrefCase "type/top-int" #[intV 42],
    mkLdrefCase "type/top-cell" #[.cell Cell.empty],
    mkLdrefCase "type/top-builder-empty" #[.builder Builder.empty],
    mkLdrefCase "type/top-tuple-empty" #[.tuple #[]],
    mkLdrefCase "type/deep-top-not-slice-null"
      #[.slice sliceOneRef, .null],
    mkLdrefCase "type/deep-top-not-slice-cell"
      #[.slice sliceOneRef, .cell refCell2],
    mkLdrefCase "type/deep-top-not-slice-builder"
      #[.slice sliceOneRef, .builder Builder.empty],

    mkLdrefCase "gas/exact-cost-succeeds"
      #[.slice sliceOneRef]
      #[.pushInt (.num ldrefSetGasExact), .tonEnvOp .setGasLimit, ldrefInstr],
    mkLdrefCase "gas/exact-minus-one-out-of-gas"
      #[.slice sliceOneRef]
      #[.pushInt (.num ldrefSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldrefInstr]
  ]
  fuzz := #[
    { seed := 2026021014
      count := 500
      gen := genLdrefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDREF
