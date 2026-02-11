import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDREFVAR

/-!
PLDREFVAR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/PldRefVar.lean` (`.cellOp .pldRefVar`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.pldRefVar` encodes to `0xd748`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd748` decodes to `.cellOp .pldRefVar`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_preload_ref`, `exec_preload_ref_fixed`, opcode table entries `0xd748`, `0xd74c..0xd74f`).

Branch map covered by this suite:
- `checkUnderflow 2` before any pop;
- index pop via `popNatUpTo 3` (`typeChk` for non-int; `rangeChk` for NaN/negative/>3);
- slice pop/type check only after index checks succeed;
- reference availability split:
  - success pushes preloaded reference cell only (prefetch contract),
  - missing ref throws `cellUnd`;
- opcode/decode boundaries around `0xd748` with nearby family members;
- dispatch fallback for non-`.cellOp .pldRefVar`.
-/

private def pldrefvarId : InstrId := { name := "PLDREFVAR" }

private def pldrefvarInstr : Instr := .cellOp .pldRefVar

private def pldrefvarWord : Nat := 0xd748

private def dispatchSentinel : Int := 941

private def execInstrCellOpPldRefVarOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpPldRefVar op next
  | _ => next

private def mkPldrefvarCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldrefvarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldrefvarId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPldrefvarProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkPldrefvarCase name stack program gasLimits fuel

private def runPldrefvarDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpPldRefVarOnly pldrefvarInstr stack

private def runPldrefvarDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpPldRefVarOnly instr (VM.push (intV dispatchSentinel)) stack

private def pldrefvarSetGasExact : Int :=
  computeExactGasBudget pldrefvarInstr

private def pldrefvarSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pldrefvarInstr

private def refCell0 : Cell := Cell.empty

private def refCell1 : Cell := Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refCell2 : Cell := Cell.mkOrdinary (natToBits 0xA5 8) #[refCell1]

private def refCell3 : Cell := Cell.mkOrdinary (natToBits 0x15 5) #[refCell1, Cell.empty]

private def refCell4 : Cell := Cell.mkOrdinary (natToBits 0x2D5 10) #[refCell2]

private def refPool : Array Cell := #[refCell0, refCell1, refCell2, refCell3, refCell4]

private def mkPatternBits (bitCount : Nat) (phase : Nat := 0) : BitString := Id.run do
  let mut bits : BitString := #[]
  for idx in [0:bitCount] do
    let p := idx + phase
    let bit := (p % 2 == 0) || (p % 5 == 1)
    bits := bits.push bit
  return bits

private def mkFullSlice (bits : BitString := #[]) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkPatternSlice (bitCount : Nat) (phase : Nat := 0) (refs : Array Cell := #[]) : Slice :=
  mkFullSlice (mkPatternBits bitCount phase) refs

private def expectedSuccessStack
    (below : Array Value)
    (source : Slice)
    (idx : Nat) : Array Value :=
  below ++ #[.cell source.cell.refs[source.refPos + idx]!]

private def genRefArray (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut refs : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (idx, rng') := randNat rng 0 (refPool.size - 1)
    refs := refs.push (refPool[idx]!)
    rng := rng'
  return (refs, rng)

private def mkRandomFullSliceWithRefCount (refCount : Nat) (rng0 : StdGen) : Slice × StdGen :=
  let (bitCount, rng1) := randNat rng0 0 96
  let (bits, rng2) := randBitString bitCount rng1
  let (refs, rng3) := genRefArray refCount rng2
  (mkFullSlice bits refs, rng3)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 255
    (intV (Int.ofNat n - 128), rng2)
  else
    (.cell refCell3, rng1)

private def pickBadIdxValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let bad : Value :=
    if pick = 0 then
      .null
    else if pick = 1 then
      .cell refCell4
    else
      .slice (mkPatternSlice 4 1 #[refCell1])
  (bad, rng1)

private def pickBadSliceValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let bad : Value :=
    if pick = 0 then
      .null
    else if pick = 1 then
      intV 17
    else
      .cell refCell2
  (bad, rng1)

private def genPldrefvarFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let (idx, rng2) := randNat rng1 0 3
    let (slice, rng3) := mkRandomFullSliceWithRefCount (idx + 1) rng2
    (mkPldrefvarCase s!"fuzz/ok/min-refs/idx-{idx}"
      #[.slice slice, intV (Int.ofNat idx)], rng3)
  else if shape = 1 then
    let (idx, rng2) := randNat rng1 0 3
    let minRefs := idx + 1
    let (extra, rng3) := randNat rng2 0 (4 - minRefs)
    let refCount := minRefs + extra
    let (slice, rng4) := mkRandomFullSliceWithRefCount refCount rng3
    (mkPldrefvarCase s!"fuzz/ok/extra-refs/idx-{idx}/refs-{refCount}"
      #[.slice slice, intV (Int.ofNat idx)], rng4)
  else if shape = 2 then
    let (idx, rng2) := randNat rng1 0 3
    let (slice, rng3) := mkRandomFullSliceWithRefCount (idx + 1) rng2
    let (noise, rng4) := pickNoiseValue rng3
    (mkPldrefvarCase s!"fuzz/ok/deep-stack/idx-{idx}"
      #[noise, .slice slice, intV (Int.ofNat idx)], rng4)
  else if shape = 3 then
    let (slice, rng2) := mkRandomFullSliceWithRefCount 4 rng1
    (mkPldrefvarCase "fuzz/ok/boundary-idx3-refs4"
      #[.slice slice, intV 3], rng2)
  else if shape = 4 then
    let (refCount, rng2) := randNat rng1 1 4
    let (slice, rng3) := mkRandomFullSliceWithRefCount refCount rng2
    (mkPldrefvarCase s!"fuzz/ok/idx0/refs-{refCount}"
      #[.slice slice, intV 0], rng3)
  else if shape = 5 then
    let (bitCount, rng2) := randNat rng1 0 96
    let (bits, rng3) := randBitString bitCount rng2
    (mkPldrefvarCase s!"fuzz/cellund/idx0-no-refs/bits-{bitCount}"
      #[.slice (mkFullSlice bits #[]), intV 0], rng3)
  else if shape = 6 then
    let (slice, rng2) := mkRandomFullSliceWithRefCount 1 rng1
    (mkPldrefvarCase "fuzz/cellund/idx1-one-ref"
      #[.slice slice, intV 1], rng2)
  else if shape = 7 then
    let (slice, rng2) := mkRandomFullSliceWithRefCount 2 rng1
    (mkPldrefvarCase "fuzz/cellund/idx2-two-refs"
      #[.slice slice, intV 2], rng2)
  else if shape = 8 then
    let (slice, rng2) := mkRandomFullSliceWithRefCount 3 rng1
    (mkPldrefvarCase "fuzz/cellund/idx3-three-refs"
      #[.slice slice, intV 3], rng2)
  else if shape = 9 then
    (mkPldrefvarCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 10 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      let (slice, rng3) := mkRandomFullSliceWithRefCount 1 rng2
      (mkPldrefvarCase "fuzz/underflow/one-item-slice" #[.slice slice], rng3)
    else
      (mkPldrefvarCase "fuzz/underflow/one-item-int" #[intV 0], rng2)
  else if shape = 11 then
    let (slice, rng2) := mkRandomFullSliceWithRefCount 4 rng1
    let (badIdx, rng3) := pickBadIdxValue rng2
    (mkPldrefvarCase "fuzz/type/idx-not-int"
      #[.slice slice, badIdx], rng3)
  else if shape = 12 then
    let (slice, rng2) := mkRandomFullSliceWithRefCount 4 rng1
    (mkPldrefvarCase "fuzz/range/idx-negative"
      #[.slice slice, intV (-1)], rng2)
  else if shape = 13 then
    let (slice, rng2) := mkRandomFullSliceWithRefCount 4 rng1
    let (delta, rng3) := randNat rng2 1 4096
    let tooLarge : Int := Int.ofNat (3 + delta)
    (mkPldrefvarCase s!"fuzz/range/idx-too-large-{tooLarge}"
      #[.slice slice, intV tooLarge], rng3)
  else if shape = 14 then
    let (refCount, rng2) := randNat rng1 0 4
    let (slice, rng3) := mkRandomFullSliceWithRefCount refCount rng2
    (mkPldrefvarProgramCase "fuzz/range/idx-nan-via-program"
      #[.slice slice]
      #[.pushInt .nan, pldrefvarInstr], rng3)
  else if shape = 15 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    (mkPldrefvarCase "fuzz/type/slice-not-slice-after-valid-idx"
      #[badSlice, intV 0], rng2)
  else if shape = 16 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    (mkPldrefvarCase "fuzz/error-order/range-before-slice-type"
      #[badSlice, intV 9], rng2)
  else if shape = 17 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    let (badIdx, rng3) := pickBadIdxValue rng2
    (mkPldrefvarCase "fuzz/error-order/idx-type-before-slice-type"
      #[badSlice, badIdx], rng3)
  else if shape = 18 then
    (mkPldrefvarCase "fuzz/gas/exact"
      #[.slice (mkPatternSlice 12 0 #[refCell1]), intV 0]
      #[.pushInt (.num pldrefvarSetGasExact), .tonEnvOp .setGasLimit, pldrefvarInstr], rng1)
  else
    (mkPldrefvarCase "fuzz/gas/exact-minus-one"
      #[.slice (mkPatternSlice 12 1 #[refCell1]), intV 0]
      #[.pushInt (.num pldrefvarSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldrefvarInstr], rng1)

private def oracleSliceRefs0Bits0 : Slice := mkPatternSlice 0 0 #[]

private def oracleSliceRefs0Bits7 : Slice := mkPatternSlice 7 1 #[]

private def oracleSliceRefs1Bits5 : Slice := mkPatternSlice 5 0 #[refCell1]

private def oracleSliceRefs1Bits13 : Slice := mkPatternSlice 13 1 #[refCell2]

private def oracleSliceRefs2Bits9 : Slice := mkPatternSlice 9 0 #[refCell1, refCell2]

private def oracleSliceRefs2Bits17 : Slice := mkPatternSlice 17 2 #[refCell2, refCell3]

private def oracleSliceRefs3Bits11 : Slice := mkPatternSlice 11 0 #[refCell1, refCell2, refCell3]

private def oracleSliceRefs3Bits24 : Slice := mkPatternSlice 24 2 #[refCell4, refCell1, refCell2]

private def oracleSliceRefs4Bits0 : Slice := mkPatternSlice 0 0 #[refCell0, refCell1, refCell2, refCell3]

private def oracleSliceRefs4Bits19 : Slice := mkPatternSlice 19 1 #[refCell1, refCell2, refCell3, refCell4]

private def oracleSliceRefs4Bits33 : Slice := mkPatternSlice 33 2 #[refCell4, refCell3, refCell2, refCell1]

def suite : InstrSuite where
  id := pldrefvarId
  unit := #[
    { name := "unit/direct/success-selects-reference-and-preserves-below"
      run := do
        let source : Slice := mkPatternSlice 21 0 #[refCell1, refCell2, refCell3, refCell4]
        for idx in [0:4] do
          expectOkStack s!"ok/idx-{idx}"
            (runPldrefvarDirect #[.slice source, intV (Int.ofNat idx)])
            (expectedSuccessStack #[] source idx)

        let zeroBits : Slice := mkPatternSlice 0 0 #[refCell0, refCell1, refCell2, refCell3]
        expectOkStack "ok/zero-bits-idx3"
          (runPldrefvarDirect #[.slice zeroBits, intV 3])
          (expectedSuccessStack #[] zeroBits 3)

        let deepBelow : Array Value := #[.null, intV 77, .cell refCell0]
        expectOkStack "ok/deep-stack-preserved"
          (runPldrefvarDirect (deepBelow ++ #[.slice source, intV 2]))
          (expectedSuccessStack deepBelow source 2)

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 37 1) #[refCell0, refCell1, refCell2, refCell3]
        let partialSlice : Slice := { cell := partialCell, bitPos := 9, refPos := 1 }
        expectOkStack "ok/uses-refpos-cursor"
          (runPldrefvarDirect #[.slice partialSlice, intV 2])
          (expectedSuccessStack #[] partialSlice 2) }
    ,
    { name := "unit/direct/cellund-when-reference-missing"
      run := do
        expectErr "cellund/idx0-no-refs"
          (runPldrefvarDirect #[.slice (mkPatternSlice 9 0 #[]), intV 0]) .cellUnd
        expectErr "cellund/idx1-one-ref"
          (runPldrefvarDirect #[.slice (mkPatternSlice 9 0 #[refCell1]), intV 1]) .cellUnd
        expectErr "cellund/idx2-two-refs"
          (runPldrefvarDirect #[.slice (mkPatternSlice 9 0 #[refCell1, refCell2]), intV 2]) .cellUnd
        expectErr "cellund/idx3-three-refs"
          (runPldrefvarDirect #[.slice (mkPatternSlice 9 0 #[refCell1, refCell2, refCell3]), intV 3]) .cellUnd

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 16 0) #[refCell0, refCell1, refCell2, refCell3]
        let nearTail : Slice := { cell := partialCell, bitPos := 0, refPos := 3 }
        expectErr "cellund/partial-cursor-near-tail"
          (runPldrefvarDirect #[.slice nearTail, intV 1]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-error-order"
      run := do
        expectErr "underflow/empty" (runPldrefvarDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runPldrefvarDirect #[.slice oracleSliceRefs1Bits5]) .stkUnd
        expectErr "underflow/one-item-int"
          (runPldrefvarDirect #[intV 0]) .stkUnd
        expectErr "underflow/one-item-null"
          (runPldrefvarDirect #[.null]) .stkUnd

        expectErr "type/idx-top-null"
          (runPldrefvarDirect #[.slice oracleSliceRefs4Bits19, .null]) .typeChk
        expectErr "type/idx-top-cell"
          (runPldrefvarDirect #[.slice oracleSliceRefs4Bits19, .cell refCell2]) .typeChk
        expectErr "type/idx-top-slice"
          (runPldrefvarDirect #[.slice oracleSliceRefs4Bits19, .slice oracleSliceRefs1Bits5]) .typeChk

        expectErr "range/idx-negative"
          (runPldrefvarDirect #[.slice oracleSliceRefs4Bits19, intV (-1)]) .rangeChk
        expectErr "range/idx-too-large-4"
          (runPldrefvarDirect #[.slice oracleSliceRefs4Bits19, intV 4]) .rangeChk
        expectErr "range/idx-too-large-4096"
          (runPldrefvarDirect #[.slice oracleSliceRefs4Bits19, intV 4096]) .rangeChk
        expectErr "range/idx-nan"
          (runPldrefvarDirect #[.slice oracleSliceRefs4Bits19, .int .nan]) .rangeChk

        expectErr "type/slice-not-slice-after-valid-idx"
          (runPldrefvarDirect #[.null, intV 0]) .typeChk
        expectErr "error-order/range-before-slice-type"
          (runPldrefvarDirect #[.null, intV 9]) .rangeChk
        expectErr "error-order/idx-type-before-slice-type"
          (runPldrefvarDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-and-assembler-path"
      run := do
        let program : Array Instr := #[
          .cellOp (.schkBitRefs true),
          pldrefvarInstr,
          .sbits,
          .srefs,
          .sbitrefs,
          .pldRefIdx 0,
          .pldRefIdx 3,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/schkbitrefsq-neighbor" s0 (.cellOp (.schkBitRefs true)) 16
        let s2 ← expectDecodeStep "decode/pldrefvar" s1 pldrefvarInstr 16
        let s3 ← expectDecodeStep "decode/sbits-neighbor" s2 .sbits 16
        let s4 ← expectDecodeStep "decode/srefs-neighbor" s3 .srefs 16
        let s5 ← expectDecodeStep "decode/sbitrefs-neighbor" s4 .sbitrefs 16
        let s6 ← expectDecodeStep "decode/pldrefidx-0-neighbor" s5 (.pldRefIdx 0) 16
        let s7 ← expectDecodeStep "decode/pldrefidx-3-neighbor" s6 (.pldRefIdx 3) 16
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [pldrefvarInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits pldrefvarWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldrefvar: expected 0xd748 encoding, got bit-length {singleCode.bits.size}")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd747 16 ++ natToBits pldrefvarWord 16 ++ natToBits 0xd749 16 ++ natToBits 0xd74a 16 ++
            natToBits 0xd74b 16 ++ natToBits 0xd74c 16 ++ natToBits 0xd74f 16 ++ addCode.bits
        let raw := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-0xd747" raw (.cellOp (.schkBitRefs true)) 16
        let r2 ← expectDecodeStep "decode/raw-0xd748-pldrefvar" r1 pldrefvarInstr 16
        let r3 ← expectDecodeStep "decode/raw-0xd749-sbits" r2 .sbits 16
        let r4 ← expectDecodeStep "decode/raw-0xd74a-srefs" r3 .srefs 16
        let r5 ← expectDecodeStep "decode/raw-0xd74b-sbitrefs" r4 .sbitrefs 16
        let r6 ← expectDecodeStep "decode/raw-0xd74c-pldrefidx0" r5 (.pldRefIdx 0) 16
        let r7 ← expectDecodeStep "decode/raw-0xd74f-pldrefidx3" r6 (.pldRefIdx 3) 16
        let r8 ← expectDecodeStep "decode/raw-tail-add" r7 .add 8
        if r8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r8.bitsRemaining} bits remaining")

        match assembleCp0 [.pldRefIdx 4] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/pldrefidx-4: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldrefidx-4: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-pldrefvar-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runPldrefvarDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-schkrefs"
          (runPldrefvarDispatchFallback (.cellOp (.schkRefs false)) #[intV (-7)])
          #[intV (-7), intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-pldrefidx"
          (runPldrefvarDispatchFallback (.pldRefIdx 1) #[.cell refCell1])
          #[.cell refCell1, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldrefvarCase "ok/idx0-single-ref-bits5" #[.slice oracleSliceRefs1Bits5, intV 0],
    mkPldrefvarCase "ok/idx0-single-ref-bits13" #[.slice oracleSliceRefs1Bits13, intV 0],
    mkPldrefvarCase "ok/idx0-four-refs-bits19" #[.slice oracleSliceRefs4Bits19, intV 0],
    mkPldrefvarCase "ok/idx1-two-refs-bits9" #[.slice oracleSliceRefs2Bits9, intV 1],
    mkPldrefvarCase "ok/idx1-four-refs-bits33" #[.slice oracleSliceRefs4Bits33, intV 1],
    mkPldrefvarCase "ok/idx2-three-refs-bits11" #[.slice oracleSliceRefs3Bits11, intV 2],
    mkPldrefvarCase "ok/idx2-four-refs-bits19" #[.slice oracleSliceRefs4Bits19, intV 2],
    mkPldrefvarCase "ok/idx3-four-refs-bits0" #[.slice oracleSliceRefs4Bits0, intV 3],
    mkPldrefvarCase "ok/idx3-four-refs-bits33" #[.slice oracleSliceRefs4Bits33, intV 3],
    mkPldrefvarCase "ok/idx0-with-zero-bits-and-refs" #[.slice oracleSliceRefs4Bits0, intV 0],
    mkPldrefvarCase "ok/deep-stack-null-below"
      #[.null, .slice oracleSliceRefs4Bits19, intV 3],
    mkPldrefvarCase "ok/deep-stack-two-below"
      #[intV (-5), .cell refCell0, .slice oracleSliceRefs3Bits24, intV 2],
    mkPldrefvarCase "ok/deep-stack-cell-below"
      #[.cell refCell4, .slice oracleSliceRefs2Bits17, intV 1],

    mkPldrefvarCase "cellund/idx0-no-refs-bits0" #[.slice oracleSliceRefs0Bits0, intV 0],
    mkPldrefvarCase "cellund/idx0-no-refs-bits7" #[.slice oracleSliceRefs0Bits7, intV 0],
    mkPldrefvarCase "cellund/idx1-one-ref" #[.slice oracleSliceRefs1Bits13, intV 1],
    mkPldrefvarCase "cellund/idx2-two-refs" #[.slice oracleSliceRefs2Bits9, intV 2],
    mkPldrefvarCase "cellund/idx3-three-refs" #[.slice oracleSliceRefs3Bits11, intV 3],
    mkPldrefvarCase "cellund/idx3-no-refs" #[.slice oracleSliceRefs0Bits7, intV 3],

    mkPldrefvarCase "range/idx-negative" #[.slice oracleSliceRefs4Bits19, intV (-1)],
    mkPldrefvarCase "range/idx-too-large-4" #[.slice oracleSliceRefs4Bits19, intV 4],
    mkPldrefvarCase "range/idx-too-large-4096" #[.slice oracleSliceRefs4Bits19, intV 4096],
    mkPldrefvarProgramCase "range/idx-nan-via-program"
      #[.slice oracleSliceRefs4Bits19]
      #[.pushInt .nan, pldrefvarInstr],

    mkPldrefvarCase "underflow/empty" #[],
    mkPldrefvarCase "underflow/one-item-slice" #[.slice oracleSliceRefs1Bits5],
    mkPldrefvarCase "underflow/one-item-int" #[intV 0],

    mkPldrefvarCase "type/idx-top-null" #[.slice oracleSliceRefs4Bits19, .null],
    mkPldrefvarCase "type/idx-top-cell" #[.slice oracleSliceRefs4Bits19, .cell refCell2],
    mkPldrefvarCase "type/slice-not-slice-after-valid-idx" #[.null, intV 0],
    mkPldrefvarCase "error-order/range-before-slice-type" #[.null, intV 9],
    mkPldrefvarCase "error-order/idx-type-before-slice-type" #[.null, .null],

    mkPldrefvarCase "gas/exact-cost-succeeds"
      #[.slice oracleSliceRefs4Bits19, intV 3]
      #[.pushInt (.num pldrefvarSetGasExact), .tonEnvOp .setGasLimit, pldrefvarInstr],
    mkPldrefvarCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSliceRefs4Bits19, intV 3]
      #[.pushInt (.num pldrefvarSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldrefvarInstr]
  ]
  fuzz := #[
    { seed := 2026021109
      count := 320
      gen := genPldrefvarFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDREFVAR
