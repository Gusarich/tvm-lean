import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCHKBITREFSQ

/-
SCHKBITREFSQ branch-mapping notes:
- Lean semantics:
  - `TvmLean/Semantics/Exec/CellOp/SchkBitRefs.lean` (`.schkBitRefs true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.schkBitRefs true` encodes to `0xd747`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd747` decodes to `.cellOp (.schkBitRefs true)`)

Quiet `SCHKBITREFSQ` path branches exercised in this suite:
- underflow check (`checkUnderflow 3`);
- pop order: `refs` (type/range `0..4`) -> `bits` (type/range `0..1023`) -> `slice` (type);
- capacity predicate: `s.haveBits bits && s.haveRefs refs`;
- quiet status push: `-1` on fit, `0` on failure.
-/

private def schkBitRefsQId : InstrId := { name := "SCHKBITREFSQ" }

private def schkBitRefsQInstr : Instr :=
  .cellOp (.schkBitRefs true)

private def schkBitRefsInstr : Instr :=
  .cellOp (.schkBitRefs false)

private def schkBitsQInstr : Instr :=
  .cellOp (.schkBits true)

private def schkRefsQInstr : Instr :=
  .cellOp (.schkRefs true)

private def pldRefVarInstr : Instr :=
  .cellOp .pldRefVar

private def schkBitsWord : Nat := 0xd741
private def schkRefsWord : Nat := 0xd742
private def schkBitRefsWord : Nat := 0xd743
private def schkBitsQWord : Nat := 0xd745
private def schkRefsQWord : Nat := 0xd746
private def schkBitRefsQWord : Nat := 0xd747
private def pldRefVarWord : Nat := 0xd748

private def execCellOpSchkBitRefsInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpSchkBitRefs op next
  | _ => next

private def mkSchkBitRefsQCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[schkBitRefsQInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkBitRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSchkBitRefsQProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkBitRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSchkBitRefsQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpSchkBitRefsInstr schkBitRefsQInstr stack

private def dispatchSentinel : Int := 55111

private def runSchkBitRefsQDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpSchkBitRefsInstr instr (VM.push (intV dispatchSentinel)) stack

private def schkBitRefsQSetGasExact : Int :=
  computeExactGasBudget schkBitRefsQInstr

private def schkBitRefsQSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne schkBitRefsQInstr

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 2 2) #[]

private def refCellC : Cell :=
  Cell.mkOrdinary (natToBits 0xA5 8) #[]

private def refCellD : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[Cell.empty]

private def refsByCount : Nat → Array Cell
  | 0 => #[]
  | 1 => #[refCellA]
  | 2 => #[refCellA, refCellB]
  | 3 => #[refCellA, refCellB, refCellC]
  | _ => #[refCellA, refCellB, refCellC, refCellD]

private def mkFullSliceBitsRefs (bits refs : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stripeBits bits phase) (refsByCount refs))

private def mkOffsetSlice
    (totalBits totalRefs bitPos refPos : Nat)
    (phase : Nat := 0) : Slice :=
  { cell := Cell.mkOrdinary (stripeBits totalBits phase) (refsByCount totalRefs)
    bitPos := bitPos
    refPos := refPos }

private def mkSchkStack
    (s : Slice)
    (bits refs : Int)
    (below : Array Value := #[]) : Array Value :=
  below ++ #[.slice s, intV bits, intV refs]

private def mkSchkStackNat
    (s : Slice)
    (bits refs : Nat)
    (below : Array Value := #[]) : Array Value :=
  mkSchkStack s (Int.ofNat bits) (Int.ofNat refs) below

private def oracleNoiseSliceA : Slice :=
  mkFullSliceBitsRefs 5 0 0

private def oracleNoiseSliceB : Slice :=
  mkFullSliceBitsRefs 9 1 1

private def mkSliceProgramBitsRefs
    (sliceBits sliceRefs : Nat) : Array Instr :=
  #[.newc]
    ++ (if sliceBits = 0 then #[] else #[.pushInt (.num (Int.ofNat sliceBits)), .stZeroes])
    ++ appendRefsToTopBuilder sliceRefs
    ++ #[.endc, .ctos]

private def mkSchkBitRefsQProgram
    (sliceBits sliceRefs needBits needRefs : Nat) : Array Instr :=
  mkSliceProgramBitsRefs sliceBits sliceRefs
    ++ #[.pushInt (.num (Int.ofNat needBits)), .pushInt (.num (Int.ofNat needRefs)), schkBitRefsQInstr]

private def schkProgramRefsNan : Array Instr :=
  #[.newc, .endc, .ctos, .pushInt (.num 0), .pushInt .nan, schkBitRefsQInstr]

private def schkProgramBitsNan : Array Instr :=
  #[.newc, .endc, .ctos, .pushInt .nan, .pushInt (.num 0), schkBitRefsQInstr]

private def needBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 767, 1022, 1023]

private def sliceBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 767, 900, 1022, 1023]

private def sliceBitsNonFullPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 767, 900, 1022]

private def sliceRefsPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def sliceRefsNonFullPool : Array Nat :=
  #[0, 1, 2, 3]

private def pickFromNatPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNeedBitsWithin (rng : StdGen) (sliceBits : Nat) : Nat × StdGen :=
  if sliceBits = 0 then
    (0, rng)
  else
    let (mode, rng1) := randNat rng 0 4
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (sliceBits, rng1)
    else if mode = 2 then
      (sliceBits - 1, rng1)
    else if mode = 3 then
      (Nat.min 1 sliceBits, rng1)
    else
      randNat rng1 0 sliceBits

private def pickNeedRefsWithin (rng : StdGen) (sliceRefs : Nat) : Nat × StdGen :=
  if sliceRefs = 0 then
    (0, rng)
  else
    let (mode, rng1) := randNat rng 0 4
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (sliceRefs, rng1)
    else if mode = 2 then
      (sliceRefs - 1, rng1)
    else if mode = 3 then
      (Nat.min 1 sliceRefs, rng1)
    else
      randNat rng1 0 sliceRefs

private def pickNeedBitsOverflow (rng : StdGen) (sliceBits : Nat) : Nat × StdGen :=
  let minNeed : Nat := sliceBits + 1
  let maxNeed : Nat := 1023
  if minNeed >= maxNeed then
    (minNeed, rng)
  else
    let (mode, rng1) := randNat rng 0 2
    if mode = 0 then
      (minNeed, rng1)
    else if mode = 1 then
      (maxNeed, rng1)
    else
      randNat rng1 minNeed maxNeed

private def pickNeedRefsOverflow (rng : StdGen) (sliceRefs : Nat) : Nat × StdGen :=
  let minNeed : Nat := sliceRefs + 1
  let maxNeed : Nat := 4
  if minNeed >= maxNeed then
    (minNeed, rng)
  else
    let (mode, rng1) := randNat rng 0 2
    if mode = 0 then
      (minNeed, rng1)
    else if mode = 1 then
      (maxNeed, rng1)
    else
      randNat rng1 minNeed maxNeed

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 19
    else if pick = 2 then .cell refCellA
    else if pick = 3 then .slice oracleNoiseSliceA
    else .slice oracleNoiseSliceB
  (v, rng1)

private def genSchkBitRefsQFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  if shape = 0 then
    let (sliceBits, rng2) := pickFromNatPool rng1 sliceBitsPool
    let (sliceRefs, rng3) := pickFromNatPool rng2 sliceRefsPool
    let (needBits, rng4) := pickNeedBitsWithin rng3 sliceBits
    let (needRefs, rng5) := pickNeedRefsWithin rng4 sliceRefs
    (mkSchkBitRefsQCase s!"fuzz/ok/direct/b{sliceBits}/r{sliceRefs}/nb{needBits}/nr{needRefs}"
      (mkSchkStackNat (mkFullSliceBitsRefs sliceBits sliceRefs) needBits needRefs), rng5)
  else if shape = 1 then
    let (sliceBits, rng2) := pickFromNatPool rng1 sliceBitsPool
    let (sliceRefs, rng3) := pickFromNatPool rng2 sliceRefsPool
    let (needBits, rng4) := pickNeedBitsWithin rng3 sliceBits
    let (needRefs, rng5) := pickNeedRefsWithin rng4 sliceRefs
    let (noise, rng6) := pickNoiseValue rng5
    (mkSchkBitRefsQCase s!"fuzz/ok/direct/noise/b{sliceBits}/r{sliceRefs}/nb{needBits}/nr{needRefs}"
      (mkSchkStackNat (mkFullSliceBitsRefs sliceBits sliceRefs) needBits needRefs #[noise]), rng6)
  else if shape = 2 then
    let (sliceBits, rng2) := pickFromNatPool rng1 sliceBitsNonFullPool
    let (sliceRefs, rng3) := pickFromNatPool rng2 sliceRefsPool
    let (needBits, rng4) := pickNeedBitsOverflow rng3 sliceBits
    let (needRefs, rng5) := pickNeedRefsWithin rng4 sliceRefs
    (mkSchkBitRefsQCase s!"fuzz/fail/direct-bits/b{sliceBits}/r{sliceRefs}/nb{needBits}/nr{needRefs}"
      (mkSchkStackNat (mkFullSliceBitsRefs sliceBits sliceRefs) needBits needRefs), rng5)
  else if shape = 3 then
    let (sliceBits, rng2) := pickFromNatPool rng1 sliceBitsPool
    let (sliceRefs, rng3) := pickFromNatPool rng2 sliceRefsNonFullPool
    let (needBits, rng4) := pickNeedBitsWithin rng3 sliceBits
    let (needRefs, rng5) := pickNeedRefsOverflow rng4 sliceRefs
    (mkSchkBitRefsQCase s!"fuzz/fail/direct-refs/b{sliceBits}/r{sliceRefs}/nb{needBits}/nr{needRefs}"
      (mkSchkStackNat (mkFullSliceBitsRefs sliceBits sliceRefs) needBits needRefs), rng5)
  else if shape = 4 then
    let (sliceBits, rng2) := pickFromNatPool rng1 sliceBitsNonFullPool
    let (sliceRefs, rng3) := pickFromNatPool rng2 sliceRefsNonFullPool
    let (needBits, rng4) := pickNeedBitsOverflow rng3 sliceBits
    let (needRefs, rng5) := pickNeedRefsOverflow rng4 sliceRefs
    let (noise, rng6) := pickNoiseValue rng5
    (mkSchkBitRefsQCase s!"fuzz/fail/direct-both/b{sliceBits}/r{sliceRefs}/nb{needBits}/nr{needRefs}"
      (mkSchkStackNat (mkFullSliceBitsRefs sliceBits sliceRefs) needBits needRefs #[noise]), rng6)
  else if shape = 5 then
    (mkSchkBitRefsQCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkSchkBitRefsQCase "fuzz/underflow/two-items"
      #[.slice (mkFullSliceBitsRefs 1 0), intV 0], rng1)
  else if shape = 7 then
    (mkSchkBitRefsQCase "fuzz/type/refs-top-not-int"
      #[.slice (mkFullSliceBitsRefs 0 0), intV 0, .null], rng1)
  else if shape = 8 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    (mkSchkBitRefsQCase s!"fuzz/range/refs-negative/b{needBits}"
      #[.slice (mkFullSliceBitsRefs 0 0), intV (Int.ofNat needBits), intV (-1)], rng2)
  else if shape = 9 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    (mkSchkBitRefsQCase s!"fuzz/range/refs-gt4/b{needBits}"
      #[.slice (mkFullSliceBitsRefs 0 0), intV (Int.ofNat needBits), intV 5], rng2)
  else if shape = 10 then
    (mkSchkBitRefsQCase "fuzz/type/bits-not-int-after-refs"
      #[.slice (mkFullSliceBitsRefs 0 0), .null, intV 0], rng1)
  else if shape = 11 then
    (mkSchkBitRefsQCase "fuzz/range/bits-gt1023"
      #[.slice (mkFullSliceBitsRefs 0 0), intV 1024, intV 0], rng1)
  else if shape = 12 then
    (mkSchkBitRefsQCase "fuzz/type/slice-not-slice"
      #[.null, intV 0, intV 0], rng1)
  else if shape = 13 then
    let (sliceBits, rng2) := pickFromNatPool rng1 sliceBitsPool
    let (sliceRefs, rng3) := pickFromNatPool rng2 sliceRefsPool
    let (needBits, rng4) := pickNeedBitsWithin rng3 sliceBits
    let (needRefs, rng5) := pickNeedRefsWithin rng4 sliceRefs
    let (noise, rng6) := pickNoiseValue rng5
    (mkSchkBitRefsQProgramCase
      s!"fuzz/ok/program/b{sliceBits}/r{sliceRefs}/nb{needBits}/nr{needRefs}"
      #[noise]
      (mkSchkBitRefsQProgram sliceBits sliceRefs needBits needRefs), rng6)
  else if shape = 14 then
    let (sliceBits, rng2) := pickFromNatPool rng1 sliceBitsNonFullPool
    let (sliceRefs, rng3) := pickFromNatPool rng2 sliceRefsNonFullPool
    let (needBits, rng4) := pickNeedBitsOverflow rng3 sliceBits
    let (needRefs, rng5) := pickNeedRefsOverflow rng4 sliceRefs
    (mkSchkBitRefsQProgramCase
      s!"fuzz/fail/program/b{sliceBits}/r{sliceRefs}/nb{needBits}/nr{needRefs}"
      #[]
      (mkSchkBitRefsQProgram sliceBits sliceRefs needBits needRefs), rng5)
  else if shape = 15 then
    let (mode, rng2) := randNat rng1 0 1
    if mode = 0 then
      (mkSchkBitRefsQProgramCase "fuzz/range/program-refs-nan" #[] schkProgramRefsNan, rng2)
    else
      (mkSchkBitRefsQProgramCase "fuzz/range/program-bits-nan" #[] schkProgramBitsNan, rng2)
  else
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    let (needRefs, rng3) := randNat rng2 0 4
    let (mode, rng4) := randNat rng3 0 1
    if mode = 0 then
      (mkSchkBitRefsQCase "fuzz/gas/exact"
        (mkSchkStackNat (mkFullSliceBitsRefs 0 0) needBits needRefs)
        #[.pushInt (.num schkBitRefsQSetGasExact), .tonEnvOp .setGasLimit, schkBitRefsQInstr], rng4)
    else
      (mkSchkBitRefsQCase "fuzz/gas/exact-minus-one"
        (mkSchkStackNat (mkFullSliceBitsRefs 0 0) needBits needRefs)
        #[.pushInt (.num schkBitRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkBitRefsQInstr], rng4)

def suite : InstrSuite where
  id := schkBitRefsQId
  unit := #[
    { name := "unit/direct/success-status-and-offset-boundaries"
      run := do
        expectOkStack "ok/empty-plus-0-0"
          (runSchkBitRefsQDirect (mkSchkStackNat (mkFullSliceBitsRefs 0 0) 0 0))
          #[intV (-1)]

        expectOkStack "ok/full-plus-1023-4"
          (runSchkBitRefsQDirect (mkSchkStackNat (mkFullSliceBitsRefs 1023 4) 1023 4))
          #[intV (-1)]

        let slicePartial := mkOffsetSlice 30 3 11 1
        expectOkStack "ok/offset-exact-fit"
          (runSchkBitRefsQDirect (mkSchkStackNat slicePartial 19 2))
          #[intV (-1)]

        let deepPartial := mkOffsetSlice 64 4 8 2
        expectOkStack "ok/deep-stack-preserve-below"
          (runSchkBitRefsQDirect
            (mkSchkStackNat deepPartial 56 2 #[.slice oracleNoiseSliceA, intV 77]))
          #[.slice oracleNoiseSliceA, intV 77, intV (-1)] }
    ,
    { name := "unit/direct/quiet-fail-returns-zero"
      run := do
        let slicePartial := mkOffsetSlice 30 3 11 1
        expectOkStack "fail/offset-bits-overflow"
          (runSchkBitRefsQDirect (mkSchkStackNat slicePartial 20 2))
          #[intV 0]
        expectOkStack "fail/offset-refs-overflow"
          (runSchkBitRefsQDirect (mkSchkStackNat slicePartial 19 3))
          #[intV 0]
        expectOkStack "fail/offset-bits-and-refs-overflow-with-noise"
          (runSchkBitRefsQDirect
            (mkSchkStackNat slicePartial 20 3 #[.slice oracleNoiseSliceB, .cell refCellC]))
          #[.slice oracleNoiseSliceB, .cell refCellC, intV 0] }
    ,
    { name := "unit/direct/underflow-range-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runSchkBitRefsQDirect #[]) .stkUnd
        expectErr "underflow/one-item"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0)]) .stkUnd
        expectErr "underflow/two-items"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), intV 0]) .stkUnd

        expectErr "type/refs-top-not-int"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), intV 0, .null]) .typeChk
        expectErr "range/refs-negative"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), intV 0, intV (-1)]) .rangeChk
        expectErr "range/refs-gt4"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), intV 0, intV 5]) .rangeChk
        expectErr "range/refs-nan"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), intV 0, .int .nan]) .rangeChk

        expectErr "type/bits-not-int-after-refs"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), .null, intV 0]) .typeChk
        expectErr "range/bits-negative"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), intV (-1), intV 0]) .rangeChk
        expectErr "range/bits-gt1023"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-nan"
          (runSchkBitRefsQDirect #[.slice (mkFullSliceBitsRefs 0 0), .int .nan, intV 0]) .rangeChk

        expectErr "type/slice-not-slice"
          (runSchkBitRefsQDirect #[.null, intV 0, intV 0]) .typeChk

        expectErr "order/refs-before-bits-and-slice"
          (runSchkBitRefsQDirect #[.null, .null, intV 5]) .rangeChk
        expectErr "order/bits-before-slice"
          (runSchkBitRefsQDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "order/bits-type-before-slice-type"
          (runSchkBitRefsQDirect #[.null, .null, intV 0]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-and-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[schkBitRefsInstr, schkBitRefsQInstr, schkBitsQInstr, schkRefsQInstr, pldRefVarInstr, .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-schkbitrefs" s0 schkBitRefsInstr 16
        let s2 ← expectDecodeStep "decode/asm-schkbitrefsq" s1 schkBitRefsQInstr 16
        let s3 ← expectDecodeStep "decode/asm-schkbitsq" s2 schkBitsQInstr 16
        let s4 ← expectDecodeStep "decode/asm-schkrefsq" s3 schkRefsQInstr 16
        let s5 ← expectDecodeStep "decode/asm-pldrefvar-neighbor" s4 pldRefVarInstr 16
        let s6 ← expectDecodeStep "decode/asm-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let codeQ ←
          match assembleCp0 [schkBitRefsQInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/schkbitrefsq failed: {e}")
        if codeQ.bits = natToBits schkBitRefsQWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/schkbitrefsq: expected 0xd747, got {codeQ.bits}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits schkBitsWord 16 ++
          natToBits schkRefsWord 16 ++
          natToBits schkBitRefsWord 16 ++
          natToBits schkBitsQWord 16 ++
          natToBits schkRefsQWord 16 ++
          natToBits schkBitRefsQWord 16 ++
          natToBits pldRefVarWord 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-schkbits" r0 (.cellOp (.schkBits false)) 16
        let r2 ← expectDecodeStep "decode/raw-schkrefs" r1 (.cellOp (.schkRefs false)) 16
        let r3 ← expectDecodeStep "decode/raw-schkbitrefs" r2 schkBitRefsInstr 16
        let r4 ← expectDecodeStep "decode/raw-schkbitsq" r3 schkBitsQInstr 16
        let r5 ← expectDecodeStep "decode/raw-schkrefsq" r4 schkRefsQInstr 16
        let r6 ← expectDecodeStep "decode/raw-schkbitrefsq" r5 schkBitRefsQInstr 16
        let r7 ← expectDecodeStep "decode/raw-pldrefvar-neighbor" r6 pldRefVarInstr 16
        let r8 ← expectDecodeStep "decode/raw-tail-add" r7 .add 8
        if r8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r8.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback-and-target-hit"
      run := do
        expectOkStack "dispatch/non-cell-op-falls-through"
          (runSchkBitRefsQDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-non-target-falls-through"
          (runSchkBitRefsQDispatchFallback schkRefsQInstr #[.slice (mkFullSliceBitsRefs 0 0), intV 0])
          #[.slice (mkFullSliceBitsRefs 0 0), intV 0, intV dispatchSentinel]

        expectOkStack "dispatch/target-hit-no-sentinel"
          (runSchkBitRefsQDispatchFallback schkBitRefsQInstr
            (mkSchkStackNat (mkFullSliceBitsRefs 8 2) 8 2 #[.cell refCellB]))
          #[.cell refCellB, intV (-1)]
        expectErr "dispatch/target-hit-error-no-sentinel"
          (runSchkBitRefsQDispatchFallback schkBitRefsQInstr
            (mkSchkStackNat (mkFullSliceBitsRefs 8 2) 0 5))
          .rangeChk }
  ]
  oracle := #[
    mkSchkBitRefsQCase "ok/direct/empty-b0-r0"
      (mkSchkStackNat (mkFullSliceBitsRefs 0 0) 0 0),
    mkSchkBitRefsQCase "ok/direct/full-b1023-r4-exact"
      (mkSchkStackNat (mkFullSliceBitsRefs 1023 4) 1023 4),
    mkSchkBitRefsQCase "ok/direct/fit-bits-only"
      (mkSchkStackNat (mkFullSliceBitsRefs 17 2) 17 0),
    mkSchkBitRefsQCase "ok/direct/fit-refs-only"
      (mkSchkStackNat (mkFullSliceBitsRefs 9 4) 0 4),
    mkSchkBitRefsQCase "ok/direct/deep-noise-slice"
      (mkSchkStackNat (mkFullSliceBitsRefs 63 3) 31 2 #[.slice oracleNoiseSliceA]),
    mkSchkBitRefsQCase "ok/direct/deep-noise-cell"
      (mkSchkStackNat (mkFullSliceBitsRefs 255 2) 200 1 #[.cell refCellB]),

    mkSchkBitRefsQCase "fail/direct/bits-overflow"
      (mkSchkStackNat (mkFullSliceBitsRefs 7 2) 8 2),
    mkSchkBitRefsQCase "fail/direct/refs-overflow"
      (mkSchkStackNat (mkFullSliceBitsRefs 20 1) 10 2),
    mkSchkBitRefsQCase "fail/direct/both-overflow"
      (mkSchkStackNat (mkFullSliceBitsRefs 0 0) 1 1),

    mkSchkBitRefsQCase "underflow/empty" #[],
    mkSchkBitRefsQCase "underflow/one-item"
      #[.slice (mkFullSliceBitsRefs 0 0)],
    mkSchkBitRefsQCase "underflow/two-items"
      #[.slice (mkFullSliceBitsRefs 0 0), intV 0],

    mkSchkBitRefsQCase "type/refs-top-not-int"
      #[.slice (mkFullSliceBitsRefs 0 0), intV 0, .null],
    mkSchkBitRefsQCase "range/refs-negative"
      #[.slice (mkFullSliceBitsRefs 0 0), intV 0, intV (-1)],
    mkSchkBitRefsQCase "range/refs-gt4"
      #[.slice (mkFullSliceBitsRefs 0 0), intV 0, intV 5],
    mkSchkBitRefsQCase "type/bits-not-int-after-refs"
      #[.slice (mkFullSliceBitsRefs 0 0), .null, intV 0],
    mkSchkBitRefsQCase "range/bits-negative"
      #[.slice (mkFullSliceBitsRefs 0 0), intV (-1), intV 0],
    mkSchkBitRefsQCase "range/bits-gt1023"
      #[.slice (mkFullSliceBitsRefs 0 0), intV 1024, intV 0],
    mkSchkBitRefsQCase "type/slice-not-slice"
      #[.null, intV 0, intV 0],

    mkSchkBitRefsQProgramCase "range/program-refs-nan" #[] schkProgramRefsNan,
    mkSchkBitRefsQProgramCase "range/program-bits-nan" #[] schkProgramBitsNan,

    mkSchkBitRefsQCase "gas/exact-cost-succeeds"
      (mkSchkStackNat (mkFullSliceBitsRefs 0 0) 0 0)
      #[.pushInt (.num schkBitRefsQSetGasExact), .tonEnvOp .setGasLimit, schkBitRefsQInstr],
    mkSchkBitRefsQCase "gas/exact-minus-one-out-of-gas"
      (mkSchkStackNat (mkFullSliceBitsRefs 0 0) 0 0)
      #[.pushInt (.num schkBitRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkBitRefsQInstr],

    mkSchkBitRefsQProgramCase "ok/program/bits900-refs2-need123-2" #[]
      (mkSchkBitRefsQProgram 900 2 123 2),
    mkSchkBitRefsQProgramCase "fail/program/bits200-refs1-need150-2" #[]
      (mkSchkBitRefsQProgram 200 1 150 2)
  ]
  fuzz := #[
    { seed := 2026021111
      count := 320
      gen := genSchkBitRefsQFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCHKBITREFSQ
