import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCHKBITREFS

/-
SCHKBITREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/SchkBitRefs.lean` (`.schkBitRefs quiet`)
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SCHKBITREFS` encode: `0xd743`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd741..0xd747` family decode, `0xd744` gap)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_chk_op_args2`, max args: bits=`1023`, refs=`4`).

Path contracts targeted by this suite:
- `checkUnderflow 3` before any pop;
- pop/range/type order is `refs` (top, `0..4`) -> `bits` (`0..1023`) -> `slice`;
- non-quiet success pushes nothing; failure in capacity check throws `cellUnd`;
- opcode/decode boundaries around `0xd743` with neighboring SCHK variants and gap `0xd744`.

Oracle harness constraint:
- oracle/fuzz stack token encoding supports only full-cell slices
  (`bitPos = 0`, `refPos = 0`); oracle/fuzz cases here obey that.
-/

private def schkbitrefsId : InstrId := { name := "SCHKBITREFS" }

private def schkbitsInstr : Instr := .cellOp (.schkBits false)
private def schkrefsInstr : Instr := .cellOp (.schkRefs false)
private def schkbitrefsInstr : Instr := .cellOp (.schkBitRefs false)
private def schkbitsqInstr : Instr := .cellOp (.schkBits true)
private def schkrefsqInstr : Instr := .cellOp (.schkRefs true)
private def schkbitrefsqInstr : Instr := .cellOp (.schkBitRefs true)

private def schkbitsWord : Nat := 0xd741
private def schkrefsWord : Nat := 0xd742
private def schkbitrefsWord : Nat := 0xd743
private def schkbitsqWord : Nat := 0xd745
private def schkrefsqWord : Nat := 0xd746
private def schkbitrefsqWord : Nat := 0xd747

private def dispatchSentinel : Int := 743

private def execInstrCellOpSchkBitRefsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpSchkBitRefs op next
  | _ => next

private def mkSchkBitRefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[schkbitrefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkbitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSchkBitRefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSchkBitRefsOnly schkbitrefsInstr stack

private def runSchkBitRefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSchkBitRefsOnly instr (VM.push (intV dispatchSentinel)) stack

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]
private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkFullSlice (bits refs : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stripeBits bits phase) (refsByCount refs))

private def mkCursorSlice
    (totalBits totalRefs bitPos refPos : Nat)
    (phase : Nat := 0) : Slice :=
  { cell := Cell.mkOrdinary (stripeBits totalBits phase) (refsByCount totalRefs)
    bitPos := bitPos
    refPos := refPos }

private def mkSchkStack (s : Slice) (bits refs : Int) (below : Array Value := #[]) :
    Array Value :=
  below ++ #[.slice s, intV bits, intV refs]

private def mkSchkStackNat (s : Slice) (bits refs : Nat) (below : Array Value := #[]) :
    Array Value :=
  mkSchkStack s (Int.ofNat bits) (Int.ofNat refs) below

private def fullSliceNoiseA : Slice := mkFullSlice 11 1 0
private def fullSliceNoiseB : Slice := mkFullSlice 17 2 1

private def schkBitRefsSetGasExact : Int :=
  computeExactGasBudget schkbitrefsInstr

private def schkBitRefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne schkbitrefsInstr

private def schkBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 255, 256, 511, 512, 1023]

private def pickSchkBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (schkBitsBoundaryPool.size - 1)
    (schkBitsBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 1023

private def pickSchkRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    (4, rng1)
  else
    randNat rng1 0 4

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 91
    else if pick = 2 then .cell refLeafB
    else .slice fullSliceNoiseA
  (noise, rng1)

private def pickReqWithinCaps (bitsCap refsCap : Nat) (rng0 : StdGen) : (Nat × Nat) × StdGen :=
  let (bitsCandidate, rng1) := pickSchkBitsMixed rng0
  let bitsReq := Nat.min bitsCandidate bitsCap
  let (refsCandidate, rng2) := pickSchkRefsMixed rng1
  let refsReq := Nat.min refsCandidate refsCap
  ((bitsReq, refsReq), rng2)

private def genSchkBitRefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      (mkSchkBitRefsCase "fuzz/ok/empty/+0+0"
        (mkSchkStackNat (mkFullSlice 0 0) 0 0), rng1)
    else if shape = 1 then
      let (availBits, rng2) := pickSchkBitsMixed rng1
      let (availRefs, rng3) := pickSchkRefsMixed rng2
      let (phase, rng4) := randNat rng3 0 1
      let ((bitsReq, refsReq), rng5) := pickReqWithinCaps availBits availRefs rng4
      (mkSchkBitRefsCase s!"fuzz/ok/within/b{availBits}-r{availRefs}/+{bitsReq}+{refsReq}"
        (mkSchkStackNat (mkFullSlice availBits availRefs phase) bitsReq refsReq), rng5)
    else if shape = 2 then
      let (availBits, rng2) := pickSchkBitsMixed rng1
      let (availRefs, rng3) := pickSchkRefsMixed rng2
      let (phase, rng4) := randNat rng3 0 1
      let ((bitsReq, refsReq), rng5) := pickReqWithinCaps availBits availRefs rng4
      let (noise, rng6) := pickNoiseValue rng5
      (mkSchkBitRefsCase s!"fuzz/ok/deep/b{availBits}-r{availRefs}/+{bitsReq}+{refsReq}"
        (mkSchkStackNat (mkFullSlice availBits availRefs phase) bitsReq refsReq #[noise]), rng6)
    else if shape = 3 then
      let (availBits, rng2) := randNat rng1 0 1022
      let (availRefs, rng3) := pickSchkRefsMixed rng2
      let (phase, rng4) := randNat rng3 0 1
      let (refsReq, rng5) := randNat rng4 0 availRefs
      (mkSchkBitRefsCase s!"fuzz/cellund/bits-by1/b{availBits}-r{availRefs}/refs{refsReq}"
        (mkSchkStackNat (mkFullSlice availBits availRefs phase) (availBits + 1) refsReq), rng5)
    else if shape = 4 then
      let (availBits, rng2) := pickSchkBitsMixed rng1
      let (availRefs, rng3) := randNat rng2 0 3
      let (phase, rng4) := randNat rng3 0 1
      let (bitsReq, rng5) := randNat rng4 0 availBits
      (mkSchkBitRefsCase s!"fuzz/cellund/refs-by1/b{availBits}-r{availRefs}/bits{bitsReq}"
        (mkSchkStackNat (mkFullSlice availBits availRefs phase) bitsReq (availRefs + 1)), rng5)
    else if shape = 5 then
      let (availBits, rng2) := randNat rng1 0 1022
      let (availRefs, rng3) := randNat rng2 0 3
      let (phase, rng4) := randNat rng3 0 1
      (mkSchkBitRefsCase s!"fuzz/cellund/both-by1/b{availBits}-r{availRefs}"
        (mkSchkStackNat (mkFullSlice availBits availRefs phase) (availBits + 1) (availRefs + 1)), rng4)
    else if shape = 6 then
      (mkSchkBitRefsCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 7 then
      (mkSchkBitRefsCase "fuzz/underflow/one-item" #[.slice (mkFullSlice 0 0)], rng1)
    else if shape = 8 then
      (mkSchkBitRefsCase "fuzz/underflow/two-items" #[.slice (mkFullSlice 3 1), intV 0], rng1)
    else if shape = 9 then
      (mkSchkBitRefsCase "fuzz/type/refs-top-null"
        #[.slice (mkFullSlice 8 1), intV 0, .null], rng1)
    else if shape = 10 then
      let (refsReq, rng2) := randNat rng1 5 7
      (mkSchkBitRefsCase s!"fuzz/range/refs-over4/{refsReq}"
        #[.slice (mkFullSlice 8 0), intV 0, intV refsReq], rng2)
    else if shape = 11 then
      (mkSchkBitRefsCase "fuzz/range/refs-negative"
        #[.slice (mkFullSlice 8 1), intV 0, intV (-1)], rng1)
    else if shape = 12 then
      (mkSchkBitRefsCase "fuzz/type/bits-not-int"
        #[.slice (mkFullSlice 8 1), .null, intV 0], rng1)
    else if shape = 13 then
      (mkSchkBitRefsCase "fuzz/range/bits-over1023"
        #[.slice (mkFullSlice 8 1), intV 1024, intV 0], rng1)
    else if shape = 14 then
      (mkSchkBitRefsCase "fuzz/range/bits-negative"
        #[.slice (mkFullSlice 8 1), intV (-1), intV 0], rng1)
    else if shape = 15 then
      (mkSchkBitRefsCase "fuzz/type/slice-not-slice"
        #[.null, intV 1, intV 1], rng1)
    else if shape = 16 then
      (mkSchkBitRefsCase "fuzz/gas/exact"
        (mkSchkStackNat (mkFullSlice 0 0) 0 0)
        #[.pushInt (.num schkBitRefsSetGasExact), .tonEnvOp .setGasLimit, schkbitrefsInstr], rng1)
    else if shape = 17 then
      (mkSchkBitRefsCase "fuzz/gas/exact-minus-one"
        (mkSchkStackNat (mkFullSlice 0 0) 0 0)
        #[.pushInt (.num schkBitRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkbitrefsInstr], rng1)
    else
      (mkSchkBitRefsCase "fuzz/order/refs-range-before-bits-type"
        #[.null, .null, intV 5], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkSchkBitRefsCase "ok/full-empty/+0+0"
      (mkSchkStackNat (mkFullSlice 0 0) 0 0),
    mkSchkBitRefsCase "ok/full-empty/+1+0"
      (mkSchkStackNat (mkFullSlice 1 0) 1 0),
    mkSchkBitRefsCase "ok/full-empty/+0+1"
      (mkSchkStackNat (mkFullSlice 0 1) 0 1),
    mkSchkBitRefsCase "ok/boundary/full/+1023+4"
      (mkSchkStackNat (mkFullSlice 1023 4) 1023 4),
    mkSchkBitRefsCase "ok/boundary/bits-only"
      (mkSchkStackNat (mkFullSlice 1023 1) 1023 0),
    mkSchkBitRefsCase "ok/boundary/refs-only"
      (mkSchkStackNat (mkFullSlice 8 4) 0 4),
    mkSchkBitRefsCase "ok/slack-large"
      (mkSchkStackNat (mkFullSlice 900 3) 512 2),
    mkSchkBitRefsCase "ok/deep-stack-preserve-below"
      (mkSchkStackNat (mkFullSlice 63 2) 32 1 #[.null, intV 42, .slice fullSliceNoiseA])
  ]

private def oracleCellUndCases : Array OracleCase :=
  #[
    mkSchkBitRefsCase "cellund/bits-by1"
      (mkSchkStackNat (mkFullSlice 7 2) 8 2),
    mkSchkBitRefsCase "cellund/refs-by1"
      (mkSchkStackNat (mkFullSlice 9 1) 9 2),
    mkSchkBitRefsCase "cellund/both-by1"
      (mkSchkStackNat (mkFullSlice 3 0) 4 1),
    mkSchkBitRefsCase "cellund/empty-needs-1-1"
      (mkSchkStackNat (mkFullSlice 0 0) 1 1)
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkSchkBitRefsCase "underflow/empty" #[],
    mkSchkBitRefsCase "underflow/one-item"
      #[.slice (mkFullSlice 0 0)],
    mkSchkBitRefsCase "type/refs-top-null"
      #[.slice (mkFullSlice 0 0), intV 0, .null],
    mkSchkBitRefsCase "range/refs-over4"
      #[.slice (mkFullSlice 0 0), intV 0, intV 5],
    mkSchkBitRefsCase "range/refs-negative"
      #[.slice (mkFullSlice 0 0), intV 0, intV (-1)],
    mkSchkBitRefsCase "range/refs-nan-via-program"
      #[.slice (mkFullSlice 4 0), intV 0]
      #[.pushInt .nan, schkbitrefsInstr],
    mkSchkBitRefsCase "type/bits-not-int"
      #[.slice (mkFullSlice 0 0), .null, intV 0],
    mkSchkBitRefsCase "range/bits-over1023"
      #[.slice (mkFullSlice 0 0), intV 1024, intV 0],
    mkSchkBitRefsCase "range/bits-nan-via-program"
      #[.slice (mkFullSlice 4 0)]
      #[.pushInt .nan, .pushInt (.num 0), schkbitrefsInstr],
    mkSchkBitRefsCase "type/slice-not-slice"
      #[.null, intV 1, intV 1],
    mkSchkBitRefsCase "order/refs-range-before-bits-type"
      #[.null, .null, intV 5]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkSchkBitRefsCase "gas/exact-cost-succeeds"
      (mkSchkStackNat (mkFullSlice 0 0) 0 0)
      #[.pushInt (.num schkBitRefsSetGasExact), .tonEnvOp .setGasLimit, schkbitrefsInstr],
    mkSchkBitRefsCase "gas/exact-minus-one-out-of-gas"
      (mkSchkStackNat (mkFullSlice 0 0) 0 0)
      #[.pushInt (.num schkBitRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkbitrefsInstr]
  ]

def suite : InstrSuite where
  id := { name := "SCHKBITREFS" }
  unit := #[
    { name := "unit/direct/success-boundaries-and-deep-stack"
      run := do
        expectOkStack "ok/empty/+0+0"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 0 0) 0 0))
          #[]
        expectOkStack "ok/empty/+1+0"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 1 0) 1 0))
          #[]
        expectOkStack "ok/empty/+0+1"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 0 1) 0 1))
          #[]
        expectOkStack "ok/exact-boundary/+1023+4"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 1023 4) 1023 4))
          #[]
        expectOkStack "ok/deep-stack-preserve-below"
          (runSchkBitRefsDirect
            (mkSchkStackNat (mkFullSlice 120 2) 64 1 #[.null, intV 99, .slice fullSliceNoiseA]))
          #[.null, intV 99, .slice fullSliceNoiseA] }
    ,
    { name := "unit/direct/partial-slice-cursor-boundaries"
      run := do
        let cursor := mkCursorSlice 32 3 20 1
        expectOkStack "ok/cursor/exact-remaining-12-2"
          (runSchkBitRefsDirect (mkSchkStackNat cursor 12 2))
          #[]
        expectOkStack "ok/cursor/deep-stack-exact"
          (runSchkBitRefsDirect (mkSchkStackNat cursor 12 2 #[intV 7]))
          #[intV 7]
        expectErr "cellund/cursor/bits-by1"
          (runSchkBitRefsDirect (mkSchkStackNat cursor 13 2))
          .cellUnd
        expectErr "cellund/cursor/refs-by1"
          (runSchkBitRefsDirect (mkSchkStackNat cursor 12 3))
          .cellUnd
        expectErr "cellund/cursor/both-by1"
          (runSchkBitRefsDirect (mkSchkStackNat cursor 13 3))
          .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty" (runSchkBitRefsDirect #[]) .stkUnd
        expectErr "underflow/one-item"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0)]) .stkUnd
        expectErr "underflow/two-items"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV 0]) .stkUnd

        expectErr "type/refs-top-null"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV 0, .null]) .typeChk
        expectErr "range/refs-over4"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV 0, intV 5]) .rangeChk
        expectErr "range/refs-negative"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV 0, intV (-1)]) .rangeChk
        expectErr "range/refs-nan"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV 0, .int .nan]) .rangeChk

        expectErr "type/bits-not-int-after-valid-refs"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), .null, intV 0]) .typeChk
        expectErr "range/bits-over1023"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-negative"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV (-1), intV 0]) .rangeChk
        expectErr "range/bits-nan"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), .int .nan, intV 0]) .rangeChk

        expectErr "type/slice-not-slice-after-valid-args"
          (runSchkBitRefsDirect #[.null, intV 1, intV 1]) .typeChk

        expectErr "order/refs-range-before-bits-type"
          (runSchkBitRefsDirect #[.null, .null, intV 5]) .rangeChk
        expectErr "order/refs-type-before-bits-range"
          (runSchkBitRefsDirect #[.slice (mkFullSlice 0 0), intV 2048, .null]) .typeChk
        expectErr "order/bits-range-before-slice-type"
          (runSchkBitRefsDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "order/bits-type-before-slice-type"
          (runSchkBitRefsDirect #[.null, .null, intV 0]) .typeChk }
    ,
    { name := "unit/direct/cellund-failure-matrix"
      run := do
        expectErr "cellund/bits-by1"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 7 2) 8 2))
          .cellUnd
        expectErr "cellund/refs-by1"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 9 1) 9 2))
          .cellUnd
        expectErr "cellund/both-by1"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 3 0) 4 1))
          .cellUnd
        expectErr "cellund/empty-needs-1-1"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 0 0) 1 1))
          .cellUnd
        expectErr "cellund/high-refs-cap-check"
          (runSchkBitRefsDirect (mkSchkStackNat (mkFullSlice 900 0) 900 4))
          .cellUnd }
    ,
    { name := "unit/opcode/decode-assembler-boundary-and-gap"
      run := do
        let asmProgram : Array Instr :=
          #[schkbitsInstr, schkrefsInstr, schkbitrefsInstr, schkbitsqInstr, schkrefsqInstr, schkbitrefsqInstr, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-schkbits" a0 schkbitsInstr 16
        let a2 ← expectDecodeStep "decode/asm-schkrefs" a1 schkrefsInstr 16
        let a3 ← expectDecodeStep "decode/asm-schkbitrefs" a2 schkbitrefsInstr 16
        let a4 ← expectDecodeStep "decode/asm-schkbitsq" a3 schkbitsqInstr 16
        let a5 ← expectDecodeStep "decode/asm-schkrefsq" a4 schkrefsqInstr 16
        let a6 ← expectDecodeStep "decode/asm-schkbitrefsq" a5 schkbitrefsqInstr 16
        let a7 ← expectDecodeStep "decode/asm-tail-add" a6 .add 8
        if a7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a7.bitsRemaining} bits remaining")

        let codeSchkBitRefs ←
          match assembleCp0 [schkbitrefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/schkbitrefs failed: {e}")
        if codeSchkBitRefs.bits = natToBits schkbitrefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/schkbitrefs: expected 0xd743, got {codeSchkBitRefs.bits}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits schkbitsWord 16 ++
          natToBits schkrefsWord 16 ++
          natToBits schkbitrefsWord 16 ++
          natToBits schkbitsqWord 16 ++
          natToBits schkrefsqWord 16 ++
          natToBits schkbitrefsqWord 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-schkbits" r0 schkbitsInstr 16
        let r2 ← expectDecodeStep "decode/raw-schkrefs" r1 schkrefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-schkbitrefs" r2 schkbitrefsInstr 16
        let r4 ← expectDecodeStep "decode/raw-schkbitsq" r3 schkbitsqInstr 16
        let r5 ← expectDecodeStep "decode/raw-schkrefsq" r4 schkrefsqInstr 16
        let r6 ← expectDecodeStep "decode/raw-schkbitrefsq" r5 schkbitrefsqInstr 16
        let r7 ← expectDecodeStep "decode/raw-tail-add" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-d744"
          (mkSliceFromBits (natToBits 0xd744 16))
          .invOpcode }
    ,
    { name := "unit/dispatch/fallback-vs-target-hit"
      run := do
        expectOkStack "dispatch/non-cell-op-add"
          (runSchkBitRefsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-schkbits"
          (runSchkBitRefsDispatchFallback schkbitsInstr #[.slice fullSliceNoiseA, intV 3])
          #[.slice fullSliceNoiseA, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-schkrefs"
          (runSchkBitRefsDispatchFallback schkrefsInstr #[.slice fullSliceNoiseB, intV 1])
          #[.slice fullSliceNoiseB, intV 1, intV dispatchSentinel]
        expectOkStack "dispatch/quiet-variant-hit-success"
          (runSchkBitRefsDispatchFallback schkbitrefsqInstr #[.slice fullSliceNoiseB, intV 1, intV 1])
          #[intV (-1)]
        expectOkStack "dispatch/quiet-variant-hit-fail"
          (runSchkBitRefsDispatchFallback schkbitrefsqInstr #[.slice (mkFullSlice 0 0), intV 1, intV 1])
          #[intV 0]

        expectOkStack "dispatch/target-hit-no-sentinel"
          (runSchkBitRefsDispatchFallback schkbitrefsInstr
            (mkSchkStackNat (mkFullSlice 12 2) 10 2 #[.cell refLeafA]))
          #[.cell refLeafA]
        expectErr "dispatch/target-hit-error-no-sentinel"
          (runSchkBitRefsDispatchFallback schkbitrefsInstr
            (mkSchkStackNat (mkFullSlice 1 0) 2 0))
          .cellUnd }
  ]
  oracle := oracleSuccessCases ++ oracleCellUndCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021113
      count := 260
      gen := genSchkBitRefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCHKBITREFS
