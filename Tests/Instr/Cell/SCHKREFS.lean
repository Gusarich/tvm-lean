import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCHKREFS

/-
SCHKREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/SchkRefs.lean` (`.schkRefs quiet`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popNatUpTo 1023` range/type behavior)
  - `TvmLean/Semantics/VM/Ops/Cells.lean` (`popSlice` type behavior)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SCHKREFS` encode: `0xd742`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd742` decode; neighbors `0xd741/0xd743/0xd745..0xd748`)
- C++ reference:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_chk_op_args`, opcode `0xd742`, `max_arg1=1023`, non-quiet).

Branch map covered by this suite (`quiet=false`):
- underflow requires exactly 2 stack items;
- pop order is `refs` (top int) before `slice`;
- refs pop enforces int/range (`0..1023`) before slice pop/type;
- success path pops both values and pushes nothing;
- failure path throws `cell_und` (not status int) when `have_refs(refs)` is false;
- `have_refs` is checked against `refPos` window (`refsRemaining`), bits are irrelevant.

Oracle/fuzz stack note:
- every slice value used in oracle/fuzz stacks is a full-cell slice
  (`bitPos = 0`, `refPos = 0`) to satisfy oracle token encoding.
-/

private def schkRefsId : InstrId := { name := "SCHKREFS" }

private def schkRefsInstr : Instr := .cellOp (.schkRefs false)
private def schkBitsInstr : Instr := .cellOp (.schkBits false)
private def schkBitRefsInstr : Instr := .cellOp (.schkBitRefs false)
private def schkBitsQInstr : Instr := .cellOp (.schkBits true)
private def schkRefsQInstr : Instr := .cellOp (.schkRefs true)
private def schkBitRefsQInstr : Instr := .cellOp (.schkBitRefs true)
private def pldRefVarInstr : Instr := .cellOp .pldRefVar

private def schkRefsWord : Nat := 0xd742
private def schkBitsWord : Nat := 0xd741
private def schkBitRefsWord : Nat := 0xd743
private def schkBitsQWord : Nat := 0xd745
private def schkRefsQWord : Nat := 0xd746
private def schkBitRefsQWord : Nat := 0xd747
private def pldRefVarWord : Nat := 0xd748

private def execInstrCellOpSchkRefsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpSchkRefs op next
  | _ => next

private def mkSchkRefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[schkRefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkRefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSchkRefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSchkRefsOnly schkRefsInstr stack

private def dispatchSentinel : Int := 74291

private def runSchkRefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSchkRefsOnly instr (VM.push (intV dispatchSentinel)) stack

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
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 11 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 2 2) #[]
private def refLeafD : Cell := Cell.mkOrdinary (natToBits 9 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkFullSlice (bits refs : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stripeBits bits phase) (refsByCount refs))

private def mkSliceWindow
    (bits refs bitPos refPos : Nat)
    (phase : Nat := 0) : Slice :=
  { cell := Cell.mkOrdinary (stripeBits bits phase) (refsByCount refs)
    bitPos := bitPos
    refPos := refPos }

private def mkSchkRefsStack (s : Slice) (refs : Int) (below : Array Value := #[]) :
    Array Value :=
  below ++ #[.slice s, intV refs]

private def mkSchkRefsStackNat (s : Slice) (refs : Nat) (below : Array Value := #[]) :
    Array Value :=
  mkSchkRefsStack s (Int.ofNat refs) below

private def sliceRefs0 : Slice := mkFullSlice 0 0
private def sliceRefs1 : Slice := mkFullSlice 5 1
private def sliceRefs2 : Slice := mkFullSlice 17 2 1
private def sliceRefs3 : Slice := mkFullSlice 31 3
private def sliceRefs4 : Slice := mkFullSlice 40 4 1
private def sliceBits1023Refs1 : Slice := mkFullSlice 1023 1
private def sliceBits1023Refs4 : Slice := mkFullSlice 1023 4 1

private def fullSliceNoiseA : Slice := mkFullSlice 13 1
private def fullSliceNoiseB : Slice := mkFullSlice 9 2 1

private def windowRefPos2 : Slice := mkSliceWindow 21 4 7 2
private def windowRefPos3 : Slice := mkSliceWindow 7 4 3 3 1

private def schkRefsSetGasExact : Int :=
  computeExactGasBudget schkRefsInstr

private def schkRefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne schkRefsInstr

private def refsReqBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 16, 255, 512, 1022, 1023]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 127, 255, 256, 1023]

private def pickFromPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNeedRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickFromPool rng1 refsReqBoundaryPool
  else
    randNat rng1 0 1023

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickFromPool rng1 bitsBoundaryPool
  else
    randNat rng1 0 1023

private def pickNeedRefsWithin (rng : StdGen) (refsAvail : Nat) : Nat × StdGen :=
  if refsAvail = 0 then
    (0, rng)
  else
    let (mode, rng1) := randNat rng 0 4
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (refsAvail, rng1)
    else if mode = 2 then
      (refsAvail - 1, rng1)
    else
      randNat rng1 0 refsAvail

private def pickNeedRefsOverflow (rng : StdGen) (refsAvail : Nat) : Nat × StdGen :=
  let minNeed : Nat := refsAvail + 1
  let (mode, rng1) := randNat rng 0 3
  if mode = 0 then
    (minNeed, rng1)
  else if mode = 1 then
    (1023, rng1)
  else if minNeed < 1023 then
    randNat rng1 minNeed 1023
  else
    (1023, rng1)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 200
    (intV (Int.ofNat n - 100), rng2)
  else if pick = 2 then
    (.cell refLeafC, rng1)
  else if pick = 3 then
    (.slice fullSliceNoiseA, rng1)
  else if pick = 4 then
    (.slice fullSliceNoiseB, rng1)
  else
    (.tuple #[], rng1)

private def genSchkRefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (case0, rng2) :=
    if shape = 0 then
      let (refsAvail, rng2) := randNat rng1 0 4
      let (needRefs, rng3) := pickNeedRefsWithin rng2 refsAvail
      let (bits, rng4) := pickBitsMixed rng3
      (mkSchkRefsCase s!"fuzz/ok/direct/refs{refsAvail}/need{needRefs}"
        (mkSchkRefsStackNat (mkFullSlice bits refsAvail) needRefs), rng4)
    else if shape = 1 then
      let (refsAvail, rng2) := randNat rng1 0 4
      let (needRefs, rng3) := pickNeedRefsWithin rng2 refsAvail
      let (bits, rng4) := pickBitsMixed rng3
      let (noise, rng5) := pickNoiseValue rng4
      (mkSchkRefsCase s!"fuzz/ok/deep1/refs{refsAvail}/need{needRefs}"
        (mkSchkRefsStackNat (mkFullSlice bits refsAvail 1) needRefs #[noise]), rng5)
    else if shape = 2 then
      let (refsAvail, rng2) := randNat rng1 0 4
      let (needRefs, rng3) := pickNeedRefsWithin rng2 refsAvail
      let (bits, rng4) := pickBitsMixed rng3
      let (noise1, rng5) := pickNoiseValue rng4
      let (noise2, rng6) := pickNoiseValue rng5
      (mkSchkRefsCase s!"fuzz/ok/deep2/refs{refsAvail}/need{needRefs}"
        (mkSchkRefsStackNat (mkFullSlice bits refsAvail 2) needRefs #[noise1, noise2]), rng6)
    else if shape = 3 then
      let (refsAvail, rng2) := randNat rng1 0 4
      let (needRefs, rng3) := pickNeedRefsOverflow rng2 refsAvail
      let (bits, rng4) := pickBitsMixed rng3
      (mkSchkRefsCase s!"fuzz/cellund/direct/refs{refsAvail}/need{needRefs}"
        (mkSchkRefsStackNat (mkFullSlice bits refsAvail) needRefs), rng4)
    else if shape = 4 then
      let (refsAvail, rng2) := randNat rng1 0 4
      let (needRefs, rng3) := pickNeedRefsOverflow rng2 refsAvail
      let (bits, rng4) := pickBitsMixed rng3
      let (noise, rng5) := pickNoiseValue rng4
      (mkSchkRefsCase s!"fuzz/cellund/deep/refs{refsAvail}/need{needRefs}"
        (mkSchkRefsStackNat (mkFullSlice bits refsAvail 1) needRefs #[noise]), rng5)
    else if shape = 5 then
      (mkSchkRefsCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 6 then
      (mkSchkRefsCase "fuzz/underflow/one-item" #[.slice sliceRefs2], rng1)
    else if shape = 7 then
      (mkSchkRefsCase "fuzz/type/refs-top-null" #[.slice sliceRefs2, .null], rng1)
    else if shape = 8 then
      (mkSchkRefsCase "fuzz/range/refs-negative" #[.slice sliceRefs2, intV (-1)], rng1)
    else if shape = 9 then
      let (needRefs, rng2) := pickNeedRefsMixed rng1
      let needOut : Nat := if needRefs ≤ 1023 then 1024 else needRefs
      (mkSchkRefsCase s!"fuzz/range/refs-over-{needOut}"
        #[.slice sliceRefs2, intV (Int.ofNat needOut)], rng2)
    else if shape = 10 then
      (mkSchkRefsCase "fuzz/type/slice-not-slice"
        #[.null, intV 0], rng1)
    else if shape = 11 then
      (mkSchkRefsCase "fuzz/order/range-before-slice-type"
        #[.null, intV 1024], rng1)
    else if shape = 12 then
      (mkSchkRefsCase "fuzz/order/type-before-slice-type"
        #[.null, .null], rng1)
    else if shape = 13 then
      let (refsAvail, rng2) := randNat rng1 0 4
      let (needRefs, rng3) := pickNeedRefsWithin rng2 refsAvail
      let stack := mkSchkRefsStackNat (mkFullSlice 32 refsAvail) needRefs
      (mkSchkRefsCase "fuzz/gas/exact" stack
        #[.pushInt (.num schkRefsSetGasExact), .tonEnvOp .setGasLimit, schkRefsInstr], rng3)
    else
      let (refsAvail, rng2) := randNat rng1 0 4
      let (needRefs, rng3) := pickNeedRefsWithin rng2 refsAvail
      let stack := mkSchkRefsStackNat (mkFullSlice 8 refsAvail 1) needRefs
      (mkSchkRefsCase "fuzz/gas/exact-minus-one" stack
        #[.pushInt (.num schkRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkRefsInstr], rng3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkSchkRefsCase "ok/direct/refs0-plus-0"
      (mkSchkRefsStackNat sliceRefs0 0),
    mkSchkRefsCase "ok/direct/refs1-plus-0"
      (mkSchkRefsStackNat sliceRefs1 0),
    mkSchkRefsCase "ok/direct/refs1-plus-1"
      (mkSchkRefsStackNat sliceRefs1 1),
    mkSchkRefsCase "ok/direct/refs2-plus-2"
      (mkSchkRefsStackNat sliceRefs2 2),
    mkSchkRefsCase "ok/direct/refs3-plus-1"
      (mkSchkRefsStackNat sliceRefs3 1),
    mkSchkRefsCase "ok/direct/refs4-plus-4"
      (mkSchkRefsStackNat sliceRefs4 4),
    mkSchkRefsCase "ok/direct/bits1023-refs1-plus-1"
      (mkSchkRefsStackNat sliceBits1023Refs1 1),
    mkSchkRefsCase "ok/direct/bits1023-refs4-plus-0"
      (mkSchkRefsStackNat sliceBits1023Refs4 0),
    mkSchkRefsCase "ok/deep/null-int/refs2-plus-2"
      (mkSchkRefsStackNat sliceRefs2 2 #[.null, intV 73]),
    mkSchkRefsCase "ok/deep/cell-slice/refs4-plus-3"
      (mkSchkRefsStackNat sliceRefs4 3 #[.cell refLeafD, .slice fullSliceNoiseA])
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkSchkRefsCase "underflow/empty" #[],
    mkSchkRefsCase "underflow/one-item-slice" #[.slice sliceRefs1],
    mkSchkRefsCase "type/refs-top-null" #[.slice sliceRefs1, .null],
    mkSchkRefsCase "type/refs-top-cell" #[.slice sliceRefs1, .cell refLeafA],
    mkSchkRefsCase "range/refs-negative" #[.slice sliceRefs2, intV (-1)],
    mkSchkRefsCase "range/refs-over-1023" #[.slice sliceRefs2, intV 1024],
    mkSchkRefsCase "type/slice-not-slice-after-valid-refs" #[.null, intV 0],
    mkSchkRefsCase "order/refs-range-before-slice-type" #[.null, intV 1024],
    mkSchkRefsCase "order/refs-type-before-slice-type" #[.null, .null],
    mkSchkRefsCase "cellund/empty-plus-1" (mkSchkRefsStackNat sliceRefs0 1),
    mkSchkRefsCase "cellund/refs2-plus-3" (mkSchkRefsStackNat sliceRefs2 3),
    mkSchkRefsCase "cellund/refs4-plus-5" (mkSchkRefsStackNat sliceRefs4 5)
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkSchkRefsCase "gas/exact-cost-succeeds"
      (mkSchkRefsStackNat sliceRefs2 1)
      #[.pushInt (.num schkRefsSetGasExact), .tonEnvOp .setGasLimit, schkRefsInstr],
    mkSchkRefsCase "gas/exact-minus-one-out-of-gas"
      (mkSchkRefsStackNat sliceRefs2 1)
      #[.pushInt (.num schkRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkRefsInstr]
  ]

def suite : InstrSuite where
  id := schkRefsId
  unit := #[
    { name := "unit/direct/success-boundaries-and-stack-shape"
      run := do
        expectOkStack "ok/refs0-plus-0"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceRefs0 0))
          #[]
        expectOkStack "ok/refs1-plus-1"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceRefs1 1))
          #[]
        expectOkStack "ok/refs4-plus-4"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceRefs4 4))
          #[]
        expectOkStack "ok/bits1023-refs4-plus-0"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceBits1023Refs4 0))
          #[]
        expectOkStack "ok/deep-stack-preserve-below"
          (runSchkRefsDirect
            (mkSchkRefsStackNat sliceRefs2 2 #[.null, intV (-8), .cell refLeafA]))
          #[.null, intV (-8), .cell refLeafA] }
    ,
    { name := "unit/direct/slice-window-refpos-controls-haveRefs"
      run := do
        expectOkStack "window/refpos2-need2"
          (runSchkRefsDirect (mkSchkRefsStackNat windowRefPos2 2))
          #[]
        expectErr "window/refpos2-need3"
          (runSchkRefsDirect (mkSchkRefsStackNat windowRefPos2 3))
          .cellUnd
        expectOkStack "window/refpos3-need1"
          (runSchkRefsDirect (mkSchkRefsStackNat windowRefPos3 1))
          #[]
        expectErr "window/refpos3-need2"
          (runSchkRefsDirect (mkSchkRefsStackNat windowRefPos3 2))
          .cellUnd
        expectOkStack "window/deep-stack-preserve-below"
          (runSchkRefsDirect
            (mkSchkRefsStackNat windowRefPos2 2 #[.slice fullSliceNoiseB, intV 44]))
          #[.slice fullSliceNoiseB, intV 44] }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty"
          (runSchkRefsDirect #[])
          .stkUnd
        expectErr "underflow/one-item"
          (runSchkRefsDirect #[.slice sliceRefs1])
          .stkUnd

        expectErr "type/refs-top-null"
          (runSchkRefsDirect #[.slice sliceRefs1, .null])
          .typeChk
        expectErr "range/refs-negative"
          (runSchkRefsDirect #[.slice sliceRefs1, intV (-1)])
          .rangeChk
        expectErr "range/refs-over-1023"
          (runSchkRefsDirect #[.slice sliceRefs1, intV 1024])
          .rangeChk
        expectErr "range/refs-nan"
          (runSchkRefsDirect #[.slice sliceRefs1, .int .nan])
          .rangeChk

        expectErr "type/slice-not-slice-after-valid-refs"
          (runSchkRefsDirect #[.null, intV 0])
          .typeChk
        expectErr "order/refs-range-before-slice-type"
          (runSchkRefsDirect #[.null, intV 1024])
          .rangeChk
        expectErr "order/refs-type-before-slice-type"
          (runSchkRefsDirect #[.null, .null])
          .typeChk }
    ,
    { name := "unit/direct/cellund-boundaries"
      run := do
        expectErr "cellund/refs0-plus-1"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceRefs0 1))
          .cellUnd
        expectErr "cellund/refs1-plus-2"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceRefs1 2))
          .cellUnd
        expectErr "cellund/refs4-plus-5"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceRefs4 5))
          .cellUnd
        expectErr "cellund/window-refpos2-plus-3"
          (runSchkRefsDirect (mkSchkRefsStackNat windowRefPos2 3))
          .cellUnd
        expectErr "cellund/max-arg-1023"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceRefs4 1023))
          .cellUnd
        expectErr "cellund/bits1023-refs1-plus-2"
          (runSchkRefsDirect (mkSchkRefsStackNat sliceBits1023Refs1 2))
          .cellUnd }
    ,
    { name := "unit/opcode/decode-assembler-neighbors-and-gap"
      run := do
        let asmProgram : Array Instr :=
          #[
            schkBitsInstr,
            schkRefsInstr,
            schkBitRefsInstr,
            schkBitsQInstr,
            schkRefsQInstr,
            schkBitRefsQInstr,
            pldRefVarInstr,
            .add
          ]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-schkbits" s0 schkBitsInstr 16
        let s2 ← expectDecodeStep "decode/asm-schkrefs" s1 schkRefsInstr 16
        let s3 ← expectDecodeStep "decode/asm-schkbitrefs" s2 schkBitRefsInstr 16
        let s4 ← expectDecodeStep "decode/asm-schkbitsq" s3 schkBitsQInstr 16
        let s5 ← expectDecodeStep "decode/asm-schkrefsq" s4 schkRefsQInstr 16
        let s6 ← expectDecodeStep "decode/asm-schkbitrefsq" s5 schkBitRefsQInstr 16
        let s7 ← expectDecodeStep "decode/asm-pldrefvar" s6 pldRefVarInstr 16
        let s8 ← expectDecodeStep "decode/asm-tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/asm-end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let codeSchkRefs ←
          match assembleCp0 [schkRefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/schkrefs failed: {e}")
        if codeSchkRefs.bits = natToBits schkRefsWord 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/schkrefs: expected 0xd742, got bits {codeSchkRefs.bits}")
        if codeSchkRefs.bits.size = 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/schkrefs: expected 16 bits, got {codeSchkRefs.bits.size}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawCell : Cell :=
          Cell.mkOrdinary
            (natToBits schkBitsWord 16
              ++ natToBits schkRefsWord 16
              ++ natToBits schkBitRefsWord 16
              ++ natToBits schkBitsQWord 16
              ++ natToBits schkRefsQWord 16
              ++ natToBits schkBitRefsQWord 16
              ++ natToBits pldRefVarWord 16
              ++ addCell.bits) #[]
        let r0 := Slice.ofCell rawCell
        let r1 ← expectDecodeStep "decode/raw-schkbits" r0 schkBitsInstr 16
        let r2 ← expectDecodeStep "decode/raw-schkrefs" r1 schkRefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-schkbitrefs" r2 schkBitRefsInstr 16
        let r4 ← expectDecodeStep "decode/raw-schkbitsq" r3 schkBitsQInstr 16
        let r5 ← expectDecodeStep "decode/raw-schkrefsq" r4 schkRefsQInstr 16
        let r6 ← expectDecodeStep "decode/raw-schkbitrefsq" r5 schkBitRefsQInstr 16
        let r7 ← expectDecodeStep "decode/raw-pldrefvar" r6 pldRefVarInstr 16
        let r8 ← expectDecodeStep "decode/raw-tail-add" r7 .add 8
        if r8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted slice, got {r8.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-d744"
          (Slice.ofCell (Cell.mkOrdinary (natToBits 0xd744 16) #[]))
          .invOpcode }
    ,
    { name := "unit/dispatch/fallthrough-and-shared-quiet-neighbor"
      run := do
        expectOkStack "dispatch/add"
          (runSchkRefsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/schkbits"
          (runSchkRefsDispatchFallback schkBitsInstr #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/schkrefsq-shared-handler"
          (runSchkRefsDispatchFallback schkRefsQInstr #[.slice sliceRefs2, intV 1])
          #[intV (-1)]
        expectOkStack "dispatch/pldrefvar"
          (runSchkRefsDispatchFallback pldRefVarInstr #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel] }
  ]
  oracle := oracleSuccessCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021038
      count := 500
      gen := genSchkRefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCHKREFS
