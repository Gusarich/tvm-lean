import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STREFR

/-
STREFR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.strefR quiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf14` decode to `.cellOp (.strefR false)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.strefR false` encode as `0xcf14`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_ref_rev`, registered at opcode `0xcf14`).

Branch map used for this suite (`quiet=false`, i.e. STREFR):
- Lean STREFR path: 4 branch sites / 5 terminal outcomes
  (`checkUnderflow 2`; pop top as cell; pop second as builder; `canExtendBy 0 1`;
   success push / `cellOv` throw).
- C++ STREFR path: 4 branch sites / 5 aligned outcomes
  (`check_underflow(2)`; `pop_cell`; `pop_builder`; `can_extend_by(0,1)`).

Key risk areas:
- reverse stack order (`... builder cell`, with `cell` on top);
- type-check ordering (`cell` pop fails before builder pop);
- ref-capacity overflow (`refs=4`) throws `cellOv` in non-quiet mode;
- bit-capacity saturation (1023 bits) must still allow adding a reference.
-/

private def strefRId : InstrId := { name := "STREFR" }

private def strefRInstr : Instr :=
  .cellOp (.strefR false)

private def strefRqInstr : Instr :=
  .cellOp (.strefR true)

private def execCellOpExtInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpExt op next
  | _ => next

private def mkStrefRCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[strefRInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefRId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStrefRProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefRId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStrefRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpExtInstr strefRInstr stack

private def runStrefRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpExtInstr .add (VM.push (intV 53012)) stack

private def strefRSetGasExact : Int :=
  computeExactGasBudget strefRInstr

private def strefRSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne strefRInstr

private def cellBit1 : Cell :=
  (Builder.empty.storeBits (natToBits 1 1)).finalize

private def cellByteA5 : Cell :=
  (Builder.empty.storeBits (natToBits 0xA5 8)).finalize

private def cellWithRef : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[Cell.empty]

private def appendRef (b : Builder) (c : Cell) : Builder :=
  { b with refs := b.refs.push c }

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder refs

private def mkStrefROnTopBuilderProgram (refsBefore : Nat) : Array Instr :=
  mkBuilderWithRefsProgram refsBefore ++ #[.newc, .endc, strefRInstr]

private def strefRCellBitProgram : Array Instr :=
  #[
    .newc,
    .newc,
    .pushInt (.num 1), .xchg0 1, .stu 1,
    .endc,
    strefRInstr
  ]

private def strefRFullBitsProgram : Array Instr :=
  build1023WithFixed .stu ++ #[.newc, .endc, strefRInstr]

private def strefRFullBitsWithNoiseProgram : Array Instr :=
  #[.pushNull] ++ strefRFullBitsProgram

private def strefROverflowRefsProgram : Array Instr :=
  mkStrefROnTopBuilderProgram 4

private def strefROverflowRefsWithNoiseProgram : Array Instr :=
  #[.pushNull] ++ strefROverflowRefsProgram

private def strefRCellPool : Array Cell :=
  #[Cell.empty, cellBit1, cellByteA5, cellWithRef]

private def pickStrefRCell (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (strefRCellPool.size - 1)
  (strefRCellPool[idx]!, rng')

private def pickStrefRNoise (rng : StdGen) : Value × StdGen :=
  let (k, rng') := randNat rng 0 3
  let v : Value :=
    if k = 0 then .null
    else if k = 1 then intV 42
    else if k = 2 then .cell Cell.empty
    else .cell cellBit1
  (v, rng')

private def genStrefRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (c, rng2) := pickStrefRCell rng1
  if shape = 0 then
    (mkStrefRCase s!"fuzz/ok/top-only/cell-bits-{c.bits.size}"
      #[.builder Builder.empty, .cell c], rng2)
  else if shape = 1 then
    let (noise, rng3) := pickStrefRNoise rng2
    (mkStrefRCase s!"fuzz/ok/deep-stack/cell-bits-{c.bits.size}"
      #[noise, .builder Builder.empty, .cell c], rng3)
  else if shape = 2 then
    (mkStrefRCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 3 then
    (mkStrefRCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStrefRCase "fuzz/underflow/one-cell" #[.cell c], rng2)
  else if shape = 5 then
    (mkStrefRCase "fuzz/type/top-not-cell-null" #[.builder Builder.empty, .null], rng2)
  else if shape = 6 then
    (mkStrefRCase "fuzz/type/second-not-builder-null" #[.null, .cell c], rng2)
  else if shape = 7 then
    (mkStrefRCase "fuzz/type/reverse-order-misuse" #[.cell c, .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStrefRCase "fuzz/type/both-wrong-top-first" #[.null, intV 5], rng2)
  else if shape = 9 then
    let (refsBefore, rng3) := randNat rng2 0 3
    (mkStrefRProgramCase s!"fuzz/program/ok/builder-refs-{refsBefore}" #[]
      (mkStrefROnTopBuilderProgram refsBefore), rng3)
  else if shape = 10 then
    (mkStrefRProgramCase "fuzz/program/cellov/refs-4" #[] strefROverflowRefsProgram, rng2)
  else if shape = 11 then
    (mkStrefRProgramCase "fuzz/program/ok/full-bits-1023" #[] strefRFullBitsProgram, rng2)
  else
    (mkStrefRProgramCase "fuzz/program/cellov/refs-4-with-noise" #[]
      strefROverflowRefsWithNoiseProgram, rng2)

def suite : InstrSuite where
  id := strefRId
  unit := #[
    { name := "unit/direct/reverse-order-success-and-append"
      run := do
        let expected0 := appendRef Builder.empty Cell.empty
        expectOkStack "ok/basic-empty-cell"
          (runStrefRDirect #[.builder Builder.empty, .cell Cell.empty])
          #[.builder expected0]

        let expectedBit := appendRef Builder.empty cellBit1
        expectOkStack "ok/basic-nonempty-cell"
          (runStrefRDirect #[.builder Builder.empty, .cell cellBit1])
          #[.builder expectedBit]

        let prefBuilder : Builder :=
          { bits := natToBits 5 3
            refs := #[cellByteA5] }
        let expectedAppend := appendRef prefBuilder cellWithRef
        expectOkStack "ok/append-to-existing-refs"
          (runStrefRDirect #[.builder prefBuilder, .cell cellWithRef])
          #[.builder expectedAppend]

        let expectedFullBits := appendRef fullBuilder1023 cellByteA5
        expectOkStack "ok/full-bits-1023-still-allows-ref"
          (runStrefRDirect #[.builder fullBuilder1023, .cell cellByteA5])
          #[.builder expectedFullBits]

        let expectedDeep := appendRef Builder.empty cellBit1
        expectOkStack "ok/deep-stack-preserve-below"
          (runStrefRDirect #[.null, .builder Builder.empty, .cell cellBit1])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStrefRDirect #[]) .stkUnd
        expectErr "underflow/one-builder" (runStrefRDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-cell" (runStrefRDirect #[.cell Cell.empty]) .stkUnd
        expectErr "underflow/one-non-cell" (runStrefRDirect #[.null]) .stkUnd

        expectErr "type/top-not-cell-null"
          (runStrefRDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/top-not-cell-int"
          (runStrefRDirect #[.builder Builder.empty, intV 1]) .typeChk
        expectErr "type/second-not-builder-null"
          (runStrefRDirect #[.null, .cell Cell.empty]) .typeChk
        expectErr "type/second-not-builder-int"
          (runStrefRDirect #[intV 7, .cell cellBit1]) .typeChk
        expectErr "type/reverse-order-misuse"
          (runStrefRDirect #[.cell Cell.empty, .builder Builder.empty]) .typeChk
        expectErr "type/both-wrong-top-fails-first"
          (runStrefRDirect #[.null, intV 5]) .typeChk }
    ,
    { name := "unit/direct/cellov-on-ref-capacity"
      run := do
        let fullRefsBuilder : Builder :=
          { bits := #[]
            refs := #[Cell.empty, cellBit1, cellByteA5, cellWithRef] }
        expectErr "cellov/refs-full"
          (runStrefRDirect #[.builder fullRefsBuilder, .cell Cell.empty]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[strefRInstr, strefRqInstr, .stref, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/strefr" s0 strefRInstr 16
        let s2 ← expectDecodeStep "decode/strefrq-neighbor" s1 strefRqInstr 16
        let s3 ← expectDecodeStep "decode/stref-8bit-neighbor" s2 .stref 8
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-cellop-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStrefRDispatchFallback #[.null])
          #[.null, intV 53012] }
  ]
  oracle := #[
    mkStrefRCase "ok/empty-cell-top-only" #[.builder Builder.empty, .cell Cell.empty],
    mkStrefRCase "ok/nonempty-cell-1bit" #[.builder Builder.empty, .cell cellBit1],
    mkStrefRCase "ok/nonempty-cell-8bits" #[.builder Builder.empty, .cell cellByteA5],
    mkStrefRCase "ok/cell-with-ref" #[.builder Builder.empty, .cell cellWithRef],
    mkStrefRCase "ok/deep-stack-preserve-null" #[.null, .builder Builder.empty, .cell cellBit1],
    mkStrefRCase "ok/deep-stack-preserve-int" #[intV 99, .builder Builder.empty, .cell cellByteA5],
    mkStrefRProgramCase "ok/program/cell-with-bit-via-program" #[] strefRCellBitProgram,
    mkStrefRProgramCase "ok/program/builder-refs0-to1" #[] (mkStrefROnTopBuilderProgram 0),
    mkStrefRProgramCase "ok/program/builder-refs1-to2" #[] (mkStrefROnTopBuilderProgram 1),
    mkStrefRProgramCase "ok/program/builder-refs2-to3" #[] (mkStrefROnTopBuilderProgram 2),
    mkStrefRProgramCase "ok/program/builder-refs3-to4" #[] (mkStrefROnTopBuilderProgram 3),
    mkStrefRProgramCase "ok/program/full-bits-1023-still-add-ref" #[] strefRFullBitsProgram,
    mkStrefRProgramCase "ok/program/full-bits-with-noise" #[] strefRFullBitsWithNoiseProgram,

    mkStrefRCase "underflow/empty" #[],
    mkStrefRCase "underflow/one-builder" #[.builder Builder.empty],
    mkStrefRCase "underflow/one-cell" #[.cell Cell.empty],
    mkStrefRCase "underflow/one-non-cell" #[.null],

    mkStrefRCase "type/top-not-cell-null" #[.builder Builder.empty, .null],
    mkStrefRCase "type/top-not-cell-int" #[.builder Builder.empty, intV 1],
    mkStrefRCase "type/second-not-builder-null" #[.null, .cell Cell.empty],
    mkStrefRCase "type/second-not-builder-int" #[intV 7, .cell cellBit1],
    mkStrefRCase "type/reverse-order-misuse" #[.cell Cell.empty, .builder Builder.empty],
    mkStrefRCase "type/both-wrong-top-fails-first" #[.null, intV 5],

    mkStrefRProgramCase "cellov/program-builder-refs4" #[] strefROverflowRefsProgram,
    mkStrefRProgramCase "cellov/program-builder-refs4-with-noise" #[] strefROverflowRefsWithNoiseProgram,

    mkStrefRCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .cell cellBit1]
      #[.pushInt (.num strefRSetGasExact), .tonEnvOp .setGasLimit, strefRInstr],
    mkStrefRCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .cell cellBit1]
      #[.pushInt (.num strefRSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefRInstr]
  ]
  fuzz := #[
    { seed := 2026021014
      count := 320
      gen := genStrefRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STREFR
