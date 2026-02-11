import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STREFRQ

/-
STREFRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.strefR quiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf1c` decode to `.cellOp (.strefR true)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.strefR true` encode as `0xcf1c`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_ref_rev(..., quiet=true)` and opcode table entry `0xcf1c`).

Branch map used for this suite (quiet=true, reverse-order store):
- Lean STREFRQ path: 5 branch sites / 7 terminal outcomes
  (`checkUnderflow 2`; pop top as cell; pop second as builder; `canExtendBy(0,1)` split;
   success pushes `builder' 0`; quiet overflow re-pushes `builder cell -1`).
- C++ STREFRQ path: 4 branch sites / 6 aligned outcomes
  (`check_underflow(2)`; `pop_cell`; `pop_builder`; `can_extend_by(0,1)` with quiet status).

Key risk areas:
- reverse operand order must be `... builder cell` (cell on top);
- type-check order follows reverse pops (cell type first, then builder type);
- quiet overflow must not throw and must preserve operand order as `builder cell -1`;
- ref-capacity overflow is independent of bit usage (`1023 bits + 3 refs` still succeeds, `+4 refs` fails quietly).
-/

private def strefRqId : InstrId := { name := "STREFRQ" }

private def strefRqInstr : Instr :=
  .cellOp (.strefR true)

private def strefRInstr : Instr :=
  .cellOp (.strefR false)

private def execCellOpExtInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpExt op next
  | _ => next

private def mkStrefRqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[strefRqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefRqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStrefRqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefRqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStrefRqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpExtInstr strefRqInstr stack

private def runStrefRqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpExtInstr .add (VM.push (intV 53014)) stack

private def strefRqSetGasExact : Int :=
  computeExactGasBudget strefRqInstr

private def strefRqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne strefRqInstr

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

private def mkStrefRqOnTopBuilderProgram (refsBefore : Nat) : Array Instr :=
  mkBuilderWithRefsProgram refsBefore ++ #[.newc, .endc, strefRqInstr]

private def strefRqCellBitProgram : Array Instr :=
  #[
    .newc,
    .newc,
    .pushInt (.num 1), .xchg0 1, .stu 1,
    .endc,
    strefRqInstr
  ]

private def strefRqFullBitsProgram : Array Instr :=
  build1023WithFixed .stu ++ #[.newc, .endc, strefRqInstr]

private def strefRqFullBitsWithNoiseProgram : Array Instr :=
  #[.pushNull] ++ strefRqFullBitsProgram

private def strefRqSuccessFullBitsRefs3Program : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder 3 ++ #[.newc, .endc, strefRqInstr]

private def strefRqOverflowRefsProgram : Array Instr :=
  mkStrefRqOnTopBuilderProgram 4

private def strefRqOverflowRefsWithNoiseProgram : Array Instr :=
  #[.pushNull] ++ strefRqOverflowRefsProgram

private def strefRqOverflowFullBitsRefs4Program : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder 4 ++ #[.newc, .endc, strefRqInstr]

private def strefRqOverflowFullBitsRefs4WithNoiseProgram : Array Instr :=
  #[.pushNull] ++ strefRqOverflowFullBitsRefs4Program

private def strefRqCellPool : Array Cell :=
  #[Cell.empty, cellBit1, cellByteA5, cellWithRef]

private def pickStrefRqCell (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (strefRqCellPool.size - 1)
  (strefRqCellPool[idx]!, rng')

private def pickStrefRqNoise (rng : StdGen) : Value × StdGen :=
  let (k, rng') := randNat rng 0 3
  let noise : Value :=
    if k = 0 then .null
    else if k = 1 then intV 39
    else if k = 2 then .cell Cell.empty
    else .cell cellBit1
  (noise, rng')

private def genStrefRqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (c, rng2) := pickStrefRqCell rng1
  if shape = 0 then
    (mkStrefRqCase s!"fuzz/ok/top-only/cell-bits-{c.bits.size}"
      #[.builder Builder.empty, .cell c], rng2)
  else if shape = 1 then
    let (noise, rng3) := pickStrefRqNoise rng2
    (mkStrefRqCase s!"fuzz/ok/deep-stack/cell-bits-{c.bits.size}"
      #[noise, .builder Builder.empty, .cell c], rng3)
  else if shape = 2 then
    (mkStrefRqCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 3 then
    (mkStrefRqCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStrefRqCase "fuzz/underflow/one-cell" #[.cell c], rng2)
  else if shape = 5 then
    (mkStrefRqCase "fuzz/type/top-not-cell-null" #[.builder Builder.empty, .null], rng2)
  else if shape = 6 then
    (mkStrefRqCase "fuzz/type/second-not-builder-null" #[.null, .cell c], rng2)
  else if shape = 7 then
    (mkStrefRqCase "fuzz/type/reverse-order-misuse" #[.cell c, .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStrefRqCase "fuzz/type/both-wrong-top-first" #[.null, intV 5], rng2)
  else if shape = 9 then
    let (refsBefore, rng3) := randNat rng2 0 3
    (mkStrefRqProgramCase s!"fuzz/program/ok/builder-refs-{refsBefore}" #[]
      (mkStrefRqOnTopBuilderProgram refsBefore), rng3)
  else if shape = 10 then
    (mkStrefRqProgramCase "fuzz/program/quiet-cellov/refs-4" #[] strefRqOverflowRefsProgram, rng2)
  else if shape = 11 then
    (mkStrefRqProgramCase "fuzz/program/ok/full-bits-1023-refs3" #[] strefRqSuccessFullBitsRefs3Program, rng2)
  else if shape = 12 then
    (mkStrefRqProgramCase "fuzz/program/quiet-cellov/full-bits-refs4" #[] strefRqOverflowFullBitsRefs4Program, rng2)
  else if shape = 13 then
    (mkStrefRqCase "fuzz/gas/exact"
      #[.builder Builder.empty, .cell c]
      #[.pushInt (.num strefRqSetGasExact), .tonEnvOp .setGasLimit, strefRqInstr], rng2)
  else
    (mkStrefRqCase "fuzz/gas/exact-minus-one"
      #[.builder Builder.empty, .cell c]
      #[.pushInt (.num strefRqSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefRqInstr], rng2)

def suite : InstrSuite where
  id := strefRqId
  unit := #[
    { name := "unit/direct/reverse-order-success-and-code0"
      run := do
        let expected0 := appendRef Builder.empty Cell.empty
        expectOkStack "ok/basic-empty-cell"
          (runStrefRqDirect #[.builder Builder.empty, .cell Cell.empty])
          #[.builder expected0, intV 0]

        let expectedBit := appendRef Builder.empty cellBit1
        expectOkStack "ok/basic-nonempty-cell"
          (runStrefRqDirect #[.builder Builder.empty, .cell cellBit1])
          #[.builder expectedBit, intV 0]

        let prefBuilder : Builder :=
          { bits := natToBits 5 3
            refs := #[cellByteA5] }
        let expectedAppend := appendRef prefBuilder cellWithRef
        expectOkStack "ok/append-to-existing-refs"
          (runStrefRqDirect #[.builder prefBuilder, .cell cellWithRef])
          #[.builder expectedAppend, intV 0]

        let expectedFullBits := appendRef fullBuilder1023 cellByteA5
        expectOkStack "ok/full-bits-1023-still-allows-ref"
          (runStrefRqDirect #[.builder fullBuilder1023, .cell cellByteA5])
          #[.builder expectedFullBits, intV 0]

        let expectedDeep := appendRef Builder.empty cellBit1
        expectOkStack "ok/deep-stack-preserve-below"
          (runStrefRqDirect #[.null, .builder Builder.empty, .cell cellBit1])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-cellov-status-minus1"
      run := do
        let refs4 : Builder :=
          { bits := #[]
            refs := #[Cell.empty, cellBit1, cellByteA5, cellWithRef] }
        expectOkStack "quiet-cellov/refs-full"
          (runStrefRqDirect #[.builder refs4, .cell cellBit1])
          #[.builder refs4, .cell cellBit1, intV (-1)]

        let refs4FullBits : Builder :=
          { fullBuilder1023 with refs := #[Cell.empty, cellBit1, cellByteA5, cellWithRef] }
        expectOkStack "quiet-cellov/refs-full-even-when-bits-full"
          (runStrefRqDirect #[.builder refs4FullBits, .cell Cell.empty])
          #[.builder refs4FullBits, .cell Cell.empty, intV (-1)]

        expectOkStack "quiet-cellov/deep-stack-preserve-below"
          (runStrefRqDirect #[.null, .builder refs4, .cell cellWithRef])
          #[.null, .builder refs4, .cell cellWithRef, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStrefRqDirect #[]) .stkUnd
        expectErr "underflow/one-builder" (runStrefRqDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-cell" (runStrefRqDirect #[.cell Cell.empty]) .stkUnd
        expectErr "underflow/one-non-cell" (runStrefRqDirect #[.null]) .stkUnd

        expectErr "type/top-not-cell-null"
          (runStrefRqDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/top-not-cell-int"
          (runStrefRqDirect #[.builder Builder.empty, intV 1]) .typeChk
        expectErr "type/second-not-builder-null"
          (runStrefRqDirect #[.null, .cell Cell.empty]) .typeChk
        expectErr "type/second-not-builder-int"
          (runStrefRqDirect #[intV 7, .cell cellBit1]) .typeChk
        expectErr "type/reverse-order-misuse"
          (runStrefRqDirect #[.cell Cell.empty, .builder Builder.empty]) .typeChk
        expectErr "type/both-wrong-top-fails-first"
          (runStrefRqDirect #[.null, intV 5]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [strefRqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits 0xcf1c 16 then
          pure ()
        else
          throw (IO.userError s!"strefrq canonical encode mismatch: got bits {canonicalOnly.bits}")

        let program : Array Instr := #[strefRqInstr, strefRInstr, .strefq, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/strefrq" s0 strefRqInstr 16
        let s2 ← expectDecodeStep "decode/strefr-neighbor" s1 strefRInstr 16
        let s3 ← expectDecodeStep "decode/strefq-neighbor" s2 .strefq 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits (natToBits 0xcf1c 16 ++ natToBits 0xcf14 16 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-cf1c" raw strefRqInstr 16
        let raw2 ← expectDecodeStep "decode/raw-cf14-neighbor" raw1 strefRInstr 16
        let raw3 ← expectDecodeStep "decode/raw-tail-add" raw2 .add 8
        if raw3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {raw3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-cellop-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStrefRqDispatchFallback #[.null])
          #[.null, intV 53014] }
  ]
  oracle := #[
    mkStrefRqCase "ok/empty-cell-top-only" #[.builder Builder.empty, .cell Cell.empty],
    mkStrefRqCase "ok/nonempty-cell-1bit" #[.builder Builder.empty, .cell cellBit1],
    mkStrefRqCase "ok/nonempty-cell-8bits" #[.builder Builder.empty, .cell cellByteA5],
    mkStrefRqCase "ok/cell-with-ref" #[.builder Builder.empty, .cell cellWithRef],
    mkStrefRqCase "ok/deep-stack-preserve-null" #[.null, .builder Builder.empty, .cell cellBit1],
    mkStrefRqCase "ok/deep-stack-preserve-int" #[intV 99, .builder Builder.empty, .cell cellByteA5],

    mkStrefRqProgramCase "ok/program/cell-with-bit-via-program" #[] strefRqCellBitProgram,
    mkStrefRqProgramCase "ok/program/builder-refs0-to1" #[] (mkStrefRqOnTopBuilderProgram 0),
    mkStrefRqProgramCase "ok/program/builder-refs1-to2" #[] (mkStrefRqOnTopBuilderProgram 1),
    mkStrefRqProgramCase "ok/program/builder-refs2-to3" #[] (mkStrefRqOnTopBuilderProgram 2),
    mkStrefRqProgramCase "ok/program/builder-refs3-to4" #[] (mkStrefRqOnTopBuilderProgram 3),
    mkStrefRqProgramCase "ok/program/full-bits-1023-still-add-ref" #[] strefRqFullBitsProgram,
    mkStrefRqProgramCase "ok/program/full-bits-refs3-to4" #[] strefRqSuccessFullBitsRefs3Program,
    mkStrefRqProgramCase "ok/program/full-bits-with-noise" #[] strefRqFullBitsWithNoiseProgram,

    mkStrefRqCase "underflow/empty" #[],
    mkStrefRqCase "underflow/one-builder" #[.builder Builder.empty],
    mkStrefRqCase "underflow/one-cell" #[.cell Cell.empty],
    mkStrefRqCase "underflow/one-non-cell" #[.null],

    mkStrefRqCase "type/top-not-cell-null" #[.builder Builder.empty, .null],
    mkStrefRqCase "type/top-not-cell-int" #[.builder Builder.empty, intV 1],
    mkStrefRqCase "type/second-not-builder-null" #[.null, .cell Cell.empty],
    mkStrefRqCase "type/second-not-builder-int" #[intV 7, .cell cellBit1],
    mkStrefRqCase "type/reverse-order-misuse" #[.cell Cell.empty, .builder Builder.empty],
    mkStrefRqCase "type/both-wrong-top-fails-first" #[.null, intV 5],

    mkStrefRqProgramCase "quiet-cellov/program-builder-refs4" #[] strefRqOverflowRefsProgram,
    mkStrefRqProgramCase "quiet-cellov/program-builder-refs4-with-noise" #[] strefRqOverflowRefsWithNoiseProgram,
    mkStrefRqProgramCase "quiet-cellov/program-full-bits-refs4" #[] strefRqOverflowFullBitsRefs4Program,
    mkStrefRqProgramCase "quiet-cellov/program-full-bits-refs4-with-noise" #[] strefRqOverflowFullBitsRefs4WithNoiseProgram,

    mkStrefRqCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .cell cellBit1]
      #[.pushInt (.num strefRqSetGasExact), .tonEnvOp .setGasLimit, strefRqInstr],
    mkStrefRqCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .cell cellBit1]
      #[.pushInt (.num strefRqSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefRqInstr]
  ]
  fuzz := #[
    { seed := 2026021022
      count := 500
      gen := genStrefRqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STREFRQ
