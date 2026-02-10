import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STREFQ

/-
STREFQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stref.lean` (`.strefq`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf18` decode to `.strefq`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.strefq` encode as `0xcf18`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_ref(..., quiet=true)` and opcode table entry `0xcf18`).

Branch map used for this suite:
- Lean STREFQ path: 6 branch sites / 8 terminal outcomes
  (`match` dispatch; `checkUnderflow 2`; top pop as builder; second pop as cell;
   `canExtendBy(0,1)` split; quiet success pushes code `0`; quiet overflow re-pushes with code `-1`).
- C++ STREFQ path: 5 branch sites / 7 aligned outcomes
  (`check_underflow(2)`; `pop_builder`; `pop_cell`; `can_extend_by(0,1)`; quiet status behavior).

Key risk areas:
- non-reversed order must be stack `... cell builder` (builder on top);
- quiet overflow must restore stack as `... cell builder -1` (same operands, same order);
- success must produce `... builder 0` with appended reference;
- underflow/type errors happen before quiet status handling.
-/

private def strefqId : InstrId := { name := "STREFQ" }

private def strefqInstr : Instr := .strefq

private def mkStrefqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[strefqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStrefqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStrefqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStref strefqInstr stack

private def runStrefqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStref .add (VM.push (intV 436)) stack

private def strefqSetGasExact : Int :=
  computeExactGasBudget strefqInstr

private def strefqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne strefqInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkCellProgram (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ #[.endc]

private def appendOneRefToTopBuilder : Array Instr :=
  mkCellProgram 0 ++ #[.xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

private def mkBuilderWithBitsAndRefsProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkStrefqProgramBuilderBitsRefs
    (builderBits builderRefs cellBits : Nat)
    (builderX : IntVal := .num 0)
    (cellX : IntVal := .num 0) : Array Instr :=
  mkBuilderWithBitsAndRefsProgram builderBits builderRefs builderX
    ++ mkCellProgram cellBits cellX
    ++ #[.xchg0 1, strefqInstr]

private def mkStrefqProgramBuilderBitsRefsWithNoise
    (builderBits builderRefs cellBits : Nat)
    (builderX : IntVal := .num 0)
    (cellX : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStrefqProgramBuilderBitsRefs builderBits builderRefs cellBits builderX cellX

private def mkCellFromBitsValue (bits : Nat) (x : Nat) : Cell :=
  if bits = 0 then
    Cell.empty
  else
    (Builder.empty.storeBits (natToBits x bits)).finalize

private def cellBits1 : Cell :=
  mkCellFromBitsValue 1 1

private def cellBits3 : Cell :=
  mkCellFromBitsValue 3 5

private def cellBits8 : Cell :=
  mkCellFromBitsValue 8 173

private def cellBits16 : Cell :=
  mkCellFromBitsValue 16 65535

private def cellWithOneRef : Cell :=
  ({ Builder.empty with refs := #[Cell.empty] }).finalize

private def strefqProgramOkRefs3Cell1 : Array Instr :=
  mkStrefqProgramBuilderBitsRefs 0 3 1 (.num 0) (.num 1)

private def strefqProgramOkRefs2Cell3 : Array Instr :=
  mkStrefqProgramBuilderBitsRefs 0 2 3 (.num 0) (.num 5)

private def strefqProgramOkBits7Refs1Cell8 : Array Instr :=
  mkStrefqProgramBuilderBitsRefs 7 1 8 (.num 65) (.num 173)

private def strefqProgramOkRefs0Cell16 : Array Instr :=
  mkStrefqProgramBuilderBitsRefs 0 0 16 (.num 0) (.num 65535)

private def strefqProgramOkWithNoise : Array Instr :=
  mkStrefqProgramBuilderBitsRefsWithNoise 3 2 1 (.num 5) (.num 1)

private def strefqProgramCellovRefs4Cell1 : Array Instr :=
  mkStrefqProgramBuilderBitsRefs 0 4 1 (.num 0) (.num 1)

private def strefqProgramCellovRefs4Cell8 : Array Instr :=
  mkStrefqProgramBuilderBitsRefs 0 4 8 (.num 0) (.num 255)

private def strefqProgramCellovBits7Refs4 : Array Instr :=
  mkStrefqProgramBuilderBitsRefs 7 4 1 (.num 79) (.num 1)

private def strefqProgramCellovWithNoise : Array Instr :=
  mkStrefqProgramBuilderBitsRefsWithNoise 0 4 1 (.num 0) (.num 1)

private def strefqCellBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 12, 16]

private def pickStrefqCellBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (strefqCellBitsBoundaryPool.size - 1)
  (strefqCellBitsBoundaryPool[idx]!, rng')

private def pickStrefqCellBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickStrefqCellBitsBoundary rng1
  else
    randNat rng1 0 16

private def maxUnsignedNatByBits (bits : Nat) : Nat :=
  if bits = 0 then 0 else (1 <<< bits) - 1

private def pickUnsignedForBits (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    let hi := maxUnsignedNatByBits bits
    let (pick, rng1) := randNat rng0 0 4
    let x : Nat :=
      if pick = 0 then 0
      else if pick = 1 then 1
      else if pick = 2 then hi
      else if pick = 3 then
        if hi > 0 then hi - 1 else 0
      else
        if hi > 1 then hi / 2 else hi
    (x, rng1)

private def pickDirectCell (rng0 : StdGen) : Cell × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  if shape = 0 then
    (Cell.empty, rng1)
  else if shape = 1 then
    (cellWithOneRef, rng1)
  else
    let (bitsRaw, rng2) := pickStrefqCellBitsMixed rng1
    let bits := if bitsRaw = 0 then 1 else bitsRaw
    let (x, rng3) := pickUnsignedForBits bits rng2
    (mkCellFromBitsValue bits x, rng3)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else if pick = 2 then .cell Cell.empty
    else .cell cellWithOneRef
  (v, rng1)

private def genStrefqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    let (cell, rng2) := pickDirectCell rng1
    (mkStrefqCase "fuzz/ok/direct/top-only" #[.cell cell, .builder Builder.empty], rng2)
  else if shape = 1 then
    let (cell, rng2) := pickDirectCell rng1
    let (noise, rng3) := pickNoiseValue rng2
    (mkStrefqCase "fuzz/ok/direct/deep-stack" #[noise, .cell cell, .builder Builder.empty], rng3)
  else if shape = 2 then
    (mkStrefqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkStrefqCase "fuzz/underflow/one-item-builder" #[.builder Builder.empty], rng1)
  else if shape = 4 then
    let (cell, rng2) := pickDirectCell rng1
    (mkStrefqCase "fuzz/underflow/one-item-cell" #[.cell cell], rng2)
  else if shape = 5 then
    let (cell, rng2) := pickDirectCell rng1
    (mkStrefqCase "fuzz/type/top-not-builder" #[.cell cell, .null], rng2)
  else if shape = 6 then
    (mkStrefqCase "fuzz/type/second-not-cell" #[.null, .builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStrefqCase "fuzz/type/both-invalid-top-first" #[.null, intV 5], rng1)
  else if shape = 8 then
    let (cellBitsRaw, rng2) := pickStrefqCellBitsMixed rng1
    let cellBits := if cellBitsRaw = 0 then 1 else cellBitsRaw
    let (cellX, rng3) := pickUnsignedForBits cellBits rng2
    (mkStrefqProgramCase s!"fuzz/quiet-cellov/refs4/cellbits-{cellBits}" #[]
      (mkStrefqProgramBuilderBitsRefs 0 4 cellBits (.num 0) (.num (Int.ofNat cellX))), rng3)
  else if shape = 9 then
    let (cellBitsRaw, rng2) := pickStrefqCellBitsMixed rng1
    let cellBits := if cellBitsRaw = 0 then 1 else cellBitsRaw
    let (cellX, rng3) := pickUnsignedForBits cellBits rng2
    (mkStrefqProgramCase s!"fuzz/quiet-cellov/refs4-noise/cellbits-{cellBits}" #[]
      (mkStrefqProgramBuilderBitsRefsWithNoise 0 4 cellBits (.num 0) (.num (Int.ofNat cellX))), rng3)
  else if shape = 10 then
    let (cellBitsRaw, rng2) := pickStrefqCellBitsMixed rng1
    let cellBits := if cellBitsRaw = 0 then 1 else cellBitsRaw
    let (cellX, rng3) := pickUnsignedForBits cellBits rng2
    (mkStrefqProgramCase s!"fuzz/ok/program/refs3/cellbits-{cellBits}" #[]
      (mkStrefqProgramBuilderBitsRefs 0 3 cellBits (.num 0) (.num (Int.ofNat cellX))), rng3)
  else if shape = 11 then
    let (builderBits, rng2) := pickStrefqCellBitsMixed rng1
    let (builderX, rng3) := pickUnsignedForBits (if builderBits = 0 then 1 else builderBits) rng2
    let (cellBitsRaw, rng4) := pickStrefqCellBitsMixed rng3
    let cellBits := if cellBitsRaw = 0 then 1 else cellBitsRaw
    let (cellX, rng5) := pickUnsignedForBits cellBits rng4
    (mkStrefqProgramCase
      s!"fuzz/ok/program/bits-and-refs/bits-{builderBits}-cellbits-{cellBits}"
      #[]
      (mkStrefqProgramBuilderBitsRefs builderBits 2 cellBits
        (.num (Int.ofNat builderX)) (.num (Int.ofNat cellX))), rng5)
  else if shape = 12 then
    let (cell, rng2) := pickDirectCell rng1
    (mkStrefqCase "fuzz/gas/exact"
      #[.cell cell, .builder Builder.empty]
      #[.pushInt (.num strefqSetGasExact), .tonEnvOp .setGasLimit, strefqInstr], rng2)
  else
    let (cell, rng2) := pickDirectCell rng1
    (mkStrefqCase "fuzz/gas/exact-minus-one"
      #[.cell cell, .builder Builder.empty]
      #[.pushInt (.num strefqSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefqInstr], rng2)

def suite : InstrSuite where
  id := strefqId
  unit := #[
    { name := "unit/direct/success-stack-order-and-code0"
      run := do
        let expectedEmpty : Builder := { Builder.empty with refs := #[cellBits1] }
        expectOkStack "ok/store-into-empty-builder"
          (runStrefqDirect #[.cell cellBits1, .builder Builder.empty])
          #[.builder expectedEmpty, intV 0]

        let bWithBitsAndRefs : Builder :=
          { (Builder.empty.storeBits (natToBits 5 3)) with refs := #[cellBits1, cellBits3] }
        let expectedAppend : Builder := { bWithBitsAndRefs with refs := bWithBitsAndRefs.refs.push cellWithOneRef }
        expectOkStack "ok/append-ref-preserve-bits-and-old-refs"
          (runStrefqDirect #[.cell cellWithOneRef, .builder bWithBitsAndRefs])
          #[.builder expectedAppend, intV 0]

        let threeRefs : Builder := { Builder.empty with refs := #[cellBits1, cellBits3, cellWithOneRef] }
        let expectedFourth : Builder := { threeRefs with refs := threeRefs.refs.push cellBits8 }
        expectOkStack "ok/builder-3refs-to-4refs"
          (runStrefqDirect #[.cell cellBits8, .builder threeRefs])
          #[.builder expectedFourth, intV 0]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStrefqDirect #[.null, .cell cellBits16, .builder Builder.empty])
          #[.null, .builder { Builder.empty with refs := #[cellBits16] }, intV 0] }
    ,
    { name := "unit/direct/quiet-cellov-returns-code-minus1"
      run := do
        let fullRefsBuilder : Builder :=
          { Builder.empty with refs := #[cellBits1, cellBits3, cellWithOneRef, cellBits8] }
        expectOkStack "quiet-cellov/refs-full"
          (runStrefqDirect #[.cell cellBits16, .builder fullRefsBuilder])
          #[.cell cellBits16, .builder fullRefsBuilder, intV (-1)]
        expectOkStack "quiet-cellov/preserve-below"
          (runStrefqDirect #[.null, .cell cellWithOneRef, .builder fullRefsBuilder])
          #[.null, .cell cellWithOneRef, .builder fullRefsBuilder, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStrefqDirect #[]) .stkUnd
        expectErr "underflow/one-item-builder" (runStrefqDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-item-cell" (runStrefqDirect #[.cell Cell.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStrefqDirect #[.cell cellBits1, .null]) .typeChk
        expectErr "type/second-not-cell"
          (runStrefqDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/top-invalid-wins"
          (runStrefqDirect #[.null, intV 9]) .typeChk
        expectErr "type/top-builder-then-cell-type"
          (runStrefqDirect #[intV 9, .builder Builder.empty]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[strefqInstr, strefqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/strefq-1" s0 strefqInstr 16
        let s2 ← expectDecodeStep "decode/strefq-2" s1 strefqInstr 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits (natToBits 0xcf18 16 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-cf18" raw strefqInstr 16
        let raw2 ← expectDecodeStep "decode/raw-tail-add" raw1 .add 8
        if raw2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {raw2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStrefqDispatchFallback #[.null])
          #[.null, intV 436] }
  ]
  oracle := #[
    mkStrefqCase "ok/direct/store-empty-cell" #[.cell Cell.empty, .builder Builder.empty],
    mkStrefqCase "ok/direct/store-nonempty-cell" #[.cell cellBits3, .builder Builder.empty],
    mkStrefqCase "ok/direct/store-cell-with-ref" #[.cell cellWithOneRef, .builder Builder.empty],
    mkStrefqCase "ok/direct/deep-stack-null" #[.null, .cell cellBits1, .builder Builder.empty],
    mkStrefqCase "ok/direct/deep-stack-int-noise" #[intV 11, .cell cellBits8, .builder Builder.empty],

    mkStrefqProgramCase "ok/program/refs3-cell1" #[] strefqProgramOkRefs3Cell1,
    mkStrefqProgramCase "ok/program/refs2-cell3" #[] strefqProgramOkRefs2Cell3,
    mkStrefqProgramCase "ok/program/bits7-refs1-cell8" #[] strefqProgramOkBits7Refs1Cell8,
    mkStrefqProgramCase "ok/program/refs0-cell16" #[] strefqProgramOkRefs0Cell16,
    mkStrefqProgramCase "ok/program/with-noise" #[] strefqProgramOkWithNoise,
    mkStrefqProgramCase "ok/program/bits4-refs3-cell4" #[]
      (mkStrefqProgramBuilderBitsRefs 4 3 4 (.num 9) (.num 7)),
    mkStrefqProgramCase "ok/program/bits0-refs1-cell0" #[]
      (mkStrefqProgramBuilderBitsRefs 0 1 0 (.num 0) (.num 0)),

    mkStrefqCase "underflow/empty" #[],
    mkStrefqCase "underflow/one-item-builder" #[.builder Builder.empty],
    mkStrefqCase "underflow/one-item-cell" #[.cell Cell.empty],
    mkStrefqCase "type/top-not-builder" #[.cell cellBits1, .null],
    mkStrefqCase "type/second-not-cell" #[.null, .builder Builder.empty],
    mkStrefqCase "type/top-invalid-wins" #[.null, intV 5],

    mkStrefqCase "gas/exact-cost-succeeds" #[.cell cellBits8, .builder Builder.empty]
      #[.pushInt (.num strefqSetGasExact), .tonEnvOp .setGasLimit, strefqInstr],
    mkStrefqCase "gas/exact-minus-one-out-of-gas" #[.cell cellBits8, .builder Builder.empty]
      #[.pushInt (.num strefqSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefqInstr],

    mkStrefqProgramCase "quiet-cellov/program/refs4-cell1" #[] strefqProgramCellovRefs4Cell1,
    mkStrefqProgramCase "quiet-cellov/program/refs4-cell8" #[] strefqProgramCellovRefs4Cell8,
    mkStrefqProgramCase "quiet-cellov/program/bits7-refs4" #[] strefqProgramCellovBits7Refs4,
    mkStrefqProgramCase "quiet-cellov/program/with-noise" #[] strefqProgramCellovWithNoise
  ]
  fuzz := #[
    { seed := 2026021018
      count := 320
      gen := genStrefqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STREFQ
