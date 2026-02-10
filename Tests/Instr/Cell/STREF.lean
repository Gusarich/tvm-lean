import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STREF

/-
STREF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stref.lean` (`.stref`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcc`, `0xcf10` decode to `.stref`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.stref` assemble as canonical `0xcc`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_ref`, non-quiet path used by `STREF` opcodes `0xcc` and `0xcf10`).

Branch map used for this suite:
- Lean STREF path: 5 branch sites / 6 terminal outcomes
  (dispatch guard; `checkUnderflow 2`; top builder pop/type; second cell pop/type;
   `canExtendBy 0 1`; success or `cellOv`).
- C++ STREF path: 4 branch sites / 5 aligned outcomes
  (`check_underflow(2)`; `pop_builder`; `pop_cell`; `can_extend_by`; success or `cell_ov`).

Key risk areas:
- non-reversed stack order is `... cell builder` (builder on top);
- success preserves existing builder bits/refs and appends exactly one new reference at the tail;
- overflow is ref-capacity based for STREF (`+0` bits, `+1` ref), including full-bit builders;
- both opcodes (`0xcc` and alias `0xcf10`) must decode to `.stref`, while assembler emits canonical `0xcc`;
- exact gas edge for `PUSHINT n; SETGASLIMIT; STREF`.
-/

private def strefId : InstrId := { name := "STREF" }

private def strefInstr : Instr := .stref

private def mkStrefCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[strefInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStrefProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStrefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStref strefInstr stack

private def runStrefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStref .add (VM.push (intV 434)) stack

private def strefSetGasExact : Int :=
  computeExactGasBudget strefInstr

private def strefSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne strefInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def buildCellWithBitsProgram (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ #[.endc]

private def appendCellWithBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  buildCellWithBitsProgram bits x ++ #[.xchg0 1, strefInstr]

private def appendOneEmptyCellRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, strefInstr]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneEmptyCellRefToTopBuilder

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder refs

private def buildCellWithOneRefProgram : Array Instr :=
  #[.newc, .newc, .endc, .xchg0 1, strefInstr, .endc]

private def mkStrefProgramCellBits
    (cellBits : Nat)
    (cellX : IntVal := .num 0) : Array Instr :=
  buildCellWithBitsProgram cellBits cellX ++ #[.newc, strefInstr]

private def mkStrefProgramBuilderBitsCellBits
    (builderBits : Nat)
    (cellBits : Nat)
    (builderX : IntVal := .num 0)
    (cellX : IntVal := .num 0) : Array Instr :=
  #[.newc]
    ++ appendBitsToTopBuilder builderBits builderX
    ++ appendCellWithBitsToTopBuilder cellBits cellX

private def mkStrefProgramBuilderRefsCellBits
    (refs : Nat)
    (cellBits : Nat)
    (cellX : IntVal := .num 0) : Array Instr :=
  mkBuilderWithRefsProgram refs ++ appendCellWithBitsToTopBuilder cellBits cellX

private def mkStrefProgramBuilderRefsCellWithRef (refs : Nat) : Array Instr :=
  mkBuilderWithRefsProgram refs ++ buildCellWithOneRefProgram ++ #[.xchg0 1, strefInstr]

private def mkStrefCellOvProgramWithCellBits
    (cellBits : Nat)
    (cellX : IntVal := .num 0) : Array Instr :=
  mkBuilderWithRefsProgram 4 ++ buildCellWithBitsProgram cellBits cellX ++ #[.xchg0 1, strefInstr]

private def strefCellOvProgram : Array Instr :=
  mkStrefCellOvProgramWithCellBits 0

private def strefCellOvWithRefCellProgram : Array Instr :=
  mkBuilderWithRefsProgram 4 ++ buildCellWithOneRefProgram ++ #[.xchg0 1, strefInstr]

private def strefAppendProgram : Array Instr :=
  mkStrefProgramBuilderBitsCellBits 3 5 (.num 5) (.num 17)

private def strefAppendWithRefsProgram : Array Instr :=
  mkStrefProgramBuilderRefsCellBits 2 4 (.num 9)

private def strefCellWithRefProgram : Array Instr :=
  buildCellWithOneRefProgram ++ #[.newc, strefInstr]

private def strefFullBitsRefs3ThenStoreProgram : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder 3 ++ #[.newc, .endc, .xchg0 1, strefInstr]

private def strefBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 15]

private def pickStrefBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (strefBitsBoundaryPool.size - 1)
  (strefBitsBoundaryPool[idx]!, rng')

private def pickStrefBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickStrefBitsBoundary rng1
  else
    randNat rng1 0 15

private def pickCellPayloadForBits (bits : Nat) (rng : StdGen) : IntVal × StdGen :=
  if bits = 0 then
    (.num 0, rng)
  else
    let hi : Int := intPow2 bits - 1
    let (pick, rng') := randNat rng 0 4
    let x : Int :=
      if pick = 0 then 0
      else if pick = 1 then 1
      else if pick = 2 then hi
      else if pick = 3 then
        if hi > 0 then hi - 1 else 0
      else
        hi / 2
    (.num x, rng')

private def genStrefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    (mkStrefCase "fuzz/ok/direct/minimal" #[.cell Cell.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noisePick, rng2) := randNat rng1 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 91 else .cell Cell.empty
    (mkStrefCase "fuzz/ok/direct/deep-stack" #[noise, .cell Cell.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    (mkStrefCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkStrefCase "fuzz/underflow/one-cell" #[.cell Cell.empty], rng1)
  else if shape = 4 then
    (mkStrefCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkStrefCase "fuzz/type/top-not-builder" #[.cell Cell.empty, .null], rng1)
  else if shape = 6 then
    (mkStrefCase "fuzz/type/second-not-cell" #[.null, .builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStrefCase "fuzz/type/both-wrong" #[intV 1, .null], rng1)
  else if shape = 8 then
    let (cellBits, rng2) := pickStrefBitsMixed rng1
    let (cellX, rng3) := pickCellPayloadForBits cellBits rng2
    (mkStrefProgramCase s!"fuzz/ok/program/cell-bits-{cellBits}" #[]
      (mkStrefProgramCellBits cellBits cellX), rng3)
  else if shape = 9 then
    let (builderBits, rng2) := pickStrefBitsMixed rng1
    let (cellBits, rng3) := pickStrefBitsMixed rng2
    let (builderX, rng4) := pickCellPayloadForBits builderBits rng3
    let (cellX, rng5) := pickCellPayloadForBits cellBits rng4
    (mkStrefProgramCase s!"fuzz/ok/program/builder-bits-{builderBits}-cell-bits-{cellBits}" #[]
      (mkStrefProgramBuilderBitsCellBits builderBits cellBits builderX cellX), rng5)
  else if shape = 10 then
    let (refs, rng2) := randNat rng1 0 3
    let (cellBits, rng3) := pickStrefBitsMixed rng2
    let (cellX, rng4) := pickCellPayloadForBits cellBits rng3
    (mkStrefProgramCase s!"fuzz/ok/program/refs-{refs}-cell-bits-{cellBits}" #[]
      (mkStrefProgramBuilderRefsCellBits refs cellBits cellX), rng4)
  else if shape = 11 then
    let (cellBits, rng2) := pickStrefBitsMixed rng1
    let (cellX, rng3) := pickCellPayloadForBits cellBits rng2
    (mkStrefProgramCase s!"fuzz/cellov/program/refs4-cell-bits-{cellBits}" #[]
      (mkStrefCellOvProgramWithCellBits cellBits cellX), rng3)
  else if shape = 12 then
    (mkStrefProgramCase "fuzz/ok/program/full-bits-refs3-then-store" #[] strefFullBitsRefs3ThenStoreProgram, rng1)
  else if shape = 13 then
    let (useExact, rng2) := randBool rng1
    if useExact then
      (mkStrefCase "fuzz/gas/exact" #[.cell Cell.empty, .builder Builder.empty]
        #[.pushInt (.num strefSetGasExact), .tonEnvOp .setGasLimit, strefInstr], rng2)
    else
      (mkStrefCase "fuzz/gas/exact-minus-one" #[.cell Cell.empty, .builder Builder.empty]
        #[.pushInt (.num strefSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefInstr], rng2)
  else
    (mkStrefProgramCase "fuzz/cellov/program/refs4-cell-with-ref" #[] strefCellOvWithRefCellProgram, rng1)

def suite : InstrSuite where
  id := strefId
  unit := #[
    { name := "unit/direct/stack-order-and-success"
      run := do
        let emptyExpected : Builder := { Builder.empty with refs := #[Cell.empty] }
        expectOkStack "ok/minimal/empty-cell-empty-builder"
          (runStrefDirect #[.cell Cell.empty, .builder Builder.empty])
          #[.builder emptyExpected]

        let existingRef : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
        let sourceCell : Cell := Cell.mkOrdinary (natToBits 17 5) #[Cell.empty]
        let prefBuilder : Builder := { bits := natToBits 6 3, refs := #[existingRef] }
        let expectedPref : Builder := { bits := prefBuilder.bits, refs := prefBuilder.refs.push sourceCell }
        expectOkStack "ok/non-empty-builder-and-cell-append-tail"
          (runStrefDirect #[.cell sourceCell, .builder prefBuilder])
          #[.builder expectedPref]

        let boundaryBuilder : Builder :=
          { bits := fullBuilder1023.bits
            refs := #[Cell.empty, Cell.empty, Cell.empty] }
        let boundaryExpected : Builder := { boundaryBuilder with refs := boundaryBuilder.refs.push Cell.empty }
        expectOkStack "ok/full-bits-with-three-refs-still-accepts-one-ref"
          (runStrefDirect #[.cell Cell.empty, .builder boundaryBuilder])
          #[.builder boundaryExpected]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStrefDirect #[.null, .cell Cell.empty, .builder Builder.empty])
          #[.null, .builder emptyExpected] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStrefDirect #[]) .stkUnd
        expectErr "underflow/one-cell" (runStrefDirect #[.cell Cell.empty]) .stkUnd
        expectErr "underflow/one-builder" (runStrefDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStrefDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "type/second-not-cell"
          (runStrefDirect #[intV 7, .builder Builder.empty]) .typeChk
        expectErr "type/reversed-args-builder-below-cell-top"
          (runStrefDirect #[.builder Builder.empty, .cell Cell.empty]) .typeChk
        expectErr "type/both-wrong-top-first"
          (runStrefDirect #[intV 1, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-ref-capacity"
      run := do
        let refs4 : Array Cell := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty]
        let bRef4 : Builder := { bits := #[], refs := refs4 }
        expectErr "cellov/refs4-empty-bits"
          (runStrefDirect #[.cell Cell.empty, .builder bRef4]) .cellOv

        let bFullRef4 : Builder := { bits := fullBuilder1023.bits, refs := refs4 }
        expectErr "cellov/refs4-full-bits"
          (runStrefDirect #[.cell Cell.empty, .builder bFullRef4]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-with-alias"
      run := do
        let canonicalOnly ←
          match assembleCp0 [strefInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits 0xcc 8 then
          pure ()
        else
          throw (IO.userError s!"stref canonical encode mismatch: got bits {canonicalOnly.bits}")

        let canonicalProgram : Array Instr := #[strefInstr, .add]
        let canonicalCode ←
          match assembleCp0 canonicalProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical sequence failed: {e}")
        let s0 := Slice.ofCell canonicalCode
        let s1 ← expectDecodeStep "decode/canonical-cc" s0 strefInstr 8
        let s2 ← expectDecodeStep "decode/canonical-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/canonical-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let aliasCode : Cell := Cell.mkOrdinary (natToBits 0xcf10 16 ++ addCell.bits) #[]
        let a0 := Slice.ofCell aliasCode
        let a1 ← expectDecodeStep "decode/alias-cf10" a0 strefInstr 16
        let a2 ← expectDecodeStep "decode/alias-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/alias-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStrefDispatchFallback #[.null])
          #[.null, intV 434] }
  ]
  oracle := #[
    mkStrefCase "ok/empty-cell-empty-builder" #[.cell Cell.empty, .builder Builder.empty],
    mkStrefCase "ok/deep-stack-preserve-below" #[.null, .cell Cell.empty, .builder Builder.empty],

    mkStrefProgramCase "ok/program/cell-bits-0" #[] (mkStrefProgramCellBits 0),
    mkStrefProgramCase "ok/program/cell-bits-1" #[] (mkStrefProgramCellBits 1 (.num 1)),
    mkStrefProgramCase "ok/program/cell-bits-8" #[] (mkStrefProgramCellBits 8 (.num 170)),
    mkStrefProgramCase "ok/program/cell-bits-15" #[] (mkStrefProgramCellBits 15 (.num 177)),
    mkStrefProgramCase "ok/program/builder-bits3-cell-bits5" #[] strefAppendProgram,
    mkStrefProgramCase "ok/program/builder-bits7-cell-bits2" #[]
      (mkStrefProgramBuilderBitsCellBits 7 2 (.num 77) (.num 3)),
    mkStrefProgramCase "ok/program/builder-refs0-cell-bits4" #[] (mkStrefProgramBuilderRefsCellBits 0 4 (.num 9)),
    mkStrefProgramCase "ok/program/builder-refs2-cell-bits4" #[] strefAppendWithRefsProgram,
    mkStrefProgramCase "ok/program/builder-refs3-cell-empty" #[] (mkStrefProgramBuilderRefsCellBits 3 0),
    mkStrefProgramCase "ok/program/full-bits-refs3-then-store" #[] strefFullBitsRefs3ThenStoreProgram,
    mkStrefProgramCase "ok/program/cell-with-ref" #[] strefCellWithRefProgram,
    mkStrefProgramCase "ok/program/builder-refs1-cell-with-ref" #[] (mkStrefProgramBuilderRefsCellWithRef 1),
    mkStrefProgramCase "ok/program/noise-below-preserved" #[] (#[.pushNull] ++ mkStrefProgramCellBits 6 (.num 41)),

    mkStrefCase "underflow/empty" #[],
    mkStrefCase "underflow/one-cell" #[.cell Cell.empty],
    mkStrefCase "underflow/one-builder" #[.builder Builder.empty],
    mkStrefCase "type/top-not-builder" #[.cell Cell.empty, .null],
    mkStrefCase "type/second-not-cell" #[.null, .builder Builder.empty],
    mkStrefCase "type/both-wrong-top-first" #[intV 1, .null],

    mkStrefCase "gas/exact-cost-succeeds" #[.cell Cell.empty, .builder Builder.empty]
      #[.pushInt (.num strefSetGasExact), .tonEnvOp .setGasLimit, strefInstr],
    mkStrefCase "gas/exact-minus-one-out-of-gas" #[.cell Cell.empty, .builder Builder.empty]
      #[.pushInt (.num strefSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefInstr],

    mkStrefProgramCase "cellov/program/refs4-empty-cell" #[] strefCellOvProgram,
    mkStrefProgramCase "cellov/program/refs4-cell-bits1" #[] (mkStrefCellOvProgramWithCellBits 1 (.num 1)),
    mkStrefProgramCase "cellov/program/refs4-cell-bits8" #[] (mkStrefCellOvProgramWithCellBits 8 (.num 255)),
    mkStrefProgramCase "cellov/program/refs4-cell-with-ref" #[] strefCellOvWithRefCellProgram,
    mkStrefProgramCase "cellov/program/noise-below-refs4" #[] (#[.pushNull] ++ strefCellOvProgram)
  ]
  fuzz := #[
    { seed := 2026021003
      count := 320
      gen := genStrefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STREF
