import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STREF_ALT

/-
STREF_ALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stref.lean` (`.stref`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xcf10` decodes to `.stref`; canonical `0xcc` decodes to `.stref`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.stref` assembles canonically as `0xcc`, not `0xcf10`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_ref(..., quiet=false)` for both opcode entries `0xcc` and `0xcf10`).

Branch map used for this suite:
- Lean STREF path: 5 branch sites / 6 terminal outcomes
  (dispatch guard; `checkUnderflow 2`; top builder pop/type; second cell pop/type;
   `canExtendBy 0 1`; success or `cellOv`).
- C++ STREF path: 4 branch sites / 5 aligned outcomes
  (`check_underflow(2)`; `pop_builder`; `pop_cell`; `can_extend_by(0,1)`;
   success or `cell_ov`).

Key risk areas:
- non-reversed stack order is `... cell builder` (builder on top);
- success preserves builder bits/refs and appends exactly one new reference at the tail;
- overflow is strictly reference-capacity based (`+0` bits, `+1` ref), including full-bit builders;
- alias opcode `0xcf10` must decode to `.stref` and execute identically to canonical `0xcc`;
- assembler must continue emitting canonical `0xcc` for `.stref`;
- exact gas threshold edge for `PUSHINT n; SETGASLIMIT; STREF`.
-/

private def strefAltId : InstrId := { name := "STREF_ALT" }

private def strefInstr : Instr := .stref

private def strefAltAliasOpcode : Nat := 0xcf10

private def strefCanonicalOpcode : Nat := 0xcc

private def mkStrefAltCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[strefInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStrefAltProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := strefAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStrefAltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStref strefInstr stack

private def runStrefAltDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStref .add (VM.push (intV 53008)) stack

private def strefAltSetGasExact : Int :=
  computeExactGasBudget strefInstr

private def strefAltSetGasExactMinusOne : Int :=
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

private def mkStrefAltProgramCellBits
    (cellBits : Nat)
    (cellX : IntVal := .num 0) : Array Instr :=
  buildCellWithBitsProgram cellBits cellX ++ #[.newc, strefInstr]

private def mkStrefAltProgramBuilderBitsCellBits
    (builderBits : Nat)
    (cellBits : Nat)
    (builderX : IntVal := .num 0)
    (cellX : IntVal := .num 0) : Array Instr :=
  #[.newc]
    ++ appendBitsToTopBuilder builderBits builderX
    ++ appendCellWithBitsToTopBuilder cellBits cellX

private def mkStrefAltProgramBuilderRefsCellBits
    (refs : Nat)
    (cellBits : Nat)
    (cellX : IntVal := .num 0) : Array Instr :=
  mkBuilderWithRefsProgram refs ++ appendCellWithBitsToTopBuilder cellBits cellX

private def mkStrefAltProgramBuilderRefsCellWithRef (refs : Nat) : Array Instr :=
  mkBuilderWithRefsProgram refs ++ buildCellWithOneRefProgram ++ #[.xchg0 1, strefInstr]

private def mkStrefAltCellOvProgramWithCellBits
    (cellBits : Nat)
    (cellX : IntVal := .num 0) : Array Instr :=
  mkBuilderWithRefsProgram 4 ++ buildCellWithBitsProgram cellBits cellX ++ #[.xchg0 1, strefInstr]

private def strefAltCellOvProgram : Array Instr :=
  mkStrefAltCellOvProgramWithCellBits 0

private def strefAltCellOvWithRefCellProgram : Array Instr :=
  mkBuilderWithRefsProgram 4 ++ buildCellWithOneRefProgram ++ #[.xchg0 1, strefInstr]

private def strefAltAppendProgram : Array Instr :=
  mkStrefAltProgramBuilderBitsCellBits 3 5 (.num 5) (.num 17)

private def strefAltAppendWithRefsProgram : Array Instr :=
  mkStrefAltProgramBuilderRefsCellBits 2 4 (.num 9)

private def strefAltCellWithRefProgram : Array Instr :=
  buildCellWithOneRefProgram ++ #[.newc, strefInstr]

private def strefAltFullBitsRefs3ThenStoreProgram : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder 3 ++ #[.newc, .endc, .xchg0 1, strefInstr]

private def strefAltBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 15]

private def pickStrefAltBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (strefAltBitsBoundaryPool.size - 1)
  (strefAltBitsBoundaryPool[idx]!, rng')

private def pickStrefAltBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickStrefAltBitsBoundary rng1
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

private def genStrefAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    (mkStrefAltCase "fuzz/ok/direct/minimal" #[.cell Cell.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noisePick, rng2) := randNat rng1 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 91 else .cell Cell.empty
    (mkStrefAltCase "fuzz/ok/direct/deep-stack" #[noise, .cell Cell.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    (mkStrefAltCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkStrefAltCase "fuzz/underflow/one-cell" #[.cell Cell.empty], rng1)
  else if shape = 4 then
    (mkStrefAltCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkStrefAltCase "fuzz/type/top-not-builder" #[.cell Cell.empty, .null], rng1)
  else if shape = 6 then
    (mkStrefAltCase "fuzz/type/second-not-cell" #[.null, .builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStrefAltCase "fuzz/type/both-wrong" #[intV 1, .null], rng1)
  else if shape = 8 then
    let (cellBits, rng2) := pickStrefAltBitsMixed rng1
    let (cellX, rng3) := pickCellPayloadForBits cellBits rng2
    (mkStrefAltProgramCase s!"fuzz/ok/program/cell-bits-{cellBits}" #[]
      (mkStrefAltProgramCellBits cellBits cellX), rng3)
  else if shape = 9 then
    let (builderBits, rng2) := pickStrefAltBitsMixed rng1
    let (cellBits, rng3) := pickStrefAltBitsMixed rng2
    let (builderX, rng4) := pickCellPayloadForBits builderBits rng3
    let (cellX, rng5) := pickCellPayloadForBits cellBits rng4
    (mkStrefAltProgramCase s!"fuzz/ok/program/builder-bits-{builderBits}-cell-bits-{cellBits}" #[]
      (mkStrefAltProgramBuilderBitsCellBits builderBits cellBits builderX cellX), rng5)
  else if shape = 10 then
    let (refs, rng2) := randNat rng1 0 3
    let (cellBits, rng3) := pickStrefAltBitsMixed rng2
    let (cellX, rng4) := pickCellPayloadForBits cellBits rng3
    (mkStrefAltProgramCase s!"fuzz/ok/program/refs-{refs}-cell-bits-{cellBits}" #[]
      (mkStrefAltProgramBuilderRefsCellBits refs cellBits cellX), rng4)
  else if shape = 11 then
    let (cellBits, rng2) := pickStrefAltBitsMixed rng1
    let (cellX, rng3) := pickCellPayloadForBits cellBits rng2
    (mkStrefAltProgramCase s!"fuzz/cellov/program/refs4-cell-bits-{cellBits}" #[]
      (mkStrefAltCellOvProgramWithCellBits cellBits cellX), rng3)
  else if shape = 12 then
    (mkStrefAltProgramCase "fuzz/ok/program/full-bits-refs3-then-store" #[] strefAltFullBitsRefs3ThenStoreProgram, rng1)
  else if shape = 13 then
    let (useExact, rng2) := randBool rng1
    if useExact then
      (mkStrefAltCase "fuzz/gas/exact" #[.cell Cell.empty, .builder Builder.empty]
        #[.pushInt (.num strefAltSetGasExact), .tonEnvOp .setGasLimit, strefInstr], rng2)
    else
      (mkStrefAltCase "fuzz/gas/exact-minus-one" #[.cell Cell.empty, .builder Builder.empty]
        #[.pushInt (.num strefAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefInstr], rng2)
  else
    (mkStrefAltProgramCase "fuzz/cellov/program/refs4-cell-with-ref" #[] strefAltCellOvWithRefCellProgram, rng1)

def suite : InstrSuite where
  id := strefAltId
  unit := #[
    { name := "unit/direct/stack-order-and-success"
      run := do
        let emptyExpected : Builder := { Builder.empty with refs := #[Cell.empty] }
        expectOkStack "ok/minimal/empty-cell-empty-builder"
          (runStrefAltDirect #[.cell Cell.empty, .builder Builder.empty])
          #[.builder emptyExpected]

        let existingRef : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
        let sourceCell : Cell := Cell.mkOrdinary (natToBits 17 5) #[Cell.empty]
        let prefBuilder : Builder := { bits := natToBits 6 3, refs := #[existingRef] }
        let expectedPref : Builder := { bits := prefBuilder.bits, refs := prefBuilder.refs.push sourceCell }
        expectOkStack "ok/non-empty-builder-and-cell-append-tail"
          (runStrefAltDirect #[.cell sourceCell, .builder prefBuilder])
          #[.builder expectedPref]

        let boundaryBuilder : Builder :=
          { bits := fullBuilder1023.bits
            refs := #[Cell.empty, Cell.empty, Cell.empty] }
        let boundaryExpected : Builder := { boundaryBuilder with refs := boundaryBuilder.refs.push Cell.empty }
        expectOkStack "ok/full-bits-with-three-refs-still-accepts-one-ref"
          (runStrefAltDirect #[.cell Cell.empty, .builder boundaryBuilder])
          #[.builder boundaryExpected]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStrefAltDirect #[.null, .cell Cell.empty, .builder Builder.empty])
          #[.null, .builder emptyExpected] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStrefAltDirect #[]) .stkUnd
        expectErr "underflow/one-cell" (runStrefAltDirect #[.cell Cell.empty]) .stkUnd
        expectErr "underflow/one-builder" (runStrefAltDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStrefAltDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "type/second-not-cell"
          (runStrefAltDirect #[intV 7, .builder Builder.empty]) .typeChk
        expectErr "type/reversed-args-builder-below-cell-top"
          (runStrefAltDirect #[.builder Builder.empty, .cell Cell.empty]) .typeChk
        expectErr "type/both-wrong-top-first"
          (runStrefAltDirect #[intV 1, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-ref-capacity"
      run := do
        let refs4 : Array Cell := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty]
        let bRef4 : Builder := { bits := #[], refs := refs4 }
        expectErr "cellov/refs4-empty-bits"
          (runStrefAltDirect #[.cell Cell.empty, .builder bRef4]) .cellOv

        let bFullRef4 : Builder := { bits := fullBuilder1023.bits, refs := refs4 }
        expectErr "cellov/refs4-full-bits"
          (runStrefAltDirect #[.cell Cell.empty, .builder bFullRef4]) .cellOv }
    ,
    { name := "unit/opcode/alt-decode-and-canonical-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [strefInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits strefCanonicalOpcode 8 then
          pure ()
        else
          throw (IO.userError s!"stref canonical encode mismatch: got bits {canonicalOnly.bits}")

        let aliasSlice := mkSliceFromBits (natToBits strefAltAliasOpcode 16)
        let _ ← expectDecodeStep "decode/alt-cf10-to-stref" aliasSlice strefInstr 16

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
        let aliasCode : Cell :=
          Cell.mkOrdinary (natToBits strefAltAliasOpcode 16 ++ natToBits strefCanonicalOpcode 8 ++ addCell.bits) #[]
        let a0 := Slice.ofCell aliasCode
        let a1 ← expectDecodeStep "decode/alias-cf10" a0 strefInstr 16
        let a2 ← expectDecodeStep "decode/alias-followed-by-canonical-cc" a1 strefInstr 8
        let a3 ← expectDecodeStep "decode/alias-tail-add" a2 .add 8
        if a3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/alias-end: expected exhausted slice, got {a3.bitsRemaining} bits remaining")

        let decodedAliasInstr ←
          match decodeCp0WithBits aliasSlice with
          | .ok (instr, _, _) => pure instr
          | .error e => throw (IO.userError s!"decode alias for direct-exec failed: {e}")
        let aliasExecInputCell : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
        let aliasExecInputBuilder : Builder := { bits := natToBits 3 2, refs := #[Cell.empty] }
        let aliasExecExpected : Builder :=
          { bits := aliasExecInputBuilder.bits
            refs := aliasExecInputBuilder.refs.push aliasExecInputCell }
        expectOkStack "alias-decoded-exec-equals-stref"
          (runHandlerDirect execInstrCellStref decodedAliasInstr
            #[.cell aliasExecInputCell, .builder aliasExecInputBuilder])
          #[.builder aliasExecExpected] }
    ,
    { name := "unit/dispatch/non-stref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStrefAltDispatchFallback #[.null])
          #[.null, intV 53008] }
  ]
  oracle := #[
    mkStrefAltCase "ok/empty-cell-empty-builder" #[.cell Cell.empty, .builder Builder.empty],
    mkStrefAltCase "ok/deep-stack-preserve-below" #[.null, .cell Cell.empty, .builder Builder.empty],

    mkStrefAltProgramCase "ok/program/cell-bits-0" #[] (mkStrefAltProgramCellBits 0),
    mkStrefAltProgramCase "ok/program/cell-bits-1" #[] (mkStrefAltProgramCellBits 1 (.num 1)),
    mkStrefAltProgramCase "ok/program/cell-bits-8" #[] (mkStrefAltProgramCellBits 8 (.num 170)),
    mkStrefAltProgramCase "ok/program/cell-bits-15" #[] (mkStrefAltProgramCellBits 15 (.num 177)),
    mkStrefAltProgramCase "ok/program/builder-bits3-cell-bits5" #[] strefAltAppendProgram,
    mkStrefAltProgramCase "ok/program/builder-bits7-cell-bits2" #[]
      (mkStrefAltProgramBuilderBitsCellBits 7 2 (.num 77) (.num 3)),
    mkStrefAltProgramCase "ok/program/builder-refs0-cell-bits4" #[]
      (mkStrefAltProgramBuilderRefsCellBits 0 4 (.num 9)),
    mkStrefAltProgramCase "ok/program/builder-refs2-cell-bits4" #[] strefAltAppendWithRefsProgram,
    mkStrefAltProgramCase "ok/program/builder-refs3-cell-empty" #[]
      (mkStrefAltProgramBuilderRefsCellBits 3 0),
    mkStrefAltProgramCase "ok/program/full-bits-refs3-then-store" #[] strefAltFullBitsRefs3ThenStoreProgram,
    mkStrefAltProgramCase "ok/program/cell-with-ref" #[] strefAltCellWithRefProgram,
    mkStrefAltProgramCase "ok/program/builder-refs1-cell-with-ref" #[]
      (mkStrefAltProgramBuilderRefsCellWithRef 1),
    mkStrefAltProgramCase "ok/program/noise-below-preserved" #[]
      (#[.pushNull] ++ mkStrefAltProgramCellBits 6 (.num 41)),

    mkStrefAltCase "underflow/empty" #[],
    mkStrefAltCase "underflow/one-cell" #[.cell Cell.empty],
    mkStrefAltCase "underflow/one-builder" #[.builder Builder.empty],
    mkStrefAltCase "type/top-not-builder" #[.cell Cell.empty, .null],
    mkStrefAltCase "type/second-not-cell" #[.null, .builder Builder.empty],
    mkStrefAltCase "type/both-wrong-top-first" #[intV 1, .null],

    mkStrefAltCase "gas/exact-cost-succeeds" #[.cell Cell.empty, .builder Builder.empty]
      #[.pushInt (.num strefAltSetGasExact), .tonEnvOp .setGasLimit, strefInstr],
    mkStrefAltCase "gas/exact-minus-one-out-of-gas" #[.cell Cell.empty, .builder Builder.empty]
      #[.pushInt (.num strefAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, strefInstr],

    mkStrefAltProgramCase "cellov/program/refs4-empty-cell" #[] strefAltCellOvProgram,
    mkStrefAltProgramCase "cellov/program/refs4-cell-bits1" #[]
      (mkStrefAltCellOvProgramWithCellBits 1 (.num 1)),
    mkStrefAltProgramCase "cellov/program/refs4-cell-bits8" #[]
      (mkStrefAltCellOvProgramWithCellBits 8 (.num 255)),
    mkStrefAltProgramCase "cellov/program/refs4-cell-with-ref" #[] strefAltCellOvWithRefCellProgram,
    mkStrefAltProgramCase "cellov/program/noise-below-refs4" #[] (#[.pushNull] ++ strefAltCellOvProgram)
  ]
  fuzz := #[
    { seed := 2026021028
      count := 500
      gen := genStrefAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STREF_ALT
