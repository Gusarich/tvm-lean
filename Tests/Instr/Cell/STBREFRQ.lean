import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STBREFRQ

/-
STBREFRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StbRef.lean` (`.stbRef true true`)
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.strefR quiet` for reversed quiet-status parity)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STBREFRQ` encode: `0xcf1d`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf1d` decode to `.stbRef true true`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder_as_ref_rev`, quiet mode).

Branch map used for this suite:
- Lean STBREFRQ path: 8 branch sites / 12 terminal outcomes
  (`checkUnderflow 2`; rev=true pop order; two builder type checks;
   capacity check `canExtendBy 0 1`; quiet success with status `0`;
   quiet overflow with status `-1`; fallthrough for non-matching instr).
- C++ STBREFRQ path: 6 branch sites / 10 aligned outcomes
  (`check_underflow(2)`; reversed pops; `can_extend_by(0,1)`; quiet status push behavior).

Key risk areas:
- reversed operand order is `... builder cb2` (cb2 on top);
- success stores `finalize(cb2)` as a single reference in destination builder;
- quiet overflow must not throw and must restore `[builder, cb2, -1]` in that order;
- overflow decision depends only on destination ref capacity (`+1 ref`), not on bits;
- cell-create gas is charged only on success path (via `finalize_copy` in C++).
-/

private def stbrefRqId : InstrId := { name := "STBREFRQ" }

private def stbrefRqInstr : Instr :=
  .stbRef true true

private def mkStbrefRqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbrefRqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefRqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbrefRqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefRqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbrefRqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStbRef stbrefRqInstr stack

private def runStbrefRqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStbRef .add (VM.push (intV 521)) stack

private def stbrefRqSetGasExact : Int :=
  computeExactGasBudget stbrefRqInstr

private def stbrefRqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stbrefRqInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkBuilderProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkStbrefRqProgram
    (bBits : Nat) (bRefs : Nat)
    (cb2Bits : Nat) (cb2Refs : Nat)
    (bX : IntVal := .num 0) (cb2X : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bBits bRefs bX
    ++ mkBuilderProgram cb2Bits cb2Refs cb2X
    ++ #[stbrefRqInstr]

private def mkStbrefRqProgramWithNoise
    (bBits : Nat) (bRefs : Nat)
    (cb2Bits : Nat) (cb2Refs : Nat)
    (bX : IntVal := .num 0) (cb2X : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStbrefRqProgram bBits bRefs cb2Bits cb2Refs bX cb2X

private def mkStbrefRqProgramB1023
    (bRefs : Nat)
    (cb2Bits : Nat)
    (cb2Refs : Nat)
    (cb2X : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu
    ++ appendRefsToTopBuilder bRefs
    ++ mkBuilderProgram cb2Bits cb2Refs cb2X
    ++ #[stbrefRqInstr]

private def mkStbrefRqProgramB1023WithNoise
    (bRefs : Nat)
    (cb2Bits : Nat)
    (cb2Refs : Nat)
    (cb2X : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStbrefRqProgramB1023 bRefs cb2Bits cb2Refs cb2X

private def mkStbrefRqProgramCb21023
    (bBits : Nat)
    (bRefs : Nat)
    (cb2Refs : Nat) : Array Instr :=
  mkBuilderProgram bBits bRefs
    ++ build1023WithFixed .stu
    ++ appendRefsToTopBuilder cb2Refs
    ++ #[stbrefRqInstr]

private def mkStbrefRqProgramCb21023WithNoise
    (bBits : Nat)
    (bRefs : Nat)
    (cb2Refs : Nat) : Array Instr :=
  #[.pushNull] ++ mkStbrefRqProgramCb21023 bBits bRefs cb2Refs

private def expectedStoreBuilderAsRef (b cb2 : Builder) : Builder :=
  { b with refs := b.refs.push cb2.finalize }

private def quietCellovRefsProgram : Array Instr :=
  mkStbrefRqProgram 0 4 0 0

private def quietCellovRefsNonEmptyProgram : Array Instr :=
  mkStbrefRqProgram 0 4 7 2

private def quietCellovRefsWithNoiseProgram : Array Instr :=
  mkStbrefRqProgramWithNoise 0 4 1 0

private def successB1023R3Program : Array Instr :=
  mkStbrefRqProgramB1023 3 1 0

private def successB1023R0Cb2Refs4Program : Array Instr :=
  mkStbrefRqProgramB1023 0 0 4

private def quietCellovB1023R4Program : Array Instr :=
  mkStbrefRqProgramB1023 4 0 0

private def quietCellovB1023R4WithNoiseProgram : Array Instr :=
  mkStbrefRqProgramB1023WithNoise 4 2 0

private def successCb21023Program : Array Instr :=
  mkStbrefRqProgramCb21023 0 1 0

private def successCb21023WithNoiseProgram : Array Instr :=
  mkStbrefRqProgramCb21023WithNoise 2 2 1

private def quietCellovCb21023Program : Array Instr :=
  mkStbrefRqProgramCb21023 0 4 0

private def stbrefRqBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31]

private def pickStbrefRqBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stbrefRqBitsBoundaryPool.size - 1)
  (stbrefRqBitsBoundaryPool[idx]!, rng')

private def pickStbrefRqBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickStbrefRqBitsBoundary rng1
  else
    randNat rng1 0 31

private def pickStbrefRqNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let noise : Value :=
    if pick = 0 then .null else if pick = 1 then intV 73 else .cell Cell.empty
  (noise, rng1)

private def genStbrefRqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    (mkStbrefRqCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noise, rng2) := pickStbrefRqNoise rng1
    (mkStbrefRqCase "fuzz/ok/deep-stack-empty-builders" #[noise, .builder Builder.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    let (bBits, rng2) := pickStbrefRqBitsMixed rng1
    let (bRefs, rng3) := randNat rng2 0 3
    let (cb2Bits, rng4) := pickStbrefRqBitsMixed rng3
    let (cb2Refs, rng5) := randNat rng4 0 4
    (mkStbrefRqProgramCase s!"fuzz/ok/program/b-{bBits}-{bRefs}/cb2-{cb2Bits}-{cb2Refs}" #[]
      (mkStbrefRqProgram bBits bRefs cb2Bits cb2Refs), rng5)
  else if shape = 3 then
    let (noise, rng2) := pickStbrefRqNoise rng1
    let (bBits, rng3) := pickStbrefRqBitsMixed rng2
    let (bRefs, rng4) := randNat rng3 0 3
    let (cb2Bits, rng5) := pickStbrefRqBitsMixed rng4
    let (cb2Refs, rng6) := randNat rng5 0 4
    (mkStbrefRqProgramCase s!"fuzz/ok/program-noise/b-{bBits}-{bRefs}/cb2-{cb2Bits}-{cb2Refs}" #[noise]
      (mkStbrefRqProgram bBits bRefs cb2Bits cb2Refs), rng6)
  else if shape = 4 then
    (mkStbrefRqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStbrefRqCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    let (noise, rng2) := pickStbrefRqNoise rng1
    (mkStbrefRqCase "fuzz/type/top-not-builder" #[.builder Builder.empty, noise], rng2)
  else if shape = 7 then
    let (noise, rng2) := pickStbrefRqNoise rng1
    (mkStbrefRqCase "fuzz/type/second-not-builder" #[noise, .builder Builder.empty], rng2)
  else if shape = 8 then
    let (noise, rng2) := pickStbrefRqNoise rng1
    (mkStbrefRqCase "fuzz/type/both-non-builder" #[noise, intV 1], rng2)
  else if shape = 9 then
    let (cb2Bits, rng2) := pickStbrefRqBitsMixed rng1
    let (cb2Refs, rng3) := randNat rng2 0 4
    (mkStbrefRqProgramCase s!"fuzz/quiet-cellov/refs4/cb2-{cb2Bits}-{cb2Refs}" #[]
      (mkStbrefRqProgram 0 4 cb2Bits cb2Refs), rng3)
  else if shape = 10 then
    let (cb2Bits, rng2) := pickStbrefRqBitsMixed rng1
    let (cb2Refs, rng3) := randNat rng2 0 4
    (mkStbrefRqProgramCase s!"fuzz/quiet-cellov/noise/refs4/cb2-{cb2Bits}-{cb2Refs}" #[.null]
      (mkStbrefRqProgram 0 4 cb2Bits cb2Refs), rng3)
  else if shape = 11 then
    let (bRefs, rng2) := randNat rng1 0 3
    let (cb2Bits, rng3) := pickStbrefRqBitsMixed rng2
    let (cb2Refs, rng4) := randNat rng3 0 4
    (mkStbrefRqProgramCase s!"fuzz/ok/b1023-r{bRefs}/cb2-{cb2Bits}-{cb2Refs}" #[]
      (mkStbrefRqProgramB1023 bRefs cb2Bits cb2Refs), rng4)
  else if shape = 12 then
    let (cb2Bits, rng2) := pickStbrefRqBitsMixed rng1
    let (cb2Refs, rng3) := randNat rng2 0 4
    (mkStbrefRqProgramCase s!"fuzz/quiet-cellov/b1023-r4/cb2-{cb2Bits}-{cb2Refs}" #[]
      (mkStbrefRqProgramB1023 4 cb2Bits cb2Refs), rng3)
  else if shape = 13 then
    let (bBits, rng2) := pickStbrefRqBitsMixed rng1
    let (bRefs, rng3) := randNat rng2 0 3
    let (cb2Refs, rng4) := randNat rng3 0 4
    (mkStbrefRqProgramCase s!"fuzz/ok/cb2-1023/b-{bBits}-{bRefs}/r{cb2Refs}" #[]
      (mkStbrefRqProgramCb21023 bBits bRefs cb2Refs), rng4)
  else
    let (bBits, rng2) := pickStbrefRqBitsMixed rng1
    let (cb2Refs, rng3) := randNat rng2 0 4
    (mkStbrefRqProgramCase s!"fuzz/quiet-cellov/cb2-1023/b-{bBits}-r4/cb2r{cb2Refs}" #[]
      (mkStbrefRqProgramCb21023 bBits 4 cb2Refs), rng3)

def suite : InstrSuite where
  id := stbrefRqId
  unit := #[
    { name := "unit/direct/reverse-order-success-and-code0"
      run := do
        let expectedEmpty : Builder := { Builder.empty with refs := #[Cell.empty] }
        expectOkStack "ok/empty-builders-store-empty-cell-ref"
          (runStbrefRqDirect #[.builder Builder.empty, .builder Builder.empty])
          #[.builder expectedEmpty, intV 0]

        let cb2 : Builder :=
          { bits := natToBits 5 3
            refs := #[Cell.ofUInt 2 3, Cell.empty] }
        let b : Builder :=
          { bits := natToBits 2 2
            refs := #[Cell.ofUInt 1 1, Cell.ofUInt 2 2] }
        let expectedNonEmpty := expectedStoreBuilderAsRef b cb2
        expectOkStack "ok/reverse-order-builder-below-receives-ref"
          (runStbrefRqDirect #[.builder b, .builder cb2])
          #[.builder expectedNonEmpty, intV 0]

        let b1023r3 : Builder :=
          { fullBuilder1023 with refs := #[Cell.empty, Cell.ofUInt 1 1, Cell.ofUInt 2 2] }
        let cb2bit1 : Builder := Builder.empty.storeBits (natToBits 1 1)
        let expected1023 := expectedStoreBuilderAsRef b1023r3 cb2bit1
        expectOkStack "ok/bits-full-with-three-refs-still-succeeds"
          (runStbrefRqDirect #[.builder b1023r3, .builder cb2bit1])
          #[.builder expected1023, intV 0]

        let expectedDeep := expectedStoreBuilderAsRef Builder.empty Builder.empty
        expectOkStack "ok/deep-stack-preserve-below"
          (runStbrefRqDirect #[.null, .builder Builder.empty, .builder Builder.empty])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/quiet-cellov-status-minus1"
      run := do
        let bRefs4 : Builder :=
          { Builder.empty with refs := #[Cell.empty, Cell.ofUInt 1 1, Cell.ofUInt 2 2, Cell.ofUInt 2 3] }
        let cb2 : Builder := Builder.empty.storeBits (natToBits 7 3)
        expectOkStack "quiet-cellov/refs-full"
          (runStbrefRqDirect #[.builder bRefs4, .builder cb2])
          #[.builder bRefs4, .builder cb2, intV (-1)]

        let b1023r4 : Builder :=
          { fullBuilder1023 with refs := #[Cell.empty, Cell.ofUInt 1 1, Cell.ofUInt 2 2, Cell.ofUInt 2 3] }
        expectOkStack "quiet-cellov/refs-full-even-with-bits-full"
          (runStbrefRqDirect #[.builder b1023r4, .builder Builder.empty])
          #[.builder b1023r4, .builder Builder.empty, intV (-1)]

        expectOkStack "quiet-cellov/deep-stack-preserve-below"
          (runStbrefRqDirect #[.cell Cell.empty, .builder bRefs4, .builder Builder.empty])
          #[.cell Cell.empty, .builder bRefs4, .builder Builder.empty, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStbrefRqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbrefRqDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder-cb2-first"
          (runStbrefRqDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder-b-second"
          (runStbrefRqDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbrefRqDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr :=
          #[stbrefRqInstr, .stbRef true false, .stbRef false true, .stbRef false false, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stbrefrq" s0 stbrefRqInstr 16
        let s2 ← expectDecodeStep "decode/stbrefr" s1 (.stbRef true false) 16
        let s3 ← expectDecodeStep "decode/stbrefq" s2 (.stbRef false true) 16
        let s4 ← expectDecodeStep "decode/stbref" s3 (.stbRef false false) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stbref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbrefRqDispatchFallback #[.null])
          #[.null, intV 521] }
  ]
  oracle := #[
    mkStbrefRqCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbrefRqCase "ok/deep-stack-empty-builders" #[.null, .builder Builder.empty, .builder Builder.empty],
    mkStbrefRqProgramCase "ok/program/b0r0-cb2b1r0" #[] (mkStbrefRqProgram 0 0 1 0),
    mkStbrefRqProgramCase "ok/program/b0r1-cb2b0r0" #[] (mkStbrefRqProgram 0 1 0 0),
    mkStbrefRqProgramCase "ok/program/b0r2-cb2b3r0" #[] (mkStbrefRqProgram 0 2 3 0),
    mkStbrefRqProgramCase "ok/program/b5r0-cb2b3r2" #[] (mkStbrefRqProgram 5 0 3 2),
    mkStbrefRqProgramCase "ok/program/b8r1-cb2b2r1" #[] (mkStbrefRqProgram 8 1 2 1),
    mkStbrefRqProgramCase "ok/program/b0r3-cb2b0r4" #[] (mkStbrefRqProgram 0 3 0 4),
    mkStbrefRqProgramCase "ok/program/noise-b1r1-cb2b4r0" #[.null] (mkStbrefRqProgram 1 1 4 0),
    mkStbrefRqProgramCase "ok/program/b1023r3-cb2b1r0" #[] successB1023R3Program,
    mkStbrefRqProgramCase "ok/program/b1023r0-cb2r4" #[] successB1023R0Cb2Refs4Program,
    mkStbrefRqProgramCase "ok/program/cb2-1023" #[] successCb21023Program,
    mkStbrefRqProgramCase "ok/program/cb2-1023-with-noise" #[] successCb21023WithNoiseProgram,

    mkStbrefRqCase "underflow/empty" #[],
    mkStbrefRqCase "underflow/one-item" #[.builder Builder.empty],
    mkStbrefRqCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbrefRqCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbrefRqCase "type/both-non-builder" #[.null, intV 1],

    mkStbrefRqProgramCase "quiet-cellov/refs4-cb2-empty" #[] quietCellovRefsProgram,
    mkStbrefRqProgramCase "quiet-cellov/refs4-cb2-nonempty" #[] quietCellovRefsNonEmptyProgram,
    mkStbrefRqProgramCase "quiet-cellov/refs4-with-noise" #[] quietCellovRefsWithNoiseProgram,
    mkStbrefRqProgramCase "quiet-cellov/b1023r4-cb2-empty" #[] quietCellovB1023R4Program,
    mkStbrefRqProgramCase "quiet-cellov/b1023r4-cb2-with-noise" #[] quietCellovB1023R4WithNoiseProgram,
    mkStbrefRqProgramCase "quiet-cellov/cb2-1023" #[] quietCellovCb21023Program,

    mkStbrefRqCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefRqSetGasExact), .tonEnvOp .setGasLimit, stbrefRqInstr],
    mkStbrefRqCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefRqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrefRqInstr]
  ]
  fuzz := #[
    { seed := 2026021012
      count := 320
      gen := genStbrefRqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STBREFRQ
