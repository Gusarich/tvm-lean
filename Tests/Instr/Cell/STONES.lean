import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STONES

/-
STONES branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StOnes.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STONES` encode: `0xcf41`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf41` decode to `.stOnes`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_same` with `val=1` for `STONES`).

Branch map used for this suite:
- Lean STONES path: 7 branch sites / 10 terminal outcomes
  (`checkUnderflow 2`; opcode guard; bits pop/type/range; builder pop/type;
   capacity check; success push).
- C++ STONES path: 6 branch sites / 9 aligned outcomes.

Key risk areas:
- stack order is `... builder bits` (`bits` on top);
- invalid `bits` must fail before builder pop;
- full-builder `cellOv` only for `bits > 0`;
- stored payload must be exactly `bits` ones.
-/

private def stonesId : InstrId := { name := "STONES" }

private def stonesInstr : Instr := .stOnes

private def mkStonesCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stonesInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stonesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStonesProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stonesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStonesDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStOnes stonesInstr stack

private def runStonesDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStOnes .add (VM.push (intV 433)) stack

private def stonesSetGasExact : Int :=
  computeExactGasBudget stonesInstr

private def stonesSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stonesInstr

private def build1023Program : Array Instr :=
  #[.newc, .pushInt (.num 1023), stonesInstr]

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1), stonesInstr]

private def fullBuilderThenBits0Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), stonesInstr]

private def fullBuilderThenBits1024Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1024), stonesInstr]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, stonesInstr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 4), stonesInstr
  ]

private def pickStonesBitsInRange (rng : StdGen) : Nat × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let n : Nat :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 2
    else if pick = 3 then 7
    else if pick = 4 then 8
    else if pick = 5 then 255
    else if pick = 6 then 1023
    else 19
  (n, rng')

private def genStonesFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (bits, rng2) := pickStonesBitsInRange rng1
    (mkStonesCase s!"fuzz/ok/top-only/bits-{bits}" #[.builder Builder.empty, intV bits], rng2)
  else if shape = 1 then
    let (bits, rng2) := pickStonesBitsInRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 71 else .cell Cell.empty
    (mkStonesCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, .builder Builder.empty, intV bits], rng3)
  else if shape = 2 then
    (mkStonesCase "fuzz/range/negative" #[.builder Builder.empty, intV (-1)], rng1)
  else if shape = 3 then
    (mkStonesCase "fuzz/range/overflow-1024" #[.builder Builder.empty, intV 1024], rng1)
  else if shape = 4 then
    (mkStonesProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else if shape = 5 then
    (mkStonesCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkStonesCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStonesCase "fuzz/type/top-not-int" #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkStonesCase "fuzz/type/builder-not-builder" #[intV 3, intV 2], rng1)
  else if shape = 9 then
    (mkStonesProgramCase "fuzz/cellov/full-builder-bits1" #[] overflowAfter1023Program, rng1)
  else if shape = 10 then
    (mkStonesProgramCase "fuzz/cellov-vs-range/range-wins" #[] fullBuilderThenBits1024Program, rng1)
  else
    let (bits, rng2) := pickStonesBitsInRange rng1
    (mkStonesProgramCase s!"fuzz/program/build-1023-then-op/bits-{bits}" #[]
      (build1023Program ++ #[.pushInt (.num bits), stonesInstr]), rng2)

def suite : InstrSuite where
  id := stonesId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array Nat := #[0, 1, 2, 7, 8, 255, 1023]
        for bits in checks do
          let expected := Builder.empty.storeBits (Array.replicate bits true)
          expectOkStack s!"ok/bits-{bits}"
            (runStonesDirect #[.builder Builder.empty, intV bits])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (Array.replicate 4 true)
        expectOkStack "ok/append-existing-bits"
          (runStonesDirect #[.builder prefBuilder, intV 4])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (Array.replicate 6 true)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStonesDirect #[.null, .builder Builder.empty, intV 6])
          #[.null, .builder expectedDeep]

        expectOkStack "ok/full-builder-bits0"
          (runStonesDirect #[.builder fullBuilder1023, intV 0])
          #[.builder fullBuilder1023] }
    ,
    { name := "unit/direct/range-and-order"
      run := do
        expectErr "range/negative"
          (runStonesDirect #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/overflow-1024"
          (runStonesDirect #[.builder Builder.empty, intV 1024]) .rangeChk
        expectErr "range/nan"
          (runStonesDirect #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "error-order/range-before-type-builder"
          (runStonesDirect #[.null, intV 1024]) .rangeChk
        expectErr "error-order/range-before-cellov"
          (runStonesDirect #[.builder fullBuilder1023, intV 1024]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStonesDirect #[]) .stkUnd
        expectErr "underflow/one-item-builder" (runStonesDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-item-int" (runStonesDirect #[intV 1]) .stkUnd

        expectErr "type/top-not-int"
          (runStonesDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/builder-pop-second"
          (runStonesDirect #[intV 2, intV 1]) .typeChk
        expectErr "type/builder-pop-second-with-valid-bits0"
          (runStonesDirect #[.null, intV 0]) .typeChk }
    ,
    { name := "unit/direct/cellov"
      run := do
        expectErr "cellov/full-builder-bits1"
          (runStonesDirect #[.builder fullBuilder1023, intV 1]) .cellOv
        expectErr "cellov/full-builder-bits17"
          (runStonesDirect #[.builder fullBuilder1023, intV 17]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stonesInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stones" s0 stonesInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stones-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStonesDispatchFallback #[.null])
          #[.null, intV 433] }
  ]
  oracle := #[
    mkStonesCase "ok/bits-0" #[.builder Builder.empty, intV 0],
    mkStonesCase "ok/bits-1" #[.builder Builder.empty, intV 1],
    mkStonesCase "ok/bits-2" #[.builder Builder.empty, intV 2],
    mkStonesCase "ok/bits-7" #[.builder Builder.empty, intV 7],
    mkStonesCase "ok/bits-8" #[.builder Builder.empty, intV 8],
    mkStonesCase "ok/bits-255" #[.builder Builder.empty, intV 255],
    mkStonesCase "ok/bits-1023" #[.builder Builder.empty, intV 1023],
    mkStonesCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 6],
    mkStonesProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,
    mkStonesProgramCase "ok/full-builder-bits0-via-program" #[] fullBuilderThenBits0Program,

    mkStonesCase "range/negative" #[.builder Builder.empty, intV (-1)],
    mkStonesCase "range/overflow-1024" #[.builder Builder.empty, intV 1024],
    mkStonesProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,
    mkStonesCase "range-before-type-builder" #[.null, intV 1024],
    mkStonesProgramCase "range-before-cellov-full-builder" #[] fullBuilderThenBits1024Program,

    mkStonesCase "underflow/empty" #[],
    mkStonesCase "underflow/one-item-builder" #[.builder Builder.empty],
    mkStonesCase "type/top-not-int" #[.builder Builder.empty, .null],
    mkStonesCase "type/builder-pop-second" #[intV 2, intV 1],

    mkStonesCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stonesSetGasExact), .tonEnvOp .setGasLimit, stonesInstr],
    mkStonesCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stonesSetGasExactMinusOne), .tonEnvOp .setGasLimit, stonesInstr],

    mkStonesProgramCase "program/build-1023-success" #[] build1023Program,
    mkStonesProgramCase "program/build-1023-then-overflow-cellov" #[] overflowAfter1023Program
  ]
  fuzz := #[
    { seed := 2026020934
      count := 320
      gen := genStonesFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STONES
