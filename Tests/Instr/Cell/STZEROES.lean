import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STZEROES

/-
STZEROES branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StZeroes.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STZEROES` encode: `0xcf40`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf40` decode to `.stZeroes`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_same` with `val=0` for `STZEROES`).

Branch map used for this suite:
- Lean STZEROES path: 7 branch sites / 10 terminal outcomes
  (`checkUnderflow 2`; opcode guard; bits pop/type/range; builder pop/type;
   capacity check; success push).
- C++ STZEROES path: 6 branch sites / 9 aligned outcomes
  (`check_underflow(2)`; `bits` pop/range; `builder` pop/type; `check_space`; success).

Key risk areas:
- stack order is `... builder bits` (`bits` on top);
- invalid `bits` (`nan`, negative, >1023) must fail before builder pop;
- full-builder `cellOv` must trigger only when `bits > 0`;
- `bits = 0` must be a no-op even on a full builder.
-/

private def stzeroesId : InstrId := { name := "STZEROES" }

private def stzeroesInstr : Instr := .stZeroes

private def mkStzeroesCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stzeroesInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stzeroesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStzeroesProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stzeroesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStzeroesDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStZeroes stzeroesInstr stack

private def runStzeroesDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStZeroes .add (VM.push (intV 432)) stack

private def stzeroesSetGasExact : Int :=
  computeExactGasBudget stzeroesInstr

private def stzeroesSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stzeroesInstr

private def build1023Program : Array Instr :=
  #[.newc, .pushInt (.num 1023), stzeroesInstr]

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1), stzeroesInstr]

private def fullBuilderThenBits0Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), stzeroesInstr]

private def fullBuilderThenBits1024Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1024), stzeroesInstr]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, stzeroesInstr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 4), stzeroesInstr
  ]

private def pickStzeroesBitsInRange (rng : StdGen) : Nat × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let n : Nat :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 2
    else if pick = 3 then 7
    else if pick = 4 then 8
    else if pick = 5 then 255
    else if pick = 6 then 1023
    else 17
  (n, rng')

private def genStzeroesFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (bits, rng2) := pickStzeroesBitsInRange rng1
    (mkStzeroesCase s!"fuzz/ok/top-only/bits-{bits}" #[.builder Builder.empty, intV bits], rng2)
  else if shape = 1 then
    let (bits, rng2) := pickStzeroesBitsInRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 77 else .cell Cell.empty
    (mkStzeroesCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, .builder Builder.empty, intV bits], rng3)
  else if shape = 2 then
    (mkStzeroesCase "fuzz/range/negative" #[.builder Builder.empty, intV (-1)], rng1)
  else if shape = 3 then
    (mkStzeroesCase "fuzz/range/overflow-1024" #[.builder Builder.empty, intV 1024], rng1)
  else if shape = 4 then
    (mkStzeroesProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else if shape = 5 then
    (mkStzeroesCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkStzeroesCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStzeroesCase "fuzz/type/top-not-int" #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkStzeroesCase "fuzz/type/builder-not-builder" #[intV 3, intV 2], rng1)
  else if shape = 9 then
    (mkStzeroesProgramCase "fuzz/cellov/full-builder-bits1" #[] overflowAfter1023Program, rng1)
  else if shape = 10 then
    (mkStzeroesProgramCase "fuzz/cellov-vs-range/range-wins" #[] fullBuilderThenBits1024Program, rng1)
  else
    let (bits, rng2) := pickStzeroesBitsInRange rng1
    (mkStzeroesProgramCase s!"fuzz/program/build-1023-then-overflow/bits-{bits}" #[]
      (build1023Program ++ #[.pushInt (.num bits), stzeroesInstr]), rng2)

def suite : InstrSuite where
  id := stzeroesId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array Nat := #[0, 1, 2, 7, 8, 255, 1023]
        for bits in checks do
          let expected := Builder.empty.storeBits (Array.replicate bits false)
          expectOkStack s!"ok/bits-{bits}"
            (runStzeroesDirect #[.builder Builder.empty, intV bits])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (Array.replicate 4 false)
        expectOkStack "ok/append-existing-bits"
          (runStzeroesDirect #[.builder prefBuilder, intV 4])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (Array.replicate 6 false)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStzeroesDirect #[.null, .builder Builder.empty, intV 6])
          #[.null, .builder expectedDeep]

        expectOkStack "ok/full-builder-bits0"
          (runStzeroesDirect #[.builder fullBuilder1023, intV 0])
          #[.builder fullBuilder1023] }
    ,
    { name := "unit/direct/range-and-order"
      run := do
        expectErr "range/negative"
          (runStzeroesDirect #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/overflow-1024"
          (runStzeroesDirect #[.builder Builder.empty, intV 1024]) .rangeChk
        expectErr "range/nan"
          (runStzeroesDirect #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "error-order/range-before-type-builder"
          (runStzeroesDirect #[.null, intV 1024]) .rangeChk
        expectErr "error-order/range-before-cellov"
          (runStzeroesDirect #[.builder fullBuilder1023, intV 1024]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStzeroesDirect #[]) .stkUnd
        expectErr "underflow/one-item-builder" (runStzeroesDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-item-int" (runStzeroesDirect #[intV 1]) .stkUnd

        expectErr "type/top-not-int"
          (runStzeroesDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/builder-pop-second"
          (runStzeroesDirect #[intV 2, intV 1]) .typeChk
        expectErr "type/builder-pop-second-with-valid-bits0"
          (runStzeroesDirect #[.null, intV 0]) .typeChk }
    ,
    { name := "unit/direct/cellov"
      run := do
        expectErr "cellov/full-builder-bits1"
          (runStzeroesDirect #[.builder fullBuilder1023, intV 1]) .cellOv
        expectErr "cellov/full-builder-bits17"
          (runStzeroesDirect #[.builder fullBuilder1023, intV 17]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stzeroesInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stzeroes" s0 stzeroesInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stzeroes-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStzeroesDispatchFallback #[.null])
          #[.null, intV 432] }
  ]
  oracle := #[
    mkStzeroesCase "ok/bits-0" #[.builder Builder.empty, intV 0],
    mkStzeroesCase "ok/bits-1" #[.builder Builder.empty, intV 1],
    mkStzeroesCase "ok/bits-2" #[.builder Builder.empty, intV 2],
    mkStzeroesCase "ok/bits-7" #[.builder Builder.empty, intV 7],
    mkStzeroesCase "ok/bits-8" #[.builder Builder.empty, intV 8],
    mkStzeroesCase "ok/bits-255" #[.builder Builder.empty, intV 255],
    mkStzeroesCase "ok/bits-1023" #[.builder Builder.empty, intV 1023],
    mkStzeroesCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 6],
    mkStzeroesProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,
    mkStzeroesProgramCase "ok/full-builder-bits0-via-program" #[] fullBuilderThenBits0Program,

    mkStzeroesCase "range/negative" #[.builder Builder.empty, intV (-1)],
    mkStzeroesCase "range/overflow-1024" #[.builder Builder.empty, intV 1024],
    mkStzeroesProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,
    mkStzeroesCase "range-before-type-builder" #[.null, intV 1024],
    mkStzeroesProgramCase "range-before-cellov-full-builder" #[] fullBuilderThenBits1024Program,

    mkStzeroesCase "underflow/empty" #[],
    mkStzeroesCase "underflow/one-item-builder" #[.builder Builder.empty],
    mkStzeroesCase "type/top-not-int" #[.builder Builder.empty, .null],
    mkStzeroesCase "type/builder-pop-second" #[intV 2, intV 1],

    mkStzeroesCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stzeroesSetGasExact), .tonEnvOp .setGasLimit, stzeroesInstr],
    mkStzeroesCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stzeroesSetGasExactMinusOne), .tonEnvOp .setGasLimit, stzeroesInstr],

    mkStzeroesProgramCase "program/build-1023-success" #[] build1023Program,
    mkStzeroesProgramCase "program/build-1023-then-overflow-cellov" #[] overflowAfter1023Program
  ]
  fuzz := #[
    { seed := 2026020933
      count := 320
      gen := genStzeroesFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STZEROES
