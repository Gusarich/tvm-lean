import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSAME

/-
STSAME branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StSame.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STSAME` encode: `0xcf42`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf42` decode to `.stSame`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_same` with `val=-1` for `STSAME`).

Branch map used for this suite:
- Lean STSAME path: 9 branch sites / 13 terminal outcomes
  (`checkUnderflow 3`; selector pop/type/range; bits pop/type/range; builder pop/type;
   capacity check; success push).
- C++ STSAME path: 8 branch sites / 12 aligned outcomes
  (`check_underflow(3)`; selector range; bits range; builder type; `check_space`; success).

Key risk areas:
- stack order is `... builder bits v` (`v` on top);
- selector range (`v ∈ {0,1}`) is checked before bits/builder;
- bits range is checked before builder/capacity;
- payload polarity (`v=0` all zeroes, `v=1` all ones) must be exact.
-/

private def stsameId : InstrId := { name := "STSAME" }

private def stsameInstr : Instr := .stSame

private def mkStsameCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stsameInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsameId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStsameProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsameId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStsameDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStSame stsameInstr stack

private def runStsameDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStSame .add (VM.push (intV 434)) stack

private def stsameSetGasExact : Int :=
  computeExactGasBudget stsameInstr

private def stsameSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stsameInstr

private def build1023Program : Array Instr :=
  #[.newc, .pushInt (.num 1023), .stZeroes]

private def fullBuilderThenBits0V0Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .pushInt (.num 0), stsameInstr]

private def fullBuilderThenBits0V1Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .pushInt (.num 1), stsameInstr]

private def fullBuilderThenBits1V0Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1), .pushInt (.num 0), stsameInstr]

private def fullBuilderThenBits1024V0Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1024), .pushInt (.num 0), stsameInstr]

private def rangeVNanProgram : Array Instr :=
  #[.pushInt (.num 7), .pushInt .nan, stsameInstr]

private def rangeBitsNanProgram : Array Instr :=
  #[.pushInt .nan, .pushInt (.num 1), stsameInstr]

private def appendExistingProgramV1 : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 4), .pushInt (.num 1), stsameInstr
  ]

private def appendExistingProgramV0 : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 4), .pushInt (.num 0), stsameInstr
  ]

private def pickStsameBitsInRange (rng : StdGen) : Nat × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let n : Nat :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 2
    else if pick = 3 then 7
    else if pick = 4 then 8
    else if pick = 5 then 255
    else if pick = 6 then 1023
    else 21
  (n, rng')

private def genStsameFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    let (bits, rng2) := pickStsameBitsInRange rng1
    (mkStsameCase s!"fuzz/ok/top-only/v0/bits-{bits}" #[.builder Builder.empty, intV bits, intV 0], rng2)
  else if shape = 1 then
    let (bits, rng2) := pickStsameBitsInRange rng1
    (mkStsameCase s!"fuzz/ok/top-only/v1/bits-{bits}" #[.builder Builder.empty, intV bits, intV 1], rng2)
  else if shape = 2 then
    let (bits, rng2) := pickStsameBitsInRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 61 else .cell Cell.empty
    (mkStsameCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, .builder Builder.empty, intV bits, intV 1], rng3)
  else if shape = 3 then
    (mkStsameCase "fuzz/range/v-negative" #[.builder Builder.empty, intV 7, intV (-1)], rng1)
  else if shape = 4 then
    (mkStsameCase "fuzz/range/v-overflow-2" #[.builder Builder.empty, intV 7, intV 2], rng1)
  else if shape = 5 then
    (mkStsameProgramCase "fuzz/range/v-nan-via-program" #[.builder Builder.empty] rangeVNanProgram, rng1)
  else if shape = 6 then
    (mkStsameCase "fuzz/range/bits-negative" #[.builder Builder.empty, intV (-1), intV 1], rng1)
  else if shape = 7 then
    (mkStsameCase "fuzz/range/bits-overflow-1024" #[.builder Builder.empty, intV 1024, intV 1], rng1)
  else if shape = 8 then
    (mkStsameProgramCase "fuzz/range/bits-nan-via-program" #[.builder Builder.empty] rangeBitsNanProgram, rng1)
  else if shape = 9 then
    (mkStsameCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 10 then
    (mkStsameCase "fuzz/type/v-not-int" #[.builder Builder.empty, intV 7, .null], rng1)
  else if shape = 11 then
    (mkStsameProgramCase "fuzz/cellov/full-builder-bits1" #[] fullBuilderThenBits1V0Program, rng1)
  else if shape = 12 then
    (mkStsameProgramCase "fuzz/range-before-cellov/bits1024" #[] fullBuilderThenBits1024V0Program, rng1)
  else
    let (bits, rng2) := pickStsameBitsInRange rng1
    let (v, rng3) := randNat rng2 0 1
    (mkStsameProgramCase s!"fuzz/program/build-1023-then-op/v-{v}/bits-{bits}" #[]
      (build1023Program ++ #[.pushInt (.num bits), .pushInt (.num v), stsameInstr]), rng3)

def suite : InstrSuite where
  id := stsameId
  unit := #[
    { name := "unit/direct/success-boundaries-and-polarity"
      run := do
        let checks : Array Nat := #[0, 1, 2, 7, 8, 255, 1023]
        for bits in checks do
          let expected0 := Builder.empty.storeBits (Array.replicate bits false)
          let expected1 := Builder.empty.storeBits (Array.replicate bits true)
          expectOkStack s!"ok/v0/bits-{bits}"
            (runStsameDirect #[.builder Builder.empty, intV bits, intV 0])
            #[.builder expected0]
          expectOkStack s!"ok/v1/bits-{bits}"
            (runStsameDirect #[.builder Builder.empty, intV bits, intV 1])
            #[.builder expected1]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended1 := prefBuilder.storeBits (Array.replicate 4 true)
        let appended0 := prefBuilder.storeBits (Array.replicate 4 false)
        expectOkStack "ok/append-existing-bits-v1"
          (runStsameDirect #[.builder prefBuilder, intV 4, intV 1])
          #[.builder appended1]
        expectOkStack "ok/append-existing-bits-v0"
          (runStsameDirect #[.builder prefBuilder, intV 4, intV 0])
          #[.builder appended0]

        let expectedDeep := Builder.empty.storeBits (Array.replicate 6 true)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStsameDirect #[.null, .builder Builder.empty, intV 6, intV 1])
          #[.null, .builder expectedDeep]

        expectOkStack "ok/full-builder-bits0-v0"
          (runStsameDirect #[.builder fullBuilder1023, intV 0, intV 0])
          #[.builder fullBuilder1023]
        expectOkStack "ok/full-builder-bits0-v1"
          (runStsameDirect #[.builder fullBuilder1023, intV 0, intV 1])
          #[.builder fullBuilder1023] }
    ,
    { name := "unit/direct/range-and-order"
      run := do
        expectErr "range/v-negative"
          (runStsameDirect #[.builder Builder.empty, intV 7, intV (-1)]) .rangeChk
        expectErr "range/v-overflow-2"
          (runStsameDirect #[.builder Builder.empty, intV 7, intV 2]) .rangeChk
        expectErr "range/v-nan"
          (runStsameDirect #[.builder Builder.empty, intV 7, .int .nan]) .rangeChk
        expectErr "range/bits-negative"
          (runStsameDirect #[.builder Builder.empty, intV (-1), intV 1]) .rangeChk
        expectErr "range/bits-overflow-1024"
          (runStsameDirect #[.builder Builder.empty, intV 1024, intV 1]) .rangeChk
        expectErr "range/bits-nan"
          (runStsameDirect #[.builder Builder.empty, .int .nan, intV 1]) .rangeChk

        expectErr "error-order/v-range-before-bits-range"
          (runStsameDirect #[.builder Builder.empty, intV 1024, intV 2]) .rangeChk
        expectErr "error-order/bits-range-before-builder-type"
          (runStsameDirect #[.null, intV 1024, intV 1]) .rangeChk
        expectErr "error-order/bits-range-before-cellov"
          (runStsameDirect #[.builder fullBuilder1023, intV 1024, intV 1]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStsameDirect #[]) .stkUnd
        expectErr "underflow/one-item-builder" (runStsameDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/two-items" (runStsameDirect #[.builder Builder.empty, intV 1]) .stkUnd

        expectErr "type/v-pop-first"
          (runStsameDirect #[.builder Builder.empty, intV 7, .null]) .typeChk
        expectErr "type/bits-pop-second"
          (runStsameDirect #[.builder Builder.empty, .null, intV 1]) .typeChk
        expectErr "type/builder-pop-third"
          (runStsameDirect #[intV 3, intV 2, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov"
      run := do
        expectErr "cellov/full-builder-bits1-v0"
          (runStsameDirect #[.builder fullBuilder1023, intV 1, intV 0]) .cellOv
        expectErr "cellov/full-builder-bits17-v1"
          (runStsameDirect #[.builder fullBuilder1023, intV 17, intV 1]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stsameInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stsame" s0 stsameInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stsame-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStsameDispatchFallback #[.null])
          #[.null, intV 434] }
  ]
  oracle := #[
    mkStsameCase "ok/v0-bits-0" #[.builder Builder.empty, intV 0, intV 0],
    mkStsameCase "ok/v1-bits-0" #[.builder Builder.empty, intV 0, intV 1],
    mkStsameCase "ok/v0-bits-1" #[.builder Builder.empty, intV 1, intV 0],
    mkStsameCase "ok/v1-bits-1" #[.builder Builder.empty, intV 1, intV 1],
    mkStsameCase "ok/v0-bits-8" #[.builder Builder.empty, intV 8, intV 0],
    mkStsameCase "ok/v1-bits-8" #[.builder Builder.empty, intV 8, intV 1],
    mkStsameCase "ok/v0-bits-1023" #[.builder Builder.empty, intV 1023, intV 0],
    mkStsameCase "ok/v1-bits-1023" #[.builder Builder.empty, intV 1023, intV 1],
    mkStsameCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 6, intV 1],
    mkStsameProgramCase "ok/append-existing-bits-v1-via-program" #[] appendExistingProgramV1,
    mkStsameProgramCase "ok/append-existing-bits-v0-via-program" #[] appendExistingProgramV0,
    mkStsameProgramCase "ok/full-builder-bits0-v0-via-program" #[] fullBuilderThenBits0V0Program,
    mkStsameProgramCase "ok/full-builder-bits0-v1-via-program" #[] fullBuilderThenBits0V1Program,

    mkStsameCase "range/v-negative" #[.builder Builder.empty, intV 7, intV (-1)],
    mkStsameCase "range/v-overflow-2" #[.builder Builder.empty, intV 7, intV 2],
    mkStsameProgramCase "range/v-nan-via-program" #[.builder Builder.empty] rangeVNanProgram,
    mkStsameCase "range/bits-negative" #[.builder Builder.empty, intV (-1), intV 1],
    mkStsameCase "range/bits-overflow-1024" #[.builder Builder.empty, intV 1024, intV 1],
    mkStsameProgramCase "range/bits-nan-via-program" #[.builder Builder.empty] rangeBitsNanProgram,
    mkStsameCase "range/bits-before-builder-type" #[.null, intV 1024, intV 1],
    mkStsameProgramCase "range/bits-before-cellov-full-builder" #[] fullBuilderThenBits1024V0Program,

    mkStsameCase "underflow/empty" #[],
    mkStsameCase "underflow/one-item-builder" #[.builder Builder.empty],
    mkStsameCase "underflow/two-items" #[.builder Builder.empty, intV 1],
    mkStsameCase "type/v-pop-first" #[.builder Builder.empty, intV 7, .null],
    mkStsameCase "type/bits-pop-second" #[.builder Builder.empty, .null, intV 1],
    mkStsameCase "type/builder-pop-third" #[intV 3, intV 2, intV 1],

    mkStsameCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7, intV 1]
      #[.pushInt (.num stsameSetGasExact), .tonEnvOp .setGasLimit, stsameInstr],
    mkStsameCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7, intV 1]
      #[.pushInt (.num stsameSetGasExactMinusOne), .tonEnvOp .setGasLimit, stsameInstr],

    mkStsameProgramCase "program/build-1023-success" #[] build1023Program,
    mkStsameProgramCase "program/build-1023-then-overflow-cellov" #[] fullBuilderThenBits1V0Program
  ]
  fuzz := #[
    { seed := 2026020935
      count := 500
      gen := genStsameFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSAME
