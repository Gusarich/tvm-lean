import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STGRAMS

/-
STGRAMS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StGrams.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STGRAMS` encode: `0xfa02`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa02` decode to `.tonEnvOp .stGrams`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_store_var_integer`, `util::store_var_integer` with `len_bits=4`, `sgnd=false`).

Branch map used for this suite:
- Lean STGRAMS path: 10 branch sites / 14 terminal outcomes
  (`checkUnderflow 2`; opcode guard; `x` pop/type; `builder` pop/type;
   NaN split; negative guard; len overflow guard; capacity guard; success push).
- C++ STGRAMS path: 8 branch sites / 12 aligned outcomes
  (`check_underflow(2)`; `x` then `builder` pop; len range before capacity;
   `range_chk` / `cell_ov` / success).

Key risk areas:
- stack order is `... builder x` (`x` on top);
- unsigned `rangeChk` (negative/overflow/NaN) must win before any capacity checks;
- exact 15-byte unsigned max must pass, first 16-byte value must fail;
- error ordering under full builder must stay `rangeChk` for out-of-range `x`.
-/

private def stgramsId : InstrId := { name := "STGRAMS" }

private def stgramsInstr : Instr :=
  .tonEnvOp .stGrams

private def mkStgramsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stgramsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stgramsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStgramsProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stgramsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStgramsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStGrams stgramsInstr stack

private def runStgramsDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStGrams .add (VM.push (intV 427)) stack

private def maxUnsigned15Bytes : Int := maxUnsignedByBytes 15

private def overflowPosUnsigned15Bytes : Int := overflowUnsignedByBytes 15

private def samplePos : Int := intPow2 96 + 314159

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def fullBuilderProgramWith (x : IntVal) : Array Instr :=
  build1023Program ++ #[.pushInt x, stgramsInstr]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, stgramsInstr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 17), stgramsInstr
  ]

private def stgramsSetGasExact : Int :=
  computeExactGasBudget stgramsInstr

private def stgramsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stgramsInstr

private def pickStgramsInRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 255
    else if pick = 3 then maxUnsigned15Bytes
    else if pick = 4 then samplePos
    else intPow2 80 + 77
  (x, rng')

private def genStgramsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  if shape = 0 then
    let (x, rng2) := pickStgramsInRange rng1
    (mkStgramsCase s!"fuzz/ok/top-only/x-{x}" #[.builder Builder.empty, intV x], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStgramsInRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 117 else .cell Cell.empty
    (mkStgramsCase s!"fuzz/ok/deep-stack/x-{x}" #[noise, .builder Builder.empty, intV x], rng3)
  else if shape = 2 then
    (mkStgramsCase "fuzz/range/overflow-pos" #[.builder Builder.empty, intV overflowPosUnsigned15Bytes], rng1)
  else if shape = 3 then
    (mkStgramsCase "fuzz/range/negative" #[.builder Builder.empty, intV (-1)], rng1)
  else if shape = 4 then
    (mkStgramsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStgramsCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStgramsCase "fuzz/type/x-not-int" #[.builder Builder.empty, .null], rng1)
  else if shape = 7 then
    (mkStgramsCase "fuzz/type/builder-not-builder" #[intV 2, intV 1], rng1)
  else if shape = 8 then
    (mkStgramsProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else if shape = 9 then
    let (x, rng2) := pickStgramsInRange rng1
    (mkStgramsProgramCase s!"fuzz/cellov/in-range-x-{x}" #[] (fullBuilderProgramWith (.num x)), rng2)
  else if shape = 10 then
    (mkStgramsProgramCase "fuzz/range-before-cellov-overflow" #[]
      (fullBuilderProgramWith (.num overflowPosUnsigned15Bytes)), rng1)
  else if shape = 11 then
    (mkStgramsProgramCase "fuzz/range-before-cellov-negative" #[]
      (fullBuilderProgramWith (.num (-1))), rng1)
  else
    (mkStgramsProgramCase "fuzz/range-before-cellov-nan" #[]
      (fullBuilderProgramWith .nan), rng1)

def suite : InstrSuite where
  id := stgramsId
  unit := #[
    { name := "unit/direct/success-boundaries-and-encoding"
      run := do
        let checks : Array Int := #[0, 1, 255, 256, samplePos, maxUnsigned15Bytes]
        for x in checks do
          let expected := Builder.empty.storeBits (encodeUnsignedVarIntBits 4 x)
          expectOkStack s!"ok/x-{x}"
            (runStgramsDirect #[.builder Builder.empty, intV x])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (encodeUnsignedVarIntBits 4 17)
        expectOkStack "ok/append-existing-bits"
          (runStgramsDirect #[.builder prefBuilder, intV 17])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (encodeUnsignedVarIntBits 4 7)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStgramsDirect #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks-and-order"
      run := do
        expectErr "range/overflow-pos"
          (runStgramsDirect #[.builder Builder.empty, intV overflowPosUnsigned15Bytes]) .rangeChk
        expectErr "range/negative"
          (runStgramsDirect #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/nan"
          (runStgramsDirect #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "error-order/range-before-cellov-overflow"
          (runStgramsDirect #[.builder fullBuilder1023, intV overflowPosUnsigned15Bytes]) .rangeChk
        expectErr "error-order/range-before-cellov-negative"
          (runStgramsDirect #[.builder fullBuilder1023, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-cellov-nan"
          (runStgramsDirect #[.builder fullBuilder1023, .int .nan]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStgramsDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStgramsDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStgramsDirect #[.null]) .stkUnd

        expectErr "type/x-pop-first-top-not-int"
          (runStgramsDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/x-pop-first-top-builder"
          (runStgramsDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/builder-pop-second"
          (runStgramsDirect #[intV 2, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-in-range-path"
      run := do
        expectErr "cellov/full-builder-x0"
          (runStgramsDirect #[.builder fullBuilder1023, intV 0]) .cellOv
        expectErr "cellov/full-builder-x1"
          (runStgramsDirect #[.builder fullBuilder1023, intV 1]) .cellOv
        expectErr "cellov/full-builder-xsample"
          (runStgramsDirect #[.builder fullBuilder1023, intV samplePos]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stgramsInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stgrams" s0 stgramsInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.stVarInt false 16)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"stgrams/uint16-alias: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "stgrams/uint16-alias: expected assemble invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-tonenv-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStgramsDispatchFallback #[.null])
          #[.null, intV 427] }
  ]
  oracle := #[
    mkStgramsCase "ok/zero" #[.builder Builder.empty, intV 0],
    mkStgramsCase "ok/one" #[.builder Builder.empty, intV 1],
    mkStgramsCase "ok/255" #[.builder Builder.empty, intV 255],
    mkStgramsCase "ok/256" #[.builder Builder.empty, intV 256],
    mkStgramsCase "ok/sample-pos" #[.builder Builder.empty, intV samplePos],
    mkStgramsCase "ok/max-unsigned-15-bytes" #[.builder Builder.empty, intV maxUnsigned15Bytes],
    mkStgramsCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7],
    mkStgramsProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkStgramsCase "range/overflow-pos" #[.builder Builder.empty, intV overflowPosUnsigned15Bytes],
    mkStgramsCase "range/negative" #[.builder Builder.empty, intV (-1)],
    mkStgramsProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,
    mkStgramsProgramCase "range-before-cellov-overflow-full-builder" #[]
      (fullBuilderProgramWith (.num overflowPosUnsigned15Bytes)),
    mkStgramsProgramCase "range-before-cellov-negative-full-builder" #[]
      (fullBuilderProgramWith (.num (-1))),
    mkStgramsProgramCase "range-before-cellov-nan-full-builder" #[]
      (fullBuilderProgramWith .nan),

    mkStgramsCase "underflow/empty" #[],
    mkStgramsCase "underflow/one-item" #[.builder Builder.empty],
    mkStgramsCase "type/x-pop-first-top-not-int" #[.builder Builder.empty, .null],
    mkStgramsCase "type/x-pop-first-top-builder" #[.null, .builder Builder.empty],
    mkStgramsCase "type/builder-pop-second" #[intV 2, intV 1],

    mkStgramsCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stgramsSetGasExact), .tonEnvOp .setGasLimit, stgramsInstr],
    mkStgramsCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stgramsSetGasExactMinusOne), .tonEnvOp .setGasLimit, stgramsInstr],

    mkStgramsProgramCase "program/build-1023-success" #[] build1023Program,
    mkStgramsProgramCase "program/build-1023-overflow-cellov" #[] (fullBuilderProgramWith (.num 0)),
    mkStgramsProgramCase "program/cellov-in-range-x1" #[] (fullBuilderProgramWith (.num 1)),
    mkStgramsProgramCase "program/cellov-in-range-xsample" #[] (fullBuilderProgramWith (.num samplePos))
  ]
  fuzz := #[
    { seed := 2026020928
      count := 320
      gen := genStgramsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STGRAMS
