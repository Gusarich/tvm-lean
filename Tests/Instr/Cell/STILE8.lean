import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STILE8

/-
STILE8 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stLeInt unsigned=false bytes=8)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STILE8` encode: `0xcf2a`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf2a` decode to `.stLeInt false 8`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_le_int`, `dump_store_le_int` for signed 64-bit little-endian).

Branch map used for this suite:
- Lean STILE8 path: 10 branch sites / 13 terminal outcomes
  (`checkUnderflow 2`; bytes guard; pop builder/int order; capacity guard;
   NaN split; signed fit check; BE-to-LE byte reordering; success push).
- C++ STILE8 path: 8 branch sites / 11 aligned outcomes.

Key risk areas:
- operand order is builder-on-top (`[x, builder]`);
- byte order must reverse bytes, not bits;
- `cellOv` must happen before range checks on full builders;
- signed 64-bit boundaries `[-2^63, 2^63-1]` must match C++.
-/

private def stile8Id : InstrId := { name := "STILE8" }

private def stile8Instr : Instr :=
  .cellExt (.stLeInt false 8)

private def mkStile8Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stile8Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stile8Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStile8ProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stile8Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStile8Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt stile8Instr stack

private def runStile8DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runStile8DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 421)) stack

private def stile8Bits : Nat := 64

private def minInt64 : Int := -(intPow2 63)

private def maxInt64 : Int := intPow2 63 - 1

private def overInt64 : Int := intPow2 63

private def underInt64 : Int := -(intPow2 63) - 1

private def minInt64PlusOne : Int := minInt64 + 1

private def maxInt64MinusOne : Int := maxInt64 - 1

private def overInt64PlusOne : Int := overInt64 + 1

private def underInt64MinusOne : Int := underInt64 - 1

private def samplePos64 : Int := 123456789012345678

private def sampleNeg64 : Int := -123456789012345678

private def patternPos64 : Int := 0x102030405060708

private def patternNeg64 : Int := -0x102030405060708

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stile8Instr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, stile8Instr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num overInt64), .xchg0 1, stile8Instr]

private def cellovBeforeRangeUnderflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num underInt64), .xchg0 1, stile8Instr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num (-2)), .xchg0 1, stile8Instr
  ]

private def build959Program : Array Instr :=
  #[
    .newc,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 191
  ]

private def build960Program : Array Instr :=
  #[
    .newc,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 192
  ]

private def fillTo1023Program : Array Instr :=
  build959Program ++ #[.pushInt (.num 0), .xchg0 1, stile8Instr]

private def overflowAfter960Program : Array Instr :=
  build960Program ++ #[.pushInt (.num 0), .xchg0 1, stile8Instr]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, .xchg0 1, stile8Instr]

private def stile8SetGasExact : Int :=
  computeExactGasBudget stile8Instr

private def stile8SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stile8Instr

private def expectedLEBitsSigned64 (x : Int) : Except Excno BitString := do
  let be ← intToBitsTwos x stile8Bits
  pure (leBytesToBitString be 8)

private def pickStile8InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 6
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then maxInt64
    else if pick = 4 then minInt64
    else if pick = 5 then samplePos64
    else sampleNeg64
  (x, rng')

private def genStile8FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (x, rng2) := pickStile8InRange rng1
    (mkStile8Case s!"fuzz/ok/top-only/x-{x}" #[intV x, .builder Builder.empty], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStile8InRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 89 else .cell Cell.empty
    (mkStile8Case s!"fuzz/ok/deep-stack/x-{x}" #[noise, intV x, .builder Builder.empty], rng3)
  else if shape = 2 then
    (mkStile8Case "fuzz/range/overflow-pos" #[intV overInt64, .builder Builder.empty], rng1)
  else if shape = 3 then
    (mkStile8Case "fuzz/range/overflow-neg" #[intV underInt64, .builder Builder.empty], rng1)
  else if shape = 4 then
    (mkStile8Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStile8Case "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStile8Case "fuzz/type/top-not-builder" #[intV 1, .null], rng1)
  else if shape = 7 then
    (mkStile8Case "fuzz/type/second-not-int" #[.null, .builder Builder.empty], rng1)
  else if shape = 8 then
    (mkStile8ProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else
    (mkStile8ProgramCase "fuzz/cellov-before-range" #[] cellovBeforeRangeOverflowProgram, rng1)

def suite : InstrSuite where
  id := stile8Id
  unit := #[
    { name := "unit/direct/success-little-endian-and-append"
      run := do
        let checks : Array Int := #[minInt64, -1, 0, 1, samplePos64, maxInt64]
        for x in checks do
          let leBits ←
            match expectedLEBitsSigned64 x with
            | .ok bs => pure bs
            | .error e => throw (IO.userError s!"unexpected conversion error {e} for x={x}")
          let expected := Builder.empty.storeBits leBits
          expectOkStack s!"ok/x-{x}"
            (runStile8Direct #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let leBits ←
          match expectedLEBitsSigned64 (-2) with
          | .ok bs => pure bs
          | .error e => throw (IO.userError s!"unexpected conversion error {e}")
        let appended := prefBuilder.storeBits leBits
        expectOkStack "ok/append-existing-bits"
          (runStile8Direct #[intV (-2), .builder prefBuilder])
          #[.builder appended]

        let deepLeBits ←
          match expectedLEBitsSigned64 7 with
          | .ok bs => pure bs
          | .error e => throw (IO.userError s!"unexpected conversion error {e}")
        let expectedDeep := Builder.empty.storeBits deepLeBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStile8Direct #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/overflow-pos"
          (runStile8Direct #[intV overInt64, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-pos-plus-one"
          (runStile8Direct #[intV overInt64PlusOne, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg"
          (runStile8Direct #[intV underInt64, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg-minus-one"
          (runStile8Direct #[intV underInt64MinusOne, .builder Builder.empty]) .rangeChk
        expectErr "range/nan"
          (runStile8Direct #[.int .nan, .builder Builder.empty]) .rangeChk
        expectErr "range/invalid-bytes-guard"
          (runStile8DirectInstr (.cellExt (.stLeInt false 6)) #[intV 0, .builder Builder.empty]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStile8Direct #[]) .stkUnd
        expectErr "underflow/one-item" (runStile8Direct #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-item-int" (runStile8Direct #[intV 7]) .stkUnd
        expectErr "underflow/single-non-int" (runStile8Direct #[.null]) .stkUnd

        expectErr "type/builder-pop-first"
          (runStile8Direct #[intV 1, .null]) .typeChk
        expectErr "type/builder-pop-first-cell"
          (runStile8Direct #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/int-pop-second"
          (runStile8Direct #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/int-pop-second-cell"
          (runStile8Direct #[.cell Cell.empty, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStile8Direct #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-range"
      run := do
        expectErr "cellov/full-builder"
          (runStile8Direct #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStile8Direct #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStile8Direct #[intV overInt64, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-underflow-range"
          (runStile8Direct #[intV underInt64, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stile8Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stile8" s0 stile8Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.stLeInt false 6)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stile8/bytes6: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stile8/bytes6: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStile8DispatchFallback #[.null])
          #[.null, intV 421] }
  ]
  oracle := #[
    -- Branch: success path (`ok`) across signed-64 boundaries and byte-order-sensitive patterns.
    mkStile8Case "ok/min-int64" #[intV minInt64, .builder Builder.empty],
    mkStile8Case "ok/min-int64-plus-one" #[intV minInt64PlusOne, .builder Builder.empty],
    mkStile8Case "ok/max-int64" #[intV maxInt64, .builder Builder.empty],
    mkStile8Case "ok/max-int64-minus-one" #[intV maxInt64MinusOne, .builder Builder.empty],
    mkStile8Case "ok/neg-one" #[intV (-1), .builder Builder.empty],
    mkStile8Case "ok/zero" #[intV 0, .builder Builder.empty],
    mkStile8Case "ok/one" #[intV 1, .builder Builder.empty],
    mkStile8Case "ok/sample-pos64" #[intV samplePos64, .builder Builder.empty],
    mkStile8Case "ok/sample-neg64" #[intV sampleNeg64, .builder Builder.empty],
    mkStile8Case "ok/pattern-0x102030405060708" #[intV patternPos64, .builder Builder.empty],
    mkStile8Case "ok/pattern-neg-0x102030405060708" #[intV patternNeg64, .builder Builder.empty],
    mkStile8Case "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty],
    mkStile8Case "ok/deep-stack-cell-below-preserved" #[.cell Cell.empty, intV 7, .builder Builder.empty],
    mkStile8ProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    -- Branch: signed-64 `rangeChk` outcomes (positive overflow, negative overflow, NaN).
    mkStile8Case "range/overflow-pos" #[intV overInt64, .builder Builder.empty],
    mkStile8Case "range/overflow-pos-plus-one" #[intV overInt64PlusOne, .builder Builder.empty],
    mkStile8Case "range/overflow-neg" #[intV underInt64, .builder Builder.empty],
    mkStile8Case "range/overflow-neg-minus-one" #[intV underInt64MinusOne, .builder Builder.empty],
    mkStile8ProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,

    -- Branch: `checkUnderflow 2` and pop-order type checks (`builder` first, then `int`).
    mkStile8Case "underflow/empty" #[],
    mkStile8Case "underflow/one-item" #[.builder Builder.empty],
    mkStile8Case "underflow/one-item-int" #[intV 7],
    mkStile8Case "type/builder-pop-first" #[intV 1, .null],
    mkStile8Case "type/builder-pop-first-cell" #[intV 1, .cell Cell.empty],
    mkStile8Case "type/int-pop-second" #[.null, .builder Builder.empty],
    mkStile8Case "type/int-pop-second-cell" #[.cell Cell.empty, .builder Builder.empty],
    mkStile8Case "type/both-non-int-builder-first" #[.cell Cell.empty, .null],

    -- Branch: exact gas boundary around the opcode's execution cost.
    mkStile8Case "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stile8SetGasExact), .tonEnvOp .setGasLimit, stile8Instr],
    mkStile8Case "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stile8SetGasExactMinusOne), .tonEnvOp .setGasLimit, stile8Instr],

    -- Branch: capacity guard (`cellOv`) and precedence over range checks.
    mkStile8Case "cellov/full-builder-direct" #[intV 0, .builder fullBuilder1023],
    mkStile8ProgramCase "program/build-959-fill-to-1023-success" #[] fillTo1023Program,
    mkStile8ProgramCase "program/build-960-overflow-cellov" #[] overflowAfter960Program,
    mkStile8ProgramCase "program/build-1023-success" #[] build1023Program,
    mkStile8ProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStile8ProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStile8ProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram,
    mkStile8ProgramCase "program/cellov-before-range-underflow" #[] cellovBeforeRangeUnderflowProgram
  ]
  fuzz := #[
    { seed := 2026020918
      count := 500
      gen := genStile8FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STILE8
