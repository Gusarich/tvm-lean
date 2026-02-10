import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STULE8

/-
STULE8 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stLeInt unsigned=true bytes=8)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STULE8` encode: `0xcf2b`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf2b` decode to `.stLeInt true 8`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_le_int`, `dump_store_le_int` for unsigned 64-bit little-endian).

Branch map used for this suite:
- Lean STULE8 path: 10 branch sites / 13 terminal outcomes
  (`checkUnderflow 2`; bytes guard; pop builder/int order; capacity guard;
   NaN split; unsigned fit check; BE-to-LE byte reordering; success push).
- C++ STULE8 path: 8 branch sites / 11 aligned outcomes.

Key risk areas:
- operand order is builder-on-top (`[x, builder]`);
- unsigned boundaries `[0, 2^64 - 1]`;
- negative inputs must fail range;
- `cellOv` must precede range errors on full builders.
-/

private def stule8Id : InstrId := { name := "STULE8" }

private def stule8Instr : Instr :=
  .cellExt (.stLeInt true 8)

private def mkStule8Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stule8Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stule8Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStule8ProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stule8Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStule8Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt stule8Instr stack

private def runStule8DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runStule8DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 423)) stack

private def stule8Bits : Nat := 64

private def maxUInt64 : Int := intPow2 64 - 1

private def nearMaxUInt64 : Int := maxUInt64 - 1

private def overUInt64 : Int := intPow2 64

private def overUInt64PlusOne : Int := overUInt64 + 1

private def highBitUInt64 : Int := intPow2 63

private def samplePos64 : Int := 123456789012345678

private def prefilled959Builder : Builder :=
  Builder.empty.storeBits (Array.replicate 959 false)

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stule8Instr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, stule8Instr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num overUInt64), .xchg0 1, stule8Instr]

private def cellovBeforeRangeNegativeProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num (-1)), .xchg0 1, stule8Instr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 17), .xchg0 1, stule8Instr
  ]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, .xchg0 1, stule8Instr]

private def stule8SetGasExact : Int :=
  computeExactGasBudget stule8Instr

private def stule8SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stule8Instr

private def expectedLEBitsUnsigned64 (x : Int) : BitString :=
  leBytesToBitString (natToBits x.toNat stule8Bits) 8

private def pickStule8InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then maxUInt64
    else if pick = 3 then nearMaxUInt64
    else if pick = 4 then highBitUInt64
    else if pick = 5 then samplePos64
    else if pick = 6 then 0x102030405060708
    else 42
  (x, rng')

private def genStule8FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (x, rng2) := pickStule8InRange rng1
    (mkStule8Case s!"fuzz/ok/top-only/x-{x}" #[intV x, .builder Builder.empty], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStule8InRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 101 else .cell Cell.empty
    (mkStule8Case s!"fuzz/ok/deep-stack/x-{x}" #[noise, intV x, .builder Builder.empty], rng3)
  else if shape = 2 then
    (mkStule8Case "fuzz/range/overflow-pos" #[intV overUInt64, .builder Builder.empty], rng1)
  else if shape = 3 then
    (mkStule8Case "fuzz/range/negative" #[intV (-1), .builder Builder.empty], rng1)
  else if shape = 4 then
    (mkStule8Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStule8Case "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStule8Case "fuzz/type/top-not-builder" #[intV 1, .null], rng1)
  else if shape = 7 then
    (mkStule8Case "fuzz/type/second-not-int" #[.null, .builder Builder.empty], rng1)
  else if shape = 8 then
    (mkStule8ProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else
    (mkStule8ProgramCase "fuzz/cellov-before-range" #[] cellovBeforeRangeOverflowProgram, rng1)

def suite : InstrSuite where
  id := stule8Id
  unit := #[
    -- Branch: success path (`ok`) + byte-order conversion + append/deep-stack behavior.
    { name := "unit/direct/success-little-endian-and-append"
      run := do
        let checks : Array Int := #[0, 1, 255, highBitUInt64, samplePos64, nearMaxUInt64, maxUInt64]
        for x in checks do
          let expected := Builder.empty.storeBits (expectedLEBitsUnsigned64 x)
          expectOkStack s!"ok/x-{x}"
            (runStule8Direct #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (expectedLEBitsUnsigned64 17)
        expectOkStack "ok/append-existing-bits"
          (runStule8Direct #[intV 17, .builder prefBuilder])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (expectedLEBitsUnsigned64 7)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStule8Direct #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    -- Branch: `rangeChk` from unsigned bounds, NaN split, and bytes guard.
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/overflow-pos"
          (runStule8Direct #[intV overUInt64, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-pos-plus-one"
          (runStule8Direct #[intV overUInt64PlusOne, .builder Builder.empty]) .rangeChk
        expectErr "range/negative"
          (runStule8Direct #[intV (-1), .builder Builder.empty]) .rangeChk
        expectErr "range/negative-two"
          (runStule8Direct #[intV (-2), .builder Builder.empty]) .rangeChk
        expectErr "range/nan"
          (runStule8Direct #[.int .nan, .builder Builder.empty]) .rangeChk
        expectErr "range/invalid-bytes-guard"
          (runStule8DirectInstr (.cellExt (.stLeInt true 6)) #[intV 0, .builder Builder.empty]) .rangeChk
        expectErr "range/invalid-bytes-guard-9"
          (runStule8DirectInstr (.cellExt (.stLeInt true 9)) #[intV 0, .builder Builder.empty]) .rangeChk }
    ,
    -- Branch: `stkUnd` and pop-order type checks (`builder` first, then `int`).
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStule8Direct #[]) .stkUnd
        expectErr "underflow/one-item" (runStule8Direct #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStule8Direct #[.null]) .stkUnd

        expectErr "type/builder-pop-first"
          (runStule8Direct #[intV 1, .null]) .typeChk
        expectErr "type/int-pop-second"
          (runStule8Direct #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStule8Direct #[.cell Cell.empty, .null]) .typeChk }
    ,
    -- Branch: capacity guard must throw `cellOv` before range checks.
    { name := "unit/direct/cellov-before-range"
      run := do
        expectErr "cellov/full-builder"
          (runStule8Direct #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStule8Direct #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-negative-range"
          (runStule8Direct #[intV (-1), .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStule8Direct #[intV overUInt64, .builder fullBuilder1023]) .cellOv }
    ,
    -- Branch: opcode encode/decode identity + neighboring opcode boundaries.
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stule8Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stule8" s0 stule8Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        let boundaryProgram : Array Instr :=
          #[stule8Instr, .cellExt (.stLeInt false 8), .cellExt (.stLeInt true 4)]
        let boundaryCode ←
          match assembleCp0 boundaryProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/boundary failed: {e}")
        let b0 := Slice.ofCell boundaryCode
        let b1 ← expectDecodeStep "decode/boundary/stule8" b0 stule8Instr 16
        let b2 ← expectDecodeStep "decode/boundary/stile8" b1 (.cellExt (.stLeInt false 8)) 16
        let b3 ← expectDecodeStep "decode/boundary/stule4" b2 (.cellExt (.stLeInt true 4)) 16
        if b3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/boundary/end: expected exhausted slice, got {b3.bitsRemaining} bits remaining")

        for badBytes in ([6, 7, 9] : List Nat) do
          match assembleCp0 [.cellExt (.stLeInt true badBytes)] with
          | .error .rangeChk => pure ()
          | .error e => throw (IO.userError s!"stule8/bytes{badBytes}: expected rangeChk, got {e}")
          | .ok _ => throw (IO.userError s!"stule8/bytes{badBytes}: expected assemble rangeChk, got success") }
    ,
    -- Branch: non-cell-ext dispatch must fall through to `next`.
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStule8DispatchFallback #[.null])
          #[.null, intV 423] }
  ]
  oracle := #[
    -- Branch: success path (`ok`) and unsigned boundary values.
    mkStule8Case "ok/zero" #[intV 0, .builder Builder.empty],
    mkStule8Case "ok/one" #[intV 1, .builder Builder.empty],
    mkStule8Case "ok/max-minus-one" #[intV nearMaxUInt64, .builder Builder.empty],
    mkStule8Case "ok/high-bit-2^63" #[intV highBitUInt64, .builder Builder.empty],
    mkStule8Case "ok/max-u64" #[intV maxUInt64, .builder Builder.empty],
    mkStule8Case "ok/sample-pos64" #[intV samplePos64, .builder Builder.empty],
    mkStule8Case "ok/pattern-0x102030405060708" #[intV 0x102030405060708, .builder Builder.empty],
    mkStule8Case "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty],
    mkStule8Case "ok/deep-stack-cell-below-preserved" #[.cell Cell.empty, intV 7, .builder Builder.empty],
    mkStule8Case "ok/prefilled-959-bits-exact-fit" #[intV 0, .builder prefilled959Builder],
    mkStule8ProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    -- Branch: range errors (`rangeChk`) from over/under bounds and NaN.
    mkStule8Case "range/overflow-pos" #[intV overUInt64, .builder Builder.empty],
    mkStule8Case "range/overflow-pos-plus-one" #[intV overUInt64PlusOne, .builder Builder.empty],
    mkStule8Case "range/negative" #[intV (-1), .builder Builder.empty],
    mkStule8Case "range/negative-two" #[intV (-2), .builder Builder.empty],
    mkStule8ProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,

    -- Branch: stack underflow (`stkUnd`) and pop-order type checks (`typeChk`).
    mkStule8Case "underflow/empty" #[],
    mkStule8Case "underflow/one-item" #[.builder Builder.empty],
    mkStule8Case "underflow/single-non-int" #[.null],
    mkStule8Case "type/builder-pop-first" #[intV 1, .null],
    mkStule8Case "type/int-pop-second" #[.null, .builder Builder.empty],
    mkStule8Case "type/both-non-int-builder-first" #[.cell Cell.empty, .null],

    -- Branch: gas boundary around exact per-instruction budget.
    mkStule8Case "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stule8SetGasExact), .tonEnvOp .setGasLimit, stule8Instr],
    mkStule8Case "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stule8SetGasExactMinusOne), .tonEnvOp .setGasLimit, stule8Instr],

    -- Branch: capacity guard (`cellOv`) including error precedence over range.
    mkStule8Case "cellov/full-builder-direct" #[intV 0, .builder fullBuilder1023],
    mkStule8ProgramCase "program/build-1023-success" #[] build1023Program,
    mkStule8ProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStule8ProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStule8ProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram,
    mkStule8ProgramCase "program/cellov-before-range-negative" #[] cellovBeforeRangeNegativeProgram
  ]
  fuzz := #[
    { seed := 2026020920
      count := 300
      gen := genStule8FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STULE8
