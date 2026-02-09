import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STILE4

/-
STILE4 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stLeInt unsigned=false bytes=4)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STILE4` encode: `0xcf28`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf28` decode to `.stLeInt false 4`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_le_int`, `dump_store_le_int` for signed 32-bit little-endian).

Branch map used for this suite:
- Lean STILE4 path: 10 branch sites / 13 terminal outcomes
  (`checkUnderflow 2`; bytes guard; pop builder/int order; capacity guard;
   NaN split; signed fit check; BE-to-LE byte reordering; success push).
- C++ STILE4 path: 8 branch sites / 11 aligned outcomes.

Key risk areas:
- operand order is builder-on-top (`[x, builder]`);
- byte order must reverse per-byte chunks (not bitwise reverse);
- `cellOv` must happen before range checks on full builders;
- signed 32-bit boundaries `[-2^31, 2^31-1]` must match C++.
-/

private def stile4Id : InstrId := { name := "STILE4" }

private def stile4Instr : Instr :=
  .cellExt (.stLeInt false 4)

private def mkStile4Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stile4Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stile4Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStile4ProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stile4Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStile4Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt stile4Instr stack

private def runStile4DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runStile4DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 420)) stack

private def stile4Bits : Nat := 32

private def minInt32 : Int := -(intPow2 31)

private def maxInt32 : Int := intPow2 31 - 1

private def overInt32 : Int := intPow2 31

private def underInt32 : Int := -(intPow2 31) - 1

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stile4Instr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, stile4Instr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num overInt32), .xchg0 1, stile4Instr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num (-2)), .xchg0 1, stile4Instr
  ]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, .xchg0 1, stile4Instr]

private def stile4SetGasExact : Int :=
  computeExactGasBudget stile4Instr

private def stile4SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stile4Instr

private def expectedLEBitsSigned32 (x : Int) : Except Excno BitString := do
  let be ← intToBitsTwos x stile4Bits
  pure (leBytesToBitString be 4)

private def pickStile4InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 6
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then maxInt32
    else if pick = 4 then minInt32
    else if pick = 5 then 123456789
    else -123456789
  (x, rng')

private def genStile4FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (x, rng2) := pickStile4InRange rng1
    (mkStile4Case s!"fuzz/ok/top-only/x-{x}" #[intV x, .builder Builder.empty], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStile4InRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 83 else .cell Cell.empty
    (mkStile4Case s!"fuzz/ok/deep-stack/x-{x}" #[noise, intV x, .builder Builder.empty], rng3)
  else if shape = 2 then
    (mkStile4Case "fuzz/range/overflow-pos" #[intV overInt32, .builder Builder.empty], rng1)
  else if shape = 3 then
    (mkStile4Case "fuzz/range/overflow-neg" #[intV underInt32, .builder Builder.empty], rng1)
  else if shape = 4 then
    (mkStile4Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStile4Case "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStile4Case "fuzz/type/top-not-builder" #[intV 1, .null], rng1)
  else if shape = 7 then
    (mkStile4Case "fuzz/type/second-not-int" #[.null, .builder Builder.empty], rng1)
  else if shape = 8 then
    (mkStile4ProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else
    (mkStile4ProgramCase "fuzz/cellov-before-range" #[] cellovBeforeRangeOverflowProgram, rng1)

def suite : InstrSuite where
  id := stile4Id
  unit := #[
    { name := "unit/direct/success-little-endian-and-append"
      run := do
        let checks : Array Int := #[minInt32, -1, 0, 1, 0x1234567, maxInt32]
        for x in checks do
          let leBits ←
            match expectedLEBitsSigned32 x with
            | .ok bs => pure bs
            | .error e => throw (IO.userError s!"unexpected conversion error {e} for x={x}")
          let expected := Builder.empty.storeBits leBits
          expectOkStack s!"ok/x-{x}"
            (runStile4Direct #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let leBits ←
          match expectedLEBitsSigned32 (-2) with
          | .ok bs => pure bs
          | .error e => throw (IO.userError s!"unexpected conversion error {e}")
        let appended := prefBuilder.storeBits leBits
        expectOkStack "ok/append-existing-bits"
          (runStile4Direct #[intV (-2), .builder prefBuilder])
          #[.builder appended]

        let deepLeBits ←
          match expectedLEBitsSigned32 7 with
          | .ok bs => pure bs
          | .error e => throw (IO.userError s!"unexpected conversion error {e}")
        let expectedDeep := Builder.empty.storeBits deepLeBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStile4Direct #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/overflow-pos"
          (runStile4Direct #[intV overInt32, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg"
          (runStile4Direct #[intV underInt32, .builder Builder.empty]) .rangeChk
        expectErr "range/nan"
          (runStile4Direct #[.int .nan, .builder Builder.empty]) .rangeChk
        expectErr "range/invalid-bytes-guard"
          (runStile4DirectInstr (.cellExt (.stLeInt false 6)) #[intV 0, .builder Builder.empty]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStile4Direct #[]) .stkUnd
        expectErr "underflow/one-item" (runStile4Direct #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStile4Direct #[.null]) .stkUnd

        expectErr "type/builder-pop-first"
          (runStile4Direct #[intV 1, .null]) .typeChk
        expectErr "type/int-pop-second"
          (runStile4Direct #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStile4Direct #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-range"
      run := do
        expectErr "cellov/full-builder"
          (runStile4Direct #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStile4Direct #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStile4Direct #[intV overInt32, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stile4Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stile4" s0 stile4Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.stLeInt false 6)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stile4/bytes6: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stile4/bytes6: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStile4DispatchFallback #[.null])
          #[.null, intV 420] }
  ]
  oracle := #[
    mkStile4Case "ok/min-int32" #[intV minInt32, .builder Builder.empty],
    mkStile4Case "ok/max-int32" #[intV maxInt32, .builder Builder.empty],
    mkStile4Case "ok/neg-one" #[intV (-1), .builder Builder.empty],
    mkStile4Case "ok/zero" #[intV 0, .builder Builder.empty],
    mkStile4Case "ok/one" #[intV 1, .builder Builder.empty],
    mkStile4Case "ok/pattern-0x1234567" #[intV 0x1234567, .builder Builder.empty],
    mkStile4Case "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty],
    mkStile4ProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkStile4Case "range/overflow-pos" #[intV overInt32, .builder Builder.empty],
    mkStile4Case "range/overflow-neg" #[intV underInt32, .builder Builder.empty],
    mkStile4ProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,

    mkStile4Case "underflow/empty" #[],
    mkStile4Case "underflow/one-item" #[.builder Builder.empty],
    mkStile4Case "type/builder-pop-first" #[intV 1, .null],
    mkStile4Case "type/int-pop-second" #[.null, .builder Builder.empty],

    mkStile4Case "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stile4SetGasExact), .tonEnvOp .setGasLimit, stile4Instr],
    mkStile4Case "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stile4SetGasExactMinusOne), .tonEnvOp .setGasLimit, stile4Instr],

    mkStile4ProgramCase "program/build-1023-success" #[] build1023Program,
    mkStile4ProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStile4ProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStile4ProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020917
      count := 300
      gen := genStile4FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STILE4
