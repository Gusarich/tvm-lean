import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STULE4

/-
STULE4 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stLeInt unsigned=true bytes=4)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STULE4` encode: `0xcf29`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf29` decode to `.stLeInt true 4`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_le_int`, `dump_store_le_int` for unsigned 32-bit little-endian).

Branch map used for this suite:
- Lean STULE4 path: 10 branch sites / 13 terminal outcomes
  (`checkUnderflow 2`; bytes guard; pop builder/int order; capacity guard;
   NaN split; unsigned fit check; BE-to-LE byte reordering; success push).
- C++ STULE4 path: 8 branch sites / 11 aligned outcomes.

Key risk areas:
- operand order is builder-on-top (`[x, builder]`);
- unsigned boundaries `[0, 2^32 - 1]`;
- negative inputs must fail range, not type;
- `cellOv` must precede range errors on full builders.
-/

private def stule4Id : InstrId := { name := "STULE4" }

private def stule4Instr : Instr :=
  .cellExt (.stLeInt true 4)

private def mkStule4Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stule4Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stule4Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStule4ProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stule4Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStule4Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt stule4Instr stack

private def runStule4DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runStule4DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 422)) stack

private def stule4Bits : Nat := 32

private def maxUInt32 : Int := intPow2 32 - 1

private def overUInt32 : Int := intPow2 32

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stule4Instr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, stule4Instr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num overUInt32), .xchg0 1, stule4Instr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 17), .xchg0 1, stule4Instr
  ]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, .xchg0 1, stule4Instr]

private def stule4SetGasExact : Int :=
  computeExactGasBudget stule4Instr

private def stule4SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stule4Instr

private def expectedLEBitsUnsigned32 (x : Int) : BitString :=
  leBytesToBitString (natToBits x.toNat stule4Bits) 4

private def pickStule4InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then maxUInt32
    else if pick = 3 then 123456789
    else if pick = 4 then 0x1020304
    else 42
  (x, rng')

private def genStule4FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (x, rng2) := pickStule4InRange rng1
    (mkStule4Case s!"fuzz/ok/top-only/x-{x}" #[intV x, .builder Builder.empty], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStule4InRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 97 else .cell Cell.empty
    (mkStule4Case s!"fuzz/ok/deep-stack/x-{x}" #[noise, intV x, .builder Builder.empty], rng3)
  else if shape = 2 then
    (mkStule4Case "fuzz/range/overflow-pos" #[intV overUInt32, .builder Builder.empty], rng1)
  else if shape = 3 then
    (mkStule4Case "fuzz/range/negative" #[intV (-1), .builder Builder.empty], rng1)
  else if shape = 4 then
    (mkStule4Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStule4Case "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStule4Case "fuzz/type/top-not-builder" #[intV 1, .null], rng1)
  else if shape = 7 then
    (mkStule4Case "fuzz/type/second-not-int" #[.null, .builder Builder.empty], rng1)
  else if shape = 8 then
    (mkStule4ProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else
    (mkStule4ProgramCase "fuzz/cellov-before-range" #[] cellovBeforeRangeOverflowProgram, rng1)

def suite : InstrSuite where
  id := stule4Id
  unit := #[
    { name := "unit/direct/success-little-endian-and-append"
      run := do
        let checks : Array Int := #[0, 1, 255, 0x1234567, maxUInt32]
        for x in checks do
          let expected := Builder.empty.storeBits (expectedLEBitsUnsigned32 x)
          expectOkStack s!"ok/x-{x}"
            (runStule4Direct #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (expectedLEBitsUnsigned32 17)
        expectOkStack "ok/append-existing-bits"
          (runStule4Direct #[intV 17, .builder prefBuilder])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (expectedLEBitsUnsigned32 7)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStule4Direct #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/overflow-pos"
          (runStule4Direct #[intV overUInt32, .builder Builder.empty]) .rangeChk
        expectErr "range/negative"
          (runStule4Direct #[intV (-1), .builder Builder.empty]) .rangeChk
        expectErr "range/nan"
          (runStule4Direct #[.int .nan, .builder Builder.empty]) .rangeChk
        expectErr "range/invalid-bytes-guard"
          (runStule4DirectInstr (.cellExt (.stLeInt true 6)) #[intV 0, .builder Builder.empty]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStule4Direct #[]) .stkUnd
        expectErr "underflow/one-item" (runStule4Direct #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStule4Direct #[.null]) .stkUnd

        expectErr "type/builder-pop-first"
          (runStule4Direct #[intV 1, .null]) .typeChk
        expectErr "type/int-pop-second"
          (runStule4Direct #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStule4Direct #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-range"
      run := do
        expectErr "cellov/full-builder"
          (runStule4Direct #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStule4Direct #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStule4Direct #[intV overUInt32, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stule4Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stule4" s0 stule4Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.stLeInt true 6)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stule4/bytes6: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stule4/bytes6: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStule4DispatchFallback #[.null])
          #[.null, intV 422] }
  ]
  oracle := #[
    mkStule4Case "ok/zero" #[intV 0, .builder Builder.empty],
    mkStule4Case "ok/one" #[intV 1, .builder Builder.empty],
    mkStule4Case "ok/max-u32" #[intV maxUInt32, .builder Builder.empty],
    mkStule4Case "ok/pattern-0x1234567" #[intV 0x1234567, .builder Builder.empty],
    mkStule4Case "ok/pattern-0x1020304" #[intV 0x1020304, .builder Builder.empty],
    mkStule4Case "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty],
    mkStule4ProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkStule4Case "range/overflow-pos" #[intV overUInt32, .builder Builder.empty],
    mkStule4Case "range/negative" #[intV (-1), .builder Builder.empty],
    mkStule4ProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,

    mkStule4Case "underflow/empty" #[],
    mkStule4Case "underflow/one-item" #[.builder Builder.empty],
    mkStule4Case "type/builder-pop-first" #[intV 1, .null],
    mkStule4Case "type/int-pop-second" #[.null, .builder Builder.empty],

    mkStule4Case "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stule4SetGasExact), .tonEnvOp .setGasLimit, stule4Instr],
    mkStule4Case "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stule4SetGasExactMinusOne), .tonEnvOp .setGasLimit, stule4Instr],

    mkStule4ProgramCase "program/build-1023-success" #[] build1023Program,
    mkStule4ProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStule4ProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStule4ProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020919
      count := 300
      gen := genStule4FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STULE4
