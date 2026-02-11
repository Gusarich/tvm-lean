import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STBQ

/-
STBQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stb.lean` (`.stb false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STBQ` encode: `0xcf1b`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf1b` decode to `.stb false true`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder`, quiet mode).

Branch map used for this suite:
- Lean STBQ specialization: 8 branch sites / 7 terminal outcomes
  (`.stb` guard; `rev` split to non-rev path; two builder pops with underflow/type outcomes;
   capacity check; quiet success status `0`; quiet overflow status `-1` with re-push).
- C++ STBQ path (quiet `exec_store_builder`): 6 branch sites / 6 aligned outcomes
  (`check_underflow(2)`; `builder` then `cb2` pop/type; `can_extend_by`;
   success push with status `0`; quiet overflow re-push with status `-1`).

Key risk areas:
- non-rev order is `... cb2 builder` (builder on top);
- append order is always `builder ++ cb2`;
- quiet overflow must not throw and must restore original pair order as `[cb2, builder, -1]`;
- quiet success must push trailing status `0`.
-/

private def stbqId : InstrId := { name := "STBQ" }

private def stbqInstr : Instr := .stb false true

private def mkStbqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStb stbqInstr stack

private def runStbqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStb .add (VM.push (intV 436)) stack

private def stbqSetGasExact : Int :=
  computeExactGasBudget stbqInstr

private def stbqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stbqInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkStbqProgramBits
    (cb2Bits : Nat) (bBits : Nat)
    (cb2X : IntVal := .num 0) (bX : IntVal := .num 0) : Array Instr :=
  #[.newc]
    ++ appendBitsToTopBuilder cb2Bits cb2X
    ++ #[.newc]
    ++ appendBitsToTopBuilder bBits bX
    ++ #[stbqInstr]

private def mkStbqProgramBitsWithNoise
    (cb2Bits : Nat) (bBits : Nat)
    (cb2X : IntVal := .num 0) (bX : IntVal := .num 0) : Array Instr :=
  #[.pushNull]
    ++ mkStbqProgramBits cb2Bits bBits cb2X bX

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder refs

private def mkStbqProgramRefs (cb2Refs : Nat) (bRefs : Nat) : Array Instr :=
  mkBuilderWithRefsProgram cb2Refs ++ mkBuilderWithRefsProgram bRefs ++ #[stbqInstr]

private def mkStbqProgramRefsWithNoise (cb2Refs : Nat) (bRefs : Nat) : Array Instr :=
  #[.pushNull] ++ mkStbqProgramRefs cb2Refs bRefs

private def mkCb2Program (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder cb2Bits cb2X

private def mkStbqProgramCb2ThenFull
    (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  mkCb2Program cb2Bits cb2X ++ build1023WithFixed .stu ++ #[stbqInstr]

private def stbqAppendProgram : Array Instr :=
  mkStbqProgramBits 5 3 (.num 17) (.num 5)

private def stbqAppendProgramWithNoise : Array Instr :=
  mkStbqProgramBitsWithNoise 4 2 (.num 9) (.num 3)

private def stbqBitsCellOvProgram : Array Instr :=
  mkStbqProgramCb2ThenFull 1

private def stbqBitsCellOvProgramAlt : Array Instr :=
  mkStbqProgramCb2ThenFull 2

private def stbqBitsCellOvProgramWithNoise : Array Instr :=
  #[.pushNull] ++ mkStbqProgramCb2ThenFull 1

private def stbqNearCapacitySuccessProgram : Array Instr :=
  mkStbqProgramCb2ThenFull 0

private def stbqRefsCellOvProgram : Array Instr :=
  mkStbqProgramRefs 1 4

private def stbqRefsCellOvProgramAlt : Array Instr :=
  mkStbqProgramRefs 2 3

private def stbqBitsSmallPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15]

private def pickStbqBitsSmall (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stbqBitsSmallPool.size - 1)
  (stbqBitsSmallPool[idx]!, rng')

private def genStbqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    (mkStbqCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noisePick, rng2) := randNat rng1 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 33 else .cell Cell.empty
    (mkStbqCase s!"fuzz/ok/deep-stack/noise-{noisePick}"
      #[noise, .builder Builder.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    let (cb2Bits, rng2) := pickStbqBitsSmall rng1
    let (bBits, rng3) := pickStbqBitsSmall rng2
    (mkStbqProgramCase s!"fuzz/ok/program/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbqProgramBits cb2Bits bBits), rng3)
  else if shape = 3 then
    let (cb2Bits, rng2) := pickStbqBitsSmall rng1
    let (bBits, rng3) := pickStbqBitsSmall rng2
    (mkStbqProgramCase s!"fuzz/ok/program-noise/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbqProgramBitsWithNoise cb2Bits bBits), rng3)
  else if shape = 4 then
    let (bRefs, rng2) := randNat rng1 0 4
    let (cb2Refs, rng3) := randNat rng2 0 (4 - bRefs)
    (mkStbqProgramCase s!"fuzz/ok/program-refs/cb2-{cb2Refs}-b-{bRefs}" #[]
      (mkStbqProgramRefs cb2Refs bRefs), rng3)
  else if shape = 5 then
    (mkStbqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkStbqCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStbqCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkStbqCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 9 then
    (mkStbqCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else if shape = 10 then
    let (cb2Bits0, rng2) := pickStbqBitsSmall rng1
    let cb2Bits := if cb2Bits0 = 0 then 1 else cb2Bits0
    (mkStbqProgramCase s!"fuzz/quiet-cellov/bits-overflow/cb2-{cb2Bits}" #[]
      (mkStbqProgramCb2ThenFull cb2Bits), rng2)
  else if shape = 11 then
    let (cb2Refs, rng2) := randNat rng1 1 3
    let bRefs := 5 - cb2Refs
    (mkStbqProgramCase s!"fuzz/quiet-cellov/refs-overflow/cb2-{cb2Refs}-b-{bRefs}" #[]
      (mkStbqProgramRefs cb2Refs bRefs), rng2)
  else if shape = 12 then
    let (cb2BitsPick, rng2) := randNat rng1 0 2
    let cb2Bits :=
      if cb2BitsPick = 0 then 0
      else if cb2BitsPick = 1 then 1
      else 2
    (mkStbqProgramCase s!"fuzz/near-capacity/bits-1023-plus-cb2-{cb2Bits}" #[]
      (mkStbqProgramCb2ThenFull cb2Bits), rng2)
  else
    (mkStbqProgramCase "fuzz/quiet-cellov/refs-overflow-noise" #[]
      (mkStbqProgramRefsWithNoise 1 4), rng1)

def suite : InstrSuite where
  id := stbqId
  unit := #[
    { name := "unit/direct/success-stack-order-and-status0"
      run := do
        expectOkStack "ok/empty-builders"
          (runStbqDirect #[.builder Builder.empty, .builder Builder.empty])
          #[.builder Builder.empty, intV 0]

        let cb2BitsBuilder := Builder.empty.storeBits (natToBits 5 3)
        let bBitsBuilder := Builder.empty.storeBits (natToBits 2 2)
        let expectedBits : Builder :=
          { bits := bBitsBuilder.bits ++ cb2BitsBuilder.bits
            refs := bBitsBuilder.refs ++ cb2BitsBuilder.refs }
        expectOkStack "ok/non-rev-order-builder-top-receives-cb2"
          (runStbqDirect #[.builder cb2BitsBuilder, .builder bBitsBuilder])
          #[.builder expectedBits, intV 0]

        let cb2RefsBuilder : Builder := { cb2BitsBuilder with refs := #[Cell.empty] }
        let bRefsBuilder : Builder := { bBitsBuilder with refs := #[Cell.empty, Cell.empty] }
        let expectedRefs : Builder :=
          { bits := bRefsBuilder.bits ++ cb2RefsBuilder.bits
            refs := bRefsBuilder.refs ++ cb2RefsBuilder.refs }
        expectOkStack "ok/append-refs-and-bits"
          (runStbqDirect #[.builder cb2RefsBuilder, .builder bRefsBuilder])
          #[.builder expectedRefs, intV 0]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStbqDirect #[.null, .builder Builder.empty, .builder Builder.empty])
          #[.null, .builder Builder.empty, intV 0] }
    ,
    { name := "unit/direct/quiet-cellov-code-minus1-and-order"
      run := do
        let cb2Bit1 := Builder.empty.storeBits (natToBits 1 1)
        expectOkStack "quiet-cellov/bits-overflow"
          (runStbqDirect #[.builder cb2Bit1, .builder fullBuilder1023])
          #[.builder cb2Bit1, .builder fullBuilder1023, intV (-1)]

        let cb2Ref1 : Builder := { Builder.empty with refs := #[Cell.empty] }
        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectOkStack "quiet-cellov/refs-overflow"
          (runStbqDirect #[.builder cb2Ref1, .builder bRef4])
          #[.builder cb2Ref1, .builder bRef4, intV (-1)]

        expectOkStack "quiet-cellov/deep-stack-preserve-below"
          (runStbqDirect #[.null, .builder cb2Bit1, .builder fullBuilder1023])
          #[.null, .builder cb2Bit1, .builder fullBuilder1023, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type"
      run := do
        expectErr "underflow/empty" (runStbqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbqDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStbqDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runStbqDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbqDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stbqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stbq" s0 stbqInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stb-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbqDispatchFallback #[.null])
          #[.null, intV 436] }
  ]
  oracle := #[
    mkStbqCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbqCase "ok/deep-stack-preserve-below" #[.null, .builder Builder.empty, .builder Builder.empty],
    mkStbqProgramCase "ok/non-empty-append-via-program" #[] stbqAppendProgram,
    mkStbqProgramCase "ok/non-empty-append-with-noise-via-program" #[] stbqAppendProgramWithNoise,

    mkStbqProgramCase "ok/program/cb2-0-b-0" #[] (mkStbqProgramBits 0 0),
    mkStbqProgramCase "ok/program/cb2-1-b-0" #[] (mkStbqProgramBits 1 0),
    mkStbqProgramCase "ok/program/cb2-0-b-1" #[] (mkStbqProgramBits 0 1),
    mkStbqProgramCase "ok/program/cb2-2-b-3" #[] (mkStbqProgramBits 2 3),
    mkStbqProgramCase "ok/program/cb2-3-b-2" #[] (mkStbqProgramBits 3 2),
    mkStbqProgramCase "ok/program/cb2-7-b-8" #[] (mkStbqProgramBits 7 8),
    mkStbqProgramCase "ok/program/cb2-8-b-7" #[] (mkStbqProgramBits 8 7),
    mkStbqProgramCase "ok/program/cb2-15-b-15" #[] (mkStbqProgramBits 15 15),

    mkStbqProgramCase "ok/program/refs-cb2-0-b-0" #[] (mkStbqProgramRefs 0 0),
    mkStbqProgramCase "ok/program/refs-cb2-1-b-0" #[] (mkStbqProgramRefs 1 0),
    mkStbqProgramCase "ok/program/refs-cb2-0-b-1" #[] (mkStbqProgramRefs 0 1),
    mkStbqProgramCase "ok/program/refs-cb2-1-b-3" #[] (mkStbqProgramRefs 1 3),
    mkStbqProgramCase "ok/program/refs-cb2-4-b-0" #[] (mkStbqProgramRefs 4 0),
    mkStbqProgramCase "ok/program/refs-cb2-2-b-2" #[] (mkStbqProgramRefs 2 2),
    mkStbqProgramCase "ok/program/b-1023-cb2-0-status0" #[] stbqNearCapacitySuccessProgram,

    mkStbqCase "underflow/empty" #[],
    mkStbqCase "underflow/one-item" #[.builder Builder.empty],
    mkStbqCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbqCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbqCase "type/both-non-builder" #[.null, intV 1],

    mkStbqCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbqSetGasExact), .tonEnvOp .setGasLimit, stbqInstr],
    mkStbqCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbqInstr],

    mkStbqProgramCase "quiet-cellov/bits-overflow-via-program" #[] stbqBitsCellOvProgram,
    mkStbqProgramCase "quiet-cellov/bits-overflow-via-program-alt" #[] stbqBitsCellOvProgramAlt,
    mkStbqProgramCase "quiet-cellov/refs-overflow-via-program" #[] stbqRefsCellOvProgram,
    mkStbqProgramCase "quiet-cellov/refs-overflow-via-program-alt" #[] stbqRefsCellOvProgramAlt,
    mkStbqProgramCase "quiet-cellov/bits-overflow-with-noise-via-program" #[] stbqBitsCellOvProgramWithNoise
  ]
  fuzz := #[
    { seed := 2026021010
      count := 500
      gen := genStbqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STBQ
