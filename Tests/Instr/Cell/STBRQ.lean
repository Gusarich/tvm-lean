import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STBRQ

/-
STBRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stb.lean` (`.stb true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STBRQ` encode: `0xcf1f`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf1f` decode to `.stb true true`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder_rev`, quiet mode).

Branch map used for this suite (STBRQ path):
- handler-match (`.stb` vs fallthrough to `next`);
- rev=true pop order (`cb2` top first, then destination `builder`);
- hard errors before quiet handling (`stkUnd`, `typeChk`);
- capacity guard over combined bits+refs;
- quiet success path pushes `[builder', 0]`;
- quiet overflow path restores `[builder, cb2]` then pushes `-1`.

Key risk areas:
- reversed stack contract (`... builder cb2`) must be preserved on quiet overflow;
- append order is destination builder first, then `cb2`;
- quiet mode affects only overflow, not underflow/type errors;
- opcode mapping must stay aligned with `0xcf1f` in both decode and assembler.
-/

private def stbrqId : InstrId := { name := "STBRQ" }

private def stbrqInstr : Instr := .stb true true

private def mkStbrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbrqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStb stbrqInstr stack

private def runStbrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStb .add (VM.push (intV 436)) stack

private def stbrqSetGasExact : Int :=
  computeExactGasBudget stbrqInstr

private def stbrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stbrqInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkBuilderBitsProgram (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x

private def mkStbrqProgramBits
    (builderBits : Nat) (cb2Bits : Nat)
    (builderX : IntVal := .num 0) (cb2X : IntVal := .num 0) : Array Instr :=
  mkBuilderBitsProgram builderBits builderX
    ++ mkBuilderBitsProgram cb2Bits cb2X
    ++ #[stbrqInstr]

private def mkStbrqProgramBitsWithNoise
    (builderBits : Nat) (cb2Bits : Nat)
    (builderX : IntVal := .num 0) (cb2X : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStbrqProgramBits builderBits cb2Bits builderX cb2X

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder refs

private def mkStbrqProgramRefs (builderRefs : Nat) (cb2Refs : Nat) : Array Instr :=
  mkBuilderWithRefsProgram builderRefs ++ mkBuilderWithRefsProgram cb2Refs ++ #[stbrqInstr]

private def mkStbrqProgramFullThenCb2Bits
    (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu ++ mkBuilderBitsProgram cb2Bits cb2X ++ #[stbrqInstr]

private def stbrqBitsCellOvProgram : Array Instr :=
  mkStbrqProgramFullThenCb2Bits 1

private def stbrqRefsCellOvProgram : Array Instr :=
  mkStbrqProgramRefs 4 1

private def stbrqAppendProgram : Array Instr :=
  mkStbrqProgramBits 5 3 (.num 17) (.num 5)

private def stbrqAppendProgramWithNoise : Array Instr :=
  mkStbrqProgramBitsWithNoise 4 2 (.num 9) (.num 3)

private def pickStbrqBitsSmall (rng : StdGen) : Nat × StdGen :=
  let (pick, rng') := randNat rng 0 6
  let n : Nat :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 2
    else if pick = 3 then 3
    else if pick = 4 then 7
    else if pick = 5 then 8
    else 15
  (n, rng')

private def pickStbrqRefsOk (rng : StdGen) : (Nat × Nat) × StdGen :=
  let (builderRefs, rng1) := randNat rng 0 4
  let (cb2Refs, rng2) := randNat rng1 0 (4 - builderRefs)
  ((builderRefs, cb2Refs), rng2)

private def pickStbrqRefsOv (rng : StdGen) : (Nat × Nat) × StdGen :=
  let (builderRefs, rng1) := randNat rng 1 4
  let minCb2 : Nat := 5 - builderRefs
  let (cb2Refs, rng2) := randNat rng1 minCb2 4
  ((builderRefs, cb2Refs), rng2)

private def genStbrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  if shape = 0 then
    (mkStbrqCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noisePick, rng2) := randNat rng1 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 73 else .cell Cell.empty
    (mkStbrqCase "fuzz/ok/deep-stack-empty-builders" #[noise, .builder Builder.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    let (builderBits, rng2) := pickStbrqBitsSmall rng1
    let (cb2Bits, rng3) := pickStbrqBitsSmall rng2
    (mkStbrqProgramCase s!"fuzz/ok/program/b-{builderBits}-cb2-{cb2Bits}" #[]
      (mkStbrqProgramBits builderBits cb2Bits), rng3)
  else if shape = 3 then
    let (builderBits, rng2) := pickStbrqBitsSmall rng1
    let (cb2Bits, rng3) := pickStbrqBitsSmall rng2
    (mkStbrqProgramCase s!"fuzz/ok/program-noise/b-{builderBits}-cb2-{cb2Bits}" #[]
      (mkStbrqProgramBitsWithNoise builderBits cb2Bits), rng3)
  else if shape = 4 then
    let ((builderRefs, cb2Refs), rng2) := pickStbrqRefsOk rng1
    (mkStbrqProgramCase s!"fuzz/ok/refs/b-{builderRefs}-cb2-{cb2Refs}" #[]
      (mkStbrqProgramRefs builderRefs cb2Refs), rng2)
  else if shape = 5 then
    (mkStbrqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkStbrqCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStbrqCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkStbrqCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 9 then
    (mkStbrqCase "fuzz/type/both-non-builder" #[.cell Cell.empty, intV 1], rng1)
  else if shape = 10 then
    let (cb2Bits, rng2) := pickStbrqBitsSmall rng1
    let bitsOv : Nat := if cb2Bits = 0 then 1 else cb2Bits
    (mkStbrqProgramCase s!"fuzz/quiet-cellov/bits/b-1023-cb2-{bitsOv}" #[]
      (mkStbrqProgramFullThenCb2Bits bitsOv), rng2)
  else if shape = 11 then
    let ((builderRefs, cb2Refs), rng2) := pickStbrqRefsOv rng1
    (mkStbrqProgramCase s!"fuzz/quiet-cellov/refs/b-{builderRefs}-cb2-{cb2Refs}" #[]
      (mkStbrqProgramRefs builderRefs cb2Refs), rng2)
  else
    (mkStbrqProgramCase "fuzz/ok/full-builder-plus-empty-cb2" #[] (mkStbrqProgramFullThenCb2Bits 0), rng1)

def suite : InstrSuite where
  id := stbrqId
  unit := #[
    { name := "unit/direct/rev-order-success-and-status"
      run := do
        expectOkStack "ok/empty-builders-code0"
          (runStbrqDirect #[.builder Builder.empty, .builder Builder.empty])
          #[.builder Builder.empty, intV 0]

        let cb2BitsBuilder := Builder.empty.storeBits (natToBits 5 3)
        let bBitsBuilder := Builder.empty.storeBits (natToBits 2 2)
        let expectedBits : Builder :=
          { bits := bBitsBuilder.bits ++ cb2BitsBuilder.bits
            refs := bBitsBuilder.refs ++ cb2BitsBuilder.refs }
        expectOkStack "ok/rev-order-builder-under-top-cb2"
          (runStbrqDirect #[.builder bBitsBuilder, .builder cb2BitsBuilder])
          #[.builder expectedBits, intV 0]

        let bRefsBuilder : Builder := { bBitsBuilder with refs := #[Cell.empty, Cell.empty] }
        let cb2RefsBuilder : Builder := { cb2BitsBuilder with refs := #[Cell.empty] }
        let expectedRefs : Builder :=
          { bits := bRefsBuilder.bits ++ cb2RefsBuilder.bits
            refs := bRefsBuilder.refs ++ cb2RefsBuilder.refs }
        expectOkStack "ok/append-refs-and-bits"
          (runStbrqDirect #[.builder bRefsBuilder, .builder cb2RefsBuilder])
          #[.builder expectedRefs, intV 0]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStbrqDirect #[.null, .builder Builder.empty, .builder Builder.empty])
          #[.null, .builder Builder.empty, intV 0] }
    ,
    { name := "unit/direct/underflow-and-type"
      run := do
        expectErr "underflow/empty" (runStbrqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbrqDirect #[.builder Builder.empty]) .stkUnd
        expectErr "type/top-not-builder"
          (runStbrqDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runStbrqDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbrqDirect #[.cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/direct/quiet-cellov-status-and-stack-restore"
      run := do
        expectOkStack "quiet-status/success-full-builder-empty-cb2"
          (runStbrqDirect #[.builder fullBuilder1023, .builder Builder.empty])
          #[.builder fullBuilder1023, intV 0]

        let cb2Bit1 := Builder.empty.storeBits (natToBits 1 1)
        expectOkStack "quiet-cellov/bits-overflow-restores-order"
          (runStbrqDirect #[.builder fullBuilder1023, .builder cb2Bit1])
          #[.builder fullBuilder1023, .builder cb2Bit1, intV (-1)]

        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        let cb2Ref1 : Builder := { Builder.empty with refs := #[Cell.empty] }
        expectOkStack "quiet-cellov/refs-overflow-restores-order"
          (runStbrqDirect #[.builder bRef4, .builder cb2Ref1])
          #[.builder bRef4, .builder cb2Ref1, intV (-1)] }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stbrqInstr, .stb true false, .stb false true, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stbrq" s0 stbrqInstr 16
        let s2 ← expectDecodeStep "decode/stbr" s1 (.stb true false) 16
        let s3 ← expectDecodeStep "decode/stbq" s2 (.stb false true) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stb-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbrqDispatchFallback #[.null])
          #[.null, intV 436] }
  ]
  oracle := #[
    mkStbrqCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbrqCase "ok/deep-stack-preserve-below" #[.null, .builder Builder.empty, .builder Builder.empty],
    mkStbrqProgramCase "ok/non-empty-append-via-program" #[] stbrqAppendProgram,
    mkStbrqProgramCase "ok/non-empty-append-with-noise-via-program" #[] stbrqAppendProgramWithNoise,

    mkStbrqProgramCase "ok/program/builder-0-cb2-0" #[] (mkStbrqProgramBits 0 0),
    mkStbrqProgramCase "ok/program/builder-1-cb2-0" #[] (mkStbrqProgramBits 1 0),
    mkStbrqProgramCase "ok/program/builder-0-cb2-1" #[] (mkStbrqProgramBits 0 1),
    mkStbrqProgramCase "ok/program/builder-2-cb2-3" #[] (mkStbrqProgramBits 2 3),
    mkStbrqProgramCase "ok/program/builder-3-cb2-2" #[] (mkStbrqProgramBits 3 2),
    mkStbrqProgramCase "ok/program/builder-7-cb2-8" #[] (mkStbrqProgramBits 7 8),
    mkStbrqProgramCase "ok/program/builder-8-cb2-7" #[] (mkStbrqProgramBits 8 7),
    mkStbrqProgramCase "ok/program/builder-15-cb2-15" #[] (mkStbrqProgramBits 15 15),
    mkStbrqProgramCase "ok/program/noise-builder-2-cb2-4" #[] (mkStbrqProgramBitsWithNoise 2 4),

    mkStbrqProgramCase "ok/program/refs-builder-0-cb2-0" #[] (mkStbrqProgramRefs 0 0),
    mkStbrqProgramCase "ok/program/refs-builder-1-cb2-2" #[] (mkStbrqProgramRefs 1 2),
    mkStbrqProgramCase "ok/program/refs-builder-2-cb2-2" #[] (mkStbrqProgramRefs 2 2),
    mkStbrqProgramCase "ok/program/refs-builder-3-cb2-1" #[] (mkStbrqProgramRefs 3 1),
    mkStbrqProgramCase "ok/program/full-builder-cb2-empty" #[] (mkStbrqProgramFullThenCb2Bits 0),

    mkStbrqCase "underflow/empty" #[],
    mkStbrqCase "underflow/one-item" #[.builder Builder.empty],
    mkStbrqCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbrqCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbrqCase "type/both-non-builder" #[.cell Cell.empty, intV 1],

    mkStbrqCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrqSetGasExact), .tonEnvOp .setGasLimit, stbrqInstr],
    mkStbrqCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrqInstr],

    mkStbrqProgramCase "quiet-cellov/bits-overflow-via-program" #[] stbrqBitsCellOvProgram,
    mkStbrqProgramCase "quiet-cellov/bits-overflow-via-program-alt" #[] (mkStbrqProgramFullThenCb2Bits 2),
    mkStbrqProgramCase "quiet-cellov/bits-overflow-via-program-alt2" #[] (mkStbrqProgramFullThenCb2Bits 7),
    mkStbrqProgramCase "quiet-cellov/refs-overflow-via-program" #[] stbrqRefsCellOvProgram,
    mkStbrqProgramCase "quiet-cellov/refs-overflow-via-program-alt" #[] (mkStbrqProgramRefs 3 2),
    mkStbrqProgramCase "quiet-cellov/refs-overflow-via-program-alt2" #[] (mkStbrqProgramRefs 2 3)
  ]
  fuzz := #[
    { seed := 2026021012
      count := 320
      gen := genStbrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STBRQ
