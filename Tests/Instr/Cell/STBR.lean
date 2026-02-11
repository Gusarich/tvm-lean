import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STBR

/-
STBR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stb.lean` (`.stb true false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STBR` encode: `0xcf17`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf17` decode to `.stb true false`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder_rev`, non-quiet).

Branch map used for this suite:
- Lean STBR path: 7 branch sites / 10 terminal outcomes
  (`checkUnderflow 2`; mode guard; top builder pop/type; second builder pop/type;
   capacity check on bits+refs; success append).
- C++ STBR path: 6 branch sites / 9 aligned outcomes
  (`check_underflow(2)`; `cb2` then `builder` pops; `can_extend_by`; success or `cell_ov`).

Key risk areas:
- rev stack order is `... builder cb2` (cb2 on top);
- result builder is `builder ++ cb2` (not the opposite order);
- capacity checks account for both bits and refs;
- in non-quiet mode overflow throws `cellOv` (no status code push).
-/

private def stbrId : InstrId := { name := "STBR" }

private def stbrInstr : Instr := .stb true false

private def mkStbrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbrProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStb stbrInstr stack

private def runStbrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStb .add (VM.push (intV 911)) stack

private def stbrSetGasExact : Int :=
  computeExactGasBudget stbrInstr

private def stbrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stbrInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkStbrProgramBits
    (bBits : Nat) (cb2Bits : Nat)
    (bX : IntVal := .num 0) (cb2X : IntVal := .num 0) : Array Instr :=
  #[.newc]
    ++ appendBitsToTopBuilder bBits bX
    ++ #[.newc]
    ++ appendBitsToTopBuilder cb2Bits cb2X
    ++ #[stbrInstr]

private def mkStbrProgramBitsWithNoise
    (bBits : Nat) (cb2Bits : Nat)
    (bX : IntVal := .num 0) (cb2X : IntVal := .num 0) : Array Instr :=
  #[.pushNull]
    ++ mkStbrProgramBits bBits cb2Bits bX cb2X

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder refs

private def mkStbrProgramRefs (bRefs : Nat) (cb2Refs : Nat) : Array Instr :=
  mkBuilderWithRefsProgram bRefs ++ mkBuilderWithRefsProgram cb2Refs ++ #[stbrInstr]

private def mkCb2Program (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder cb2Bits cb2X

private def mkStbrProgramFullThenCb2
    (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu ++ mkCb2Program cb2Bits cb2X ++ #[stbrInstr]

private def stbrBitsCellOvProgram : Array Instr :=
  mkStbrProgramFullThenCb2 1

private def stbrRefsCellOvProgram : Array Instr :=
  mkStbrProgramRefs 4 1

private def stbrAppendProgram : Array Instr :=
  mkStbrProgramBits 3 5 (.num 5) (.num 17)

private def stbrAppendProgramWithNoise : Array Instr :=
  mkStbrProgramBitsWithNoise 2 4 (.num 3) (.num 9)

private def stbrBitsSmallPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15]

private def stbrBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 7, 8, 15, 31, 63, 127, 255, 256]

private def stbrOverflowBitsPool : Array Nat :=
  #[1, 2, 7, 8, 15]

private def stbrRefsSuccessPool : Array (Nat × Nat) :=
  #[(0, 0), (1, 0), (0, 1), (2, 1), (1, 2), (2, 2), (3, 1), (4, 0)]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickStbrRefPair (rng : StdGen) : (Nat × Nat) × StdGen :=
  let (idx, rng') := randNat rng 0 (stbrRefsSuccessPool.size - 1)
  (stbrRefsSuccessPool[idx]!, rng')

private def genStbrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    (mkStbrCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    (mkStbrCase "fuzz/ok/deep-stack-preserve-below"
      #[.null, .builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 2 then
    let (bBits, rng2) := pickNatFromPool stbrBitsSmallPool rng1
    let (cb2Bits, rng3) := pickNatFromPool stbrBitsSmallPool rng2
    (mkStbrProgramCase s!"fuzz/ok/program/b-{bBits}-cb2-{cb2Bits}" #[]
      (mkStbrProgramBits bBits cb2Bits), rng3)
  else if shape = 3 then
    let (bBits, rng2) := pickNatFromPool stbrBitsBoundaryPool rng1
    let (cb2Bits, rng3) := pickNatFromPool stbrBitsBoundaryPool rng2
    (mkStbrProgramCase s!"fuzz/ok/program-boundary/b-{bBits}-cb2-{cb2Bits}" #[]
      (mkStbrProgramBits bBits cb2Bits), rng3)
  else if shape = 4 then
    let (bBits, rng2) := pickNatFromPool stbrBitsSmallPool rng1
    let (cb2Bits, rng3) := pickNatFromPool stbrBitsSmallPool rng2
    (mkStbrProgramCase s!"fuzz/ok/program-noise/b-{bBits}-cb2-{cb2Bits}" #[]
      (mkStbrProgramBitsWithNoise bBits cb2Bits), rng3)
  else if shape = 5 then
    let ((bRefs, cb2Refs), rng2) := pickStbrRefPair rng1
    (mkStbrProgramCase s!"fuzz/ok/refs/b-{bRefs}-cb2-{cb2Refs}" #[]
      (mkStbrProgramRefs bRefs cb2Refs), rng2)
  else if shape = 6 then
    (mkStbrCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkStbrCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 8 then
    (mkStbrCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 9 then
    (mkStbrCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 10 then
    (mkStbrCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else if shape = 11 then
    let (ovBits, rng2) := pickNatFromPool stbrOverflowBitsPool rng1
    (mkStbrProgramCase s!"fuzz/cellov/bits-overflow/cb2-{ovBits}" #[]
      (mkStbrProgramFullThenCb2 ovBits), rng2)
  else if shape = 12 then
    (mkStbrProgramCase "fuzz/cellov/refs-overflow" #[] stbrRefsCellOvProgram, rng1)
  else if shape = 13 then
    (mkStbrCase "fuzz/gas/exact-cost-succeeds"
      #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrSetGasExact), .tonEnvOp .setGasLimit, stbrInstr], rng1)
  else
    (mkStbrCase "fuzz/gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrInstr], rng1)

def suite : InstrSuite where
  id := stbrId
  unit := #[
    { name := "unit/direct/success-order-and-append"
      run := do
        expectOkStack "ok/empty-builders"
          (runStbrDirect #[.builder Builder.empty, .builder Builder.empty])
          #[.builder Builder.empty]

        let bBitsBuilder := Builder.empty.storeBits (natToBits 2 2)
        let cb2BitsBuilder := Builder.empty.storeBits (natToBits 5 3)
        let expectedBits : Builder :=
          { bits := bBitsBuilder.bits ++ cb2BitsBuilder.bits
            refs := bBitsBuilder.refs ++ cb2BitsBuilder.refs }
        expectOkStack "ok/rev-order-cb2-top-builder-receives-cb2"
          (runStbrDirect #[.builder bBitsBuilder, .builder cb2BitsBuilder])
          #[.builder expectedBits]

        let bRefsBuilder : Builder := { bBitsBuilder with refs := #[Cell.empty, Cell.empty] }
        let cb2RefsBuilder : Builder := { cb2BitsBuilder with refs := #[Cell.empty] }
        let expectedRefs : Builder :=
          { bits := bRefsBuilder.bits ++ cb2RefsBuilder.bits
            refs := bRefsBuilder.refs ++ cb2RefsBuilder.refs }
        expectOkStack "ok/append-refs-and-bits"
          (runStbrDirect #[.builder bRefsBuilder, .builder cb2RefsBuilder])
          #[.builder expectedRefs]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStbrDirect #[.null, .builder Builder.empty, .builder Builder.empty])
          #[.null, .builder Builder.empty] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStbrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbrDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStbrDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runStbrDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbrDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-bits-and-refs"
      run := do
        let cb2Bit1 := Builder.empty.storeBits (natToBits 1 1)
        expectErr "cellov/bits-overflow"
          (runStbrDirect #[.builder fullBuilder1023, .builder cb2Bit1]) .cellOv

        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        let cb2Ref1 : Builder := { Builder.empty with refs := #[Cell.empty] }
        expectErr "cellov/refs-overflow"
          (runStbrDirect #[.builder bRef4, .builder cb2Ref1]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stbrInstr, .stb true true, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stbr" s0 stbrInstr 16
        let s2 ← expectDecodeStep "decode/stbrq" s1 (.stb true true) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stbr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbrDispatchFallback #[.null])
          #[.null, intV 911] }
  ]
  oracle := #[
    mkStbrCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbrCase "ok/deep-stack-preserve-below" #[.null, .builder Builder.empty, .builder Builder.empty],
    mkStbrProgramCase "ok/non-empty-append-via-program" #[] stbrAppendProgram,
    mkStbrProgramCase "ok/non-empty-append-with-noise-via-program" #[] stbrAppendProgramWithNoise,

    mkStbrProgramCase "ok/program/b-0-cb2-0" #[] (mkStbrProgramBits 0 0),
    mkStbrProgramCase "ok/program/b-1-cb2-0" #[] (mkStbrProgramBits 1 0),
    mkStbrProgramCase "ok/program/b-0-cb2-1" #[] (mkStbrProgramBits 0 1),
    mkStbrProgramCase "ok/program/b-2-cb2-3" #[] (mkStbrProgramBits 2 3),
    mkStbrProgramCase "ok/program/b-3-cb2-2" #[] (mkStbrProgramBits 3 2),
    mkStbrProgramCase "ok/program/b-7-cb2-8" #[] (mkStbrProgramBits 7 8),
    mkStbrProgramCase "ok/program/b-8-cb2-7" #[] (mkStbrProgramBits 8 7),
    mkStbrProgramCase "ok/program/b-15-cb2-15" #[] (mkStbrProgramBits 15 15),
    mkStbrProgramCase "ok/program/b-255-cb2-1" #[] (mkStbrProgramBits 255 1),
    mkStbrProgramCase "ok/program/full-builder-plus-empty-cb2" #[] (mkStbrProgramFullThenCb2 0),

    mkStbrProgramCase "ok/program/refs-b-3-cb2-1" #[] (mkStbrProgramRefs 3 1),
    mkStbrProgramCase "ok/program/refs-b-4-cb2-0" #[] (mkStbrProgramRefs 4 0),
    mkStbrProgramCase "ok/program/refs-b-2-cb2-2" #[] (mkStbrProgramRefs 2 2),

    mkStbrCase "underflow/empty" #[],
    mkStbrCase "underflow/one-item" #[.builder Builder.empty],
    mkStbrCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbrCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbrCase "type/both-non-builder" #[.null, intV 1],

    mkStbrCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrSetGasExact), .tonEnvOp .setGasLimit, stbrInstr],
    mkStbrCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrInstr],

    mkStbrProgramCase "cellov/bits-overflow/full-plus-1" #[] stbrBitsCellOvProgram,
    mkStbrProgramCase "cellov/bits-overflow/full-plus-2" #[] (mkStbrProgramFullThenCb2 2),
    mkStbrProgramCase "cellov/bits-overflow/full-plus-7" #[] (mkStbrProgramFullThenCb2 7),
    mkStbrProgramCase "cellov/refs-overflow/b-4-cb2-1" #[] stbrRefsCellOvProgram
  ]
  fuzz := #[
    { seed := 2026021001
      count := 500
      gen := genStbrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STBR
