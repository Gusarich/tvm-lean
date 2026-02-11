import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STBREFQ

/-
STBREFQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StbRef.lean` (`.stbRef false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STBREFQ` encode: `0xcf19`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf19` decode to `.stbRef false true`)
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (adjacent `strefR` quiet conventions)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder_as_ref`, quiet mode).

Branch map used for this suite:
- Lean STBREFQ path: 8 branch sites / 12 terminal outcomes
  (`checkUnderflow 2`; non-rev branch; two builder pops/type checks;
   `canExtendBy 0 1` capacity guard; success creates ref-cell + status `0`;
   overflow quiet re-pushes original builders + status `-1`).
- C++ STBREFQ path: 7 branch sites / 10 aligned outcomes
  (`check_underflow(2)`; pop order `builder` then `builder2`; `can_extend_by`;
   success `store_ref(builder2->finalize_copy())` with quiet `0`;
   overflow quiet stack restore with `-1`).

Key risk areas:
- non-rev stack order is `... cb2 builder` (builder on top);
- success must append `finalize(cb2)` as a single reference to `builder`;
- quiet overflow must not throw and must preserve order as `cb2 builder -1`;
- success must return trailing status `0`;
- success path includes one cell-create gas charge (via finalized `cb2`).
-/

private def stbrefqId : InstrId := { name := "STBREFQ" }

private def stbrefqInstr : Instr := .stbRef false true

private def mkStbrefqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbrefqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbrefqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbrefqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStbRef stbrefqInstr stack

private def runStbrefqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStbRef .add (VM.push (intV 641)) stack

private def gasForInstrWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def setGasNeedForInstrWithExtra (instr : Instr) (extra : Int) (n : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + gasForInstrWithFallback (.tonEnvOp .setGasLimit)
    + gasForInstrWithFallback instr
    + extra
    + implicitRetGasPrice

private def exactGasBudgetWithExtraFixedPoint (instr : Instr) (extra : Int) (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := setGasNeedForInstrWithExtra instr extra n
      if n' = n then n else exactGasBudgetWithExtraFixedPoint instr extra n' k

private def computeExactGasBudgetWithExtra (instr : Instr) (extra : Int) : Int :=
  exactGasBudgetWithExtraFixedPoint instr extra 64 20

private def computeExactGasBudgetMinusOneWithExtra (instr : Instr) (extra : Int) : Int :=
  let budget := computeExactGasBudgetWithExtra instr extra
  if budget > 0 then budget - 1 else 0

private def stbrefqSetGasExact : Int :=
  computeExactGasBudgetWithExtra stbrefqInstr cellCreateGasPrice

private def stbrefqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOneWithExtra stbrefqInstr cellCreateGasPrice

private def appendBitsToTopBuilder (bits : Nat) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt (.num 0), .xchg0 1, .stu bits]

private def mkBuilderProgram (bits refs : Nat) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits ++ appendRefsToTopBuilder refs

private def mkStbrefqProgram (cb2Bits cb2Refs bBits bRefs : Nat) : Array Instr :=
  mkBuilderProgram cb2Bits cb2Refs ++ mkBuilderProgram bBits bRefs ++ #[stbrefqInstr]

private def mkStbrefqProgramWithNoise (cb2Bits cb2Refs bBits bRefs : Nat) : Array Instr :=
  #[.pushNull] ++ mkStbrefqProgram cb2Bits cb2Refs bBits bRefs

private def mkStbrefqOverflowProgram (cb2Bits cb2Refs : Nat) : Array Instr :=
  mkStbrefqProgram cb2Bits cb2Refs 0 4

private def mkStbrefqOverflowProgramWithNoise (cb2Bits cb2Refs : Nat) : Array Instr :=
  #[.pushNull] ++ mkStbrefqOverflowProgram cb2Bits cb2Refs

private def stbrefqBitsPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 15]

private def pickStbrefqBits (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stbrefqBitsPool.size - 1)
  (stbrefqBitsPool[idx]!, rng')

private def pickStbrefqCb2Refs (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 4

private def pickStbrefqBRefsOk (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 3

private def genStbrefqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    (mkStbrefqCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    (mkStbrefqCase "fuzz/ok/deep-stack-preserve-below"
      #[.null, .builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 2 then
    (mkStbrefqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkStbrefqCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 4 then
    (mkStbrefqCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 5 then
    (mkStbrefqCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStbrefqCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else if shape = 7 then
    let (cb2Bits, rng2) := pickStbrefqBits rng1
    let (cb2Refs, rng3) := pickStbrefqCb2Refs rng2
    let (bBits, rng4) := pickStbrefqBits rng3
    let (bRefs, rng5) := pickStbrefqBRefsOk rng4
    (mkStbrefqProgramCase s!"fuzz/ok/program/cb2-{cb2Bits}r{cb2Refs}-b-{bBits}r{bRefs}" #[]
      (mkStbrefqProgram cb2Bits cb2Refs bBits bRefs), rng5)
  else if shape = 8 then
    let (cb2Bits, rng2) := pickStbrefqBits rng1
    let (cb2Refs, rng3) := pickStbrefqCb2Refs rng2
    let (bBits, rng4) := pickStbrefqBits rng3
    let (bRefs, rng5) := pickStbrefqBRefsOk rng4
    (mkStbrefqProgramCase s!"fuzz/ok/program-noise/cb2-{cb2Bits}r{cb2Refs}-b-{bBits}r{bRefs}" #[]
      (mkStbrefqProgramWithNoise cb2Bits cb2Refs bBits bRefs), rng5)
  else if shape = 9 then
    let (cb2Bits, rng2) := pickStbrefqBits rng1
    let (cb2Refs, rng3) := pickStbrefqCb2Refs rng2
    (mkStbrefqProgramCase s!"fuzz/quiet-cellov/program/cb2-{cb2Bits}r{cb2Refs}" #[]
      (mkStbrefqOverflowProgram cb2Bits cb2Refs), rng3)
  else if shape = 10 then
    let (cb2Bits, rng2) := pickStbrefqBits rng1
    let (cb2Refs, rng3) := pickStbrefqCb2Refs rng2
    (mkStbrefqProgramCase s!"fuzz/quiet-cellov/program-noise/cb2-{cb2Bits}r{cb2Refs}" #[]
      (mkStbrefqOverflowProgramWithNoise cb2Bits cb2Refs), rng3)
  else if shape = 11 then
    (mkStbrefqCase "fuzz/gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefqSetGasExact), .tonEnvOp .setGasLimit, stbrefqInstr], rng1)
  else if shape = 12 then
    (mkStbrefqCase "fuzz/gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrefqInstr], rng1)
  else
    let (cb2Bits, rng2) := pickStbrefqBits rng1
    let (bBits, rng3) := pickStbrefqBits rng2
    (mkStbrefqProgramCase s!"fuzz/ok/boundary/cb2-{cb2Bits}r4-b-{bBits}r3" #[]
      (mkStbrefqProgram cb2Bits 4 bBits 3), rng3)

def suite : InstrSuite where
  id := stbrefqId
  unit := #[
    { name := "unit/direct/success-stack-order-status-and-preserve"
      run := do
        let expectedEmpty : Builder := { Builder.empty with refs := #[Builder.empty.finalize] }
        expectOkStack "ok/empty-builders"
          (runStbrefqDirect #[.builder Builder.empty, .builder Builder.empty])
          #[.builder expectedEmpty, intV 0]

        let cb2Child : Cell := (Builder.empty.storeBits (natToBits 3 2)).finalize
        let cb2Bits := Builder.empty.storeBits (natToBits 5 3)
        let cb2 : Builder := { cb2Bits with refs := #[cb2Child] }
        let bBits := Builder.empty.storeBits (natToBits 2 2)
        let b : Builder := { bBits with refs := #[Cell.empty, Cell.empty] }
        let expected : Builder := { b with refs := b.refs.push cb2.finalize }
        expectOkStack "ok/non-rev-builder-top-receives-finalized-cb2"
          (runStbrefqDirect #[.builder cb2, .builder b])
          #[.builder expected, intV 0]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStbrefqDirect #[.null, .builder Builder.empty, .builder Builder.empty])
          #[.null, .builder expectedEmpty, intV 0] }
    ,
    { name := "unit/direct/quiet-cellov-status-minus1"
      run := do
        let cb2 : Builder := { Builder.empty.storeBits (natToBits 1 1) with refs := #[Cell.empty] }
        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectOkStack "quiet-cellov/restore-order"
          (runStbrefqDirect #[.builder cb2, .builder bRef4])
          #[.builder cb2, .builder bRef4, intV (-1)]

        expectOkStack "quiet-cellov/deep-stack-preserve-below"
          (runStbrefqDirect #[.null, .builder cb2, .builder bRef4])
          #[.null, .builder cb2, .builder bRef4, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type"
      run := do
        expectErr "underflow/empty" (runStbrefqDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbrefqDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-builder" (runStbrefqDirect #[.null]) .stkUnd

        expectErr "type/top-not-builder"
          (runStbrefqDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runStbrefqDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbrefqDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stbrefqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stbrefq" s0 stbrefqInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stbrefq-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbrefqDispatchFallback #[.null])
          #[.null, intV 641] }
  ]
  oracle := #[
    mkStbrefqCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbrefqCase "ok/deep-stack-preserve-below" #[.null, .builder Builder.empty, .builder Builder.empty],

    mkStbrefqProgramCase "ok/program/cb2-0r0-b-0r0" #[] (mkStbrefqProgram 0 0 0 0),
    mkStbrefqProgramCase "ok/program/cb2-1r0-b-0r0" #[] (mkStbrefqProgram 1 0 0 0),
    mkStbrefqProgramCase "ok/program/cb2-3r1-b-1r0" #[] (mkStbrefqProgram 3 1 1 0),
    mkStbrefqProgramCase "ok/program/cb2-0r2-b-2r1" #[] (mkStbrefqProgram 0 2 2 1),
    mkStbrefqProgramCase "ok/program/cb2-2r1-b-3r2" #[] (mkStbrefqProgram 2 1 3 2),
    mkStbrefqProgramCase "ok/program/cb2-7r0-b-4r3" #[] (mkStbrefqProgram 7 0 4 3),
    mkStbrefqProgramCase "ok/program/cb2-8r1-b-5r3" #[] (mkStbrefqProgram 8 1 5 3),
    mkStbrefqProgramCase "ok/program/cb2-1r4-b-0r0" #[] (mkStbrefqProgram 1 4 0 0),
    mkStbrefqProgramCase "ok/program-noise/cb2-2r1-b-1r1" #[] (mkStbrefqProgramWithNoise 2 1 1 1),
    mkStbrefqProgramCase "ok/program-noise/cb2-0r0-b-0r3" #[] (mkStbrefqProgramWithNoise 0 0 0 3),

    mkStbrefqCase "underflow/empty" #[],
    mkStbrefqCase "underflow/one-item" #[.builder Builder.empty],
    mkStbrefqCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbrefqCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbrefqCase "type/both-non-builder" #[.null, intV 1],

    mkStbrefqCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefqSetGasExact), .tonEnvOp .setGasLimit, stbrefqInstr],
    mkStbrefqCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrefqInstr],

    mkStbrefqProgramCase "quiet-cellov/program/cb2-0r0-b-refs4" #[] (mkStbrefqOverflowProgram 0 0),
    mkStbrefqProgramCase "quiet-cellov/program/cb2-1r0-b-refs4" #[] (mkStbrefqOverflowProgram 1 0),
    mkStbrefqProgramCase "quiet-cellov/program/cb2-0r1-b-refs4" #[] (mkStbrefqOverflowProgram 0 1),
    mkStbrefqProgramCase "quiet-cellov/program/cb2-7r2-b-refs4" #[] (mkStbrefqOverflowProgram 7 2),
    mkStbrefqProgramCase "quiet-cellov/program/cb2-8r4-b-refs4" #[] (mkStbrefqOverflowProgram 8 4),
    mkStbrefqProgramCase "quiet-cellov/program-noise/cb2-2r1-b-refs4" #[] (mkStbrefqOverflowProgramWithNoise 2 1),
    mkStbrefqProgramCase "quiet-cellov/program-noise/cb2-0r0-b-refs4" #[] (mkStbrefqOverflowProgramWithNoise 0 0)
  ]
  fuzz := #[
    { seed := 2026021019
      count := 500
      gen := genStbrefqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STBREFQ
