import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STBREFR

/-
STBREFR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StbRef.lean` (`.stbRef true false`)
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (reverse store-ref conventions cross-check)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf15` decode to `.stbRef true false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STBREFR` encode: `0xcf15`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder_as_ref_rev`, non-quiet).

Branch map used for this suite:
- Lean STBREFR path: 6 branch sites / 8 terminal outcomes
  (`checkUnderflow 2`; pop top builder (cb2) type; pop second builder (b) type;
   `b.canExtendBy 0 1` overflow/success; success consumes `cellCreateGasPrice` and pushes updated builder).
- C++ STBREFR path: 5 branch sites / 7 aligned outcomes
  (`check_underflow(2)`; pop `builder2` then `builder`; `can_extend_by(0,1)`; success `store_ref(finalize_copy)`).

Key risk areas:
- reverse stack order is `... builder cb2` (cb2 on top);
- only ref capacity is checked (`canExtendBy 0 1`), not bits capacity;
- cb2 is finalized into a child cell and appended as exactly one ref;
- overflow happens after both pops and before finalize/cell-create gas.
-/

private def stbrefRId : InstrId := { name := "STBREFR" }

private def stbrefRInstr : Instr := .stbRef true false

private def mkStbrefRCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbrefRInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefRId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbrefRProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefRId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbrefRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStbRef stbrefRInstr stack

private def runStbrefRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStbRef .add (VM.push (intV 531)) stack

private def gasForInstrWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def stbrefRSetGasNeed (n : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + gasForInstrWithFallback (.tonEnvOp .setGasLimit)
    + gasForInstrWithFallback stbrefRInstr
    + cellCreateGasPrice
    + implicitRetGasPrice

private def stbrefRExactGasBudgetFixedPoint (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := stbrefRSetGasNeed n
      if n' = n then n else stbrefRExactGasBudgetFixedPoint n' k

private def stbrefRSetGasExact : Int :=
  stbrefRExactGasBudgetFixedPoint 64 20

private def stbrefRSetGasExactMinusOne : Int :=
  if stbrefRSetGasExact > 0 then stbrefRSetGasExact - 1 else 0

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkBuilderProgram (bits refs : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkStbrefRProgram
    (bBits bRefs cb2Bits cb2Refs : Nat)
    (bX : IntVal := .num 0)
    (cb2X : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bBits bRefs bX
    ++ mkBuilderProgram cb2Bits cb2Refs cb2X
    ++ #[stbrefRInstr]

private def mkStbrefRProgramTarget1023
    (cb2Bits : Nat) (cb2X : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu ++ mkBuilderProgram cb2Bits 0 cb2X ++ #[stbrefRInstr]

private def stbrefROkProgramWithRefs : Array Instr :=
  mkStbrefRProgram 2 2 4 1 (.num 1) (.num 9)

private def stbrefROkProgramTarget1023 : Array Instr :=
  mkStbrefRProgramTarget1023 1 (.num 1)

private def stbrefRCellOvProgram : Array Instr :=
  mkStbrefRProgram 0 4 0 0

private def stbrefRCellOvProgramWithBits : Array Instr :=
  mkStbrefRProgram 11 4 5 1 (.num 7) (.num 19)

private def stbrefRBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 64, 127, 255, 256]

private def pickStbrefRBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stbrefRBitsBoundaryPool.size - 1)
  (stbrefRBitsBoundaryPool[idx]!, rng')

private def pickStbrefRBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStbrefRBitsBoundary rng1
  else
    randNat rng1 0 256

private def pickStbrefRRefs0To3 (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 3

private def pickStbrefRRefs0To2 (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 2

private def pickStbrefRNoise (rng : StdGen) : Value × StdGen :=
  let (k, rng') := randNat rng 0 2
  let v : Value :=
    if k = 0 then .null else if k = 1 then intV 77 else .cell Cell.empty
  (v, rng')

private def genStbrefRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    (mkStbrefRCase "fuzz/ok/init-empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noise, rng2) := pickStbrefRNoise rng1
    (mkStbrefRCase "fuzz/ok/init-deep-stack" #[noise, .builder Builder.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    let (bBits, rng2) := pickStbrefRBitsMixed rng1
    let (cb2Bits, rng3) := pickStbrefRBitsMixed rng2
    let (bRefs, rng4) := pickStbrefRRefs0To3 rng3
    let (cb2Refs, rng5) := pickStbrefRRefs0To2 rng4
    (mkStbrefRProgramCase
      s!"fuzz/ok/program/bb-{bBits}-br-{bRefs}-cb-{cb2Bits}-cr-{cb2Refs}"
      #[]
      (mkStbrefRProgram bBits bRefs cb2Bits cb2Refs),
      rng5)
  else if shape = 3 then
    let (bBits, rng2) := pickStbrefRBitsMixed rng1
    let (cb2Bits, rng3) := pickStbrefRBitsMixed rng2
    (mkStbrefRProgramCase
      s!"fuzz/ok/program/ref-boundary/br-3-bb-{bBits}-cb-{cb2Bits}"
      #[]
      (mkStbrefRProgram bBits 3 cb2Bits 1),
      rng3)
  else if shape = 4 then
    let (cb2Bits, rng2) := pickStbrefRBitsMixed rng1
    (mkStbrefRProgramCase
      s!"fuzz/ok/program/target-1023/cb-{cb2Bits}"
      #[]
      (mkStbrefRProgramTarget1023 cb2Bits),
      rng2)
  else if shape = 5 then
    (mkStbrefRCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkStbrefRCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStbrefRCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkStbrefRCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 9 then
    (mkStbrefRCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else if shape = 10 then
    let (bBits, rng2) := pickStbrefRBitsMixed rng1
    let (cb2Bits, rng3) := pickStbrefRBitsMixed rng2
    let (cb2Refs, rng4) := pickStbrefRRefs0To2 rng3
    (mkStbrefRProgramCase
      s!"fuzz/cellov/program/bb-{bBits}-br-4-cb-{cb2Bits}-cr-{cb2Refs}"
      #[]
      (mkStbrefRProgram bBits 4 cb2Bits cb2Refs),
      rng4)
  else if shape = 11 then
    let (cb2Bits, rng2) := pickStbrefRBitsMixed rng1
    (mkStbrefRProgramCase
      s!"fuzz/cellov/program/bits-heavy/br-4-cb-{cb2Bits}"
      #[]
      (mkStbrefRProgram 31 4 cb2Bits 2),
      rng2)
  else if shape = 12 then
    let (noise, rng2) := pickStbrefRNoise rng1
    let (bBits, rng3) := pickStbrefRBitsMixed rng2
    let (cb2Bits, rng4) := pickStbrefRBitsMixed rng3
    let (bRefs, rng5) := pickStbrefRRefs0To3 rng4
    let (cb2Refs, rng6) := pickStbrefRRefs0To2 rng5
    (mkStbrefRProgramCase
      s!"fuzz/ok/program-with-noise/bb-{bBits}-br-{bRefs}-cb-{cb2Bits}-cr-{cb2Refs}"
      #[noise]
      (mkStbrefRProgram bBits bRefs cb2Bits cb2Refs),
      rng6)
  else
    let (minusOne, rng2) := randBool rng1
    let budget := if minusOne then stbrefRSetGasExactMinusOne else stbrefRSetGasExact
    let tag := if minusOne then "minus-one" else "exact"
    (mkStbrefRCase s!"fuzz/gas/{tag}"
      #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num budget), .tonEnvOp .setGasLimit, stbrefRInstr], rng2)

def suite : InstrSuite where
  id := stbrefRId
  unit := #[
    { name := "unit/direct/reverse-order-success-and-preserve"
      run := do
        let child : Cell := (Builder.empty.storeBits (natToBits 3 2)).finalize
        let cb2 : Builder := { bits := natToBits 5 3, refs := #[child] }
        let b : Builder := { bits := natToBits 9 4, refs := #[Cell.empty, Cell.empty] }
        let expected : Builder := { b with refs := b.refs.push cb2.finalize }
        expectOkStack "ok/reverse-order-finalize-cb2"
          (runStbrefRDirect #[.builder b, .builder cb2])
          #[.builder expected]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStbrefRDirect #[.null, .builder b, .builder cb2])
          #[.null, .builder expected]

        let bRef3 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty] }
        let expectedRef4 : Builder := { bRef3 with refs := bRef3.refs.push Cell.empty }
        expectOkStack "ok/ref-boundary-three-to-four"
          (runStbrefRDirect #[.builder bRef3, .builder Builder.empty])
          #[.builder expectedRef4]

        let expectedBitsFull : Builder := { fullBuilder1023 with refs := #[Cell.empty] }
        expectOkStack "ok/full-bits-1023-still-accepts-ref"
          (runStbrefRDirect #[.builder fullBuilder1023, .builder Builder.empty])
          #[.builder expectedBitsFull] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStbrefRDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbrefRDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-builder" (runStbrefRDirect #[.null]) .stkUnd

        expectErr "type/top-not-builder"
          (runStbrefRDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runStbrefRDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbrefRDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-ref-capacity"
      run := do
        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        let cb2Bits := Builder.empty.storeBits (natToBits 7 3)
        expectErr "cellov/target-has-four-refs-empty-cb2"
          (runStbrefRDirect #[.builder bRef4, .builder Builder.empty]) .cellOv
        expectErr "cellov/target-has-four-refs-nonempty-cb2"
          (runStbrefRDirect #[.builder bRef4, .builder cb2Bits]) .cellOv

        let bRef4Bits : Builder :=
          { (Builder.empty.storeBits (natToBits 31 5)) with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectErr "cellov/four-refs-even-with-target-bits"
          (runStbrefRDirect #[.builder bRef4Bits, .builder Builder.empty]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stbrefRInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stbrefR" s0 stbrefRInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stbref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbrefRDispatchFallback #[.null])
          #[.null, intV 531] }
  ]
  oracle := #[
    mkStbrefRCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbrefRCase "ok/deep-stack-preserve-below" #[.null, .builder Builder.empty, .builder Builder.empty],
    mkStbrefRProgramCase "ok/program/b0r0-cb0r0" #[] (mkStbrefRProgram 0 0 0 0),
    mkStbrefRProgramCase "ok/program/b5r0-cb1r0" #[] (mkStbrefRProgram 5 0 1 0 (.num 17) (.num 1)),
    mkStbrefRProgramCase "ok/program/b0r1-cb3r0" #[] (mkStbrefRProgram 0 1 3 0 (.num 0) (.num 5)),
    mkStbrefRProgramCase "ok/program/b2r2-cb4r1" #[] stbrefROkProgramWithRefs,
    mkStbrefRProgramCase "ok/program/b0r3-cb7r0" #[] (mkStbrefRProgram 0 3 7 0 (.num 0) (.num 33)),
    mkStbrefRProgramCase "ok/program/b7r3-cb0r2" #[] (mkStbrefRProgram 7 3 0 2 (.num 9) (.num 0)),
    mkStbrefRProgramCase "ok/program/b31r1-cb256r0" #[] (mkStbrefRProgram 31 1 256 0 (.num 1) (.num 0)),
    mkStbrefRProgramCase "ok/program/b1023r0-cb1r0" #[] stbrefROkProgramTarget1023,
    mkStbrefRProgramCase "ok/program/noise-preserved" #[.null] (mkStbrefRProgram 3 1 2 1 (.num 5) (.num 3)),
    mkStbrefRProgramCase "ok/program/cb2-refs-3" #[] (mkStbrefRProgram 1 2 0 3 (.num 1) (.num 0)),

    mkStbrefRCase "underflow/empty" #[],
    mkStbrefRCase "underflow/one-item" #[.builder Builder.empty],
    mkStbrefRCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbrefRCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbrefRCase "type/both-non-builder" #[.null, intV 1],

    mkStbrefRCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefRSetGasExact), .tonEnvOp .setGasLimit, stbrefRInstr],
    mkStbrefRCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefRSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrefRInstr],

    mkStbrefRProgramCase "cellov/program/brefs4-cb-empty" #[] stbrefRCellOvProgram,
    mkStbrefRProgramCase "cellov/program/brefs4-cb-bits1" #[] (mkStbrefRProgram 0 4 1 0),
    mkStbrefRProgramCase "cellov/program/brefs4-cb-ref1" #[] (mkStbrefRProgram 0 4 0 1),
    mkStbrefRProgramCase "cellov/program/brefs4-cb-bits8-ref2" #[] (mkStbrefRProgram 12 4 8 2 (.num 7) (.num 13)),
    mkStbrefRProgramCase "cellov/program/bits-heavy" #[] stbrefRCellOvProgramWithBits
  ]
  fuzz := #[
    { seed := 2026021001
      count := 320
      gen := genStbrefRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STBREFR
