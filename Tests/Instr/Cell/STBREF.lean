import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STBREF

/-
STBREF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StbRef.lean` (`.stbRef false false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STBREF` encode: `0xcf11`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf11` decode to `.stbRef false false`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder_as_ref`, non-quiet).

Branch map used for this suite (STBREF only, non-rev/non-quiet):
- 5 branch sites / 7 terminal outcomes:
  (`checkUnderflow 2`; top builder pop/type; second builder pop/type;
   capacity check on refs; success path with cell-create gas and ref append).

Key risk areas:
- stack order is `... cb2 builder` (`builder` on top);
- result is `builder` with one appended ref `finalize(cb2)`;
- overflow depends only on available refs (bits are irrelevant here);
- cell-create gas is charged only on successful finalization/store path.
-/

private def stbrefId : InstrId := { name := "STBREF" }

private def stbrefInstr : Instr := .stbRef false false

private def mkStbrefCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stbrefInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStbrefProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stbrefId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStbrefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStbRef stbrefInstr stack

private def runStbrefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStbRef .add (VM.push (intV 436)) stack

private def gasForInstrWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def setGasNeedForInstrWithExtra (instr : Instr) (n : Int) (extra : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + gasForInstrWithFallback (.tonEnvOp .setGasLimit)
    + gasForInstrWithFallback instr
    + implicitRetGasPrice
    + extra

private def exactGasBudgetFixedPointWithExtra (instr : Instr) (n : Int) (extra : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := setGasNeedForInstrWithExtra instr n extra
      if n' = n then n else exactGasBudgetFixedPointWithExtra instr n' extra k

private def computeExactGasBudgetWithExtra (instr : Instr) (extra : Int) : Int :=
  exactGasBudgetFixedPointWithExtra instr 64 extra 20

private def stbrefSetGasExact : Int :=
  computeExactGasBudgetWithExtra stbrefInstr cellCreateGasPrice

private def stbrefSetGasExactMinusOne : Int :=
  if stbrefSetGasExact > 0 then stbrefSetGasExact - 1 else 0

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkBuilderProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkStbrefProgram
    (cb2Bits cb2Refs bBits bRefs : Nat)
    (cb2X : IntVal := .num 0)
    (bX : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram cb2Bits cb2Refs cb2X ++
    mkBuilderProgram bBits bRefs bX ++
    #[stbrefInstr]

private def mkStbrefProgramWithNoise
    (cb2Bits cb2Refs bBits bRefs : Nat)
    (cb2X : IntVal := .num 0)
    (bX : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkStbrefProgram cb2Bits cb2Refs bBits bRefs cb2X bX

private def mkStbrefProgramBits
    (cb2Bits bBits : Nat)
    (cb2X : IntVal := .num 0)
    (bX : IntVal := .num 0) : Array Instr :=
  mkStbrefProgram cb2Bits 0 bBits 0 cb2X bX

private def mkStbrefProgramRefs (cb2Refs bRefs : Nat) : Array Instr :=
  mkStbrefProgram 0 cb2Refs 0 bRefs

private def stbrefAppendProgram : Array Instr :=
  mkStbrefProgram 5 1 3 2 (.num 17) (.num 5)

private def stbrefAppendProgramWithNoise : Array Instr :=
  mkStbrefProgramWithNoise 4 0 2 1 (.num 9) (.num 3)

private def stbrefCb2FullBitsProgram : Array Instr :=
  build1023WithFixed .stu ++ #[.newc, stbrefInstr]

private def stbrefCellOvProgram : Array Instr :=
  mkStbrefProgramRefs 0 4

private def stbrefCellOvRichCb2Program : Array Instr :=
  mkStbrefProgram 7 2 1 4 (.num 13) (.num 6)

private def pickStbrefBitsSmall (rng : StdGen) : Nat × StdGen :=
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

private def pickStbrefRefsOk (rng : StdGen) : Nat × StdGen :=
  let (pick, rng') := randNat rng 0 3
  (pick, rng')

private def pickNoiseValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let noise : Value :=
    if pick = 0 then .null else if pick = 1 then intV 79 else .cell Cell.empty
  (noise, rng')

private def genStbrefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    (mkStbrefCase "fuzz/ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkStbrefCase "fuzz/ok/deep-stack/empty-builders"
      #[noise, .builder Builder.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    let (cb2Bits, rng2) := pickStbrefBitsSmall rng1
    let (bBits, rng3) := pickStbrefBitsSmall rng2
    (mkStbrefProgramCase s!"fuzz/ok/program-bits/cb2-{cb2Bits}-b-{bBits}" #[]
      (mkStbrefProgramBits cb2Bits bBits), rng3)
  else if shape = 3 then
    let (cb2Refs, rng2) := pickStbrefRefsOk rng1
    let (bRefs, rng3) := pickStbrefRefsOk rng2
    (mkStbrefProgramCase s!"fuzz/ok/program-refs/cb2-{cb2Refs}-b-{bRefs}" #[]
      (mkStbrefProgramRefs cb2Refs bRefs), rng3)
  else if shape = 4 then
    let (cb2Bits, rng2) := pickStbrefBitsSmall rng1
    let (cb2Refs, rng3) := pickStbrefRefsOk rng2
    let (bBits, rng4) := pickStbrefBitsSmall rng3
    let (bRefs, rng5) := pickStbrefRefsOk rng4
    (mkStbrefProgramCase
      s!"fuzz/ok/program-mixed/cb2-b{cb2Bits}-r{cb2Refs}-b-b{bBits}-r{bRefs}" #[]
      (mkStbrefProgram cb2Bits cb2Refs bBits bRefs), rng5)
  else if shape = 5 then
    (mkStbrefCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkStbrefCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStbrefCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkStbrefCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 9 then
    (mkStbrefCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else if shape = 10 then
    (mkStbrefProgramCase "fuzz/cellov/refs-overflow" #[] stbrefCellOvProgram, rng1)
  else if shape = 11 then
    (mkStbrefProgramCase "fuzz/cellov/refs-overflow-rich-cb2" #[] stbrefCellOvRichCb2Program, rng1)
  else if shape = 12 then
    (mkStbrefCase "fuzz/gas/exact-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefSetGasExact), .tonEnvOp .setGasLimit, stbrefInstr], rng1)
  else if shape = 13 then
    (mkStbrefCase "fuzz/gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrefInstr], rng1)
  else
    let (bBits, rng2) := pickStbrefBitsSmall rng1
    (mkStbrefProgramCase s!"fuzz/ok/cb2-full-1023/b-{bBits}" #[]
      (build1023WithFixed .stu ++ #[.newc] ++ appendBitsToTopBuilder bBits ++ #[stbrefInstr]), rng2)

def suite : InstrSuite where
  id := stbrefId
  unit := #[
    { name := "unit/direct/success-order-and-finalize"
      run := do
        expectOkStack "ok/empty-builders"
          (runStbrefDirect #[.builder Builder.empty, .builder Builder.empty])
          #[.builder { Builder.empty with refs := #[Builder.empty.finalize] }]

        let cb2Bits : Builder := Builder.empty.storeBits (natToBits 5 3)
        let cb2 : Builder := { cb2Bits with refs := #[Cell.empty] }
        let bBits : Builder := Builder.empty.storeBits (natToBits 2 2)
        let b : Builder := { bBits with refs := #[Cell.empty, Cell.empty] }

        let expected : Builder := { b with refs := b.refs.push cb2.finalize }
        expectOkStack "ok/non-rev-stack-order-top-builder-receives-cb2-as-ref"
          (runStbrefDirect #[.builder cb2, .builder b])
          #[.builder expected]

        let expectedSwapped : Builder := { cb2 with refs := cb2.refs.push b.finalize }
        expectOkStack "ok/order-check-swapped-input-swaps-target"
          (runStbrefDirect #[.builder b, .builder cb2])
          #[.builder expectedSwapped]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStbrefDirect #[.null, .builder cb2, .builder b])
          #[.null, .builder expected] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStbrefDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStbrefDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStbrefDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runStbrefDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runStbrefDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-refs"
      run := do
        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectErr "cellov/target-builder-already-has-4-refs"
          (runStbrefDirect #[.builder Builder.empty, .builder bRef4]) .cellOv

        let cb2Rich : Builder :=
          { (Builder.empty.storeBits (natToBits 11 4)) with refs := #[Cell.empty, Cell.empty] }
        expectErr "cellov/target-builder-full-even-with-rich-cb2"
          (runStbrefDirect #[.builder cb2Rich, .builder bRef4]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[stbrefInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stbref" s0 stbrefInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stbref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStbrefDispatchFallback #[.null])
          #[.null, intV 436] }
  ]
  oracle := #[
    mkStbrefCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkStbrefCase "ok/deep-stack-preserve-below"
      #[.null, .builder Builder.empty, .builder Builder.empty],
    mkStbrefProgramCase "ok/program/bits/cb2-0-b-0" #[] (mkStbrefProgramBits 0 0),
    mkStbrefProgramCase "ok/program/bits/cb2-1-b-0" #[] (mkStbrefProgramBits 1 0),
    mkStbrefProgramCase "ok/program/bits/cb2-0-b-1" #[] (mkStbrefProgramBits 0 1),
    mkStbrefProgramCase "ok/program/bits/cb2-2-b-3" #[] (mkStbrefProgramBits 2 3),
    mkStbrefProgramCase "ok/program/bits/cb2-3-b-2" #[] (mkStbrefProgramBits 3 2),
    mkStbrefProgramCase "ok/program/bits/cb2-8-b-7" #[] (mkStbrefProgramBits 8 7),
    mkStbrefProgramCase "ok/program/bits/cb2-15-b-15" #[] (mkStbrefProgramBits 15 15),
    mkStbrefProgramCase "ok/program/refs/cb2-0-b-0" #[] (mkStbrefProgramRefs 0 0),
    mkStbrefProgramCase "ok/program/refs/cb2-1-b-0" #[] (mkStbrefProgramRefs 1 0),
    mkStbrefProgramCase "ok/program/refs/cb2-0-b-1" #[] (mkStbrefProgramRefs 0 1),
    mkStbrefProgramCase "ok/program/refs/cb2-2-b-3" #[] (mkStbrefProgramRefs 2 3),
    mkStbrefProgramCase "ok/program/mixed/cb2-b4-r1-b-b2-r2" #[] stbrefAppendProgram,
    mkStbrefProgramCase "ok/program/mixed/with-noise-below" #[] stbrefAppendProgramWithNoise,
    mkStbrefProgramCase "ok/program/cb2-full-1023bits" #[] stbrefCb2FullBitsProgram,

    mkStbrefCase "underflow/empty" #[],
    mkStbrefCase "underflow/one-item" #[.builder Builder.empty],
    mkStbrefCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkStbrefCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkStbrefCase "type/both-non-builder" #[.null, intV 1],

    mkStbrefCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefSetGasExact), .tonEnvOp .setGasLimit, stbrefInstr],
    mkStbrefCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num stbrefSetGasExactMinusOne), .tonEnvOp .setGasLimit, stbrefInstr],

    mkStbrefProgramCase "cellov/refs-overflow-via-program" #[] stbrefCellOvProgram,
    mkStbrefProgramCase "cellov/refs-overflow-via-program-rich-cb2" #[] stbrefCellOvRichCb2Program
  ]
  fuzz := #[
    { seed := 2026021037
      count := 320
      gen := genStbrefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STBREF
