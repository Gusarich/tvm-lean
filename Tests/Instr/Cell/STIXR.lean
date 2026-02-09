import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STIXR

/-
STIXR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=false rev=true quiet=false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STIXR` encode: `0xcf02`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common` with args bit `rev=1`).

Branch map used for this suite:
- Lean STIXR path: 11 branch sites / 15 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=true pop order; builder capacity;
   fits check including `bits=0`; quiet=false throw path; success push).
- C++ STIXR path (args=2): 8 branch sites / 12 aligned outcomes
  (`check_underflow(3)`; bits range [0..257]; reversed pop order; capacity; signed fit).

Key risk areas:
- bits are popped first; bits failures must happen before x/builder type checks;
- reversed pop order (`x` first, then `builder`) controls type/error ordering;
- `bits=0` is valid only for `x=0`;
- `cellOv` must win over value-range errors when builder is already full.
-/

private def stixrId : InstrId := { name := "STIXR" }

private def stixrInstr : Instr :=
  .stIntVar false true false

private def mkStixrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stixrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStixrProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stixrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStixrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stixrInstr stack

private def runStixrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 408)) stack

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def overflowPosSignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 (bits - 1)

private def overflowNegSignedBits (bits : Nat) : Int :=
  if bits = 0 then -1 else -(intPow2 (bits - 1)) - 1

private def build1023Program : Array Instr :=
  build1023WithVarRev stixrInstr

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .pushInt (.num 1), stixrInstr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .pushInt (.num 1), stixrInstr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1), .pushInt (.num 1), stixrInstr]

private def stixrSetGasExact : Int :=
  computeExactGasBudget stixrInstr

private def stixrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stixrInstr

private def stixrBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257]

private def pickStixrBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stixrBitsBoundaryPool.size - 1)
  (stixrBitsBoundaryPool[idx]!, rng')

private def pickStixrBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStixrBitsBoundary rng1
  else
    randNat rng1 0 257

private def pickStixrInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let lo := minSignedBits bits
  let hi := maxSignedBits bits
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if bits = 0 then
      0
    else if pick = 0 then
      0
    else if pick = 1 then
      1
    else if pick = 2 then
      -1
    else if pick = 3 then
      hi
    else if pick = 4 then
      lo
    else if hi > lo then
      hi - 1
    else
      lo
  (x, rng')

private def genStixrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStixrBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStixrInRange bits rng2
    (mkStixrCase s!"fuzz/ok/top-only/bits-{bits}" #[.builder Builder.empty, intV x, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStixrInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 31 else .cell Cell.empty
    (mkStixrCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, .builder Builder.empty, intV x, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixrCase s!"fuzz/range/overflow-pos/bits-{bitsOv}"
      #[.builder Builder.empty, intV (overflowPosSignedBits bitsOv), intV bitsOv], rng2)
  else if shape = 3 then
    let bitsOv := if bits = 257 then 256 else bits
    (mkStixrCase s!"fuzz/range/overflow-neg/bits-{bitsOv}"
      #[.builder Builder.empty, intV (overflowNegSignedBits bitsOv), intV bitsOv], rng2)
  else if shape = 4 then
    (mkStixrCase "fuzz/range/bits-too-large" #[.builder Builder.empty, intV 0, intV 258], rng2)
  else if shape = 5 then
    (mkStixrCase "fuzz/range/bits-negative" #[.builder Builder.empty, intV 0, intV (-1)], rng2)
  else if shape = 6 then
    (mkStixrCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStixrCase s!"fuzz/underflow/two-items/bits-{bits}" #[.builder Builder.empty, intV 1], rng2)
  else if shape = 8 then
    (mkStixrCase s!"fuzz/type/x-not-int/bits-{bits}" #[.builder Builder.empty, .null, intV bits], rng2)
  else if shape = 9 then
    (mkStixrCase s!"fuzz/type/builder-not-builder/bits-{bits}" #[.null, intV 1, intV bits], rng2)
  else
    (mkStixrProgramCase s!"fuzz/range/nan-program/bits-{bits}"
      #[.builder Builder.empty]
      #[.pushInt .nan, .pushInt (.num bits), stixrInstr], rng2)

def suite : InstrSuite where
  id := stixrId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (0, 0),
            (1, -1),
            (1, 0),
            (8, -128),
            (8, 127),
            (257, minInt257),
            (257, maxInt257)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          let bs : BitString ←
            if bits = 0 then
              pure #[]
            else
              match intToBitsTwos x bits with
              | .ok out => pure out
              | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e} for bits={bits}, x={x}")
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStixrDirect #[.builder Builder.empty, intV x, intV bits])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appendedBits ←
          match intToBitsTwos (-3) 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let appended := prefBuilder.storeBits appendedBits
        expectOkStack "ok/append-existing-bits"
          (runStixrDirect #[.builder prefBuilder, intV (-3), intV 4])
          #[.builder appended]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStixrDirect #[.null, .builder Builder.empty, intV 7, intV 4])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks-for-value-and-bits"
      run := do
        expectErr "range/bits0-x1"
          (runStixrDirect #[.builder Builder.empty, intV 1, intV 0]) .rangeChk
        expectErr "range/bits0-xminus1"
          (runStixrDirect #[.builder Builder.empty, intV (-1), intV 0]) .rangeChk
        expectErr "range/overflow-pos-bits1"
          (runStixrDirect #[.builder Builder.empty, intV 1, intV 1]) .rangeChk
        expectErr "range/overflow-neg-bits1"
          (runStixrDirect #[.builder Builder.empty, intV (-2), intV 1]) .rangeChk
        expectErr "range/overflow-pos-bits8"
          (runStixrDirect #[.builder Builder.empty, intV 128, intV 8]) .rangeChk
        expectErr "range/overflow-neg-bits8"
          (runStixrDirect #[.builder Builder.empty, intV (-129), intV 8]) .rangeChk
        expectErr "range/nan"
          (runStixrDirect #[.builder Builder.empty, .int .nan, intV 8]) .rangeChk

        expectErr "range/bits-too-large"
          (runStixrDirect #[.builder Builder.empty, intV 0, intV 258]) .rangeChk
        expectErr "range/bits-negative"
          (runStixrDirect #[.builder Builder.empty, intV 0, intV (-1)]) .rangeChk
        expectErr "range/bits-nan"
          (runStixrDirect #[.builder Builder.empty, intV 0, .int .nan]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStixrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStixrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStixrDirect #[.builder Builder.empty, intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runStixrDirect #[.null]) .stkUnd

        expectErr "type/pop-x-first-after-bits"
          (runStixrDirect #[.builder Builder.empty, .null, intV 8]) .typeChk
        expectErr "type/pop-builder-second"
          (runStixrDirect #[.null, intV 1, intV 8]) .typeChk
        expectErr "type/both-non-int-x-first"
          (runStixrDirect #[.null, .cell Cell.empty, intV 8]) .typeChk

        expectErr "error-order/bits-range-before-x-type"
          (runStixrDirect #[.builder Builder.empty, .null, intV 258]) .rangeChk
        expectErr "error-order/bits-range-before-builder-type"
          (runStixrDirect #[.null, intV 0, intV (-1)]) .rangeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStixrDirect #[.builder fullBuilder1023, intV 0, intV 1]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStixrDirect #[.builder fullBuilder1023, .int .nan, intV 1]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStixrDirect #[.builder fullBuilder1023, intV 1, intV 1]) .cellOv }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stixrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stixr" s0 stixrInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStixrDispatchFallback #[.null])
          #[.null, intV 408] }
  ]
  oracle := #[
    mkStixrCase "ok/bits-0-zero" #[.builder Builder.empty, intV 0, intV 0],
    mkStixrCase "ok/bits-1-min" #[.builder Builder.empty, intV (-1), intV 1],
    mkStixrCase "ok/bits-1-max" #[.builder Builder.empty, intV 0, intV 1],
    mkStixrCase "ok/bits-8-min" #[.builder Builder.empty, intV (-128), intV 8],
    mkStixrCase "ok/bits-8-max" #[.builder Builder.empty, intV 127, intV 8],
    mkStixrCase "ok/bits-16-min" #[.builder Builder.empty, intV (-32768), intV 16],
    mkStixrCase "ok/bits-16-max" #[.builder Builder.empty, intV 32767, intV 16],
    mkStixrCase "ok/bits-257-minInt257" #[.builder Builder.empty, intV minInt257, intV 257],
    mkStixrCase "ok/bits-257-maxInt257" #[.builder Builder.empty, intV maxInt257, intV 257],
    mkStixrCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7, intV 4],

    mkStixrCase "range/value-bits0-pos" #[.builder Builder.empty, intV 1, intV 0],
    mkStixrCase "range/value-bits0-neg" #[.builder Builder.empty, intV (-1), intV 0],
    mkStixrCase "range/overflow-pos-bits1" #[.builder Builder.empty, intV 1, intV 1],
    mkStixrCase "range/overflow-neg-bits1" #[.builder Builder.empty, intV (-2), intV 1],
    mkStixrCase "range/overflow-pos-bits8" #[.builder Builder.empty, intV 128, intV 8],
    mkStixrCase "range/overflow-neg-bits8" #[.builder Builder.empty, intV (-129), intV 8],
    mkStixrProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .pushInt (.num 8), stixrInstr],
    mkStixrCase "range/bits-too-large" #[.builder Builder.empty, intV 0, intV 258],
    mkStixrCase "range/bits-negative" #[.builder Builder.empty, intV 0, intV (-1)],

    mkStixrCase "underflow/empty" #[],
    mkStixrCase "underflow/one-item" #[intV 1],
    mkStixrCase "underflow/two-items" #[.builder Builder.empty, intV 1],
    mkStixrCase "type/x-not-int-after-bits" #[.builder Builder.empty, .null, intV 8],
    mkStixrCase "type/builder-not-builder" #[.null, intV 1, intV 8],

    mkStixrCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stixrSetGasExact), .tonEnvOp .setGasLimit, stixrInstr],
    mkStixrCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stixrSetGasExactMinusOne), .tonEnvOp .setGasLimit, stixrInstr],

    mkStixrProgramCase "program/build-1023-success" #[] build1023Program,
    mkStixrProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStixrProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStixrProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020905
      count := 300
      gen := genStixrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STIXR
