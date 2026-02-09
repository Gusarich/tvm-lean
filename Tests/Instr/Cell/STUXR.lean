import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STUXR

/-
STUXR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=true rev=true quiet=false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STUXR` encode: `0xcf03`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common` with args bit `rev=1`).

Branch map used for this suite:
- Lean STUXR path: 11 branch sites / 15 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=true pop order; builder capacity;
   fits check including `bits=0`; quiet=false throw path; success push).
- C++ STUXR path (args=3): 8 branch sites / 12 aligned outcomes
  (`check_underflow(3)`; bits range [0..256]; reversed pop order; capacity; unsigned fit).

Key risk areas:
- bits are popped first; bits failures must happen before x/builder type checks;
- reversed pop order (`x` first, then `builder`) controls type/error ordering;
- `bits=0` is valid only for `x=0`;
- `cellOv` must win over value-range errors when builder is already full.
-/

private def stuxrId : InstrId := { name := "STUXR" }

private def stuxrInstr : Instr :=
  .stIntVar true true false

private def mkStuxrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stuxrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStuxrProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStuxrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stuxrInstr stack

private def runStuxrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 409)) stack

private def maxUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 bits - 1

private def overflowUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 bits

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithVarRev stuxrInstr

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .pushInt (.num 1), stuxrInstr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .pushInt (.num 1), stuxrInstr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 2), .pushInt (.num 1), stuxrInstr]

private def stuxrSetGasExact : Int :=
  computeExactGasBudget stuxrInstr

private def stuxrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stuxrInstr

private def stuxrBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStuxrBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stuxrBitsBoundaryPool.size - 1)
  (stuxrBitsBoundaryPool[idx]!, rng')

private def pickStuxrBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStuxrBitsBoundary rng1
  else
    randNat rng1 0 256

private def pickStuxrInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let hi := maxUnsignedBits bits
  let (pick, rng') := randNat rng 0 4
  let x : Int :=
    if bits = 0 then
      0
    else if pick = 0 then
      0
    else if pick = 1 then
      1
    else if pick = 2 then
      hi
    else if pick = 3 then
      if hi > 0 then hi - 1 else 0
    else
      if hi > 1 then hi / 2 else hi
  (x, rng')

private def genStuxrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStuxrBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStuxrInRange bits rng2
    (mkStuxrCase s!"fuzz/ok/top-only/bits-{bits}" #[.builder Builder.empty, intV x, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStuxrInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 37 else .cell Cell.empty
    (mkStuxrCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, .builder Builder.empty, intV x, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 256 then 255 else bits
    (mkStuxrCase s!"fuzz/range/overflow-pos/bits-{bitsOv}"
      #[.builder Builder.empty, intV (overflowUnsignedBits bitsOv), intV bitsOv], rng2)
  else if shape = 3 then
    (mkStuxrCase s!"fuzz/range/negative/bits-{bits}" #[.builder Builder.empty, intV (-1), intV bits], rng2)
  else if shape = 4 then
    (mkStuxrCase "fuzz/range/bits-too-large" #[.builder Builder.empty, intV 0, intV 257], rng2)
  else if shape = 5 then
    (mkStuxrCase "fuzz/range/bits-negative" #[.builder Builder.empty, intV 0, intV (-1)], rng2)
  else if shape = 6 then
    (mkStuxrCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStuxrCase s!"fuzz/underflow/two-items/bits-{bits}" #[.builder Builder.empty, intV 1], rng2)
  else if shape = 8 then
    (mkStuxrCase s!"fuzz/type/x-not-int/bits-{bits}" #[.builder Builder.empty, .null, intV bits], rng2)
  else if shape = 9 then
    (mkStuxrCase s!"fuzz/type/builder-not-builder/bits-{bits}" #[.null, intV 1, intV bits], rng2)
  else
    (mkStuxrProgramCase s!"fuzz/range/nan-program/bits-{bits}"
      #[.builder Builder.empty]
      #[.pushInt .nan, .pushInt (.num bits), stuxrInstr], rng2)

def suite : InstrSuite where
  id := stuxrId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (0, 0),
            (1, 0),
            (1, 1),
            (8, 0),
            (8, 255),
            (256, 0),
            (256, maxUInt256)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          let bs : BitString :=
            if bits = 0 then #[]
            else natToBits x.toNat bits
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStuxrDirect #[.builder Builder.empty, intV x, intV bits])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (natToBits 17 5)
        expectOkStack "ok/append-existing-bits"
          (runStuxrDirect #[.builder prefBuilder, intV 17, intV 5])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStuxrDirect #[.null, .builder Builder.empty, intV 7, intV 4])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks-for-value-and-bits"
      run := do
        expectErr "range/bits0-x1"
          (runStuxrDirect #[.builder Builder.empty, intV 1, intV 0]) .rangeChk
        expectErr "range/bits0-xminus1"
          (runStuxrDirect #[.builder Builder.empty, intV (-1), intV 0]) .rangeChk
        expectErr "range/overflow-bits1"
          (runStuxrDirect #[.builder Builder.empty, intV 2, intV 1]) .rangeChk
        expectErr "range/negative-bits1"
          (runStuxrDirect #[.builder Builder.empty, intV (-1), intV 1]) .rangeChk
        expectErr "range/overflow-bits8"
          (runStuxrDirect #[.builder Builder.empty, intV 256, intV 8]) .rangeChk
        expectErr "range/negative-bits8"
          (runStuxrDirect #[.builder Builder.empty, intV (-1), intV 8]) .rangeChk
        expectErr "range/overflow-bits256"
          (runStuxrDirect #[.builder Builder.empty, intV overUInt256, intV 256]) .rangeChk
        expectErr "range/negative-bits256"
          (runStuxrDirect #[.builder Builder.empty, intV (-1), intV 256]) .rangeChk
        expectErr "range/nan"
          (runStuxrDirect #[.builder Builder.empty, .int .nan, intV 8]) .rangeChk

        expectErr "range/bits-too-large"
          (runStuxrDirect #[.builder Builder.empty, intV 0, intV 257]) .rangeChk
        expectErr "range/bits-negative"
          (runStuxrDirect #[.builder Builder.empty, intV 0, intV (-1)]) .rangeChk
        expectErr "range/bits-nan"
          (runStuxrDirect #[.builder Builder.empty, intV 0, .int .nan]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStuxrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStuxrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStuxrDirect #[.builder Builder.empty, intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runStuxrDirect #[.null]) .stkUnd

        expectErr "type/pop-x-first-after-bits"
          (runStuxrDirect #[.builder Builder.empty, .null, intV 8]) .typeChk
        expectErr "type/pop-builder-second"
          (runStuxrDirect #[.null, intV 1, intV 8]) .typeChk
        expectErr "type/both-non-int-x-first"
          (runStuxrDirect #[.null, .cell Cell.empty, intV 8]) .typeChk

        expectErr "error-order/bits-range-before-x-type"
          (runStuxrDirect #[.builder Builder.empty, .null, intV 257]) .rangeChk
        expectErr "error-order/bits-range-before-builder-type"
          (runStuxrDirect #[.null, intV 0, intV (-1)]) .rangeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStuxrDirect #[.builder fullBuilder1023, intV 0, intV 1]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStuxrDirect #[.builder fullBuilder1023, .int .nan, intV 1]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStuxrDirect #[.builder fullBuilder1023, intV 2, intV 1]) .cellOv }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stuxrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stuxr" s0 stuxrInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStuxrDispatchFallback #[.null])
          #[.null, intV 409] }
  ]
  oracle := #[
    mkStuxrCase "ok/bits-0-zero" #[.builder Builder.empty, intV 0, intV 0],
    mkStuxrCase "ok/bits-1-zero" #[.builder Builder.empty, intV 0, intV 1],
    mkStuxrCase "ok/bits-1-one" #[.builder Builder.empty, intV 1, intV 1],
    mkStuxrCase "ok/bits-8-max" #[.builder Builder.empty, intV 255, intV 8],
    mkStuxrCase "ok/bits-16-max" #[.builder Builder.empty, intV 65535, intV 16],
    mkStuxrCase "ok/bits-256-max" #[.builder Builder.empty, intV maxUInt256, intV 256],
    mkStuxrCase "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7, intV 4],

    mkStuxrCase "range/value-bits0-pos" #[.builder Builder.empty, intV 1, intV 0],
    mkStuxrCase "range/value-bits0-neg" #[.builder Builder.empty, intV (-1), intV 0],
    mkStuxrCase "range/overflow-bits1" #[.builder Builder.empty, intV 2, intV 1],
    mkStuxrCase "range/negative-bits1" #[.builder Builder.empty, intV (-1), intV 1],
    mkStuxrCase "range/overflow-bits8" #[.builder Builder.empty, intV 256, intV 8],
    mkStuxrCase "range/negative-bits8" #[.builder Builder.empty, intV (-1), intV 8],
    mkStuxrCase "range/overflow-bits255" #[.builder Builder.empty, intV (intPow2 255), intV 255],
    mkStuxrCase "range/negative-bits256" #[.builder Builder.empty, intV (-1), intV 256],
    mkStuxrProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .pushInt (.num 8), stuxrInstr],
    mkStuxrCase "range/bits-too-large" #[.builder Builder.empty, intV 0, intV 257],
    mkStuxrCase "range/bits-negative" #[.builder Builder.empty, intV 0, intV (-1)],

    mkStuxrCase "underflow/empty" #[],
    mkStuxrCase "underflow/one-item" #[intV 1],
    mkStuxrCase "underflow/two-items" #[.builder Builder.empty, intV 1],
    mkStuxrCase "type/x-not-int-after-bits" #[.builder Builder.empty, .null, intV 8],
    mkStuxrCase "type/builder-not-builder" #[.null, intV 1, intV 8],

    mkStuxrCase "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stuxrSetGasExact), .tonEnvOp .setGasLimit, stuxrInstr],
    mkStuxrCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7, intV 8]
      #[.pushInt (.num stuxrSetGasExactMinusOne), .tonEnvOp .setGasLimit, stuxrInstr],

    mkStuxrProgramCase "program/build-1023-success" #[] build1023Program,
    mkStuxrProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStuxrProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStuxrProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020906
      count := 300
      gen := genStuxrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STUXR
