import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STUX

/-
STUX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntVar.lean` (`.stIntVar unsigned=true rev=false quiet=false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STUX` encode: `0xcf01`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf00..0xcf07` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_var`, `exec_store_int_common`).

Branch map used for this suite:
- Lean STUX path: 11 branch sites / 15 terminal outcomes
  (`checkUnderflow 3`; bits pop/range; rev=false pop order; builder capacity;
   fits check including `bits=0`; quiet=false throw path; success push).
- C++ STUX path (args=1): 8 branch sites / 12 aligned outcomes
  (`check_underflow(3)`; bits range [0..256]; pop order; capacity; unsigned fit).

Key risk areas:
- bits are popped first; bits range/type failures must happen before builder/int type checks;
- `bits=0` is valid only for `x=0` (stores zero bits);
- unsigned boundary off-by-one for variable width;
- `cellOv` must win over value-range errors when builder is already full.
-/

private def stuxId : InstrId := { name := "STUX" }

private def stuxInstr : Instr :=
  .stIntVar true false false

private def mkStuxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stuxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStuxProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStuxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntVar stuxInstr stack

private def runStuxDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntVar .add (VM.push (intV 407)) stack

private def maxUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then
    0
  else
    intPow2 bits - 1

private def overflowUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then
    1
  else
    intPow2 bits

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithVar stuxInstr

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, .pushInt (.num 1), stuxInstr]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, .pushInt (.num 1), stuxInstr]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 2), .xchg0 1, .pushInt (.num 1), stuxInstr]

private def stuxSetGasExact : Int :=
  computeExactGasBudget stuxInstr

private def stuxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stuxInstr

private def stuxBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStuxBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stuxBitsBoundaryPool.size - 1)
  (stuxBitsBoundaryPool[idx]!, rng')

private def pickStuxBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStuxBitsBoundary rng1
  else
    randNat rng1 0 256

private def pickStuxInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
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

private def genStuxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStuxBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStuxInRange bits rng2
    (mkStuxCase s!"fuzz/ok/top-only/bits-{bits}" #[intV x, .builder Builder.empty, intV bits], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStuxInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 29 else .cell Cell.empty
    (mkStuxCase s!"fuzz/ok/deep-stack/bits-{bits}" #[noise, intV x, .builder Builder.empty, intV bits], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 256 then 255 else bits
    (mkStuxCase s!"fuzz/range/overflow-pos/bits-{bitsOv}"
      #[intV (overflowUnsignedBits bitsOv), .builder Builder.empty, intV bitsOv], rng2)
  else if shape = 3 then
    (mkStuxCase s!"fuzz/range/negative/bits-{bits}" #[intV (-1), .builder Builder.empty, intV bits], rng2)
  else if shape = 4 then
    (mkStuxCase "fuzz/range/bits-too-large" #[intV 0, .builder Builder.empty, intV 257], rng2)
  else if shape = 5 then
    (mkStuxCase "fuzz/range/bits-negative" #[intV 0, .builder Builder.empty, intV (-1)], rng2)
  else if shape = 6 then
    (mkStuxCase s!"fuzz/underflow/empty/bits-{bits}" #[], rng2)
  else if shape = 7 then
    (mkStuxCase s!"fuzz/underflow/two-items/bits-{bits}" #[intV 1, .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStuxCase s!"fuzz/type/top-not-builder/bits-{bits}" #[intV 1, .null, intV bits], rng2)
  else if shape = 9 then
    (mkStuxCase s!"fuzz/type/second-not-int/bits-{bits}" #[.null, .builder Builder.empty, intV bits], rng2)
  else
    (mkStuxProgramCase s!"fuzz/range/nan-program/bits-{bits}"
      #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, .pushInt (.num bits), stuxInstr], rng2)

def suite : InstrSuite where
  id := stuxId
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
            (runStuxDirect #[intV x, .builder Builder.empty, intV bits])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (natToBits 17 5)
        expectOkStack "ok/append-existing-bits"
          (runStuxDirect #[intV 17, .builder prefBuilder, intV 5])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStuxDirect #[.null, intV 7, .builder Builder.empty, intV 4])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks-for-value-and-bits"
      run := do
        expectErr "range/bits0-x1"
          (runStuxDirect #[intV 1, .builder Builder.empty, intV 0]) .rangeChk
        expectErr "range/bits0-xminus1"
          (runStuxDirect #[intV (-1), .builder Builder.empty, intV 0]) .rangeChk
        expectErr "range/overflow-bits1"
          (runStuxDirect #[intV 2, .builder Builder.empty, intV 1]) .rangeChk
        expectErr "range/negative-bits1"
          (runStuxDirect #[intV (-1), .builder Builder.empty, intV 1]) .rangeChk
        expectErr "range/overflow-bits8"
          (runStuxDirect #[intV 256, .builder Builder.empty, intV 8]) .rangeChk
        expectErr "range/negative-bits8"
          (runStuxDirect #[intV (-1), .builder Builder.empty, intV 8]) .rangeChk
        expectErr "range/overflow-bits256"
          (runStuxDirect #[intV overUInt256, .builder Builder.empty, intV 256]) .rangeChk
        expectErr "range/negative-bits256"
          (runStuxDirect #[intV (-1), .builder Builder.empty, intV 256]) .rangeChk
        expectErr "range/nan"
          (runStuxDirect #[.int .nan, .builder Builder.empty, intV 8]) .rangeChk

        expectErr "range/bits-too-large"
          (runStuxDirect #[intV 0, .builder Builder.empty, intV 257]) .rangeChk
        expectErr "range/bits-negative"
          (runStuxDirect #[intV 0, .builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/bits-nan"
          (runStuxDirect #[intV 0, .builder Builder.empty, .int .nan]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStuxDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runStuxDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runStuxDirect #[intV 1, .builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStuxDirect #[.null]) .stkUnd

        expectErr "type/pop-builder-after-bits"
          (runStuxDirect #[intV 1, .null, intV 8]) .typeChk
        expectErr "type/pop-int-after-builder"
          (runStuxDirect #[.null, .builder Builder.empty, intV 8]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStuxDirect #[.cell Cell.empty, .null, intV 8]) .typeChk

        expectErr "error-order/bits-range-before-builder-type"
          (runStuxDirect #[intV 1, .null, intV 257]) .rangeChk
        expectErr "error-order/bits-range-before-int-type"
          (runStuxDirect #[.null, .builder Builder.empty, intV (-1)]) .rangeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStuxDirect #[intV 0, .builder fullBuilder1023, intV 1]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStuxDirect #[.int .nan, .builder fullBuilder1023, intV 1]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStuxDirect #[intV 2, .builder fullBuilder1023, intV 1]) .cellOv }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[stuxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stux" s0 stuxInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stintvar-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStuxDispatchFallback #[.null])
          #[.null, intV 407] }
  ]
  oracle := #[
    mkStuxCase "ok/bits-0-zero" #[intV 0, .builder Builder.empty, intV 0],
    mkStuxCase "ok/bits-1-zero" #[intV 0, .builder Builder.empty, intV 1],
    mkStuxCase "ok/bits-1-one" #[intV 1, .builder Builder.empty, intV 1],
    mkStuxCase "ok/bits-8-max" #[intV 255, .builder Builder.empty, intV 8],
    mkStuxCase "ok/bits-16-max" #[intV 65535, .builder Builder.empty, intV 16],
    mkStuxCase "ok/bits-256-max" #[intV maxUInt256, .builder Builder.empty, intV 256],
    mkStuxCase "ok/deep-stack-below-preserved" #[.null, intV 7, .builder Builder.empty, intV 4],

    mkStuxCase "range/value-bits0-pos" #[intV 1, .builder Builder.empty, intV 0],
    mkStuxCase "range/value-bits0-neg" #[intV (-1), .builder Builder.empty, intV 0],
    mkStuxCase "range/overflow-bits1" #[intV 2, .builder Builder.empty, intV 1],
    mkStuxCase "range/negative-bits1" #[intV (-1), .builder Builder.empty, intV 1],
    mkStuxCase "range/overflow-bits8" #[intV 256, .builder Builder.empty, intV 8],
    mkStuxCase "range/negative-bits8" #[intV (-1), .builder Builder.empty, intV 8],
    mkStuxCase "range/overflow-bits255" #[intV (intPow2 255), .builder Builder.empty, intV 255],
    mkStuxCase "range/negative-bits256" #[intV (-1), .builder Builder.empty, intV 256],
    mkStuxProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, .pushInt (.num 8), stuxInstr],
    mkStuxCase "range/bits-too-large" #[intV 0, .builder Builder.empty, intV 257],
    mkStuxCase "range/bits-negative" #[intV 0, .builder Builder.empty, intV (-1)],

    mkStuxCase "underflow/empty" #[],
    mkStuxCase "underflow/one-item" #[intV 1],
    mkStuxCase "underflow/two-items" #[intV 1, .builder Builder.empty],
    mkStuxCase "type/top-not-builder-after-bits" #[intV 1, .null, intV 8],
    mkStuxCase "type/second-not-int" #[.null, .builder Builder.empty, intV 8],

    mkStuxCase "gas/exact-cost-succeeds" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stuxSetGasExact), .tonEnvOp .setGasLimit, stuxInstr],
    mkStuxCase "gas/exact-minus-one-out-of-gas" #[intV 7, .builder Builder.empty, intV 8]
      #[.pushInt (.num stuxSetGasExactMinusOne), .tonEnvOp .setGasLimit, stuxInstr],

    mkStuxProgramCase "program/build-1023-success" #[] build1023Program,
    mkStuxProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStuxProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStuxProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020904
      count := 300
      gen := genStuxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STUX
