import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STUR

/-
STUR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean` (`.stIntFixed unsigned=true rev=true quiet=false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STUR` as `0xcf08`-family with `unsigned=1`, `rev=1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf08` fixed-width family decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, args with `unsigned=1`, `rev=1`, `quiet=0`).

Branch map used for this suite:
- Lean STUR path: 10 branch sites / 13 terminal outcomes
  (`checkUnderflow 2`; rev pop order; capacity guard; unsigned fit;
   non-quiet throw outcomes; success append).
- C++ STUR path: 8 branch sites / 11 aligned outcomes.

Key risk areas:
- reversed pop order (`x` first, then `builder`) controls type ordering;
- unsigned range boundaries at `[0, 2^bits - 1]`;
- negative and NaN inputs must throw `rangeChk` (not `typeChk`);
- `cellOv` must be raised before range checks when builder is full.
-/

private def sturId : InstrId := { name := "STUR" }

private def sturInstr (bits : Nat) : Instr :=
  .stIntFixed true true false bits

private def mkSturCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[sturInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sturId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSturProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sturId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSturDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (sturInstr bits) stack

private def runSturDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed .add (VM.push (intV 416)) stack

private def maxUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 bits - 1

private def overflowUnsignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 bits

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithFixedRev sturInstr

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), sturInstr 1]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, sturInstr 1]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 2), sturInstr 1]

private def sturGasProbeBits : Nat := 8

private def sturSetGasExact : Int :=
  computeExactGasBudget (sturInstr sturGasProbeBits)

private def sturSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (sturInstr sturGasProbeBits)

private def sturBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickSturBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (sturBitsBoundaryPool.size - 1)
  (sturBitsBoundaryPool[idx]!, rng')

private def pickSturBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickSturBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickSturInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let hi := maxUnsignedBits bits
  let (pick, rng') := randNat rng 0 4
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then hi
    else if pick = 3 then
      if hi > 0 then hi - 1 else 0
    else
      if hi > 1 then hi / 2 else hi
  (x, rng')

private def genSturFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (bits, rng2) := pickSturBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickSturInRange bits rng2
    (mkSturCase s!"fuzz/ok/top-only/bits-{bits}" bits #[.builder Builder.empty, intV x], rng3)
  else if shape = 1 then
    let (x, rng3) := pickSturInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 67 else .cell Cell.empty
    (mkSturCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, .builder Builder.empty, intV x], rng4)
  else if shape = 2 then
    let bitsOv := if bits = 256 then 255 else bits
    (mkSturCase s!"fuzz/range/overflow-pos/bits-{bitsOv}" bitsOv
      #[.builder Builder.empty, intV (overflowUnsignedBits bitsOv)], rng2)
  else if shape = 3 then
    (mkSturCase s!"fuzz/range/negative/bits-{bits}" bits #[.builder Builder.empty, intV (-1)], rng2)
  else if shape = 4 then
    (mkSturCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkSturCase s!"fuzz/underflow/one-item/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 6 then
    (mkSturCase s!"fuzz/type/x-not-int/bits-{bits}" bits #[.builder Builder.empty, .null], rng2)
  else if shape = 7 then
    (mkSturCase s!"fuzz/type/builder-not-builder/bits-{bits}" bits #[.null, intV 1], rng2)
  else if shape = 8 then
    (mkSturProgramCase s!"fuzz/range/nan-via-program/bits-{bits}" #[.builder Builder.empty]
      #[.pushInt .nan, sturInstr bits], rng2)
  else
    let (x, rng3) := pickSturInRange 1 rng2
    (mkSturProgramCase s!"fuzz/cellov-before-range/bits-1/x-{x}" #[]
      (build1023Program ++ #[.pushInt (.num x), sturInstr 1]), rng3)

def suite : InstrSuite where
  id := sturId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array (Nat × Int) :=
          #[
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
          let bs : BitString := natToBits x.toNat bits
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runSturDirect bits #[.builder Builder.empty, intV x])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (natToBits 17 5)
        expectOkStack "ok/append-existing-bits"
          (runSturDirect 5 #[.builder prefBuilder, intV 17])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runSturDirect 4 #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/overflow-pos-bits1"
          (runSturDirect 1 #[.builder Builder.empty, intV 2]) .rangeChk
        expectErr "range/negative-bits1"
          (runSturDirect 1 #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/overflow-pos-bits8"
          (runSturDirect 8 #[.builder Builder.empty, intV 256]) .rangeChk
        expectErr "range/negative-bits8"
          (runSturDirect 8 #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/overflow-pos-bits256"
          (runSturDirect 256 #[.builder Builder.empty, intV overUInt256]) .rangeChk
        expectErr "range/negative-bits256"
          (runSturDirect 256 #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/nan"
          (runSturDirect 8 #[.builder Builder.empty, .int .nan]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runSturDirect 8 #[]) .stkUnd
        expectErr "underflow/one-item" (runSturDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runSturDirect 8 #[.null]) .stkUnd

        expectErr "type/x-not-int-after-pop"
          (runSturDirect 8 #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/builder-not-builder"
          (runSturDirect 8 #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-x-first"
          (runSturDirect 8 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runSturDirect 1 #[.builder fullBuilder1023, intV 0]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runSturDirect 1 #[.builder fullBuilder1023, .int .nan]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runSturDirect 1 #[.builder fullBuilder1023, intV 2]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[sturInstr 1, sturInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stur-1" s0 (sturInstr 1) 24
        let s2 ← expectDecodeStep "decode/stur-256" s1 (sturInstr 256) 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        match assembleCp0 [sturInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stur/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stur/0: expected assemble rangeChk, got success")
        match assembleCp0 [sturInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stur/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stur/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runSturDispatchFallback #[.null])
          #[.null, intV 416] }
  ]
  oracle := #[
    mkSturCase "ok/bits1-zero" 1 #[.builder Builder.empty, intV 0],
    mkSturCase "ok/bits1-one" 1 #[.builder Builder.empty, intV 1],
    mkSturCase "ok/bits8-zero" 8 #[.builder Builder.empty, intV 0],
    mkSturCase "ok/bits8-max" 8 #[.builder Builder.empty, intV 255],
    mkSturCase "ok/bits16-zero" 16 #[.builder Builder.empty, intV 0],
    mkSturCase "ok/bits16-max" 16 #[.builder Builder.empty, intV 65535],
    mkSturCase "ok/bits32-zero" 32 #[.builder Builder.empty, intV 0],
    mkSturCase "ok/bits32-max" 32 #[.builder Builder.empty, intV (intPow2 32 - 1)],
    mkSturCase "ok/bits256-zero" 256 #[.builder Builder.empty, intV 0],
    mkSturCase "ok/bits256-max" 256 #[.builder Builder.empty, intV maxUInt256],
    mkSturCase "ok/deep-stack-below-preserved" 4 #[.null, .builder Builder.empty, intV 7],
    mkSturProgramCase "ok/append-existing-bits-via-program" #[] #[
      .newc,
      .pushInt (.num 5), .xchg0 1, .stu 3,
      .pushInt (.num 17), sturInstr 5
    ],

    mkSturCase "range/overflow-pos-bits1" 1 #[.builder Builder.empty, intV 2],
    mkSturCase "range/negative-bits1" 1 #[.builder Builder.empty, intV (-1)],
    mkSturCase "range/overflow-pos-bits8" 8 #[.builder Builder.empty, intV 256],
    mkSturCase "range/negative-bits8" 8 #[.builder Builder.empty, intV (-1)],
    mkSturCase "range/overflow-pos-bits255" 255 #[.builder Builder.empty, intV (intPow2 255)],
    mkSturCase "range/negative-bits256" 256 #[.builder Builder.empty, intV (-1)],
    mkSturProgramCase "range/nan-via-program" #[.builder Builder.empty] #[.pushInt .nan, sturInstr 8],

    mkSturCase "underflow/empty" 8 #[],
    mkSturCase "underflow/one-item" 8 #[.builder Builder.empty],
    mkSturCase "type/x-not-int" 8 #[.builder Builder.empty, .null],
    mkSturCase "type/builder-not-builder" 8 #[.null, intV 1],

    mkSturCase "gas/exact-cost-succeeds" sturGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num sturSetGasExact), .tonEnvOp .setGasLimit, sturInstr sturGasProbeBits],
    mkSturCase "gas/exact-minus-one-out-of-gas" sturGasProbeBits #[.builder Builder.empty, intV 7]
      #[.pushInt (.num sturSetGasExactMinusOne), .tonEnvOp .setGasLimit, sturInstr sturGasProbeBits],

    mkSturProgramCase "program/build-1023-success" #[] build1023Program,
    mkSturProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkSturProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkSturProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020913
      count := 500
      gen := genSturFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STUR
