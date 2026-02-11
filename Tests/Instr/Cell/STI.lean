import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cell.STI

/-
STI branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sti.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STI` encode: `0xca, imm8 = bits-1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`STI` decode: `bits = imm8 + 1`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int`, `exec_store_int_common`, opcode registration `0xca`).

Branch map used for this suite:
- Lean STI path: 8 branch sites / 10 terminal outcomes
  (dispatch; explicit `bits=0` guard; `checkUnderflow 2`; builder/int pop type checks;
   capacity guard; NaN-vs-num split; signed fit via `intToBitsTwos`; success append).
- C++ STI path (fixed-width, non-quiet, non-reversed): 6 branch sites / 8 aligned outcomes
  (`check_underflow(2)`; pop order builder then int; `can_extend_by`; signed fit;
   `cell_ov` / `range_chk` / success).

Key risk areas:
- error order must be `cellOv` before integer-range checks when builder is full;
- pop order must be builder first, then integer (`STI` stack convention);
- signed boundary off-by-one at `[-2^(bits-1), 2^(bits-1)-1]`;
- opcode boundary bits (`1`, `256`) and assembler range checks (`0`, `257`);
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; STI`.
-/

private def stiId : InstrId := { name := "STI" }

private def stiInstr (bits : Nat) : Instr :=
  .sti bits

private def mkStiCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stiInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stiId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStiProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stiId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStiDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSti (stiInstr bits) stack

private def runStiDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSti .add (VM.push (intV 405)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def minSti256 : Int :=
  -(intPow2 255)

private def maxSti256 : Int :=
  intPow2 255 - 1

private def overMaxSti256 : Int :=
  intPow2 255

private def underMinSti256 : Int :=
  -(intPow2 255) - 1

private def fullBuilder1023 : Builder :=
  Builder.empty.storeBits (Array.replicate 1023 false)

private def build1023Program : Array Instr :=
  #[
    .newc,
    .pushInt (.num 0), .xchg0 1, .sti 256,
    .pushInt (.num 0), .xchg0 1, .sti 256,
    .pushInt (.num 0), .xchg0 1, .sti 256,
    .pushInt (.num 0), .xchg0 1, .sti 255
  ]

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, .sti 1]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, .sti 1]

private def stiGasProbeBits : Nat := 8

private def stiSetGasExact : Int :=
  computeExactGasBudget (stiInstr stiGasProbeBits)

private def stiSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stiInstr stiGasProbeBits)

private def stiBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStiBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stiBitsBoundaryPool.size - 1)
  (stiBitsBoundaryPool[idx]!, rng')

private def pickStiBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStiBitsBoundary rng1
  else
    randNat rng1 1 256

private def minSignedForBits (bits : Nat) : Int :=
  -(intPow2 (bits - 1))

private def maxSignedForBits (bits : Nat) : Int :=
  intPow2 (bits - 1) - 1

private def pickStiInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let lo := minSignedForBits bits
  let hi := maxSignedForBits bits
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if pick = 0 then
      0
    else if pick = 1 then
      1
    else if pick = 2 then
      -1
    else if pick = 3 then
      hi
    else if pick = 4 then
      lo
    else
      if hi > lo then hi - 1 else lo
  (x, rng')

private def genStiFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let (bits, rng2) := pickStiBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStiInRange bits rng2
    (mkStiCase s!"fuzz/ok/top-only/bits-{bits}" bits #[intV x, .builder Builder.empty], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStiInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then
        .null
      else if noisePick = 1 then
        intV 19
      else
        .cell Cell.empty
    (mkStiCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, intV x, .builder Builder.empty], rng4)
  else if shape = 2 then
    (mkStiCase s!"fuzz/range/overflow-pos/bits-{bits}" bits #[intV (intPow2 (bits - 1)), .builder Builder.empty], rng2)
  else if shape = 3 then
    (mkStiCase s!"fuzz/range/overflow-neg/bits-{bits}" bits #[intV (-(intPow2 (bits - 1)) - 1), .builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStiCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStiCase s!"fuzz/underflow/one-int/bits-{bits}" bits #[intV 5], rng2)
  else if shape = 6 then
    (mkStiCase s!"fuzz/type/top-not-builder/bits-{bits}" bits #[.builder Builder.empty, intV 3], rng2)
  else if shape = 7 then
    (mkStiCase s!"fuzz/type/second-not-int/bits-{bits}" bits #[.null, .builder Builder.empty], rng2)
  else
    (mkStiProgramCase s!"fuzz/range/nan-program/bits-{bits}"
      #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stiInstr bits], rng2)

def suite : InstrSuite where
  id := stiId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, -1),
            (1, 0),
            (8, -128),
            (8, 127),
            (256, minSti256),
            (256, maxSti256)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          let bs ←
            match intToBitsTwos x bits with
            | .ok bitsV => pure bitsV
            | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e} for bits={bits}, x={x}")
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStiDirect bits #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appendedBits ←
          match intToBitsTwos (-3) 4 with
          | .ok bitsV => pure bitsV
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let appended := prefBuilder.storeBits appendedBits
        expectOkStack "ok/append-existing-bits"
          (runStiDirect 4 #[intV (-3), .builder prefBuilder])
          #[.builder appended]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok bitsV => pure bitsV
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStiDirect 4 #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/bits-zero-before-underflow"
          (runStiDirect 0 #[]) .rangeChk
        expectErr "range/bits-zero-before-type"
          (runStiDirect 0 #[.null, .null]) .rangeChk
        expectErr "range/nan"
          (runStiDirect 8 #[.int .nan, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-pos-bits1"
          (runStiDirect 1 #[intV 1, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg-bits1"
          (runStiDirect 1 #[intV (-2), .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-pos-bits8"
          (runStiDirect 8 #[intV 128, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg-bits8"
          (runStiDirect 8 #[intV (-129), .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-pos-bits256"
          (runStiDirect 256 #[intV overMaxSti256, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg-bits256"
          (runStiDirect 256 #[intV underMinSti256, .builder Builder.empty]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStiDirect 8 #[]) .stkUnd
        expectErr "underflow/one-int" (runStiDirect 8 #[intV 3]) .stkUnd
        expectErr "underflow/one-builder" (runStiDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-non-int" (runStiDirect 8 #[.null]) .stkUnd

        expectErr "type/pop-builder-first"
          (runStiDirect 8 #[intV 1, .null]) .typeChk
        expectErr "type/pop-int-second"
          (runStiDirect 8 #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-pop-builder-first"
          (runStiDirect 8 #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStiDirect 1 #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStiDirect 1 #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStiDirect 1 #[intV 1, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr := #[stiInstr 1, stiInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sti-1" s0 (stiInstr 1) 16
        let s2 ← expectDecodeStep "decode/sti-256" s1 (stiInstr 256) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        match assembleCp0 [stiInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"sti/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "sti/0: expected assemble rangeChk, got success")

        match assembleCp0 [stiInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"sti/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "sti/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-cellsti-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStiDispatchFallback #[.null])
          #[.null, intV 405] }
  ]
  oracle := #[
    mkStiCase "ok/bits-1/min" 1 #[intV (-1), .builder Builder.empty],
    mkStiCase "ok/bits-1/max" 1 #[intV 0, .builder Builder.empty],
    mkStiCase "ok/bits-8/min" 8 #[intV (-128), .builder Builder.empty],
    mkStiCase "ok/bits-8/max" 8 #[intV 127, .builder Builder.empty],
    mkStiCase "ok/bits-16/min" 16 #[intV (-32768), .builder Builder.empty],
    mkStiCase "ok/bits-16/max" 16 #[intV 32767, .builder Builder.empty],
    mkStiCase "ok/bits-256/min" 256 #[intV minSti256, .builder Builder.empty],
    mkStiCase "ok/bits-256/max" 256 #[intV maxSti256, .builder Builder.empty],
    mkStiCase "ok/deep-stack-below-preserved" 4 #[.null, intV 7, .builder Builder.empty],

    mkStiCase "range/overflow-pos-bits-1" 1 #[intV 1, .builder Builder.empty],
    mkStiCase "range/overflow-neg-bits-1" 1 #[intV (-2), .builder Builder.empty],
    mkStiCase "range/overflow-pos-bits-8" 8 #[intV 128, .builder Builder.empty],
    mkStiCase "range/overflow-neg-bits-8" 8 #[intV (-129), .builder Builder.empty],
    mkStiCase "range/overflow-pos-bits-256" 256 #[intV overMaxSti256, .builder Builder.empty],
    mkStiCase "range/overflow-neg-bits-256" 256 #[intV underMinSti256, .builder Builder.empty],
    mkStiProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stiInstr 8],

    mkStiCase "underflow/empty" 8 #[],
    mkStiCase "underflow/one-int" 8 #[intV 1],
    mkStiCase "underflow/one-builder" 8 #[.builder Builder.empty],
    mkStiCase "type/top-not-builder" 8 #[.builder Builder.empty, intV 3],
    mkStiCase "type/second-not-int" 8 #[.null, .builder Builder.empty],

    mkStiCase "gas/exact-cost-succeeds" stiGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stiSetGasExact), .tonEnvOp .setGasLimit, stiInstr stiGasProbeBits],
    mkStiCase "gas/exact-minus-one-out-of-gas" stiGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stiSetGasExactMinusOne), .tonEnvOp .setGasLimit, stiInstr stiGasProbeBits],

    mkStiProgramCase "program/build-1023-success" #[] build1023Program,
    mkStiProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStiProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram
  ]
  fuzz := #[
    { seed := 2026020902
      count := 500
      gen := genStiFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STI
