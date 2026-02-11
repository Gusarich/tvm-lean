import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cell.STU

/-
STU branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Stu.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STU` encode: `0xcb, imm8 = bits-1`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`STU` decode: `bits = imm8 + 1`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int`, `exec_store_int_common`, opcode registration `0xcb`).

Branch map used for this suite:
- Lean STU path: 8 branch sites / 10 terminal outcomes
  (dispatch; explicit `bits=0` guard; `checkUnderflow 2`; builder/int pop type checks;
   capacity guard; NaN-vs-num split; unsigned range fit; success append).
- C++ STU path (fixed-width, non-quiet, non-reversed): 6 branch sites / 8 aligned outcomes
  (`check_underflow(2)`; pop order builder then int; `can_extend_by`; unsigned fit;
   `cell_ov` / `range_chk` / success).

Key risk areas:
- error order must be `cellOv` before integer-range checks when builder is full;
- pop order must be builder first, then integer (`STU` stack convention);
- unsigned boundary off-by-one at `0` and `2^bits - 1`;
- opcode boundary bits (`1`, `256`) and assembler range checks (`0`, `257`);
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; STU`.
-/

private def stuId : InstrId := { name := "STU" }

private def stuInstr (bits : Nat) : Instr :=
  .stu bits

private def mkStuCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stuInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStuProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStuDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStu (stuInstr bits) stack

private def runStuDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStu .add (VM.push (intV 404)) stack

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

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def fullBuilder1023 : Builder :=
  Builder.empty.storeBits (Array.replicate 1023 false)

private def build1023Program : Array Instr :=
  #[
    .newc,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 256,
    .pushInt (.num 0), .xchg0 1, .stu 255
  ]

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, .stu 1]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, .stu 1]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 2), .xchg0 1, .stu 1]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 17), .xchg0 1, .stu 5
  ]

private def stuGasProbeBits : Nat := 8

private def stuSetGasExact : Int :=
  computeExactGasBudget (stuInstr stuGasProbeBits)

private def stuSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stuInstr stuGasProbeBits)

private def stuBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStuBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stuBitsBoundaryPool.size - 1)
  (stuBitsBoundaryPool[idx]!, rng')

private def pickStuBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStuBitsBoundary rng1
  else
    randNat rng1 1 256

private def maxUnsignedForBits (bits : Nat) : Int :=
  intPow2 bits - 1

private def pickStuInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let maxv := maxUnsignedForBits bits
  let (pick, rng') := randNat rng 0 3
  let x : Int :=
    if pick = 0 then
      0
    else if pick = 1 then
      1
    else if pick = 2 then
      maxv
    else
      if maxv > 0 then maxv - 1 else 0
  (x, rng')

private def genStuFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let (bits, rng2) := pickStuBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStuInRange bits rng2
    (mkStuCase s!"fuzz/ok/top-only/bits-{bits}" bits #[intV x, .builder Builder.empty], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStuInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then
        .null
      else if noisePick = 1 then
        intV 17
      else
        .cell Cell.empty
    (mkStuCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, intV x, .builder Builder.empty], rng4)
  else if shape = 2 then
    (mkStuCase s!"fuzz/range/negative/bits-{bits}" bits #[intV (-1), .builder Builder.empty], rng2)
  else if shape = 3 then
    let overflowBits := if bits = 256 then 255 else bits
    (mkStuCase s!"fuzz/range/overflow/bits-{overflowBits}" overflowBits
      #[intV (intPow2 overflowBits), .builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStuCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStuCase s!"fuzz/underflow/one-int/bits-{bits}" bits #[intV 5], rng2)
  else if shape = 6 then
    (mkStuCase s!"fuzz/type/top-not-builder/bits-{bits}" bits #[.builder Builder.empty, intV 3], rng2)
  else if shape = 7 then
    (mkStuCase s!"fuzz/type/second-not-int/bits-{bits}" bits #[.null, .builder Builder.empty], rng2)
  else
    (mkStuProgramCase s!"fuzz/range/nan-program/bits-{bits}"
      #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stuInstr bits], rng2)

def suite : InstrSuite where
  id := stuId
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
          let expected := Builder.empty.storeBits (natToBits x.toNat bits)
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStuDirect bits #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (natToBits 17 5)
        expectOkStack "ok/append-existing-bits"
          (runStuDirect 5 #[intV 17, .builder prefBuilder])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStuDirect 4 #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/bits-zero-before-underflow"
          (runStuDirect 0 #[]) .rangeChk
        expectErr "range/bits-zero-before-type"
          (runStuDirect 0 #[.null, .null]) .rangeChk
        expectErr "range/nan"
          (runStuDirect 8 #[.int .nan, .builder Builder.empty]) .rangeChk
        expectErr "range/negative"
          (runStuDirect 8 #[intV (-1), .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-bits1"
          (runStuDirect 1 #[intV 2, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-bits8"
          (runStuDirect 8 #[intV 256, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-bits256"
          (runStuDirect 256 #[intV overUInt256, .builder Builder.empty]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStuDirect 8 #[]) .stkUnd
        expectErr "underflow/one-int" (runStuDirect 8 #[intV 3]) .stkUnd
        expectErr "underflow/one-builder" (runStuDirect 8 #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-non-int" (runStuDirect 8 #[.null]) .stkUnd

        expectErr "type/pop-builder-first"
          (runStuDirect 8 #[intV 1, .null]) .typeChk
        expectErr "type/pop-int-second"
          (runStuDirect 8 #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-pop-builder-first"
          (runStuDirect 8 #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStuDirect 1 #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStuDirect 1 #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStuDirect 1 #[intV 2, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr := #[stuInstr 1, stuInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stu-1" s0 (stuInstr 1) 16
        let s2 ← expectDecodeStep "decode/stu-256" s1 (stuInstr 256) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        match assembleCp0 [stuInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stu/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stu/0: expected assemble rangeChk, got success")

        match assembleCp0 [stuInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"stu/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "stu/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-cellstu-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStuDispatchFallback #[.null])
          #[.null, intV 404] }
  ]
  oracle := #[
    -- Branch map: success path (`unsigned fit` + append into builder).
    mkStuCase "ok/bits-1/zero" 1 #[intV 0, .builder Builder.empty],
    mkStuCase "ok/bits-1/one" 1 #[intV 1, .builder Builder.empty],
    mkStuCase "ok/bits-8/zero" 8 #[intV 0, .builder Builder.empty],
    mkStuCase "ok/bits-8/max" 8 #[intV 255, .builder Builder.empty],
    mkStuCase "ok/bits-16/zero" 16 #[intV 0, .builder Builder.empty],
    mkStuCase "ok/bits-16/max" 16 #[intV 65535, .builder Builder.empty],
    mkStuCase "ok/bits-32/max" 32 #[intV (intPow2 32 - 1), .builder Builder.empty],
    mkStuCase "ok/bits-256/zero" 256 #[intV 0, .builder Builder.empty],
    mkStuCase "ok/bits-256/max" 256 #[intV maxUInt256, .builder Builder.empty],
    mkStuCase "ok/deep-stack-below-preserved" 4 #[.null, intV 7, .builder Builder.empty],
    mkStuProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    -- Branch map: range path (`NaN`/negative/overflow => `rangeChk`).
    mkStuCase "range/negative-bits-1" 1 #[intV (-1), .builder Builder.empty],
    mkStuCase "range/negative" 8 #[intV (-1), .builder Builder.empty],
    mkStuCase "range/overflow-bits-1" 1 #[intV 2, .builder Builder.empty],
    mkStuCase "range/overflow-bits-8" 8 #[intV 256, .builder Builder.empty],
    mkStuCase "range/overflow-bits-255" 255 #[intV (intPow2 255), .builder Builder.empty],
    mkStuCase "range/negative-bits-256" 256 #[intV (-1), .builder Builder.empty],
    mkStuProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stuInstr 8],

    -- Branch map: stack discipline (`checkUnderflow` + pop-order type checks).
    mkStuCase "underflow/empty" 8 #[],
    mkStuCase "underflow/one-int" 8 #[intV 1],
    mkStuCase "underflow/one-builder" 8 #[.builder Builder.empty],
    mkStuCase "underflow/one-non-int" 8 #[.null],
    mkStuCase "type/top-not-builder" 8 #[.builder Builder.empty, intV 3],
    mkStuCase "type/second-not-int" 8 #[.null, .builder Builder.empty],

    -- Branch map: deterministic gas cliff for STU execution.
    mkStuCase "gas/exact-cost-succeeds" stuGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stuSetGasExact), .tonEnvOp .setGasLimit, stuInstr stuGasProbeBits],
    mkStuCase "gas/exact-minus-one-out-of-gas" stuGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stuSetGasExactMinusOne), .tonEnvOp .setGasLimit, stuInstr stuGasProbeBits],

    -- Branch map: capacity guard (`cellOv`) and its precedence over range diagnostics.
    mkStuProgramCase "program/build-1023-success" #[] build1023Program,
    mkStuProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStuProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStuProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026020901
      count := 500
      gen := genStuFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STU
