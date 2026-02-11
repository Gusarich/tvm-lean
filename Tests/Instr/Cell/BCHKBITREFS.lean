import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKBITREFS

/-
BCHKBITREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Bchk.lean` (`.bchk needBits needRefs quiet`)
  - `TvmLean/Semantics/Exec/CellOp.lean` (dispatch chain for `.cellOp`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`BCHKBITREFS` encode: `0xcf3b`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xcf3b` decode; neighboring `0xcf39/0xcf3a/0xcf3d/0xcf3f`;
     24-bit `BCHKBITS{Q}` immediate prefixes `0xcf38/0xcf3c`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_chk_bits_refs`, mode=`3` for `BCHKBITREFS`).

Mode=3 alignment used in this suite:
- underflow check requires 3 stack items;
- pop order is `refs` (top) → `bits` → `builder`;
- range/type errors for refs and bits happen before builder pop/type;
- non-quiet mode throws `cell_ov` on capacity failure, otherwise pushes nothing.

Oracle/fuzz slice constraint:
- whenever this suite places slices in oracle/fuzz stacks (as deep noise),
  they are full-cell slices only (`bitPos = 0`, `refPos = 0`).
-/

private def bchkbitrefsId : InstrId := { name := "BCHKBITREFS" }

private def bchkbitrefsInstr : Instr := .cellOp (.bchk true true false)
private def bchkbitsInstr : Instr := .cellOp (.bchk true false false)
private def bchkrefsInstr : Instr := .cellOp (.bchk false true false)
private def bchkbitsqInstr : Instr := .cellOp (.bchk true false true)
private def bchkbitrefsqInstr : Instr := .cellOp (.bchk true true true)

private def bchkbitrefsWord : Nat := 0xcf3b
private def bchkrefsWord : Nat := 0xcf3a
private def bchkbitsqWord : Nat := 0xcf3d

private def bchkBitsImmInstr (bits : Nat) (quiet : Bool := false) : Instr :=
  .cellOp (.bchkBitsImm bits quiet)

private def bchkBitsImmWord (bits : Nat) (quiet : Bool := false) : Nat :=
  ((if quiet then 0xcf3c else 0xcf38) <<< 8) + (bits - 1)

private def execInstrCellOpBchkOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def mkBchkBitRefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bchkbitrefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkbitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkBitRefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkOnly bchkbitrefsInstr stack

private def dispatchSentinel : Int := 653

private def runBchkBitRefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBchkOnly instr (VM.push (intV dispatchSentinel)) stack

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkBuilderWithCounts (bits refs : Nat) (phase : Nat := 0) : Builder :=
  { bits := stripeBits bits phase
    refs := refsByCount refs }

private def mkFullSlice (bits : Nat) (phase : Nat := 0) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stripeBits bits phase) refs)

private def mkBchkStack (builder : Builder) (bits refs : Int) (below : Array Value := #[]) :
    Array Value :=
  below ++ #[.builder builder, intV bits, intV refs]

private def mkBchkStackNat (builder : Builder) (bits refs : Nat) (below : Array Value := #[]) :
    Array Value :=
  mkBchkStack builder (Int.ofNat bits) (Int.ofNat refs) below

private def fullSliceNoiseA : Slice := mkFullSlice 9 0
private def fullSliceNoiseB : Slice := mkFullSlice 13 1 #[refLeafA]

private def bchkBitRefsSetGasExact : Int :=
  computeExactGasBudget bchkbitrefsInstr

private def bchkBitRefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bchkbitrefsInstr

private def bchkBitsReqBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 255, 256, 511, 512, 1023]

private def bchkBuilderBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 255, 256, 511, 512, 1022, 1023]

private def pickBchkBitsReqMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (bchkBitsReqBoundaryPool.size - 1)
    (bchkBitsReqBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 1023

private def pickBchkBuilderBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (bchkBuilderBitsBoundaryPool.size - 1)
    (bchkBuilderBitsBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 1023

private def pickBchkBuilderRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    (4, rng1)
  else
    randNat rng1 0 4

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 73
    else if pick = 2 then .cell refLeafB
    else if pick = 3 then .slice (mkFullSlice 7 1)
    else .slice (mkFullSlice 5 0)
  (noise, rng1)

private def pickBuilderForFuzz (rng0 : StdGen) : (Builder × Nat × Nat) × StdGen :=
  ((Builder.empty, 0, 0), rng0)

private def pickBuilderForBitsOverflow (rng0 : StdGen) : (Builder × Nat × Nat) × StdGen :=
  let (builderBits, rng1) := randNat rng0 1 1023
  let (builderRefs, rng2) := pickBchkBuilderRefsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  ((mkBuilderWithCounts builderBits builderRefs phase, builderBits, builderRefs), rng3)

private def pickReqWithinCaps (bitsCap refsCap : Nat) (rng0 : StdGen) : (Nat × Nat) × StdGen :=
  let (bitsCandidate, rng1) := pickBchkBitsReqMixed rng0
  let bitsReq := Nat.min bitsCandidate bitsCap
  let (refsCandidate, rng2) := randNat rng1 0 7
  let refsReq := Nat.min refsCandidate refsCap
  ((bitsReq, refsReq), rng2)

private def genBchkBitRefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let ((builder, bBits, bRefs), rng2) := pickBuilderForFuzz rng1
    let bitsCap := 1023 - bBits
    let refsCap := 4 - bRefs
    let ((bitsReq, refsReq), rng3) := pickReqWithinCaps bitsCap refsCap rng2
    (mkBchkBitRefsCase s!"fuzz/ok/exact/b{bBits}-r{bRefs}/+{bitsReq}+{refsReq}"
      (mkBchkStackNat builder bitsReq refsReq), rng3)
  else if shape = 1 then
    let ((builder, bBits, bRefs), rng2) := pickBuilderForFuzz rng1
    let bitsCap := 1023 - bBits
    let refsCap := 4 - bRefs
    let ((bitsReq, refsReq), rng3) := pickReqWithinCaps bitsCap refsCap rng2
    let (noise, rng4) := pickNoiseValue rng3
    (mkBchkBitRefsCase s!"fuzz/ok/deep1/b{bBits}-r{bRefs}/+{bitsReq}+{refsReq}"
      (mkBchkStackNat builder bitsReq refsReq #[noise]), rng4)
  else if shape = 2 then
    let ((builder, bBits, bRefs), rng2) := pickBuilderForFuzz rng1
    let bitsCap := 1023 - bBits
    let refsCap := 4 - bRefs
    let ((bitsReq, refsReq), rng3) := pickReqWithinCaps bitsCap refsCap rng2
    let (noise, rng4) := pickNoiseValue rng3
    (mkBchkBitRefsCase s!"fuzz/ok/deep2/b{bBits}-r{bRefs}/+{bitsReq}+{refsReq}"
      (mkBchkStackNat builder bitsReq refsReq #[.slice (mkFullSlice 11 0 #[refLeafA]), noise]), rng4)
  else if shape = 3 then
    let (bitsReq, rng2) := pickBchkBitsReqMixed rng1
    let (refsReq, rng3) := randNat rng2 5 7
    (mkBchkBitRefsCase s!"fuzz/cellov/refs-empty/+{bitsReq}+{refsReq}"
      (mkBchkStackNat Builder.empty bitsReq refsReq), rng3)
  else if shape = 4 then
    let ((builder, bBits, bRefs), rng2) := pickBuilderForFuzz rng1
    let bitsCap := 1023 - bBits
    let refsCap := 4 - bRefs
    let (bitsReq, rng3) := randNat rng2 0 bitsCap
    let (refsReq, rng4) := randNat rng3 (refsCap + 1) 7
    (mkBchkBitRefsCase s!"fuzz/cellov/refs/b{bBits}-r{bRefs}/+{bitsReq}+{refsReq}"
      (mkBchkStackNat builder bitsReq refsReq), rng4)
  else if shape = 5 then
    let (bitsReq, rng2) := pickBchkBitsReqMixed rng1
    let (refsReq, rng3) := randNat rng2 5 7
    let (noise, rng4) := pickNoiseValue rng3
    (mkBchkBitRefsCase s!"fuzz/cellov/deep-empty/+{bitsReq}+{refsReq}"
      (mkBchkStackNat Builder.empty bitsReq refsReq #[noise]), rng4)
  else if shape = 6 then
    (mkBchkBitRefsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkBchkBitRefsCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 8 then
    (mkBchkBitRefsCase "fuzz/underflow/two-items" #[.builder Builder.empty, intV 0], rng1)
  else if shape = 9 then
    let ((builder, _, _), rng2) := pickBuilderForFuzz rng1
    (mkBchkBitRefsCase "fuzz/type/refs-top-null"
      #[.builder builder, intV 0, .null], rng2)
  else if shape = 10 then
    let ((builder, _, _), rng2) := pickBuilderForFuzz rng1
    (mkBchkBitRefsCase "fuzz/range/refs-over7"
      #[.builder builder, intV 0, intV 8], rng2)
  else if shape = 11 then
    let ((builder, _, _), rng2) := pickBuilderForFuzz rng1
    (mkBchkBitRefsCase "fuzz/range/refs-negative"
      #[.builder builder, intV 0, intV (-1)], rng2)
  else if shape = 12 then
    let ((builder, _, _), rng2) := pickBuilderForFuzz rng1
    (mkBchkBitRefsCase "fuzz/type/bits-not-int"
      #[.builder builder, .null, intV 0], rng2)
  else if shape = 13 then
    let ((builder, _, _), rng2) := pickBuilderForFuzz rng1
    (mkBchkBitRefsCase "fuzz/range/bits-over1023"
      #[.builder builder, intV 1024, intV 0], rng2)
  else if shape = 14 then
    let ((builder, _, _), rng2) := pickBuilderForFuzz rng1
    (mkBchkBitRefsCase "fuzz/range/bits-negative"
      #[.builder builder, intV (-1), intV 0], rng2)
  else if shape = 15 then
    (mkBchkBitRefsCase "fuzz/type/builder-not-builder"
      #[.null, intV 1, intV 1], rng1)
  else if shape = 16 then
    (mkBchkBitRefsCase "fuzz/gas/exact"
      (mkBchkStackNat Builder.empty 1 1)
      #[.pushInt (.num bchkBitRefsSetGasExact), .tonEnvOp .setGasLimit, bchkbitrefsInstr], rng1)
  else if shape = 17 then
    (mkBchkBitRefsCase "fuzz/gas/exact-minus-one"
      (mkBchkStackNat Builder.empty 1 1)
      #[.pushInt (.num bchkBitRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkbitrefsInstr], rng1)
  else if shape = 18 then
    let ((builder, _, _), rng2) := pickBuilderForFuzz rng1
    (mkBchkBitRefsCase "fuzz/order/refs-range-before-bits-type"
      #[.builder builder, .null, intV 8], rng2)
  else
    (mkBchkBitRefsCase "fuzz/order/bits-range-before-builder-type"
      #[.null, intV 1024, intV 0], rng1)

def suite : InstrSuite where
  id := bchkbitrefsId
  unit := #[
    { name := "unit/direct/success-boundaries-and-deep-stack"
      run := do
        expectOkStack "ok/empty-plus-0-0"
          (runBchkBitRefsDirect (mkBchkStackNat Builder.empty 0 0))
          #[]
        expectOkStack "ok/empty-plus-1-0"
          (runBchkBitRefsDirect (mkBchkStackNat Builder.empty 1 0))
          #[]
        expectOkStack "ok/empty-plus-0-1"
          (runBchkBitRefsDirect (mkBchkStackNat Builder.empty 0 1))
          #[]
        expectOkStack "ok/exact-boundary-bits-1023"
          (runBchkBitRefsDirect (mkBchkStackNat Builder.empty 1023 0))
          #[]
        expectOkStack "ok/exact-boundary-refs-4"
          (runBchkBitRefsDirect (mkBchkStackNat Builder.empty 0 4))
          #[]
        expectOkStack "ok/exact-both-boundary"
          (runBchkBitRefsDirect (mkBchkStackNat (mkBuilderWithCounts 1000 1) 23 3))
          #[]
        expectOkStack "ok/deep-stack-preserve-below"
          (runBchkBitRefsDirect
            (mkBchkStackNat (mkBuilderWithCounts 900 2) 120 2 #[.null, intV 99, .slice fullSliceNoiseA]))
          #[.null, intV 99, .slice fullSliceNoiseA] }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty" (runBchkBitRefsDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runBchkBitRefsDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/two-items" (runBchkBitRefsDirect #[.builder Builder.empty, intV 0]) .stkUnd

        expectErr "type/refs-top-null"
          (runBchkBitRefsDirect #[.builder Builder.empty, intV 0, .null]) .typeChk
        expectErr "range/refs-over7"
          (runBchkBitRefsDirect #[.builder Builder.empty, intV 0, intV 8]) .rangeChk
        expectErr "range/refs-negative"
          (runBchkBitRefsDirect #[.builder Builder.empty, intV 0, intV (-1)]) .rangeChk
        expectErr "range/refs-nan"
          (runBchkBitRefsDirect #[.builder Builder.empty, intV 0, .int .nan]) .rangeChk

        expectErr "type/bits-not-int-after-valid-refs"
          (runBchkBitRefsDirect #[.builder Builder.empty, .null, intV 0]) .typeChk
        expectErr "range/bits-over1023"
          (runBchkBitRefsDirect #[.builder Builder.empty, intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-negative"
          (runBchkBitRefsDirect #[.builder Builder.empty, intV (-1), intV 0]) .rangeChk
        expectErr "range/bits-nan"
          (runBchkBitRefsDirect #[.builder Builder.empty, .int .nan, intV 0]) .rangeChk

        expectErr "type/builder-not-builder-after-valid-args"
          (runBchkBitRefsDirect #[.null, intV 1, intV 1]) .typeChk

        expectErr "order/refs-range-before-bits-type"
          (runBchkBitRefsDirect #[.builder Builder.empty, .null, intV 8]) .rangeChk
        expectErr "order/refs-type-before-bits-range"
          (runBchkBitRefsDirect #[.builder Builder.empty, intV 2048, .null]) .typeChk
        expectErr "order/bits-range-before-builder-type"
          (runBchkBitRefsDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "order/bits-type-before-builder-type"
          (runBchkBitRefsDirect #[.null, .null, intV 0]) .typeChk }
    ,
    { name := "unit/direct/cellov-paths"
      run := do
        expectErr "cellov/bits-overflow-b1-plus-1023"
          (runBchkBitRefsDirect (mkBchkStackNat (mkBuilderWithCounts 1 0) 1023 0))
          .cellOv
        expectErr "cellov/bits-overflow-b1023-plus-1"
          (runBchkBitRefsDirect (mkBchkStackNat (mkBuilderWithCounts 1023 0) 1 0))
          .cellOv
        expectErr "cellov/refs-overflow-empty-plus-5"
          (runBchkBitRefsDirect (mkBchkStackNat Builder.empty 0 5))
          .cellOv
        expectErr "cellov/refs-overflow-r4-plus-1"
          (runBchkBitRefsDirect (mkBchkStackNat (mkBuilderWithCounts 0 4) 0 1))
          .cellOv
        expectErr "cellov/both-overflow-full-plus-1-1"
          (runBchkBitRefsDirect (mkBchkStackNat (mkBuilderWithCounts 1023 4) 1 1))
          .cellOv
        expectErr "cellov/bits-overflow-refs-still-ok"
          (runBchkBitRefsDirect (mkBchkStackNat (mkBuilderWithCounts 1020 4) 4 0))
          .cellOv
        expectErr "cellov/refs-overflow-bits-still-ok"
          (runBchkBitRefsDirect (mkBchkStackNat (mkBuilderWithCounts 1000 3) 20 2))
          .cellOv }
    ,
    { name := "unit/opcode/decode-assembler-and-24bit-order"
      run := do
        let asmProgram : Array Instr :=
          #[bchkrefsInstr, bchkbitrefsInstr, bchkbitsInstr, bchkbitrefsqInstr, .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-bchkrefs" s0 bchkrefsInstr 16
        let s2 ← expectDecodeStep "decode/asm-bchkbitrefs" s1 bchkbitrefsInstr 16
        let s3 ← expectDecodeStep "decode/asm-bchkbits" s2 bchkbitsInstr 16
        let s4 ← expectDecodeStep "decode/asm-bchkbitrefsq" s3 bchkbitrefsqInstr 16
        let s5 ← expectDecodeStep "decode/asm-tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let codeBchk ←
          match assembleCp0 [bchkbitrefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bchkbitrefs failed: {e}")
        if codeBchk.bits = natToBits bchkbitrefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/bchkbitrefs: expected 0xcf3b, got {codeBchk.bits}")

        match assembleCp0 [.cellOp (.bchk false false false)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/bchk-invalid: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/bchk-invalid: expected invOpcode, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits bchkrefsWord 16 ++
          natToBits bchkbitrefsWord 16 ++
          natToBits bchkbitsqWord 16 ++
          natToBits (bchkBitsImmWord 1 false) 24 ++
          natToBits (bchkBitsImmWord 256 true) 24 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-bchkrefs" r0 bchkrefsInstr 16
        let r2 ← expectDecodeStep "decode/raw-bchkbitrefs" r1 bchkbitrefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-bchkbitsq" r2 bchkbitsqInstr 16
        let r4 ← expectDecodeStep "decode/raw-bchkbitsimm-1" r3 (bchkBitsImmInstr 1 false) 24
        let r5 ← expectDecodeStep "decode/raw-bchkbitsimmq-256" r4 (bchkBitsImmInstr 256 true) 24
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/bchk-only-fallback-and-hit"
      run := do
        expectOkStack "dispatch/non-cell-op-falls-through"
          (runBchkBitRefsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-non-bchk-falls-through"
          (runBchkBitRefsDispatchFallback (.cellOp .bdepth) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-bchkbitsimm-falls-through"
          (runBchkBitRefsDispatchFallback (bchkBitsImmInstr 8 false) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]

        expectOkStack "dispatch/target-hit-no-sentinel"
          (runBchkBitRefsDispatchFallback bchkbitrefsInstr
            (mkBchkStackNat Builder.empty 0 0 #[.slice fullSliceNoiseB]))
          #[.slice fullSliceNoiseB]

        expectErr "dispatch/target-hit-error-no-sentinel"
          (runBchkBitRefsDispatchFallback bchkbitrefsInstr
            (mkBchkStackNat (mkBuilderWithCounts 1023 4) 1 1))
          .cellOv }
  ]
  oracle := #[
    mkBchkBitRefsCase "ok/empty/+0+0"
      (mkBchkStackNat Builder.empty 0 0),
    mkBchkBitRefsCase "ok/empty/+1+0"
      (mkBchkStackNat Builder.empty 1 0),
    mkBchkBitRefsCase "ok/empty/+0+1"
      (mkBchkStackNat Builder.empty 0 1),
    mkBchkBitRefsCase "ok/exact-bits-1023"
      (mkBchkStackNat Builder.empty 1023 0),
    mkBchkBitRefsCase "ok/exact-refs-4"
      (mkBchkStackNat Builder.empty 0 4),
    mkBchkBitRefsCase "ok/exact-both-empty/+23+3"
      (mkBchkStackNat Builder.empty 23 3),
    mkBchkBitRefsCase "ok/exact-both-empty/+1+1"
      (mkBchkStackNat Builder.empty 1 1),
    mkBchkBitRefsCase "ok/full-empty-check-zero"
      (mkBchkStackNat Builder.empty 0 0),
    mkBchkBitRefsCase "ok/deep/null-noise"
      (mkBchkStackNat Builder.empty 100 2 #[.null]),
    mkBchkBitRefsCase "ok/deep/int-noise"
      (mkBchkStackNat Builder.empty 100 2 #[intV 42]),
    mkBchkBitRefsCase "ok/deep/cell-noise"
      (mkBchkStackNat Builder.empty 256 3 #[.cell refLeafC]),
    mkBchkBitRefsCase "ok/deep/full-slice-noise"
      (mkBchkStackNat Builder.empty 200 2 #[.slice fullSliceNoiseA]),
    mkBchkBitRefsCase "ok/deep/two-noise-full-slice"
      (mkBchkStackNat Builder.empty 400 4 #[.slice fullSliceNoiseB, .null]),

    mkBchkBitRefsCase "cellov/refs-overflow/b0-r0/+0+5"
      (mkBchkStackNat Builder.empty 0 5),
    mkBchkBitRefsCase "cellov/refs-overflow/b0-r0/+20+6"
      (mkBchkStackNat Builder.empty 20 6),
    mkBchkBitRefsCase "cellov/refs-overflow/b0-r0/+1023+5"
      (mkBchkStackNat Builder.empty 1023 5),
    mkBchkBitRefsCase "cellov/refs-overflow/deep-noise"
      (mkBchkStackNat Builder.empty 100 7 #[.slice fullSliceNoiseA]),

    mkBchkBitRefsCase "underflow/empty" #[],
    mkBchkBitRefsCase "underflow/one-item"
      #[.builder Builder.empty],
    mkBchkBitRefsCase "underflow/two-items"
      #[.builder Builder.empty, intV 0],
    mkBchkBitRefsCase "type/refs-top-null"
      #[.builder Builder.empty, intV 0, .null],
    mkBchkBitRefsCase "range/refs-over7"
      #[.builder Builder.empty, intV 0, intV 8],
    mkBchkBitRefsCase "range/refs-negative"
      #[.builder Builder.empty, intV 0, intV (-1)],
    mkBchkBitRefsCase "range/refs-nan-via-program"
      #[.builder Builder.empty, intV 0]
      #[.pushInt .nan, bchkbitrefsInstr],
    mkBchkBitRefsCase "type/bits-not-int"
      #[.builder Builder.empty, .null, intV 0],
    mkBchkBitRefsCase "range/bits-over1023"
      #[.builder Builder.empty, intV 1024, intV 0],
    mkBchkBitRefsCase "range/bits-negative"
      #[.builder Builder.empty, intV (-1), intV 0],
    mkBchkBitRefsCase "range/bits-nan-via-program"
      #[.builder Builder.empty]
      #[.pushInt .nan, .pushInt (.num 0), bchkbitrefsInstr],
    mkBchkBitRefsCase "type/builder-not-builder"
      #[.null, intV 1, intV 1],

    mkBchkBitRefsCase "gas/exact-cost-succeeds"
      (mkBchkStackNat Builder.empty 1 1)
      #[.pushInt (.num bchkBitRefsSetGasExact), .tonEnvOp .setGasLimit, bchkbitrefsInstr],
    mkBchkBitRefsCase "gas/exact-minus-one-out-of-gas"
      (mkBchkStackNat Builder.empty 1 1)
      #[.pushInt (.num bchkBitRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkbitrefsInstr]
  ]
  fuzz := #[
    { seed := 2026021109
      count := 500
      gen := genBchkBitRefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKBITREFS
