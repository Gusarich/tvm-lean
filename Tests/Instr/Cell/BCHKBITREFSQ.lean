import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKBITREFSQ

/-
BCHKBITREFSQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Bchk.lean` (`.bchk true true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.bchk true true true` encode: `0xcf3f`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf3f` decode to `.cellOp (.bchk true true true)`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_chk_bits_refs`, mode `7`, opcode `0xcf3f`).

Branch map used for this suite (`needBits=true`, `needRefs=true`, `quiet=true`):
- Lean BCHKBITREFSQ path: 6 branch sites / 9 terminal outcomes
  (`checkUnderflow 3`; refs pop type/range; bits pop type/range; builder pop type;
   `canExtendBy(bits, refs)` split; quiet status `-1/0`).
- C++ BCHKBITREFSQ path: 5 branch sites / 8 aligned outcomes
  (`check_underflow(3)`; `pop_smallint_range(7)`; `pop_smallint_range(1023)`;
   `pop_builder`; `can_extend_by(bits, refs)` -> push `-1/0`).

Key risk areas:
- operand order is `... builder bits refs` (refs are popped first);
- quiet failure returns status `0` and consumes all operands;
- refs use VM range `0..7` while builder capacity is `0..4` (refs `5..7` are quiet-fail, not range errors);
- oracle harness accepts only empty builders in `initStack`, so non-empty builders must be constructed in program.
-/

private def bchkBitRefsQId : InstrId := { name := "BCHKBITREFSQ" }

private def bchkBitRefsQInstr : Instr :=
  .cellOp (.bchk true true true)

private def bchkBitRefsInstr : Instr :=
  .cellOp (.bchk true true false)

private def bchkBitsQInstr : Instr :=
  .cellOp (.bchk true false true)

private def bchkRefsQInstr : Instr :=
  .cellOp (.bchk false true true)

private def execCellOpBchkInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def mkBchkBitRefsQCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bchkBitRefsQInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBchkBitRefsQProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkBitRefsQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpBchkInstr bchkBitRefsQInstr stack

private def runBchkBitRefsQDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpBchkInstr instr (VM.push (intV 53055)) stack

private def bchkBitRefsQSetGasExact : Int :=
  computeExactGasBudget bchkBitRefsQInstr

private def bchkBitRefsQSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bchkBitRefsQInstr

private def refCellA : Cell :=
  (Builder.empty.storeBits (natToBits 1 1)).finalize

private def refCellB : Cell :=
  (Builder.empty.storeBits (natToBits 2 2)).finalize

private def refCellC : Cell :=
  (Builder.empty.storeBits (natToBits 0xA5 8)).finalize

private def refCellD : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[Cell.empty]

private def mkRefCells : Nat → Array Cell
  | 0 => #[]
  | 1 => #[refCellA]
  | 2 => #[refCellA, refCellB]
  | 3 => #[refCellA, refCellB, refCellC]
  | _ => #[refCellA, refCellB, refCellC, refCellD]

private def mkBuilderBitsRefs (bits refs : Nat) : Builder :=
  { bits := Array.replicate bits false
    refs := mkRefCells refs }

private def oracleNoiseSliceA : Slice :=
  mkSliceFromBits (natToBits 0x15 5)

private def oracleNoiseSliceB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 2 2) #[Cell.empty])

private def mkBuilderProgramBitsRefs
    (builderBits builderRefs : Nat) : Array Instr :=
  #[.newc]
    ++ (if builderBits = 0 then #[] else #[.pushInt (.num (Int.ofNat builderBits)), .stZeroes])
    ++ appendRefsToTopBuilder builderRefs

private def mkBchkBitRefsQProgram
    (builderBits builderRefs needBits needRefs : Nat) : Array Instr :=
  mkBuilderProgramBitsRefs builderBits builderRefs
    ++ #[.pushInt (.num (Int.ofNat needBits)), .pushInt (.num (Int.ofNat needRefs)), bchkBitRefsQInstr]

private def bchkProgramRefsNan : Array Instr :=
  #[.newc, .pushInt (.num 0), .pushInt .nan, bchkBitRefsQInstr]

private def bchkProgramBitsNan : Array Instr :=
  #[.newc, .pushInt .nan, .pushInt (.num 0), bchkBitRefsQInstr]

private def needBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 767, 1022, 1023]

private def builderBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 768, 900, 1022, 1023]

private def builderBitsNonZeroPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 768, 900, 1022, 1023]

private def builderRefsPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def pickFromNatPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNatUpToEdge (rng : StdGen) (max : Nat) : Nat × StdGen :=
  if max = 0 then
    (0, rng)
  else
    let (mode, rng1) := randNat rng 0 4
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (max, rng1)
    else if mode = 2 then
      (if max > 0 then max - 1 else 0, rng1)
    else if mode = 3 then
      (Nat.min 1 max, rng1)
    else
      randNat rng1 0 max

private def pickNeedBitsOverflow (rng : StdGen) (builderBits : Nat) : Nat × StdGen :=
  let minNeed : Nat := (1023 - builderBits) + 1
  let maxNeed : Nat := 1023
  if minNeed >= maxNeed then
    (minNeed, rng)
  else
    let (mode, rng1) := randNat rng 0 2
    if mode = 0 then
      (minNeed, rng1)
    else if mode = 1 then
      (maxNeed, rng1)
    else
      randNat rng1 minNeed maxNeed

private def pickNeedRefsOverflow (rng : StdGen) (builderRefs : Nat) : Nat × StdGen :=
  let minNeed : Nat := (4 - builderRefs) + 1
  let maxNeed : Nat := 7
  if minNeed >= maxNeed then
    (minNeed, rng)
  else
    let (mode, rng1) := randNat rng 0 2
    if mode = 0 then
      (minNeed, rng1)
    else if mode = 1 then
      (maxNeed, rng1)
    else
      randNat rng1 minNeed maxNeed

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else if pick = 2 then .cell refCellA
    else if pick = 3 then .slice oracleNoiseSliceA
    else .slice oracleNoiseSliceB
  (v, rng1)

private def genBchkBitRefsQFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  if shape = 0 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    let (needRefs, rng3) := randNat rng2 0 4
    (mkBchkBitRefsQCase s!"fuzz/ok/direct/empty/b{needBits}/r{needRefs}"
      #[.builder Builder.empty, intV (Int.ofNat needBits), intV (Int.ofNat needRefs)], rng3)
  else if shape = 1 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    let (needRefs, rng3) := randNat rng2 0 4
    let (noise, rng4) := pickNoiseValue rng3
    (mkBchkBitRefsQCase s!"fuzz/ok/direct/noise/b{needBits}/r{needRefs}"
      #[noise, .builder Builder.empty, intV (Int.ofNat needBits), intV (Int.ofNat needRefs)], rng4)
  else if shape = 2 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    let (needRefs, rng3) := randNat rng2 5 7
    (mkBchkBitRefsQCase s!"fuzz/fail/direct/empty/b{needBits}/r{needRefs}"
      #[.builder Builder.empty, intV (Int.ofNat needBits), intV (Int.ofNat needRefs)], rng3)
  else if shape = 3 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    let (needRefs, rng3) := randNat rng2 5 7
    let (noise, rng4) := pickNoiseValue rng3
    (mkBchkBitRefsQCase s!"fuzz/fail/direct/noise/b{needBits}/r{needRefs}"
      #[noise, .builder Builder.empty, intV (Int.ofNat needBits), intV (Int.ofNat needRefs)], rng4)
  else if shape = 4 then
    (mkBchkBitRefsQCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkBchkBitRefsQCase "fuzz/underflow/two-items" #[.builder Builder.empty, intV 0], rng1)
  else if shape = 6 then
    (mkBchkBitRefsQCase "fuzz/type/refs-top-not-int" #[.builder Builder.empty, intV 0, .null], rng1)
  else if shape = 7 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    (mkBchkBitRefsQCase s!"fuzz/range/refs-negative/b{needBits}"
      #[.builder Builder.empty, intV (Int.ofNat needBits), intV (-1)], rng2)
  else if shape = 8 then
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    (mkBchkBitRefsQCase s!"fuzz/range/refs-gt7/b{needBits}"
      #[.builder Builder.empty, intV (Int.ofNat needBits), intV 8], rng2)
  else if shape = 9 then
    (mkBchkBitRefsQCase "fuzz/range/bits-gt1023"
      #[.builder Builder.empty, intV 1024, intV 0], rng1)
  else if shape = 10 then
    (mkBchkBitRefsQCase "fuzz/type/bits-not-int-after-refs"
      #[.builder Builder.empty, .null, intV 0], rng1)
  else if shape = 11 then
    (mkBchkBitRefsQCase "fuzz/type/builder-not-builder"
      #[.null, intV 0, intV 0], rng1)
  else if shape = 12 then
    let (builderBits, rng2) := pickFromNatPool rng1 builderBitsPool
    let (builderRefs, rng3) := pickFromNatPool rng2 builderRefsPool
    let (needBits, rng4) := pickNatUpToEdge rng3 (1023 - builderBits)
    let (needRefs, rng5) := pickNatUpToEdge rng4 (4 - builderRefs)
    let (withNoise, rng6) := randNat rng5 0 1
    let initStack : Array Value :=
      if withNoise = 0 then #[] else #[.slice oracleNoiseSliceA]
    (mkBchkBitRefsQProgramCase
      s!"fuzz/ok/program/bb{builderBits}/br{builderRefs}/nb{needBits}/nr{needRefs}"
      initStack
      (mkBchkBitRefsQProgram builderBits builderRefs needBits needRefs), rng6)
  else if shape = 13 then
    let (builderBits, rng2) := pickFromNatPool rng1 builderBitsNonZeroPool
    let (builderRefs, rng3) := pickFromNatPool rng2 builderRefsPool
    let (needBits, rng4) := pickNeedBitsOverflow rng3 builderBits
    let (needRefs, rng5) := pickNatUpToEdge rng4 (4 - builderRefs)
    (mkBchkBitRefsQProgramCase
      s!"fuzz/fail/program-bits/bb{builderBits}/br{builderRefs}/nb{needBits}/nr{needRefs}"
      #[]
      (mkBchkBitRefsQProgram builderBits builderRefs needBits needRefs), rng5)
  else if shape = 14 then
    let (builderBits, rng2) := pickFromNatPool rng1 builderBitsPool
    let (builderRefs, rng3) := pickFromNatPool rng2 builderRefsPool
    let (needBits, rng4) := pickNatUpToEdge rng3 (1023 - builderBits)
    let (needRefs, rng5) := pickNeedRefsOverflow rng4 builderRefs
    let (noise, rng6) := pickNoiseValue rng5
    (mkBchkBitRefsQProgramCase
      s!"fuzz/fail/program-refs/bb{builderBits}/br{builderRefs}/nb{needBits}/nr{needRefs}"
      #[noise]
      (mkBchkBitRefsQProgram builderBits builderRefs needBits needRefs), rng6)
  else if shape = 15 then
    let (mode, rng2) := randNat rng1 0 1
    if mode = 0 then
      (mkBchkBitRefsQProgramCase "fuzz/range/program-refs-nan" #[] bchkProgramRefsNan, rng2)
    else
      (mkBchkBitRefsQProgramCase "fuzz/range/program-bits-nan" #[] bchkProgramBitsNan, rng2)
  else
    let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
    let (needRefs, rng3) := randNat rng2 0 4
    let (mode, rng4) := randNat rng3 0 1
    if mode = 0 then
      (mkBchkBitRefsQCase "fuzz/gas/exact"
        #[.builder Builder.empty, intV (Int.ofNat needBits), intV (Int.ofNat needRefs)]
        #[.pushInt (.num bchkBitRefsQSetGasExact), .tonEnvOp .setGasLimit, bchkBitRefsQInstr], rng4)
    else
      (mkBchkBitRefsQCase "fuzz/gas/exact-minus-one"
        #[.builder Builder.empty, intV (Int.ofNat needBits), intV (Int.ofNat needRefs)]
        #[.pushInt (.num bchkBitRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitRefsQInstr], rng4)

def suite : InstrSuite where
  id := bchkBitRefsQId
  unit := #[
    { name := "unit/direct/success-status-and-order"
      run := do
        expectOkStack "ok/empty-builder-max-need"
          (runBchkBitRefsQDirect #[.builder Builder.empty, intV 1023, intV 4])
          #[intV (-1)]

        let nearFullBitsRefs3 := mkBuilderBitsRefs 1022 3
        expectOkStack "ok/near-full-exact-fit"
          (runBchkBitRefsQDirect #[.builder nearFullBitsRefs3, intV 1, intV 1])
          #[intV (-1)]

        let fullBitsRefs3 := mkBuilderBitsRefs 1023 3
        expectOkStack "ok/deep-stack-preserve-noise"
          (runBchkBitRefsQDirect
            #[.slice oracleNoiseSliceA, intV 99, .builder fullBitsRefs3, intV 0, intV 1])
          #[.slice oracleNoiseSliceA, intV 99, intV (-1)] }
    ,
    { name := "unit/direct/quiet-overflow-returns-zero"
      run := do
        let fullBitsRefs4 := mkBuilderBitsRefs 1023 4
        expectOkStack "quiet-fail/bits-overflow"
          (runBchkBitRefsQDirect #[.builder fullBitsRefs4, intV 1, intV 0])
          #[intV 0]

        expectOkStack "quiet-fail/refs-overflow"
          (runBchkBitRefsQDirect #[.builder fullBitsRefs4, intV 0, intV 1])
          #[intV 0]

        let bits1022Refs4 := mkBuilderBitsRefs 1022 4
        expectOkStack "quiet-fail/bits-and-refs-overflow-with-noise"
          (runBchkBitRefsQDirect #[.slice oracleNoiseSliceB, .builder bits1022Refs4, intV 1, intV 1])
          #[.slice oracleNoiseSliceB, intV 0] }
    ,
    { name := "unit/direct/underflow-range-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runBchkBitRefsQDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runBchkBitRefsQDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/two-items" (runBchkBitRefsQDirect #[.builder Builder.empty, intV 0]) .stkUnd

        expectErr "type/refs-top-not-int"
          (runBchkBitRefsQDirect #[.builder Builder.empty, intV 0, .null]) .typeChk
        expectErr "range/refs-negative"
          (runBchkBitRefsQDirect #[.builder Builder.empty, intV 0, intV (-1)]) .rangeChk
        expectErr "range/refs-gt7"
          (runBchkBitRefsQDirect #[.builder Builder.empty, intV 0, intV 8]) .rangeChk
        expectErr "range/refs-nan"
          (runBchkBitRefsQDirect #[.builder Builder.empty, intV 0, .int .nan]) .rangeChk

        expectErr "type/bits-not-int-after-refs"
          (runBchkBitRefsQDirect #[.builder Builder.empty, .null, intV 0]) .typeChk
        expectErr "range/bits-negative"
          (runBchkBitRefsQDirect #[.builder Builder.empty, intV (-1), intV 0]) .rangeChk
        expectErr "range/bits-gt1023"
          (runBchkBitRefsQDirect #[.builder Builder.empty, intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-nan"
          (runBchkBitRefsQDirect #[.builder Builder.empty, .int .nan, intV 0]) .rangeChk

        expectErr "order/refs-before-builder"
          (runBchkBitRefsQDirect #[.null, intV 0, intV 8]) .rangeChk
        expectErr "order/bits-before-builder"
          (runBchkBitRefsQDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "type/builder-popped-last"
          (runBchkBitRefsQDirect #[.null, intV 0, intV 0]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-and-family-boundaries"
      run := do
        let program : Array Instr := #[
          bchkBitRefsInstr,
          bchkBitRefsQInstr,
          bchkRefsQInstr,
          bchkBitsQInstr,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/bchkbitrefs" s0 bchkBitRefsInstr 16
        let s2 ← expectDecodeStep "decode/bchkbitrefsq" s1 bchkBitRefsQInstr 16
        let s3 ← expectDecodeStep "decode/bchkrefsq" s2 bchkRefsQInstr 16
        let s4 ← expectDecodeStep "decode/bchkbitsq" s3 bchkBitsQInstr 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits
          (natToBits 0xcf3d 16 ++ natToBits 0xcf3e 16 ++ natToBits 0xcf3f 16 ++ natToBits 0xa0 8)
        let r1 ← expectDecodeStep "decode/raw-cf3d-bchkbitsq" raw bchkBitsQInstr 16
        let r2 ← expectDecodeStep "decode/raw-cf3e-bchkrefsq" r1 bchkRefsQInstr 16
        let r3 ← expectDecodeStep "decode/raw-cf3f-bchkbitrefsq" r2 bchkBitRefsQInstr 16
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-bchk-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-op"
          (runBchkBitRefsQDispatchFallback .add #[.null])
          #[.null, intV 53055]
        expectOkStack "dispatch/other-cellop"
          (runBchkBitRefsQDispatchFallback (.cellOp .bdepth) #[intV 7])
          #[intV 7, intV 53055] }
  ]
  oracle := #[
    mkBchkBitRefsQCase "ok/direct/empty-b0-r0"
      #[.builder Builder.empty, intV 0, intV 0],
    mkBchkBitRefsQCase "ok/direct/empty-b1-r0"
      #[.builder Builder.empty, intV 1, intV 0],
    mkBchkBitRefsQCase "ok/direct/empty-b1023-r4"
      #[.builder Builder.empty, intV 1023, intV 4],
    mkBchkBitRefsQCase "ok/direct/deep-noise-slice"
      #[.slice oracleNoiseSliceA, .builder Builder.empty, intV 7, intV 1],
    mkBchkBitRefsQCase "ok/direct/deep-noise-cell"
      #[.cell refCellA, .builder Builder.empty, intV 255, intV 2],

    mkBchkBitRefsQCase "fail/direct/empty-r5"
      #[.builder Builder.empty, intV 0, intV 5],
    mkBchkBitRefsQCase "fail/direct/empty-b1023-r7"
      #[.builder Builder.empty, intV 1023, intV 7],

    mkBchkBitRefsQCase "underflow/empty" #[],
    mkBchkBitRefsQCase "underflow/one-item"
      #[.builder Builder.empty],
    mkBchkBitRefsQCase "underflow/two-items"
      #[.builder Builder.empty, intV 0],

    mkBchkBitRefsQCase "type/refs-top-not-int"
      #[.builder Builder.empty, intV 0, .null],
    mkBchkBitRefsQCase "type/bits-not-int-after-refs"
      #[.builder Builder.empty, .null, intV 0],
    mkBchkBitRefsQCase "type/builder-not-builder"
      #[.null, intV 0, intV 0],

    mkBchkBitRefsQCase "range/refs-negative"
      #[.builder Builder.empty, intV 0, intV (-1)],
    mkBchkBitRefsQCase "range/refs-gt7"
      #[.builder Builder.empty, intV 0, intV 8],
    mkBchkBitRefsQCase "range/bits-negative"
      #[.builder Builder.empty, intV (-1), intV 0],
    mkBchkBitRefsQCase "range/bits-gt1023"
      #[.builder Builder.empty, intV 1024, intV 0],

    mkBchkBitRefsQProgramCase "range/program-refs-nan" #[] bchkProgramRefsNan,
    mkBchkBitRefsQProgramCase "range/program-bits-nan" #[] bchkProgramBitsNan,

    mkBchkBitRefsQCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty, intV 0, intV 0]
      #[.pushInt (.num bchkBitRefsQSetGasExact), .tonEnvOp .setGasLimit, bchkBitRefsQInstr],
    mkBchkBitRefsQCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, intV 0, intV 0]
      #[.pushInt (.num bchkBitRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitRefsQInstr],

    mkBchkBitRefsQProgramCase "ok/program/b1022-r3-need1-1" #[]
      (mkBchkBitRefsQProgram 1022 3 1 1),
    mkBchkBitRefsQProgramCase "ok/program/b1023-r3-need0-1-noise-slice"
      #[.slice oracleNoiseSliceB]
      (mkBchkBitRefsQProgram 1023 3 0 1),
    mkBchkBitRefsQProgramCase "ok/program/b1023-r4-need0-0" #[]
      (mkBchkBitRefsQProgram 1023 4 0 0),

    mkBchkBitRefsQProgramCase "fail/program/b1023-r4-need1-0" #[]
      (mkBchkBitRefsQProgram 1023 4 1 0),
    mkBchkBitRefsQProgramCase "fail/program/b1023-r4-need0-1-noise-cell"
      #[.cell Cell.empty]
      (mkBchkBitRefsQProgram 1023 4 0 1),
    mkBchkBitRefsQProgramCase "fail/program/b1022-r4-need1-1" #[]
      (mkBchkBitRefsQProgram 1022 4 1 1)
  ]
  fuzz := #[
    { seed := 2026021035
      count := 500
      gen := genBchkBitRefsQFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKBITREFSQ
