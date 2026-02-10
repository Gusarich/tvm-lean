import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKREFS

/-
BCHKREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Bchk.lean` (`.bchk needBits needRefs quiet`)
  - `TvmLean/Semantics/Exec/CellOp.lean` (dispatch chain for `.cellOp`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`BCHKREFS` encode: `0xcf3a`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xcf3a` decode; neighboring `0xcf39/0xcf3b/0xcf3e`;
     24-bit `BCHKBITS{Q}` immediate prefixes `0xcf38/0xcf3c`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_chk_bits_refs`, mode=`2` for `BCHKREFS`).

Mode=2 alignment used in this suite:
- underflow check requires 2 stack items;
- pop order is `refs` (top) → `builder`;
- refs range/type errors happen before builder pop/type;
- non-quiet mode throws `cell_ov` on capacity failure, otherwise pushes nothing.

Oracle/fuzz slice constraint:
- whenever this suite places slices in oracle/fuzz stacks (as deep noise),
  they are full-cell slices only (`bitPos = 0`, `refPos = 0`).
-/

private def bchkrefsId : InstrId := { name := "BCHKREFS" }

private def bchkrefsInstr : Instr := .cellOp (.bchk false true false)
private def bchkbitsInstr : Instr := .cellOp (.bchk true false false)
private def bchkbitrefsInstr : Instr := .cellOp (.bchk true true false)
private def bchkrefsqInstr : Instr := .cellOp (.bchk false true true)

private def bchkrefsWord : Nat := 0xcf3a
private def bchkbitsWord : Nat := 0xcf39
private def bchkbitrefsWord : Nat := 0xcf3b
private def bchkrefsqWord : Nat := 0xcf3e

private def bchkBitsImmInstr (bits : Nat) (quiet : Bool := false) : Instr :=
  .cellOp (.bchkBitsImm bits quiet)

private def bchkBitsImmWord (bits : Nat) (quiet : Bool := false) : Nat :=
  ((if quiet then 0xcf3c else 0xcf38) <<< 8) + (bits - 1)

private def execInstrCellOpBchkOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def mkBchkRefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bchkrefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkRefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkOnly bchkrefsInstr stack

private def dispatchSentinel : Int := 654

private def runBchkRefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBchkOnly instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok ls, .ok rs => ls == rs
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got lhs={reprStr lhs}, rhs={reprStr rhs}")

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]
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

private def mkBchkRefsStack (builder : Builder) (refs : Int) (below : Array Value := #[]) :
    Array Value :=
  below ++ #[.builder builder, intV refs]

private def mkBchkRefsStackNat (builder : Builder) (refs : Nat) (below : Array Value := #[]) :
    Array Value :=
  mkBchkRefsStack builder (Int.ofNat refs) below

private def mkBchkBitRefsAlignedStackNat
    (builder : Builder)
    (refs : Nat)
    (below : Array Value := #[]) : Array Value :=
  below ++ #[.builder builder, intV 0, intV (Int.ofNat refs)]

private def runBchkBitRefsAlignedDirect
    (builder : Builder)
    (refs : Nat)
    (below : Array Value := #[]) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkOnly bchkbitrefsInstr (mkBchkBitRefsAlignedStackNat builder refs below)

private def fullSliceNoiseA : Slice := mkFullSlice 9 0
private def fullSliceNoiseB : Slice := mkFullSlice 13 1 #[refLeafA]

private def bchkRefsSetGasExact : Int :=
  computeExactGasBudget bchkrefsInstr

private def bchkRefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bchkrefsInstr

private def bchkRefsReqBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7]

private def pickBchkRefsReqMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 5 then
    let (idx, rng2) := randNat rng1 0 (bchkRefsReqBoundaryPool.size - 1)
    (bchkRefsReqBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 7

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 73
    else if pick = 2 then .cell refLeafB
    else if pick = 3 then .slice (mkFullSlice 7 1)
    else .slice (mkFullSlice 5 0 #[refLeafA])
  (noise, rng1)

private def genBchkRefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    let (refsReq, rng2) := randNat rng1 0 4
    (mkBchkRefsCase s!"fuzz/ok/empty/+{refsReq}"
      (mkBchkRefsStackNat Builder.empty refsReq), rng2)
  else if shape = 1 then
    let (refsReq, rng2) := randNat rng1 0 4
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkRefsCase s!"fuzz/ok/deep1/+{refsReq}"
      (mkBchkRefsStackNat Builder.empty refsReq #[noise]), rng3)
  else if shape = 2 then
    let (refsReq, rng2) := randNat rng1 0 4
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkRefsCase s!"fuzz/ok/deep2/+{refsReq}"
      (mkBchkRefsStackNat Builder.empty refsReq #[.slice fullSliceNoiseA, noise]), rng3)
  else if shape = 3 then
    let (refsReq, rng2) := randNat rng1 5 7
    (mkBchkRefsCase s!"fuzz/cellov/empty/+{refsReq}"
      (mkBchkRefsStackNat Builder.empty refsReq), rng2)
  else if shape = 4 then
    let (refsReq, rng2) := randNat rng1 5 7
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkRefsCase s!"fuzz/cellov/deep/+{refsReq}"
      (mkBchkRefsStackNat Builder.empty refsReq #[noise]), rng3)
  else if shape = 5 then
    (mkBchkRefsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkBchkRefsCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkBchkRefsCase "fuzz/type/refs-top-null"
      #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkBchkRefsCase "fuzz/range/refs-over7"
      #[.builder Builder.empty, intV 8], rng1)
  else if shape = 9 then
    (mkBchkRefsCase "fuzz/range/refs-negative"
      #[.builder Builder.empty, intV (-1)], rng1)
  else if shape = 10 then
    (mkBchkRefsCase "fuzz/type/builder-not-builder"
      #[.null, intV 0], rng1)
  else if shape = 11 then
    (mkBchkRefsCase "fuzz/order/refs-range-before-builder-type"
      #[.null, intV 8], rng1)
  else if shape = 12 then
    let (refsReq, rng2) := pickBchkRefsReqMixed rng1
    (mkBchkRefsCase s!"fuzz/gas/exact/+{refsReq}"
      (mkBchkRefsStackNat Builder.empty refsReq)
      #[.pushInt (.num bchkRefsSetGasExact), .tonEnvOp .setGasLimit, bchkrefsInstr], rng2)
  else
    let (refsReq, rng2) := pickBchkRefsReqMixed rng1
    (mkBchkRefsCase s!"fuzz/gas/exact-minus-one/+{refsReq}"
      (mkBchkRefsStackNat Builder.empty refsReq)
      #[.pushInt (.num bchkRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkrefsInstr], rng2)

def suite : InstrSuite where
  id := bchkrefsId
  unit := #[
    { name := "unit/direct/success-boundaries-and-deep-stack"
      run := do
        expectOkStack "ok/empty-plus-0"
          (runBchkRefsDirect (mkBchkRefsStackNat Builder.empty 0))
          #[]
        expectOkStack "ok/empty-plus-1"
          (runBchkRefsDirect (mkBchkRefsStackNat Builder.empty 1))
          #[]
        expectOkStack "ok/empty-plus-4"
          (runBchkRefsDirect (mkBchkRefsStackNat Builder.empty 4))
          #[]

        expectOkStack "ok/full-bits-refs3-plus-1"
          (runBchkRefsDirect (mkBchkRefsStackNat (mkBuilderWithCounts 1023 3) 1))
          #[]
        expectOkStack "ok/full-bits-refs4-plus-0"
          (runBchkRefsDirect (mkBchkRefsStackNat (mkBuilderWithCounts 1023 4) 0))
          #[]
        expectOkStack "ok/deep-stack-preserve-below"
          (runBchkRefsDirect
            (mkBchkRefsStackNat (mkBuilderWithCounts 700 2) 2
              #[.null, intV 91, .slice fullSliceNoiseA]))
          #[.null, intV 91, .slice fullSliceNoiseA] }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty" (runBchkRefsDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runBchkRefsDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/refs-top-null"
          (runBchkRefsDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "range/refs-over7"
          (runBchkRefsDirect #[.builder Builder.empty, intV 8]) .rangeChk
        expectErr "range/refs-negative"
          (runBchkRefsDirect #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/refs-nan"
          (runBchkRefsDirect #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "type/builder-not-builder-after-valid-refs"
          (runBchkRefsDirect #[.null, intV 0]) .typeChk

        expectErr "order/refs-range-before-builder-type"
          (runBchkRefsDirect #[.null, intV 8]) .rangeChk
        expectErr "order/refs-type-before-builder-type"
          (runBchkRefsDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-boundaries"
      run := do
        expectErr "cellov/empty-plus-5"
          (runBchkRefsDirect (mkBchkRefsStackNat Builder.empty 5))
          .cellOv
        expectErr "cellov/refs4-plus-1"
          (runBchkRefsDirect (mkBchkRefsStackNat (mkBuilderWithCounts 0 4) 1))
          .cellOv
        expectErr "cellov/refs2-plus-3"
          (runBchkRefsDirect (mkBchkRefsStackNat (mkBuilderWithCounts 0 2) 3))
          .cellOv
        expectErr "cellov/full-bits-refs3-plus-2"
          (runBchkRefsDirect (mkBchkRefsStackNat (mkBuilderWithCounts 1023 3) 2))
          .cellOv
        expectErr "cellov/full-bits-refs4-plus-1"
          (runBchkRefsDirect (mkBchkRefsStackNat (mkBuilderWithCounts 1023 4) 1))
          .cellOv
        expectErr "cellov/deep-stack-preserve-noise-on-error"
          (runBchkRefsDirect
            (mkBchkRefsStackNat (mkBuilderWithCounts 400 4) 1 #[.slice fullSliceNoiseB]))
          .cellOv }
    ,
    { name := "unit/opcode/decode-assembler-and-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[bchkbitsInstr, bchkrefsInstr, bchkbitrefsInstr, bchkrefsqInstr, .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-bchkbits-neighbor" s0 bchkbitsInstr 16
        let s2 ← expectDecodeStep "decode/asm-bchkrefs" s1 bchkrefsInstr 16
        let s3 ← expectDecodeStep "decode/asm-bchkbitrefs-neighbor" s2 bchkbitrefsInstr 16
        let s4 ← expectDecodeStep "decode/asm-bchkrefsq-neighbor" s3 bchkrefsqInstr 16
        let s5 ← expectDecodeStep "decode/asm-tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let codeBchk ←
          match assembleCp0 [bchkrefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bchkrefs failed: {e}")
        if codeBchk.bits = natToBits bchkrefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/bchkrefs: expected 0xcf3a, got {codeBchk.bits}")

        match assembleCp0 [.cellOp (.bchk false false false)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/bchk-invalid: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/bchk-invalid: expected invOpcode, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits bchkbitsWord 16 ++
          natToBits bchkrefsWord 16 ++
          natToBits bchkrefsqWord 16 ++
          natToBits (bchkBitsImmWord 1 false) 24 ++
          natToBits bchkbitrefsWord 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-bchkbits-neighbor" r0 bchkbitsInstr 16
        let r2 ← expectDecodeStep "decode/raw-bchkrefs" r1 bchkrefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-bchkrefsq-neighbor" r2 bchkrefsqInstr 16
        let r4 ← expectDecodeStep "decode/raw-bchkbitsimm-1-neighbor" r3 (bchkBitsImmInstr 1 false) 24
        let r5 ← expectDecodeStep "decode/raw-bchkbitrefs-neighbor" r4 bchkbitrefsInstr 16
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/bchk-only-fallback-and-hit"
      run := do
        expectOkStack "dispatch/non-cell-op-falls-through"
          (runBchkRefsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-non-bchk-falls-through"
          (runBchkRefsDispatchFallback (.cellOp .bdepth) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-bchkbitsimm-falls-through"
          (runBchkRefsDispatchFallback (bchkBitsImmInstr 8 false) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]

        expectOkStack "dispatch/target-hit-no-sentinel"
          (runBchkRefsDispatchFallback bchkrefsInstr
            (mkBchkRefsStackNat Builder.empty 0 #[.slice fullSliceNoiseB]))
          #[.slice fullSliceNoiseB]

        expectErr "dispatch/target-hit-error-no-sentinel"
          (runBchkRefsDispatchFallback bchkrefsInstr
            (mkBchkRefsStackNat (mkBuilderWithCounts 1000 4) 1))
          .cellOv }
    ,
    { name := "unit/alias-equivalence/bchkrefs-vs-bchkbitrefs-with-bits-0"
      run := do
        let successChecks : Array (Builder × Nat × Array Value) :=
          #[
            (Builder.empty, 0, #[]),
            (Builder.empty, 4, #[]),
            (mkBuilderWithCounts 1023 3, 1, #[]),
            (mkBuilderWithCounts 500 2, 2, #[.null, .slice fullSliceNoiseA])
          ]
        for (b, refsReq, below) in successChecks do
          expectSameOutcome s!"align/success/refs-{refsReq}/bits-used-{b.bits.size}/refs-used-{b.refs.size}"
            (runBchkRefsDirect (mkBchkRefsStackNat b refsReq below))
            (runBchkBitRefsAlignedDirect b refsReq below)

        let cellOvChecks : Array (Builder × Nat) :=
          #[
            (Builder.empty, 5),
            (mkBuilderWithCounts 0 4, 1),
            (mkBuilderWithCounts 1023 4, 1)
          ]
        for (b, refsReq) in cellOvChecks do
          expectSameOutcome s!"align/cellov/refs-{refsReq}/refs-used-{b.refs.size}"
            (runBchkRefsDirect (mkBchkRefsStackNat b refsReq))
            (runBchkBitRefsAlignedDirect b refsReq)

        expectSameOutcome "align/error/refs-range-over7-before-builder-type"
          (runBchkRefsDirect #[.null, intV 8])
          (runHandlerDirect execInstrCellOpBchkOnly bchkbitrefsInstr #[.null, intV 0, intV 8])
        expectSameOutcome "align/error/refs-type-before-builder-type"
          (runBchkRefsDirect #[.null, .null])
          (runHandlerDirect execInstrCellOpBchkOnly bchkbitrefsInstr #[.null, intV 0, .null]) }
  ]
  oracle := #[
    mkBchkRefsCase "ok/empty/+0"
      (mkBchkRefsStackNat Builder.empty 0),
    mkBchkRefsCase "ok/empty/+1"
      (mkBchkRefsStackNat Builder.empty 1),
    mkBchkRefsCase "ok/empty/+2"
      (mkBchkRefsStackNat Builder.empty 2),
    mkBchkRefsCase "ok/empty/+3"
      (mkBchkRefsStackNat Builder.empty 3),
    mkBchkRefsCase "ok/empty/+4"
      (mkBchkRefsStackNat Builder.empty 4),

    mkBchkRefsCase "ok/deep/null-noise"
      (mkBchkRefsStackNat Builder.empty 2 #[.null]),
    mkBchkRefsCase "ok/deep/int-noise"
      (mkBchkRefsStackNat Builder.empty 3 #[intV 42]),
    mkBchkRefsCase "ok/deep/cell-noise"
      (mkBchkRefsStackNat Builder.empty 1 #[.cell refLeafC]),
    mkBchkRefsCase "ok/deep/full-slice-noise"
      (mkBchkRefsStackNat Builder.empty 4 #[.slice fullSliceNoiseA]),
    mkBchkRefsCase "ok/deep/two-noise"
      (mkBchkRefsStackNat Builder.empty 0 #[.slice fullSliceNoiseB, .null]),

    mkBchkRefsCase "cellov/empty/+5"
      (mkBchkRefsStackNat Builder.empty 5),
    mkBchkRefsCase "cellov/empty/+6"
      (mkBchkRefsStackNat Builder.empty 6),
    mkBchkRefsCase "cellov/empty/+7"
      (mkBchkRefsStackNat Builder.empty 7),
    mkBchkRefsCase "cellov/deep/+7"
      (mkBchkRefsStackNat Builder.empty 7 #[.slice fullSliceNoiseA]),

    mkBchkRefsCase "underflow/empty" #[],
    mkBchkRefsCase "underflow/one-item"
      #[.builder Builder.empty],
    mkBchkRefsCase "type/refs-top-null"
      #[.builder Builder.empty, .null],
    mkBchkRefsCase "range/refs-over7"
      #[.builder Builder.empty, intV 8],
    mkBchkRefsCase "range/refs-negative"
      #[.builder Builder.empty, intV (-1)],
    mkBchkRefsCase "range/refs-nan-via-program"
      #[.builder Builder.empty]
      #[.pushInt .nan, bchkrefsInstr],
    mkBchkRefsCase "type/builder-not-builder"
      #[.null, intV 1],
    mkBchkRefsCase "order/refs-range-before-builder-type"
      #[.null, intV 8],
    mkBchkRefsCase "order/refs-type-before-builder-type"
      #[.null, .null],

    mkBchkRefsCase "gas/exact-cost-succeeds"
      (mkBchkRefsStackNat Builder.empty 1)
      #[.pushInt (.num bchkRefsSetGasExact), .tonEnvOp .setGasLimit, bchkrefsInstr],
    mkBchkRefsCase "gas/exact-minus-one-out-of-gas"
      (mkBchkRefsStackNat Builder.empty 1)
      #[.pushInt (.num bchkRefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkrefsInstr]
  ]
  fuzz := #[
    { seed := 2026021117
      count := 320
      gen := genBchkRefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKREFS
