import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKREFSQ

/-
BCHKREFSQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Bchk.lean` (`.bchk false true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.bchk false true true` encode: `0xcf3e`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf3e` decode to `.cellOp (.bchk false true true)`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_chk_bits_refs`, mode `6`, opcode `0xcf3e`).

Branch map used for this suite (`needBits=false`, `needRefs=true`, `quiet=true`):
- underflow check requires exactly 2 stack items;
- pop order is `refs` (top) then `builder`;
- refs pop enforces type/range (`0..7`) before builder pop/type;
- quiet path always pushes a status: `-1` on fit, `0` on overflow;
- refs `5..7` are valid argument values (range-ok) that can still return quiet failure.
-/

private def bchkRefsQId : InstrId := { name := "BCHKREFSQ" }

private def bchkRefsQInstr : Instr :=
  .cellOp (.bchk false true true)

private def bchkRefsInstr : Instr :=
  .cellOp (.bchk false true false)

private def bchkBitsQInstr : Instr :=
  .cellOp (.bchk true false true)

private def bchkBitRefsQInstr : Instr :=
  .cellOp (.bchk true true true)

private def bchkBitsImmQInstr (bits : Nat) : Instr :=
  .cellOp (.bchkBitsImm bits true)

private def bchkRefsQWord : Nat := 0xcf3e
private def bchkRefsWord : Nat := 0xcf3a
private def bchkBitsQWord : Nat := 0xcf3d
private def bchkBitRefsQWord : Nat := 0xcf3f

private def bchkBitsImmQWord (bits : Nat) : Nat :=
  (0xcf3c <<< 8) + (bits - 1)

private def execCellOpBchkInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def mkBchkRefsQCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bchkRefsQInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBchkRefsQProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkRefsQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpBchkInstr bchkRefsQInstr stack

private def dispatchSentinel : Int := 53054

private def runBchkRefsQDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpBchkInstr instr (VM.push (intV dispatchSentinel)) stack

private def bchkRefsQSetGasExact : Int :=
  computeExactGasBudget bchkRefsQInstr

private def bchkRefsQSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bchkRefsQInstr

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

private def mkBuilderWithRefs (refs : Nat) : Builder :=
  { bits := #[]
    refs := mkRefCells refs }

private def oracleNoiseSliceA : Slice :=
  mkSliceFromBits (natToBits 0x15 5)

private def oracleNoiseSliceB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 2 2) #[Cell.empty])

private def mkBuilderProgramRefs (builderRefs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder builderRefs

private def mkBchkRefsQProgram (builderRefs needRefs : Nat) : Array Instr :=
  mkBuilderProgramRefs builderRefs
    ++ #[.pushInt (.num (Int.ofNat needRefs)), bchkRefsQInstr]

private def bchkProgramRefsNan : Array Instr :=
  #[.newc, .pushInt .nan, bchkRefsQInstr]

private def needRefsPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def builderRefsPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def pickFromNatPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNeedRefsWithin (rng : StdGen) (builderRefs : Nat) : Nat × StdGen :=
  let refsCap : Nat := 4 - builderRefs
  if refsCap = 0 then
    (0, rng)
  else
    let (mode, rng1) := randNat rng 0 4
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (refsCap, rng1)
    else if mode = 2 then
      (refsCap - 1, rng1)
    else if mode = 3 then
      (Nat.min 1 refsCap, rng1)
    else
      randNat rng1 0 refsCap

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

private def genBchkRefsQFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    let (needRefs, rng2) := pickFromNatPool rng1 needRefsPool
    (mkBchkRefsQCase s!"fuzz/ok/direct/empty/r{needRefs}"
      #[.builder Builder.empty, intV (Int.ofNat needRefs)], rng2)
  else if shape = 1 then
    let (needRefs, rng2) := pickFromNatPool rng1 needRefsPool
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkRefsQCase s!"fuzz/ok/direct/noise/r{needRefs}"
      #[noise, .builder Builder.empty, intV (Int.ofNat needRefs)], rng3)
  else if shape = 2 then
    let (needRefs, rng2) := randNat rng1 5 7
    (mkBchkRefsQCase s!"fuzz/fail/direct/empty/r{needRefs}"
      #[.builder Builder.empty, intV (Int.ofNat needRefs)], rng2)
  else if shape = 3 then
    let (needRefs, rng2) := randNat rng1 5 7
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkRefsQCase s!"fuzz/fail/direct/noise/r{needRefs}"
      #[noise, .builder Builder.empty, intV (Int.ofNat needRefs)], rng3)
  else if shape = 4 then
    (mkBchkRefsQCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkBchkRefsQCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkBchkRefsQCase "fuzz/type/refs-top-not-int" #[.builder Builder.empty, .null], rng1)
  else if shape = 7 then
    (mkBchkRefsQCase "fuzz/range/refs-negative" #[.builder Builder.empty, intV (-1)], rng1)
  else if shape = 8 then
    (mkBchkRefsQCase "fuzz/range/refs-gt7" #[.builder Builder.empty, intV 8], rng1)
  else if shape = 9 then
    (mkBchkRefsQCase "fuzz/type/builder-not-builder" #[.null, intV 0], rng1)
  else if shape = 10 then
    (mkBchkRefsQCase "fuzz/order/refs-range-before-builder-type" #[.null, intV 8], rng1)
  else if shape = 11 then
    let (builderRefs, rng2) := pickFromNatPool rng1 builderRefsPool
    let (needRefs, rng3) := pickNeedRefsWithin rng2 builderRefs
    let (withNoise, rng4) := randNat rng3 0 1
    let initStack : Array Value :=
      if withNoise = 0 then #[] else #[.slice oracleNoiseSliceA]
    (mkBchkRefsQProgramCase
      s!"fuzz/ok/program/br{builderRefs}/nr{needRefs}"
      initStack
      (mkBchkRefsQProgram builderRefs needRefs), rng4)
  else if shape = 12 then
    let (builderRefs, rng2) := pickFromNatPool rng1 builderRefsPool
    let (needRefs, rng3) := pickNeedRefsOverflow rng2 builderRefs
    let (noise, rng4) := pickNoiseValue rng3
    (mkBchkRefsQProgramCase
      s!"fuzz/fail/program/br{builderRefs}/nr{needRefs}"
      #[noise]
      (mkBchkRefsQProgram builderRefs needRefs), rng4)
  else if shape = 13 then
    (mkBchkRefsQProgramCase "fuzz/range/program-refs-nan" #[] bchkProgramRefsNan, rng1)
  else if shape = 14 then
    let (needRefs, rng2) := pickFromNatPool rng1 needRefsPool
    (mkBchkRefsQCase "fuzz/gas/exact"
      #[.builder Builder.empty, intV (Int.ofNat needRefs)]
      #[.pushInt (.num bchkRefsQSetGasExact), .tonEnvOp .setGasLimit, bchkRefsQInstr], rng2)
  else
    let (needRefs, rng2) := pickFromNatPool rng1 needRefsPool
    (mkBchkRefsQCase "fuzz/gas/exact-minus-one"
      #[.builder Builder.empty, intV (Int.ofNat needRefs)]
      #[.pushInt (.num bchkRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkRefsQInstr], rng2)

def suite : InstrSuite where
  id := { name := "BCHKREFSQ" }
  unit := #[
    { name := "unit/direct/success-status-and-stack-shape"
      run := do
        expectOkStack "ok/empty-plus-0"
          (runBchkRefsQDirect #[.builder Builder.empty, intV 0])
          #[intV (-1)]
        expectOkStack "ok/empty-plus-4"
          (runBchkRefsQDirect #[.builder Builder.empty, intV 4])
          #[intV (-1)]
        expectOkStack "ok/non-empty-builder-exact-fit"
          (runBchkRefsQDirect #[.builder (mkBuilderWithRefs 3), intV 1])
          #[intV (-1)]
        expectOkStack "ok/full-ref-builder-plus-0"
          (runBchkRefsQDirect #[.builder (mkBuilderWithRefs 4), intV 0])
          #[intV (-1)]
        expectOkStack "ok/deep-stack-preserve-below"
          (runBchkRefsQDirect
            #[.slice oracleNoiseSliceA, intV 99, .builder (mkBuilderWithRefs 2), intV 2])
          #[.slice oracleNoiseSliceA, intV 99, intV (-1)] }
    ,
    { name := "unit/direct/quiet-overflow-returns-zero"
      run := do
        expectOkStack "fail/empty-plus-5"
          (runBchkRefsQDirect #[.builder Builder.empty, intV 5])
          #[intV 0]
        expectOkStack "fail/non-empty-plus-2"
          (runBchkRefsQDirect #[.builder (mkBuilderWithRefs 3), intV 2])
          #[intV 0]
        expectOkStack "fail/full-plus-1-with-noise"
          (runBchkRefsQDirect #[.slice oracleNoiseSliceB, .builder (mkBuilderWithRefs 4), intV 1])
          #[.slice oracleNoiseSliceB, intV 0]
        expectOkStack "fail/empty-plus-7"
          (runBchkRefsQDirect #[.builder Builder.empty, intV 7])
          #[intV 0] }
    ,
    { name := "unit/direct/underflow-range-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runBchkRefsQDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runBchkRefsQDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/refs-top-not-int"
          (runBchkRefsQDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "range/refs-negative"
          (runBchkRefsQDirect #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/refs-gt7"
          (runBchkRefsQDirect #[.builder Builder.empty, intV 8]) .rangeChk
        expectErr "range/refs-nan"
          (runBchkRefsQDirect #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "type/builder-not-builder-after-valid-refs"
          (runBchkRefsQDirect #[.null, intV 0]) .typeChk
        expectErr "order/refs-range-before-builder-type"
          (runBchkRefsQDirect #[.null, intV 8]) .rangeChk
        expectErr "order/refs-type-before-builder-type"
          (runBchkRefsQDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-and-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[bchkRefsInstr, bchkRefsQInstr, bchkBitsQInstr, bchkBitRefsQInstr, .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-bchkrefs" s0 bchkRefsInstr 16
        let s2 ← expectDecodeStep "decode/asm-bchkrefsq" s1 bchkRefsQInstr 16
        let s3 ← expectDecodeStep "decode/asm-bchkbitsq" s2 bchkBitsQInstr 16
        let s4 ← expectDecodeStep "decode/asm-bchkbitrefsq" s3 bchkBitRefsQInstr 16
        let s5 ← expectDecodeStep "decode/asm-tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let codeQ ←
          match assembleCp0 [bchkRefsQInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bchkrefsq failed: {e}")
        if codeQ.bits = natToBits bchkRefsQWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/bchkrefsq: expected 0xcf3e, got {codeQ.bits}")

        match assembleCp0 [.cellOp (.bchk false false true)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/bchk-invalid-quiet: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/bchk-invalid-quiet: expected invOpcode, got success")

        match assembleCp0 [.cellOp (.bchk false false false)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/bchk-invalid-nonquiet: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/bchk-invalid-nonquiet: expected invOpcode, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits (bchkBitsImmQWord 1) 24 ++
          natToBits bchkRefsWord 16 ++
          natToBits bchkRefsQWord 16 ++
          natToBits bchkBitsQWord 16 ++
          natToBits bchkBitRefsQWord 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-bchkbitsimmq-1" r0 (bchkBitsImmQInstr 1) 24
        let r2 ← expectDecodeStep "decode/raw-bchkrefs" r1 bchkRefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-bchkrefsq" r2 bchkRefsQInstr 16
        let r4 ← expectDecodeStep "decode/raw-bchkbitsq" r3 bchkBitsQInstr 16
        let r5 ← expectDecodeStep "decode/raw-bchkbitrefsq" r4 bchkBitRefsQInstr 16
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback-vs-target-hit"
      run := do
        expectOkStack "dispatch/non-cell-op-falls-through"
          (runBchkRefsQDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-non-bchk-falls-through"
          (runBchkRefsQDispatchFallback (.cellOp .bdepth) #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/target-hit-no-sentinel"
          (runBchkRefsQDispatchFallback bchkRefsQInstr
            #[.slice oracleNoiseSliceB, .builder Builder.empty, intV 4])
          #[.slice oracleNoiseSliceB, intV (-1)]
        expectErr "dispatch/target-hit-error-no-sentinel"
          (runBchkRefsQDispatchFallback bchkRefsQInstr #[.null, intV 0])
          .typeChk }
  ]
  oracle := #[
    mkBchkRefsQCase "ok/direct/empty-r0"
      #[.builder Builder.empty, intV 0],
    mkBchkRefsQCase "ok/direct/empty-r1"
      #[.builder Builder.empty, intV 1],
    mkBchkRefsQCase "ok/direct/empty-r4"
      #[.builder Builder.empty, intV 4],
    mkBchkRefsQCase "ok/direct/deep-noise-slice-r2"
      #[.slice oracleNoiseSliceA, .builder Builder.empty, intV 2],
    mkBchkRefsQCase "ok/direct/deep-noise-cell-r3"
      #[.cell refCellB, .builder Builder.empty, intV 3],
    mkBchkRefsQCase "ok/direct/deep-noise-int-r4"
      #[intV 42, .builder Builder.empty, intV 4],

    mkBchkRefsQCase "fail/direct/empty-r5"
      #[.builder Builder.empty, intV 5],
    mkBchkRefsQCase "fail/direct/empty-r6"
      #[.builder Builder.empty, intV 6],
    mkBchkRefsQCase "fail/direct/empty-r7"
      #[.builder Builder.empty, intV 7],
    mkBchkRefsQCase "fail/direct/deep-noise-slice-r7"
      #[.slice oracleNoiseSliceB, .builder Builder.empty, intV 7],

    mkBchkRefsQCase "underflow/empty" #[],
    mkBchkRefsQCase "underflow/one-item"
      #[.builder Builder.empty],

    mkBchkRefsQCase "type/refs-top-not-int"
      #[.builder Builder.empty, .null],
    mkBchkRefsQCase "range/refs-negative"
      #[.builder Builder.empty, intV (-1)],
    mkBchkRefsQCase "range/refs-gt7"
      #[.builder Builder.empty, intV 8],
    mkBchkRefsQCase "type/builder-not-builder"
      #[.null, intV 0],
    mkBchkRefsQCase "order/refs-range-before-builder-type"
      #[.null, intV 8],
    mkBchkRefsQCase "order/refs-type-before-builder-type"
      #[.null, .null],
    mkBchkRefsQProgramCase "range/refs-nan-via-program" #[] bchkProgramRefsNan,

    mkBchkRefsQCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty, intV 0]
      #[.pushInt (.num bchkRefsQSetGasExact), .tonEnvOp .setGasLimit, bchkRefsQInstr],
    mkBchkRefsQCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, intV 0]
      #[.pushInt (.num bchkRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkRefsQInstr],

    mkBchkRefsQProgramCase "ok/program/brefs1-need3" #[]
      (mkBchkRefsQProgram 1 3),
    mkBchkRefsQProgramCase "ok/program/brefs2-need2-noise-slice"
      #[.slice oracleNoiseSliceA]
      (mkBchkRefsQProgram 2 2),
    mkBchkRefsQProgramCase "ok/program/brefs3-need1" #[]
      (mkBchkRefsQProgram 3 1),
    mkBchkRefsQProgramCase "ok/program/brefs4-need0-noise-cell"
      #[.cell Cell.empty]
      (mkBchkRefsQProgram 4 0),
    mkBchkRefsQProgramCase "ok/program/brefs0-need4" #[]
      (mkBchkRefsQProgram 0 4),

    mkBchkRefsQProgramCase "fail/program/brefs4-need1" #[]
      (mkBchkRefsQProgram 4 1),
    mkBchkRefsQProgramCase "fail/program/brefs3-need2" #[]
      (mkBchkRefsQProgram 3 2),
    mkBchkRefsQProgramCase "fail/program/brefs2-need3-noise-int"
      #[intV 7]
      (mkBchkRefsQProgram 2 3),
    mkBchkRefsQProgramCase "fail/program/brefs0-need7" #[]
      (mkBchkRefsQProgram 0 7)
  ]
  fuzz := #[
    { seed := 2026021042
      count := 500
      gen := genBchkRefsQFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKREFSQ
