import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKBITSQ_VAR

/-
BCHKBITSQ_VAR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Bchk.lean` (`.bchk true false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.bchk true false true` encode: `0xcf3d`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf3d` decode to `.cellOp (.bchk true false true)`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_chk_bits_refs`, mode `5`, opcode `0xcf3d`).

Branch map used for this suite (`needBits=true`, `needRefs=false`, `quiet=true`):
- underflow check requires exactly 2 stack items;
- pop order is `bits` (top, `0..1023`) then `builder`;
- quiet path always pushes status: `-1` on fit, `0` on overflow;
- opcode boundary with immediate quiet form (`0xcf3cxx`) is covered explicitly.
-/

private def bchkBitsQVarId : InstrId := { name := "BCHKBITSQ_VAR" }

private def bchkBitsQVarInstr : Instr :=
  .cellOp (.bchk true false true)

private def bchkBitsVarInstr : Instr :=
  .cellOp (.bchk true false false)

private def bchkRefsQInstr : Instr :=
  .cellOp (.bchk false true true)

private def bchkBitRefsQInstr : Instr :=
  .cellOp (.bchk true true true)

private def bchkBitsImmQInstr (bits : Nat) : Instr :=
  .cellOp (.bchkBitsImm bits true)

private def bchkBitsQVarWord : Nat := 0xcf3d
private def bchkBitsVarWord : Nat := 0xcf39
private def bchkRefsQWord : Nat := 0xcf3e
private def bchkBitRefsQWord : Nat := 0xcf3f

private def bchkBitsImmQWord (bits : Nat) : Nat :=
  (0xcf3c <<< 8) + (bits - 1)

private def execCellOpBchkInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def mkBchkBitsQVarCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bchkBitsQVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitsQVarId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBchkBitsQVarProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitsQVarId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkBitsQVarDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpBchkInstr bchkBitsQVarInstr stack

private def dispatchSentinel : Int := 53058

private def runBchkBitsQVarDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpBchkInstr instr (VM.push (intV dispatchSentinel)) stack

private def bchkBitsQVarSetGasExact : Int :=
  computeExactGasBudget bchkBitsQVarInstr

private def bchkBitsQVarSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bchkBitsQVarInstr

private def mkBuilderWithBits (bits : Nat) : Builder :=
  { bits := Array.replicate bits false
    refs := #[] }

private def refCellA : Cell :=
  (Builder.empty.storeBits (natToBits 1 1)).finalize

private def refCellB : Cell :=
  (Builder.empty.storeBits (natToBits 5 3)).finalize

private def oracleNoiseSliceA : Slice :=
  mkSliceFromBits (natToBits 0x15 5)

private def oracleNoiseSliceB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 2 2) #[Cell.empty])

private def mkBuilderProgramBits (builderBits : Nat) : Array Instr :=
  #[.newc] ++
    (if builderBits = 0 then #[] else #[.pushInt (.num (Int.ofNat builderBits)), .stZeroes])

private def mkBchkBitsQVarProgram
    (builderBits needBits : Nat) : Array Instr :=
  mkBuilderProgramBits builderBits
    ++ #[.pushInt (.num (Int.ofNat needBits)), bchkBitsQVarInstr]

private def bchkProgramBitsNan : Array Instr :=
  #[.newc, .pushInt .nan, bchkBitsQVarInstr]

private def needBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 256, 511, 767, 1022, 1023]

private def builderBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 767, 900, 1022, 1023]

private def builderBitsNonZeroPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 767, 900, 1022, 1023]

private def pickFromNatPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNeedBitsWithin (rng : StdGen) (builderBits : Nat) : Nat × StdGen :=
  let bitsCap : Nat := 1023 - builderBits
  if bitsCap = 0 then
    (0, rng)
  else
    let (mode, rng1) := randNat rng 0 4
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (bitsCap, rng1)
    else if mode = 2 then
      (bitsCap - 1, rng1)
    else if mode = 3 then
      (Nat.min 1 bitsCap, rng1)
    else
      randNat rng1 0 bitsCap

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

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else if pick = 2 then .cell refCellA
    else if pick = 3 then .slice oracleNoiseSliceA
    else .slice oracleNoiseSliceB
  (v, rng1)

private def genBchkBitsQVarFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
      (mkBchkBitsQVarCase s!"fuzz/ok/direct/empty/b{needBits}"
        #[.builder Builder.empty, intV (Int.ofNat needBits)], rng2)
    else if shape = 1 then
      let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
      let (noise, rng3) := pickNoiseValue rng2
      (mkBchkBitsQVarCase s!"fuzz/ok/direct/noise/b{needBits}"
        #[noise, .builder Builder.empty, intV (Int.ofNat needBits)], rng3)
    else if shape = 2 then
      let (builderBits, rng2) := pickFromNatPool rng1 builderBitsNonZeroPool
      let (needBits, rng3) := pickNeedBitsOverflow rng2 builderBits
      (mkBchkBitsQVarProgramCase
        s!"fuzz/fail/program/bb{builderBits}/nb{needBits}"
        #[]
        (mkBchkBitsQVarProgram builderBits needBits), rng3)
    else if shape = 3 then
      (mkBchkBitsQVarCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 4 then
      (mkBchkBitsQVarCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
    else if shape = 5 then
      (mkBchkBitsQVarCase "fuzz/type/bits-top-not-int" #[.builder Builder.empty, .null], rng1)
    else if shape = 6 then
      (mkBchkBitsQVarCase "fuzz/range/bits-negative" #[.builder Builder.empty, intV (-1)], rng1)
    else if shape = 7 then
      (mkBchkBitsQVarCase "fuzz/range/bits-gt1023" #[.builder Builder.empty, intV 1024], rng1)
    else if shape = 8 then
      (mkBchkBitsQVarCase "fuzz/type/builder-not-builder" #[.null, intV 0], rng1)
    else if shape = 9 then
      (mkBchkBitsQVarCase "fuzz/order/bits-range-before-builder-type" #[.null, intV 1024], rng1)
    else if shape = 10 then
      let (builderBits, rng2) := pickFromNatPool rng1 builderBitsPool
      let (needBits, rng3) := pickNeedBitsWithin rng2 builderBits
      let (withNoise, rng4) := randBool rng3
      let initStack : Array Value := if withNoise then #[.slice oracleNoiseSliceA] else #[]
      (mkBchkBitsQVarProgramCase
        s!"fuzz/ok/program/bb{builderBits}/nb{needBits}"
        initStack
        (mkBchkBitsQVarProgram builderBits needBits), rng4)
    else if shape = 11 then
      (mkBchkBitsQVarProgramCase "fuzz/range/program-bits-nan" #[] bchkProgramBitsNan, rng1)
    else if shape = 12 then
      let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
      (mkBchkBitsQVarCase "fuzz/gas/exact"
        #[.builder Builder.empty, intV (Int.ofNat needBits)]
        #[.pushInt (.num bchkBitsQVarSetGasExact), .tonEnvOp .setGasLimit, bchkBitsQVarInstr], rng2)
    else if shape = 13 then
      let (needBits, rng2) := pickFromNatPool rng1 needBitsPool
      (mkBchkBitsQVarCase "fuzz/gas/exact-minus-one"
        #[.builder Builder.empty, intV (Int.ofNat needBits)]
        #[.pushInt (.num bchkBitsQVarSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsQVarInstr], rng2)
    else if shape = 14 then
      let (builderBits, rng2) := pickFromNatPool rng1 builderBitsNonZeroPool
      let (needBits, rng3) := pickNeedBitsOverflow rng2 builderBits
      let (noise, rng4) := pickNoiseValue rng3
      (mkBchkBitsQVarProgramCase
        s!"fuzz/fail/program-noise/bb{builderBits}/nb{needBits}"
        #[noise]
        (mkBchkBitsQVarProgram builderBits needBits), rng4)
    else
      let (builderBits, rng2) := pickFromNatPool rng1 builderBitsPool
      let (needBits, rng3) := pickNeedBitsWithin rng2 builderBits
      (mkBchkBitsQVarProgramCase
        s!"fuzz/ok/program-clean/bb{builderBits}/nb{needBits}"
        #[]
        (mkBchkBitsQVarProgram builderBits needBits), rng3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := { name := "BCHKBITSQ_VAR" }
  unit := #[
    { name := "unit/direct/success-status-and-stack-shape"
      run := do
        expectOkStack "ok/empty-plus-0"
          (runBchkBitsQVarDirect #[.builder Builder.empty, intV 0])
          #[intV (-1)]
        expectOkStack "ok/empty-plus-1023"
          (runBchkBitsQVarDirect #[.builder Builder.empty, intV 1023])
          #[intV (-1)]
        expectOkStack "ok/non-empty-exact-fit"
          (runBchkBitsQVarDirect #[.builder (mkBuilderWithBits 1022), intV 1])
          #[intV (-1)]
        expectOkStack "ok/full-plus-0"
          (runBchkBitsQVarDirect #[.builder fullBuilder1023, intV 0])
          #[intV (-1)]
        expectOkStack "ok/deep-stack-preserve-below"
          (runBchkBitsQVarDirect
            #[.slice oracleNoiseSliceA, intV 99, .builder (mkBuilderWithBits 900), intV 123])
          #[.slice oracleNoiseSliceA, intV 99, intV (-1)] }
    ,
    { name := "unit/direct/quiet-overflow-returns-zero"
      run := do
        expectOkStack "fail/full-plus-1"
          (runBchkBitsQVarDirect #[.builder fullBuilder1023, intV 1])
          #[intV 0]
        expectOkStack "fail/b900-plus-124"
          (runBchkBitsQVarDirect #[.builder (mkBuilderWithBits 900), intV 124])
          #[intV 0]
        expectOkStack "fail/b1022-plus-2"
          (runBchkBitsQVarDirect #[.builder (mkBuilderWithBits 1022), intV 2])
          #[intV 0]
        expectOkStack "fail/deep-stack-noise-preserved"
          (runBchkBitsQVarDirect
            #[.slice oracleNoiseSliceB, .builder (mkBuilderWithBits 768), intV 256])
          #[.slice oracleNoiseSliceB, intV 0] }
    ,
    { name := "unit/direct/underflow-range-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runBchkBitsQVarDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runBchkBitsQVarDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/bits-top-not-int"
          (runBchkBitsQVarDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "range/bits-negative"
          (runBchkBitsQVarDirect #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/bits-gt1023"
          (runBchkBitsQVarDirect #[.builder Builder.empty, intV 1024]) .rangeChk
        expectErr "range/bits-nan"
          (runBchkBitsQVarDirect #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "type/builder-not-builder-after-valid-bits"
          (runBchkBitsQVarDirect #[.null, intV 0]) .typeChk
        expectErr "order/bits-range-before-builder-type"
          (runBchkBitsQVarDirect #[.null, intV 1024]) .rangeChk
        expectErr "order/bits-type-before-builder-type"
          (runBchkBitsQVarDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-and-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[bchkBitsVarInstr, bchkBitsQVarInstr, bchkRefsQInstr, bchkBitRefsQInstr, bchkBitsImmQInstr 1, .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-bchkbits-var" s0 bchkBitsVarInstr 16
        let s2 ← expectDecodeStep "decode/asm-bchkbitsq-var" s1 bchkBitsQVarInstr 16
        let s3 ← expectDecodeStep "decode/asm-bchkrefsq" s2 bchkRefsQInstr 16
        let s4 ← expectDecodeStep "decode/asm-bchkbitrefsq" s3 bchkBitRefsQInstr 16
        let s5 ← expectDecodeStep "decode/asm-bchkbitsq-imm-1" s4 (bchkBitsImmQInstr 1) 24
        let s6 ← expectDecodeStep "decode/asm-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let codeQ ←
          match assembleCp0 [bchkBitsQVarInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bchkbitsq-var failed: {e}")
        if codeQ.bits = natToBits bchkBitsQVarWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/bchkbitsq-var: expected 0xcf3d, got {codeQ.bits}")

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
          natToBits (bchkBitsImmQWord 256) 24 ++
          natToBits bchkBitsQVarWord 16 ++
          natToBits bchkBitsVarWord 16 ++
          natToBits bchkRefsQWord 16 ++
          natToBits bchkBitRefsQWord 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-bchkbitsq-imm-256" r0 (bchkBitsImmQInstr 256) 24
        let r2 ← expectDecodeStep "decode/raw-bchkbitsq-var" r1 bchkBitsQVarInstr 16
        let r3 ← expectDecodeStep "decode/raw-bchkbits-var" r2 bchkBitsVarInstr 16
        let r4 ← expectDecodeStep "decode/raw-bchkrefsq" r3 bchkRefsQInstr 16
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
          (runBchkBitsQVarDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-non-bchk-falls-through"
          (runBchkBitsQVarDispatchFallback (.cellOp .bdepth) #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/target-hit-no-sentinel"
          (runBchkBitsQVarDispatchFallback bchkBitsQVarInstr
            #[.slice oracleNoiseSliceB, .builder Builder.empty, intV 1023])
          #[.slice oracleNoiseSliceB, intV (-1)]
        expectErr "dispatch/target-hit-error-no-sentinel"
          (runBchkBitsQVarDispatchFallback bchkBitsQVarInstr #[.null, intV 0])
          .typeChk }
  ]
  oracle := #[
    mkBchkBitsQVarCase "ok/direct/empty-b0"
      #[.builder Builder.empty, intV 0],
    mkBchkBitsQVarCase "ok/direct/empty-b1"
      #[.builder Builder.empty, intV 1],
    mkBchkBitsQVarCase "ok/direct/empty-b255"
      #[.builder Builder.empty, intV 255],
    mkBchkBitsQVarCase "ok/direct/empty-b1023"
      #[.builder Builder.empty, intV 1023],
    mkBchkBitsQVarCase "ok/direct/deep-noise-slice-b7"
      #[.slice oracleNoiseSliceA, .builder Builder.empty, intV 7],
    mkBchkBitsQVarCase "ok/direct/deep-noise-cell-b511"
      #[.cell refCellB, .builder Builder.empty, intV 511],

    mkBchkBitsQVarCase "underflow/empty" #[],
    mkBchkBitsQVarCase "underflow/one-item"
      #[.builder Builder.empty],

    mkBchkBitsQVarCase "type/bits-top-not-int"
      #[.builder Builder.empty, .null],
    mkBchkBitsQVarCase "range/bits-negative"
      #[.builder Builder.empty, intV (-1)],
    mkBchkBitsQVarCase "range/bits-gt1023"
      #[.builder Builder.empty, intV 1024],
    mkBchkBitsQVarCase "type/builder-not-builder"
      #[.null, intV 0],
    mkBchkBitsQVarCase "order/bits-range-before-builder-type"
      #[.null, intV 1024],
    mkBchkBitsQVarCase "order/bits-type-before-builder-type"
      #[.null, .null],
    mkBchkBitsQVarProgramCase "range/program-bits-nan" #[] bchkProgramBitsNan,

    mkBchkBitsQVarCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty, intV 0]
      #[.pushInt (.num bchkBitsQVarSetGasExact), .tonEnvOp .setGasLimit, bchkBitsQVarInstr],
    mkBchkBitsQVarCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, intV 0]
      #[.pushInt (.num bchkBitsQVarSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsQVarInstr],

    mkBchkBitsQVarProgramCase "ok/program/bits0-need1023" #[]
      (mkBchkBitsQVarProgram 0 1023),
    mkBchkBitsQVarProgramCase "ok/program/bits1-need1022" #[]
      (mkBchkBitsQVarProgram 1 1022),
    mkBchkBitsQVarProgramCase "ok/program/bits767-need256" #[]
      (mkBchkBitsQVarProgram 767 256),
    mkBchkBitsQVarProgramCase "ok/program/bits900-need123-noise-slice"
      #[.slice oracleNoiseSliceA]
      (mkBchkBitsQVarProgram 900 123),
    mkBchkBitsQVarProgramCase "ok/program/bits1023-need0-noise-int"
      #[intV 3]
      (mkBchkBitsQVarProgram 1023 0),

    mkBchkBitsQVarProgramCase "fail/program/bits1023-need1" #[]
      (mkBchkBitsQVarProgram 1023 1),
    mkBchkBitsQVarProgramCase "fail/program/bits900-need124" #[]
      (mkBchkBitsQVarProgram 900 124),
    mkBchkBitsQVarProgramCase "fail/program/bits768-need256-noise-cell"
      #[.cell Cell.empty]
      (mkBchkBitsQVarProgram 768 256)
  ]
  fuzz := #[
    { seed := 2026021061
      count := 500
      gen := genBchkBitsQVarFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKBITSQ_VAR
