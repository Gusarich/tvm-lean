import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKBITS_VAR

/-
BCHKBITS_VAR branch map (Lean + C++):
- Lean: `execCellOpBchk` with mode `.bchk true false false`.
  Path shape: underflow(2) -> pop `bits` (`popNatUpTo 1023`) -> pop `builder`
  -> capacity check `canExtendBy bits` -> success or `cellOv` (non-quiet).
- Asm/decode: opcode `0xcf39` (16-bit), with nearby boundaries:
  `0xcf38xx`/`0xcf3cxx` (`BCHKBITS{Q}` immediate, 24-bit), `0xcf3a`, `0xcf3d`.
- C++ alignment target: `exec_builder_chk_bits_refs` mode=1 (`BCHKBITS` var form).
-/

private def bchkBitsVarId : InstrId := { name := "BCHKBITS_VAR" }

private def bchkBitsVarInstr : Instr := .cellOp (.bchk true false false)
private def bchkBitRefsInstr : Instr := .cellOp (.bchk true true false)
private def bchkRefsInstr : Instr := .cellOp (.bchk false true false)
private def bchkBitsQVarInstr : Instr := .cellOp (.bchk true false true)
private def bchkBitsImmInstr (bits : Nat) : Instr := .cellOp (.bchkBitsImm bits false)
private def bchkBitsImmQInstr (bits : Nat) : Instr := .cellOp (.bchkBitsImm bits true)

private def bchkBitsVarWord : Nat := 0xcf39
private def bchkRefsWord : Nat := 0xcf3a
private def bchkBitsQVarWord : Nat := 0xcf3d
private def bchkBitsImmWord (bits : Nat) (quiet : Bool := false) : Nat :=
  ((if quiet then 0xcf3c else 0xcf38) <<< 8) + (bits - 1)

private def execInstrCellOpBchkOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def execInstrCellOpBchkBitsImmOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchkBitsImm op next
  | _ => next

private def mkBchkBitsVarCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bchkBitsVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitsVarId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkBitsVarDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkOnly bchkBitsVarInstr stack

private def runBchkBitsImmDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkBitsImmOnly (bchkBitsImmInstr bits) stack

private def runBchkBitRefsAlignedDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkOnly bchkBitRefsInstr (stack.push (intV 0))

private def dispatchSentinel : Int := 539

private def runBchkBitsVarDispatchFallback (instr : Instr) (stack : Array Value) :
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

private def mkVarStack (builder : Builder) (bits : Int) (below : Array Value := #[]) : Array Value :=
  below ++ #[.builder builder, intV bits]

private def mkVarStackNat (builder : Builder) (bits : Nat) (below : Array Value := #[]) : Array Value :=
  mkVarStack builder (Int.ofNat bits) below

private def fullSliceNoiseA : Slice := mkFullSlice 9 0
private def fullSliceNoiseB : Slice := mkFullSlice 13 1 #[refLeafA]

private def appendStuChunk (bits : Nat) : Array Instr :=
  #[.pushInt (.num 0), .xchg0 1, .stu bits]

private def buildBuilderByChunks (chunks : Array Nat) : Array Instr :=
  chunks.foldl (fun (acc : Array Instr) (chunk : Nat) => acc ++ appendStuChunk chunk) #[.newc]

private def mkVarProgram (buildProgram : Array Instr) (bits : Nat) : Array Instr :=
  buildProgram ++ #[.pushInt (.num (Int.ofNat bits)), bchkBitsVarInstr]

private def build767Program : Array Instr := buildBuilderByChunks #[256, 256, 255]
private def build768Program : Array Instr := buildBuilderByChunks #[256, 256, 256]
private def build900Program : Array Instr := buildBuilderByChunks #[256, 256, 256, 132]
private def build1022Program : Array Instr := buildBuilderByChunks #[256, 256, 256, 254]
private def build1023Program : Array Instr := build1023WithFixed .stu

private def successBuild767Bits256Program : Array Instr := mkVarProgram build767Program 256
private def successBuild900Bits123Program : Array Instr := mkVarProgram build900Program 123
private def successBuild1022Bits1Program : Array Instr := mkVarProgram build1022Program 1
private def successBuild1023Bits0Program : Array Instr := mkVarProgram build1023Program 0

private def cellovBuild768Bits256Program : Array Instr := mkVarProgram build768Program 256
private def cellovBuild900Bits124Program : Array Instr := mkVarProgram build900Program 124
private def cellovBuild1022Bits2Program : Array Instr := mkVarProgram build1022Program 2
private def cellovBuild1023Bits1Program : Array Instr := mkVarProgram build1023Program 1

private def bchkBitsVarSetGasExact : Int :=
  computeExactGasBudget bchkBitsVarInstr

private def bchkBitsVarSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bchkBitsVarInstr

private def bitsReqBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 767, 768, 900, 1022, 1023]

private def pickFromPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickBitsReqMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickFromPool rng1 bitsReqBoundaryPool
  else
    randNat rng1 0 1023

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 73
    else if pick = 2 then .cell refLeafC
    else if pick = 3 then .slice (mkFullSlice 7 1)
    else .slice (mkFullSlice 5 0 #[refLeafA])
  (noise, rng1)

private def genBchkBitsVarFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (bitsReq, rng2) := pickBitsReqMixed rng1
    (mkBchkBitsVarCase s!"fuzz/ok/empty/+{bitsReq}"
      (mkVarStackNat Builder.empty bitsReq), rng2)
  else if shape = 1 then
    let (bitsReq, rng2) := pickBitsReqMixed rng1
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkBitsVarCase s!"fuzz/ok/deep1/+{bitsReq}"
      (mkVarStackNat Builder.empty bitsReq #[noise]), rng3)
  else if shape = 2 then
    let (bitsReq, rng2) := pickBitsReqMixed rng1
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkBitsVarCase s!"fuzz/ok/deep2/+{bitsReq}"
      (mkVarStackNat Builder.empty bitsReq #[.slice fullSliceNoiseA, noise]), rng3)
  else if shape = 3 then
    (mkBchkBitsVarCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 4 then
    (mkBchkBitsVarCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkBchkBitsVarCase "fuzz/type/bits-top-null" #[.builder Builder.empty, .null], rng1)
  else if shape = 6 then
    (mkBchkBitsVarCase "fuzz/type/bits-top-cell" #[.builder Builder.empty, .cell refLeafA], rng1)
  else if shape = 7 then
    (mkBchkBitsVarCase "fuzz/range/bits-negative" #[.builder Builder.empty, intV (-1)], rng1)
  else if shape = 8 then
    (mkBchkBitsVarCase "fuzz/range/bits-over-1023" #[.builder Builder.empty, intV 1024], rng1)
  else if shape = 9 then
    (mkBchkBitsVarCase "fuzz/range/bits-nan-via-program"
      #[.builder Builder.empty] #[.pushInt .nan, bchkBitsVarInstr], rng1)
  else if shape = 10 then
    (mkBchkBitsVarCase "fuzz/type/builder-not-builder" #[.null, intV 0], rng1)
  else if shape = 11 then
    (mkBchkBitsVarCase "fuzz/order/bits-range-before-builder-type" #[.null, intV 1024], rng1)
  else if shape = 12 then
    let (bitsReq, rng2) := pickBitsReqMixed rng1
    (mkBchkBitsVarCase s!"fuzz/align-bitrefs/refs0/+{bitsReq}"
      (mkVarStackNat Builder.empty bitsReq), rng2)
  else if shape = 13 then
    let (bitsReq, rng2) := randNat rng1 0 256
    let (withNoise, rng3) := randNat rng2 0 1
    let initStack : Array Value := if withNoise = 0 then #[] else #[.slice fullSliceNoiseA]
    (mkBchkBitsVarCase s!"fuzz/ok/program-b767/+{bitsReq}"
      initStack (mkVarProgram build767Program bitsReq), rng3)
  else if shape = 14 then
    let (bitsReq, rng2) := randNat rng1 124 400
    let (noise, rng3) := pickNoiseValue rng2
    (mkBchkBitsVarCase s!"fuzz/cellov/program-b900/+{bitsReq}"
      #[noise] (mkVarProgram build900Program bitsReq), rng3)
  else if shape = 15 then
    (mkBchkBitsVarCase "fuzz/cellov/program-b1023/+1"
      #[] cellovBuild1023Bits1Program, rng1)
  else if shape = 16 then
    let (bitsReq, rng2) := pickBitsReqMixed rng1
    (mkBchkBitsVarCase "fuzz/gas/exact"
      (mkVarStackNat Builder.empty bitsReq)
      #[.pushInt (.num bchkBitsVarSetGasExact), .tonEnvOp .setGasLimit, bchkBitsVarInstr], rng2)
  else if shape = 17 then
    let (bitsReq, rng2) := pickBitsReqMixed rng1
    (mkBchkBitsVarCase "fuzz/gas/exact-minus-one"
      (mkVarStackNat Builder.empty bitsReq)
      #[.pushInt (.num bchkBitsVarSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsVarInstr], rng2)
  else
    let (bitsReq, rng2) := pickBitsReqMixed rng1
    (mkBchkBitsVarCase s!"fuzz/fallback/+{bitsReq}"
      (mkVarStackNat Builder.empty bitsReq), rng2)

def suite : InstrSuite where
  id := { name := "BCHKBITS_VAR" }
  unit := #[
    { name := "unit/direct/success-boundaries-and-deep-stack"
      run := do
        expectOkStack "ok/empty-plus-0"
          (runBchkBitsVarDirect (mkVarStackNat Builder.empty 0))
          #[]
        expectOkStack "ok/empty-plus-1"
          (runBchkBitsVarDirect (mkVarStackNat Builder.empty 1))
          #[]
        expectOkStack "ok/empty-plus-256"
          (runBchkBitsVarDirect (mkVarStackNat Builder.empty 256))
          #[]
        expectOkStack "ok/empty-plus-1023"
          (runBchkBitsVarDirect (mkVarStackNat Builder.empty 1023))
          #[]
        expectOkStack "ok/b767-plus-256"
          (runBchkBitsVarDirect (mkVarStackNat (mkBuilderWithCounts 767 0) 256))
          #[]
        expectOkStack "ok/b900-plus-123"
          (runBchkBitsVarDirect (mkVarStackNat (mkBuilderWithCounts 900 0) 123))
          #[]
        expectOkStack "ok/b1022-plus-1"
          (runBchkBitsVarDirect (mkVarStackNat (mkBuilderWithCounts 1022 0) 1))
          #[]
        expectOkStack "ok/deep-stack-preserve-below"
          (runBchkBitsVarDirect
            (mkVarStackNat (mkBuilderWithCounts 700 4) 323 #[.null, intV 91, .slice fullSliceNoiseA]))
          #[.null, intV 91, .slice fullSliceNoiseA] }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty" (runBchkBitsVarDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runBchkBitsVarDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/bits-top-null"
          (runBchkBitsVarDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/bits-top-cell"
          (runBchkBitsVarDirect #[.builder Builder.empty, .cell refLeafA]) .typeChk
        expectErr "range/bits-negative"
          (runBchkBitsVarDirect #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/bits-over-1023"
          (runBchkBitsVarDirect #[.builder Builder.empty, intV 1024]) .rangeChk
        expectErr "range/bits-nan"
          (runBchkBitsVarDirect #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "type/builder-not-builder-after-valid-bits"
          (runBchkBitsVarDirect #[.null, intV 0]) .typeChk

        expectErr "order/bits-range-before-builder-type"
          (runBchkBitsVarDirect #[.null, intV 1024]) .rangeChk
        expectErr "order/bits-type-before-builder-type"
          (runBchkBitsVarDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-boundaries"
      run := do
        expectErr "cellov/b768-plus-256"
          (runBchkBitsVarDirect (mkVarStackNat (mkBuilderWithCounts 768 0) 256))
          .cellOv
        expectErr "cellov/b900-plus-124"
          (runBchkBitsVarDirect (mkVarStackNat (mkBuilderWithCounts 900 0) 124))
          .cellOv
        expectErr "cellov/b1022-plus-2"
          (runBchkBitsVarDirect (mkVarStackNat (mkBuilderWithCounts 1022 0) 2))
          .cellOv
        expectErr "cellov/b1023-plus-1"
          (runBchkBitsVarDirect (mkVarStackNat fullBuilder1023 1))
          .cellOv
        expectErr "cellov/deep-stack-preserve-noise-on-error"
          (runBchkBitsVarDirect
            (mkVarStackNat (mkBuilderWithCounts 1000 4) 24 #[.slice fullSliceNoiseB]))
          .cellOv }
    ,
    { name := "unit/opcode/decode-assembler-and-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[.cellOp .brembitrefs, bchkBitsVarInstr, bchkRefsInstr, bchkBitsQVarInstr,
            bchkBitsImmInstr 256, bchkBitRefsInstr, .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-brembitrefs-neighbor" s0 (.cellOp .brembitrefs) 16
        let s2 ← expectDecodeStep "decode/asm-bchkbits-var" s1 bchkBitsVarInstr 16
        let s3 ← expectDecodeStep "decode/asm-bchkrefs-neighbor" s2 bchkRefsInstr 16
        let s4 ← expectDecodeStep "decode/asm-bchkbitsq-var-neighbor" s3 bchkBitsQVarInstr 16
        let s5 ← expectDecodeStep "decode/asm-bchkbits-imm-256-neighbor" s4 (bchkBitsImmInstr 256) 24
        let s6 ← expectDecodeStep "decode/asm-bchkbitrefs-neighbor" s5 bchkBitRefsInstr 16
        let s7 ← expectDecodeStep "decode/asm-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let codeVar ←
          match assembleCp0 [bchkBitsVarInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bchkbits-var failed: {e}")
        if codeVar.bits = natToBits bchkBitsVarWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/bchkbits-var: expected 0xcf39, got {codeVar.bits}")

        match assembleCp0 [.cellOp (.bchk false false false)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/bchk-invalid: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/bchk-invalid: expected invOpcode, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits (bchkBitsImmWord 1 false) 24 ++
          natToBits bchkBitsVarWord 16 ++
          natToBits bchkRefsWord 16 ++
          natToBits (bchkBitsImmWord 256 true) 24 ++
          natToBits bchkBitsQVarWord 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-bchkbits-imm-1" r0 (bchkBitsImmInstr 1) 24
        let r2 ← expectDecodeStep "decode/raw-bchkbits-var" r1 bchkBitsVarInstr 16
        let r3 ← expectDecodeStep "decode/raw-bchkrefs-neighbor" r2 bchkRefsInstr 16
        let r4 ← expectDecodeStep "decode/raw-bchkbitsq-imm-256-neighbor" r3 (bchkBitsImmQInstr 256) 24
        let r5 ← expectDecodeStep "decode/raw-bchkbitsq-var-neighbor" r4 bchkBitsQVarInstr 16
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/bchk-only-fallback-and-hit"
      run := do
        expectOkStack "dispatch/non-cell-op-falls-through"
          (runBchkBitsVarDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-non-bchk-falls-through"
          (runBchkBitsVarDispatchFallback (.cellOp .bdepth) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-bchkbitsimm-falls-through"
          (runBchkBitsVarDispatchFallback (bchkBitsImmInstr 8) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]

        expectOkStack "dispatch/target-hit-no-sentinel"
          (runBchkBitsVarDispatchFallback bchkBitsVarInstr
            (mkVarStackNat (mkBuilderWithCounts 700 2) 10 #[.slice fullSliceNoiseB]))
          #[.slice fullSliceNoiseB]

        expectErr "dispatch/target-hit-error-no-sentinel"
          (runBchkBitsVarDispatchFallback bchkBitsVarInstr
            (mkVarStackNat (mkBuilderWithCounts 1000 1) 24))
          .cellOv }
    ,
    { name := "unit/alias-equivalence/var-vs-bitrefs-refs0-and-imm"
      run := do
        let alignChecks : Array (Builder × Nat × Array Value) :=
          #[
            (Builder.empty, 0, #[]),
            (Builder.empty, 1, #[]),
            (Builder.empty, 256, #[]),
            (mkBuilderWithCounts 767 0, 256, #[]),
            (mkBuilderWithCounts 900 2, 123, #[.slice fullSliceNoiseA]),
            (mkBuilderWithCounts 1022 4, 1, #[.null]),
            (mkBuilderWithCounts 1023 0, 0, #[])
          ]
        for (b, bitsReq, below) in alignChecks do
          let varStack := mkVarStackNat b bitsReq below
          expectSameOutcome
            s!"align/bitrefs/ok-or-cellov/b{b.bits.size}/r{b.refs.size}/+{bitsReq}"
            (runBchkBitsVarDirect varStack)
            (runBchkBitRefsAlignedDirect varStack)

        let alignErrChecks : Array (Array Value) :=
          #[
            #[],
            #[.builder Builder.empty],
            #[.builder Builder.empty, .null],
            #[.builder Builder.empty, intV (-1)],
            #[.builder Builder.empty, intV 1024],
            #[.null, intV 0],
            #[.null, intV 1024]
          ]
        for st in alignErrChecks do
          expectSameOutcome s!"align/bitrefs/error/{reprStr st}"
            (runBchkBitsVarDirect st)
            (runBchkBitRefsAlignedDirect st)

        let immAlignChecks : Array (Nat × Builder) :=
          #[
            (1, Builder.empty),
            (8, Builder.empty),
            (256, mkBuilderWithCounts 767 1),
            (123, mkBuilderWithCounts 900 4)
          ]
        for (bitsReq, b) in immAlignChecks do
          expectSameOutcome s!"align/imm/bits-{bitsReq}/b{b.bits.size}/r{b.refs.size}"
            (runBchkBitsVarDirect (mkVarStackNat b bitsReq))
            (runBchkBitsImmDirect bitsReq #[.builder b])

        let immErrChecks : Array (Nat × Builder) :=
          #[
            (256, mkBuilderWithCounts 768 0),
            (124, mkBuilderWithCounts 900 3)
          ]
        for (bitsReq, b) in immErrChecks do
          expectSameOutcome s!"align/imm/error/bits-{bitsReq}/b{b.bits.size}"
            (runBchkBitsVarDirect (mkVarStackNat b bitsReq))
            (runBchkBitsImmDirect bitsReq #[.builder b]) }
  ]
  oracle := #[
    mkBchkBitsVarCase "ok/empty/+0"
      (mkVarStackNat Builder.empty 0),
    mkBchkBitsVarCase "ok/empty/+1"
      (mkVarStackNat Builder.empty 1),
    mkBchkBitsVarCase "ok/empty/+2"
      (mkVarStackNat Builder.empty 2),
    mkBchkBitsVarCase "ok/empty/+256"
      (mkVarStackNat Builder.empty 256),
    mkBchkBitsVarCase "ok/empty/+1023"
      (mkVarStackNat Builder.empty 1023),

    mkBchkBitsVarCase "ok/deep/null-noise"
      (mkVarStackNat Builder.empty 32 #[.null]),
    mkBchkBitsVarCase "ok/deep/int-noise"
      (mkVarStackNat Builder.empty 64 #[intV 42]),
    mkBchkBitsVarCase "ok/deep/cell-noise"
      (mkVarStackNat Builder.empty 128 #[.cell refLeafD]),
    mkBchkBitsVarCase "ok/deep/full-slice-noise"
      (mkVarStackNat Builder.empty 255 #[.slice fullSliceNoiseA]),
    mkBchkBitsVarCase "ok/deep/two-noise"
      (mkVarStackNat Builder.empty 0 #[.slice fullSliceNoiseB, .null]),

    mkBchkBitsVarCase "ok/program-build767/+256" #[] successBuild767Bits256Program,
    mkBchkBitsVarCase "ok/program-build900/+123" #[] successBuild900Bits123Program,
    mkBchkBitsVarCase "ok/program-build1022/+1" #[] successBuild1022Bits1Program,
    mkBchkBitsVarCase "ok/program-build1023/+0" #[] successBuild1023Bits0Program,

    mkBchkBitsVarCase "cellov/program-build768/+256" #[] cellovBuild768Bits256Program,
    mkBchkBitsVarCase "cellov/program-build900/+124" #[] cellovBuild900Bits124Program,
    mkBchkBitsVarCase "cellov/program-build1022/+2" #[] cellovBuild1022Bits2Program,
    mkBchkBitsVarCase "cellov/program-build1023/+1" #[] cellovBuild1023Bits1Program,

    mkBchkBitsVarCase "underflow/empty" #[],
    mkBchkBitsVarCase "underflow/one-item"
      #[.builder Builder.empty],
    mkBchkBitsVarCase "type/bits-top-null"
      #[.builder Builder.empty, .null],
    mkBchkBitsVarCase "range/bits-negative"
      #[.builder Builder.empty, intV (-1)],
    mkBchkBitsVarCase "range/bits-over-1023"
      #[.builder Builder.empty, intV 1024],
    mkBchkBitsVarCase "range/bits-nan-via-program"
      #[.builder Builder.empty]
      #[.pushInt .nan, bchkBitsVarInstr],
    mkBchkBitsVarCase "type/builder-not-builder"
      #[.null, intV 0],
    mkBchkBitsVarCase "order/bits-range-before-builder-type"
      #[.null, intV 1024],
    mkBchkBitsVarCase "order/bits-type-before-builder-type"
      #[.null, .null],

    mkBchkBitsVarCase "gas/exact-cost-succeeds"
      (mkVarStackNat Builder.empty 8)
      #[.pushInt (.num bchkBitsVarSetGasExact), .tonEnvOp .setGasLimit, bchkBitsVarInstr],
    mkBchkBitsVarCase "gas/exact-minus-one-out-of-gas"
      (mkVarStackNat Builder.empty 8)
      #[.pushInt (.num bchkBitsVarSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsVarInstr]
  ]
  fuzz := #[
    { seed := 2026021019
      count := 500
      gen := genBchkBitsVarFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKBITS_VAR
