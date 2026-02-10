import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKBITSQ

/-
BCHKBITSQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/BchkBitsImm.lean` (`.bchkBitsImm bits quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`BCHKBITSQ <bits>` encode: `0xcf3c` + 8-bit `(bits-1)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf3cxx` decode to `.bchkBitsImm bits true`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_chk_bits`, quiet mode, opcode family `0xcf3cxx`).

Branch map used for this suite:
- dispatch guard: only `.cellOp (.bchkBitsImm _ true)` executes in this handler, others must call `next`;
- stack gate: `checkUnderflow 1` then `popBuilder` type check for top stack item;
- quiet behavior: always pushes status (`-1` when extendable, `0` on overflow), never throws `.cellOv`;
- non-quiet contrast: identical checks, but overflow path throws `.cellOv`;
- opcode/decode boundaries: immediate forms are 24-bit (`0xcf38xx` non-quiet, `0xcf3cxx` quiet).
-/

private def bchkBitsQId : InstrId := { name := "BCHKBITSQ" }

private def dispatchSentinel : Int := 53845

private def bchkBitsQInstr (bits : Nat) : Instr :=
  .cellOp (.bchkBitsImm bits true)

private def bchkBitsInstr (bits : Nat) : Instr :=
  .cellOp (.bchkBitsImm bits false)

private def bchkBitsVarQInstr : Instr :=
  .cellOp (.bchk true false true)

private def bchkBitsVarInstr : Instr :=
  .cellOp (.bchk true false false)

private def bchkBitRefsInstr : Instr :=
  .cellOp (.bchk true true false)

private def execInstrCellOpBchkBitsImmOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchkBitsImm op next
  | _ => next

private def execInstrCellOpBchkVarOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def mkBchkBitsQCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[bchkBitsQInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBchkBitsQProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkBitsQDirect (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkBitsImmOnly (bchkBitsQInstr bits) stack

private def runBchkBitsDirect (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkBitsImmOnly (bchkBitsInstr bits) stack

private def runBchkBitsVarQAligned (bits : Nat) (immStack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkVarOnly bchkBitsVarQInstr
    (immStack.push (intV (Int.ofNat bits)))

private def runBchkBitsQDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBchkBitsImmOnly instr
    (VM.push (intV dispatchSentinel)) stack

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

private def bchkBitsImmWord (bits : Nat) (quiet : Bool := false) : Nat :=
  ((if quiet then 0xcf3c else 0xcf38) <<< 8) + (bits - 1)

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkFullSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[]

private def fullSliceA : Slice :=
  mkFullSlice (natToBits 37 6) #[refLeafA]

private def fullSliceB : Slice :=
  mkFullSlice (natToBits 149 8) #[refLeafA, refLeafB]

private def builder767 : Builder :=
  { bits := Array.replicate 767 false, refs := #[] }

private def builder768 : Builder :=
  { bits := Array.replicate 768 false, refs := #[] }

private def builder900 : Builder :=
  { bits := Array.replicate 900 false, refs := #[] }

private def builder767Refs4 : Builder :=
  { bits := Array.replicate 767 false
    refs := #[refLeafA, refLeafB, refLeafC, Cell.empty] }

private def appendStuChunk (bits : Nat) : Array Instr :=
  #[.pushInt (.num 0), .xchg0 1, .stu bits]

private def buildBuilderByChunks (chunks : Array Nat) : Array Instr :=
  chunks.foldl (fun (acc : Array Instr) (chunk : Nat) => acc ++ appendStuChunk chunk) #[.newc]

private def appendOneRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

private def mkBchkBitsQProgram (buildProgram : Array Instr) (bits : Nat) : Array Instr :=
  buildProgram ++ #[bchkBitsQInstr bits]

private def build767Program : Array Instr :=
  buildBuilderByChunks #[256, 256, 255]

private def build768Program : Array Instr :=
  buildBuilderByChunks #[256, 256, 256]

private def build900Program : Array Instr :=
  buildBuilderByChunks #[256, 256, 256, 132]

private def build767Refs4Program : Array Instr :=
  build767Program ++ appendRefsToTopBuilder 4

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def successBuild767Bits256Program : Array Instr :=
  mkBchkBitsQProgram build767Program 256

private def successBuild767Refs4Bits256Program : Array Instr :=
  mkBchkBitsQProgram build767Refs4Program 256

private def successBuild768Bits255Program : Array Instr :=
  mkBchkBitsQProgram build768Program 255

private def successBuild900Bits123Program : Array Instr :=
  mkBchkBitsQProgram build900Program 123

private def failBuild768Bits256Program : Array Instr :=
  mkBchkBitsQProgram build768Program 256

private def failBuild900Bits124Program : Array Instr :=
  mkBchkBitsQProgram build900Program 124

private def failBuild900Bits255Program : Array Instr :=
  mkBchkBitsQProgram build900Program 255

private def failBuild1023Bits1Program : Array Instr :=
  mkBchkBitsQProgram build1023Program 1

private def failBuild1023Bits256Program : Array Instr :=
  mkBchkBitsQProgram build1023Program 256

private def bchkBitsQGasProbeBits : Nat := 8

private def bchkBitsQSetGasExact : Int :=
  computeExactGasBudget (bchkBitsQInstr bchkBitsQGasProbeBits)

private def bchkBitsQSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (bchkBitsQInstr bchkBitsQGasProbeBits)

private def bchkBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickBchkBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (bchkBitsBoundaryPool.size - 1)
  (bchkBitsBoundaryPool[idx]!, rng')

private def pickBchkBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickBchkBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    (intV 41, rng1)
  else if pick = 2 then
    (.cell refLeafA, rng1)
  else
    (.slice fullSliceA, rng1)

private def genBchkBitsQFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    (mkBchkBitsQCase s!"fuzz/ok/empty/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 1 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    let (noise, rng3) := pickNoise rng2
    (mkBchkBitsQCase s!"fuzz/ok/deep-one/bits-{bits}" bits #[noise, .builder Builder.empty], rng3)
  else if shape = 2 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    (mkBchkBitsQProgramCase s!"fuzz/fail/program-b1023/bits-{bits}" #[]
      (mkBchkBitsQProgram build1023Program bits), rng2)
  else if shape = 3 then
    (mkBchkBitsQProgramCase "fuzz/fail/program-b768/bits-256" #[] failBuild768Bits256Program, rng1)
  else if shape = 4 then
    (mkBchkBitsQCase "fuzz/underflow/empty" 8 #[], rng1)
  else if shape = 5 then
    (mkBchkBitsQCase "fuzz/type/top-null" 8 #[.null], rng1)
  else if shape = 6 then
    let (n, rng2) := randNat rng1 0 120
    (mkBchkBitsQCase s!"fuzz/type/top-int-{n}" 8 #[intV (Int.ofNat n)], rng2)
  else if shape = 7 then
    (mkBchkBitsQCase "fuzz/type/top-cell" 8 #[.cell refLeafB], rng1)
  else if shape = 8 then
    (mkBchkBitsQCase "fuzz/type/top-slice" 8 #[.slice fullSliceB], rng1)
  else if shape = 9 then
    (mkBchkBitsQCase "fuzz/type/order-top-null-over-builder" 8 #[.builder Builder.empty, .null], rng1)
  else if shape = 10 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    (mkBchkBitsQProgramCase s!"fuzz/ok/program-b767/bits-{bits}" #[]
      (mkBchkBitsQProgram build767Program bits), rng2)
  else if shape = 11 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    (mkBchkBitsQProgramCase s!"fuzz/fail/program-b1023/bits-{bits}" #[]
      (mkBchkBitsQProgram build1023Program bits), rng2)
  else if shape = 12 then
    (mkBchkBitsQCase "fuzz/gas/exact" bchkBitsQGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsQSetGasExact), .tonEnvOp .setGasLimit, bchkBitsQInstr bchkBitsQGasProbeBits],
      rng1)
  else if shape = 13 then
    (mkBchkBitsQCase "fuzz/gas/exact-minus-one" bchkBitsQGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsQInstr bchkBitsQGasProbeBits],
      rng1)
  else
    let (cellov, rng2) := randBool rng1
    if cellov then
      (mkBchkBitsQProgramCase "fuzz/fail/program-b900/bits-124" #[] failBuild900Bits124Program, rng2)
    else
      (mkBchkBitsQProgramCase "fuzz/ok/program-b900/bits-123" #[] successBuild900Bits123Program, rng2)

def suite : InstrSuite where
  id := { name := "BCHKBITSQ" }
  unit := #[
    { name := "unit/direct/success-status-and-stack-shape"
      run := do
        let emptyChecks : Array Nat := #[1, 2, 8, 64, 255, 256]
        for bits in emptyChecks do
          expectOkStack s!"ok/empty-builder/bits-{bits}"
            (runBchkBitsQDirect bits #[.builder Builder.empty])
            #[intV (-1)]

        expectOkStack "ok/deep-stack-preserve-below-full-slice"
          (runBchkBitsQDirect 8 #[.null, .slice fullSliceA, .builder Builder.empty])
          #[.null, .slice fullSliceA, intV (-1)]

        expectOkStack "ok/deep-stack-preserve-two-below"
          (runBchkBitsQDirect 64 #[.cell refLeafB, intV 7, .builder Builder.empty])
          #[.cell refLeafB, intV 7, intV (-1)]

        expectOkStack "ok/b767-plus-256"
          (runBchkBitsQDirect 256 #[.builder builder767]) #[intV (-1)]
        expectOkStack "ok/b768-plus-255"
          (runBchkBitsQDirect 255 #[.builder builder768]) #[intV (-1)]
        expectOkStack "ok/b900-plus-123"
          (runBchkBitsQDirect 123 #[.builder builder900]) #[intV (-1)]
        expectOkStack "ok/b767-refs4-plus-256"
          (runBchkBitsQDirect 256 #[.builder builder767Refs4]) #[intV (-1)] }
    ,
    { name := "unit/direct/quiet-overflow-returns-zero"
      run := do
        expectOkStack "fail/full-1023-plus-1"
          (runBchkBitsQDirect 1 #[.builder fullBuilder1023]) #[intV 0]
        expectOkStack "fail/full-1023-plus-256"
          (runBchkBitsQDirect 256 #[.builder fullBuilder1023]) #[intV 0]
        expectOkStack "fail/b768-plus-256"
          (runBchkBitsQDirect 256 #[.builder builder768]) #[intV 0]
        expectOkStack "fail/b900-plus-124"
          (runBchkBitsQDirect 124 #[.builder builder900]) #[intV 0]
        expectOkStack "fail/b900-plus-255"
          (runBchkBitsQDirect 255 #[.builder builder900]) #[intV 0]
        expectOkStack "fail/deep-noise-slice-preserved"
          (runBchkBitsQDirect 256 #[.slice fullSliceB, .builder builder768])
          #[.slice fullSliceB, intV 0] }
    ,
    { name := "unit/direct/underflow-type-and-order"
      run := do
        expectErr "underflow/empty"
          (runBchkBitsQDirect 8 #[]) .stkUnd

        expectErr "type/top-null"
          (runBchkBitsQDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runBchkBitsQDirect 8 #[intV 7]) .typeChk
        expectErr "type/top-cell"
          (runBchkBitsQDirect 8 #[.cell refLeafA]) .typeChk
        expectErr "type/top-full-slice"
          (runBchkBitsQDirect 8 #[.slice fullSliceB]) .typeChk

        expectErr "type/order-top-null-over-full-builder"
          (runBchkBitsQDirect 8 #[.builder fullBuilder1023, .null]) .typeChk
        expectErr "type/order-top-slice-over-full-builder"
          (runBchkBitsQDirect 8 #[.builder fullBuilder1023, .slice fullSliceA]) .typeChk }
    ,
    { name := "unit/direct/contrast-with-nonquiet-bchkbits"
      run := do
        expectOkStack "quiet/success-pushes-minus1"
          (runBchkBitsQDirect 64 #[.builder Builder.empty])
          #[intV (-1)]
        expectOkStack "nonquiet/success-pushes-nothing"
          (runBchkBitsDirect 64 #[.builder Builder.empty])
          #[]

        expectOkStack "quiet/failure-pushes-zero"
          (runBchkBitsQDirect 1 #[.builder fullBuilder1023])
          #[intV 0]
        expectErr "nonquiet/failure-throws-cellov"
          (runBchkBitsDirect 1 #[.builder fullBuilder1023]) .cellOv

        expectOkStack "quiet/deep-stack-preserves-below"
          (runBchkBitsQDirect 8 #[intV 33, .builder Builder.empty])
          #[intV 33, intV (-1)]
        expectOkStack "nonquiet/deep-stack-preserves-below"
          (runBchkBitsDirect 8 #[intV 33, .builder Builder.empty])
          #[intV 33] }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr :=
          #[.cellOp .brembitrefs, bchkBitsInstr 1, bchkBitsQInstr 1, bchkBitsInstr 256,
            bchkBitsQInstr 256, bchkBitsVarInstr, bchkBitsVarQInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")

        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/brembitrefs-neighbor" s0 (.cellOp .brembitrefs) 16
        let s2 ← expectDecodeStep "decode/bchkbits-imm-1" s1 (bchkBitsInstr 1) 24
        let s3 ← expectDecodeStep "decode/bchkbitsq-imm-1" s2 (bchkBitsQInstr 1) 24
        let s4 ← expectDecodeStep "decode/bchkbits-imm-256" s3 (bchkBitsInstr 256) 24
        let s5 ← expectDecodeStep "decode/bchkbitsq-imm-256" s4 (bchkBitsQInstr 256) 24
        let s6 ← expectDecodeStep "decode/bchkbits-var-neighbor" s5 bchkBitsVarInstr 16
        let s7 ← expectDecodeStep "decode/bchkbitsq-var-neighbor" s6 bchkBitsVarQInstr 16
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let asmQ8 ←
          match assembleCp0 [bchkBitsQInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bitsq-8 failed: {e}")
        if asmQ8.bits = natToBits (bchkBitsImmWord 8 true) 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bitsq-8: expected opcode word {bchkBitsImmWord 8 true}, got bits {asmQ8.bits}")
        if asmQ8.bits.size = 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bitsq-8: expected 24 bits, got {asmQ8.bits.size}")

        match assembleCp0 [bchkBitsQInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bitsq-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bitsq-0: expected rangeChk, got success")

        match assembleCp0 [bchkBitsQInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bitsq-257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bitsq-257: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xcf3b 16
            ++ natToBits (bchkBitsImmWord 256 true) 24
            ++ natToBits 0xcf39 16
            ++ natToBits 0xcf3d 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-bchkbitrefs" r0 bchkBitRefsInstr 16
        let r2 ← expectDecodeStep "decode/raw-bchkbitsq-imm-256" r1 (bchkBitsQInstr 256) 24
        let r3 ← expectDecodeStep "decode/raw-bchkbits-var" r2 bchkBitsVarInstr 16
        let r4 ← expectDecodeStep "decode/raw-bchkbitsq-var" r3 bchkBitsVarQInstr 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/alias-equivalence/immq-vs-varq-bchkbits"
      run := do
        let successChecks : Array (Nat × Builder) :=
          #[
            (1, Builder.empty),
            (8, Builder.empty),
            (64, Builder.empty),
            (255, builder768),
            (256, builder767),
            (123, builder900)
          ]
        for (bits, b) in successChecks do
          expectSameOutcome s!"align/success/bits-{bits}/bits-used-{b.bits.size}"
            (runBchkBitsQDirect bits #[.builder b])
            (runBchkBitsVarQAligned bits #[.builder b])

        let failChecks : Array (Nat × Builder) :=
          #[
            (1, fullBuilder1023),
            (256, builder768),
            (124, builder900)
          ]
        for (bits, b) in failChecks do
          expectSameOutcome s!"align/fail/bits-{bits}/bits-used-{b.bits.size}"
            (runBchkBitsQDirect bits #[.builder b])
            (runBchkBitsVarQAligned bits #[.builder b])

        expectSameOutcome "align/underflow-empty"
          (runBchkBitsQDirect 8 #[])
          (runBchkBitsVarQAligned 8 #[])
        expectSameOutcome "align/type-top-null"
          (runBchkBitsQDirect 8 #[.null])
          (runBchkBitsVarQAligned 8 #[.null])
        expectSameOutcome "align/type-top-full-slice"
          (runBchkBitsQDirect 8 #[.slice fullSliceA])
          (runBchkBitsVarQAligned 8 #[.slice fullSliceA])
        expectSameOutcome "align/deep-stack-preserve-full-slice"
          (runBchkBitsQDirect 8 #[.slice fullSliceB, .builder Builder.empty])
          (runBchkBitsVarQAligned 8 #[.slice fullSliceB, .builder Builder.empty]) }
    ,
    { name := "unit/dispatch/non-bchkbitsqimm-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runBchkBitsQDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/bchk-var-neighbor"
          (runBchkBitsQDispatchFallback bchkBitsVarQInstr #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-neighbor"
          (runBchkBitsQDispatchFallback (.cellOp .brefs) #[.slice fullSliceA])
          #[.slice fullSliceA, intV dispatchSentinel]
        expectOkStack "dispatch/target-hit-no-sentinel"
          (runBchkBitsQDispatchFallback (bchkBitsQInstr 8) #[.builder Builder.empty])
          #[intV (-1)]
        expectErr "dispatch/target-hit-error-no-sentinel"
          (runBchkBitsQDispatchFallback (bchkBitsQInstr 8) #[.null])
          .typeChk }
  ]
  oracle := #[
    mkBchkBitsQCase "ok/empty-builder/bits-1" 1 #[.builder Builder.empty],
    mkBchkBitsQCase "ok/empty-builder/bits-2" 2 #[.builder Builder.empty],
    mkBchkBitsQCase "ok/empty-builder/bits-8" 8 #[.builder Builder.empty],
    mkBchkBitsQCase "ok/empty-builder/bits-64" 64 #[.builder Builder.empty],
    mkBchkBitsQCase "ok/empty-builder/bits-255" 255 #[.builder Builder.empty],
    mkBchkBitsQCase "ok/empty-builder/bits-256" 256 #[.builder Builder.empty],
    mkBchkBitsQCase "ok/deep-stack-null-below" 8 #[.null, .builder Builder.empty],
    mkBchkBitsQCase "ok/deep-stack-full-slice-below" 8 #[.slice fullSliceA, .builder Builder.empty],
    mkBchkBitsQCase "ok/deep-stack-two-below" 8 #[.cell refLeafA, .slice fullSliceB, .builder Builder.empty],
    mkBchkBitsQProgramCase "ok/program-build767refs4-check256" #[] successBuild767Refs4Bits256Program,

    mkBchkBitsQProgramCase "fail/program-build1023-check1" #[] failBuild1023Bits1Program,
    mkBchkBitsQProgramCase "fail/program-build1023-check256" #[] failBuild1023Bits256Program,
    mkBchkBitsQProgramCase "fail/program-build1023-check255" #[]
      (mkBchkBitsQProgram build1023Program 255),
    mkBchkBitsQProgramCase "fail/program-build768-check256" #[] failBuild768Bits256Program,
    mkBchkBitsQProgramCase "fail/program-build900-check124" #[] failBuild900Bits124Program,
    mkBchkBitsQProgramCase "fail/program-build900-check255" #[] failBuild900Bits255Program,
    mkBchkBitsQProgramCase "fail/program-build768-check256-with-slice-noise"
      #[.slice fullSliceB] failBuild768Bits256Program,

    mkBchkBitsQCase "underflow/empty" 8 #[],
    mkBchkBitsQCase "type/top-null" 8 #[.null],
    mkBchkBitsQCase "type/top-int" 8 #[intV 11],
    mkBchkBitsQCase "type/top-cell" 8 #[.cell refLeafB],
    mkBchkBitsQCase "type/top-full-slice" 8 #[.slice fullSliceA],
    mkBchkBitsQCase "type/order-top-null-over-builder" 8 #[.builder Builder.empty, .null],
    mkBchkBitsQCase "type/order-top-slice-over-builder" 8 #[.builder Builder.empty, .slice fullSliceB],

    mkBchkBitsQProgramCase "ok/program-build767-check256" #[] successBuild767Bits256Program,
    mkBchkBitsQProgramCase "ok/program-build768-check255" #[] successBuild768Bits255Program,
    mkBchkBitsQProgramCase "ok/program-build900-check123" #[] successBuild900Bits123Program,
    mkBchkBitsQProgramCase "ok/program-build767-check1-with-slice-noise"
      #[.slice fullSliceA] (mkBchkBitsQProgram build767Program 1),

    mkBchkBitsQCase "gas/exact-cost-succeeds" bchkBitsQGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsQSetGasExact), .tonEnvOp .setGasLimit, bchkBitsQInstr bchkBitsQGasProbeBits],
    mkBchkBitsQCase "gas/exact-minus-one-out-of-gas" bchkBitsQGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsQInstr bchkBitsQGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026021051
      count := 320
      gen := genBchkBitsQFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKBITSQ
