import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BCHKBITS

/-
BCHKBITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/BchkBitsImm.lean` (`.bchkBitsImm bits quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`BCHKBITS <bits>` encode: `0xcf38` + 8-bit `(bits-1)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf38xx` decode to `.bchkBitsImm bits false`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_chk_bits`, non-quiet path; opcode registration `0xcf38`).

Branch map used for this suite:
- Lean BCHKBITS path: dispatch guard, `checkUnderflow 1`, `popBuilder` type check,
  capacity branch (`canExtendBy bits`) to success-or-`cellOv`.
- C++ BCHKBITS path: `check_underflow(1)`, `pop_builder`, `check_space(*builder,bits)`,
  with aligned success and `cell_ov` outcomes.

Harness note:
- Oracle stack tokens cannot serialize non-empty builders directly.
  Non-empty-builder boundary scenarios are therefore modeled via setup programs
  that construct builders before executing `BCHKBITS`.
-/

private def bchkBitsId : InstrId := { name := "BCHKBITS" }

private def dispatchSentinel : Int := 537

private def bchkBitsInstr (bits : Nat) : Instr :=
  .cellOp (.bchkBitsImm bits false)

private def bchkBitsVarInstr : Instr :=
  .cellOp (.bchk true false false)

private def execInstrCellOpBchkBitsImmOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchkBitsImm op next
  | _ => next

private def execInstrCellOpBchkVarOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBchk op next
  | _ => next

private def mkBchkBitsCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[bchkBitsInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBchkBitsProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bchkBitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBchkBitsImmDirect (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkBitsImmOnly (bchkBitsInstr bits) stack

private def runBchkBitsVarAligned (bits : Nat) (immStack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBchkVarOnly bchkBitsVarInstr (immStack.push (intV (Int.ofNat bits)))

private def runBchkBitsImmDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBchkBitsImmOnly instr (VM.push (intV dispatchSentinel)) stack

private def bchkBitsImmWord (bits : Nat) (quiet : Bool := false) : Nat :=
  ((if quiet then 0xcf3c else 0xcf38) <<< 8) + (bits - 1)

private def mkFullSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[]

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

private def mkBchkBitsProgram (buildProgram : Array Instr) (bits : Nat) : Array Instr :=
  buildProgram ++ #[bchkBitsInstr bits]

private def build767Program : Array Instr :=
  buildBuilderByChunks #[256, 256, 255]

private def build768Program : Array Instr :=
  buildBuilderByChunks #[256, 256, 256]

private def build900Program : Array Instr :=
  buildBuilderByChunks #[256, 256, 256, 132]

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def successBuild767Bits256Program : Array Instr :=
  mkBchkBitsProgram build767Program 256

private def successBuild768Bits255Program : Array Instr :=
  mkBchkBitsProgram build768Program 255

private def successBuild900Bits123Program : Array Instr :=
  mkBchkBitsProgram build900Program 123

private def cellovBuild768Bits256Program : Array Instr :=
  mkBchkBitsProgram build768Program 256

private def cellovBuild900Bits124Program : Array Instr :=
  mkBchkBitsProgram build900Program 124

private def cellovBuild1023Bits1Program : Array Instr :=
  mkBchkBitsProgram build1023Program 1

private def cellovBuild1023Bits256Program : Array Instr :=
  mkBchkBitsProgram build1023Program 256

private def bchkBitsGasProbeBits : Nat := 8

private def bchkBitsSetGasExact : Int :=
  computeExactGasBudget (bchkBitsInstr bchkBitsGasProbeBits)

private def bchkBitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (bchkBitsInstr bchkBitsGasProbeBits)

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

private def pickFullSliceNoise (rng0 : StdGen) : Slice × StdGen :=
  let (len, rng1) := randNat rng0 0 24
  let (phase, rng2) := randNat rng1 0 1
  let (refsPick, rng3) := randNat rng2 0 2
  let refs :=
    if refsPick = 0 then #[]
    else if refsPick = 1 then #[refLeafA]
    else #[refLeafA, refLeafB]
  (mkFullSlice (stripeBits len phase) refs, rng3)

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    (intV 73, rng1)
  else if pick = 2 then
    (.cell refLeafC, rng1)
  else if pick = 3 then
    (.slice fullSliceA, rng1)
  else
    let (s, rng2) := pickFullSliceNoise rng1
    (.slice s, rng2)

private def genBchkBitsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    (mkBchkBitsCase s!"fuzz/ok/empty/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 1 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    let (noise, rng3) := pickNoise rng2
    (mkBchkBitsCase s!"fuzz/ok/deep-one/bits-{bits}" bits #[noise, .builder Builder.empty], rng3)
  else if shape = 2 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    let (noise1, rng3) := pickNoise rng2
    let (noise2, rng4) := pickNoise rng3
    (mkBchkBitsCase s!"fuzz/ok/deep-two/bits-{bits}" bits #[noise1, noise2, .builder Builder.empty], rng4)
  else if shape = 3 then
    (mkBchkBitsCase "fuzz/underflow/empty" 8 #[], rng1)
  else if shape = 4 then
    (mkBchkBitsCase "fuzz/type/top-null" 8 #[.null], rng1)
  else if shape = 5 then
    let (n, rng2) := randNat rng1 0 120
    (mkBchkBitsCase s!"fuzz/type/top-int-{n}" 8 #[intV (Int.ofNat n)], rng2)
  else if shape = 6 then
    (mkBchkBitsCase "fuzz/type/top-cell" 8 #[.cell refLeafA], rng1)
  else if shape = 7 then
    let (s, rng2) := pickFullSliceNoise rng1
    (mkBchkBitsCase s!"fuzz/type/top-slice/len-{s.bitsRemaining}/refs-{s.refsRemaining}" 8 #[.slice s], rng2)
  else if shape = 8 then
    (mkBchkBitsCase "fuzz/type/order-top-null-over-builder" 8 #[.builder Builder.empty, .null], rng1)
  else if shape = 9 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    (mkBchkBitsProgramCase s!"fuzz/ok/program-b767/bits-{bits}" #[]
      (mkBchkBitsProgram build767Program bits), rng2)
  else if shape = 10 then
    let (noise, rng2) := pickNoise rng1
    (mkBchkBitsProgramCase "fuzz/ok/program-b768/bits-255/deep"
      #[noise] successBuild768Bits255Program, rng2)
  else if shape = 11 then
    let (noise, rng2) := pickNoise rng1
    (mkBchkBitsProgramCase "fuzz/cellov/program-b768/bits-256/deep"
      #[noise] cellovBuild768Bits256Program, rng2)
  else if shape = 12 then
    let (bits, rng2) := pickBchkBitsMixed rng1
    (mkBchkBitsProgramCase s!"fuzz/cellov/program-b1023/bits-{bits}" #[]
      (mkBchkBitsProgram build1023Program bits), rng2)
  else if shape = 13 then
    (mkBchkBitsCase "fuzz/gas/exact" bchkBitsGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsSetGasExact), .tonEnvOp .setGasLimit, bchkBitsInstr bchkBitsGasProbeBits],
      rng1)
  else if shape = 14 then
    (mkBchkBitsCase "fuzz/gas/exact-minus-one" bchkBitsGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsInstr bchkBitsGasProbeBits],
      rng1)
  else
    let (cellov, rng2) := randBool rng1
    if cellov then
      (mkBchkBitsProgramCase "fuzz/cellov/program-b900/bits-124" #[]
        cellovBuild900Bits124Program, rng2)
    else
      (mkBchkBitsProgramCase "fuzz/ok/program-b900/bits-123" #[]
        successBuild900Bits123Program, rng2)

def suite : InstrSuite where
  id := bchkBitsId
  unit := #[
    { name := "unit/direct/success-consumes-top-builder-and-preserves-below"
      run := do
        let emptyChecks : Array Nat := #[1, 2, 8, 64, 255, 256]
        for bits in emptyChecks do
          expectOkStack s!"ok/empty-builder/bits-{bits}"
            (runBchkBitsImmDirect bits #[.builder Builder.empty])
            #[]

        expectOkStack "ok/deep-stack-preserve-below-full-slice"
          (runBchkBitsImmDirect 8 #[.null, .slice fullSliceA, .builder Builder.empty])
          #[.null, .slice fullSliceA]

        expectOkStack "ok/b767-plus-256"
          (runBchkBitsImmDirect 256 #[.builder builder767]) #[]
        expectOkStack "ok/b768-plus-255"
          (runBchkBitsImmDirect 255 #[.builder builder768]) #[]
        expectOkStack "ok/b900-plus-123"
          (runBchkBitsImmDirect 123 #[.builder builder900]) #[]
        expectOkStack "ok/b767-refs4-plus-256"
          (runBchkBitsImmDirect 256 #[.builder builder767Refs4]) #[] }
    ,
    { name := "unit/direct/cellov-boundaries"
      run := do
        expectErr "cellov/full-1023-plus-1"
          (runBchkBitsImmDirect 1 #[.builder fullBuilder1023]) .cellOv
        expectErr "cellov/full-1023-plus-256"
          (runBchkBitsImmDirect 256 #[.builder fullBuilder1023]) .cellOv
        expectErr "cellov/b768-plus-256"
          (runBchkBitsImmDirect 256 #[.builder builder768]) .cellOv
        expectErr "cellov/b900-plus-124"
          (runBchkBitsImmDirect 124 #[.builder builder900]) .cellOv
        expectErr "cellov/b900-plus-255"
          (runBchkBitsImmDirect 255 #[.builder builder900]) .cellOv }
    ,
    { name := "unit/direct/underflow-type-and-order"
      run := do
        expectErr "underflow/empty"
          (runBchkBitsImmDirect 8 #[]) .stkUnd

        expectErr "type/top-null"
          (runBchkBitsImmDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runBchkBitsImmDirect 8 #[intV 7]) .typeChk
        expectErr "type/top-cell"
          (runBchkBitsImmDirect 8 #[.cell refLeafA]) .typeChk
        expectErr "type/top-full-slice"
          (runBchkBitsImmDirect 8 #[.slice fullSliceB]) .typeChk

        expectErr "type/order-top-null-over-full-builder"
          (runBchkBitsImmDirect 8 #[.builder fullBuilder1023, .null]) .typeChk
        expectErr "type/order-top-slice-over-full-builder"
          (runBchkBitsImmDirect 8 #[.builder fullBuilder1023, .slice fullSliceA]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr :=
          #[.cellOp .brembitrefs, bchkBitsInstr 1, bchkBitsInstr 8, bchkBitsInstr 255,
            bchkBitsInstr 256, bchkBitsVarInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")

        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/brembitrefs-neighbor" s0 (.cellOp .brembitrefs) 16
        let s2 ← expectDecodeStep "decode/bchkbits-imm-1" s1 (bchkBitsInstr 1) 24
        let s3 ← expectDecodeStep "decode/bchkbits-imm-8" s2 (bchkBitsInstr 8) 24
        let s4 ← expectDecodeStep "decode/bchkbits-imm-255" s3 (bchkBitsInstr 255) 24
        let s5 ← expectDecodeStep "decode/bchkbits-imm-256" s4 (bchkBitsInstr 256) 24
        let s6 ← expectDecodeStep "decode/bchkbits-var-neighbor" s5 bchkBitsVarInstr 16
        let s7 ← expectDecodeStep "decode/tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let asm8 ←
          match assembleCp0 [bchkBitsInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bits-8 failed: {e}")
        if asm8.bits = natToBits (bchkBitsImmWord 8) 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bits-8: expected opcode word {bchkBitsImmWord 8}, got bits {asm8.bits}")
        if asm8.bits.size = 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bits-8: expected 24 bits, got {asm8.bits.size}")

        match assembleCp0 [bchkBitsInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits-0: expected rangeChk, got success")

        match assembleCp0 [bchkBitsInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits-257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits-257: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xcf37 16
            ++ natToBits (bchkBitsImmWord 1) 24
            ++ natToBits 0xcf39 16
            ++ natToBits (bchkBitsImmWord 256 true) 24
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-brembitrefs" r0 (.cellOp .brembitrefs) 16
        let r2 ← expectDecodeStep "decode/raw-bchkbits-imm-1" r1 (bchkBitsInstr 1) 24
        let r3 ← expectDecodeStep "decode/raw-bchkbits-var" r2 bchkBitsVarInstr 16
        let r4 ← expectDecodeStep "decode/raw-bchkbitsq-imm-256" r3 (.cellOp (.bchkBitsImm 256 true)) 24
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/alias-equivalence/imm-vs-var-bchkbits"
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
            (runBchkBitsImmDirect bits #[.builder b])
            (runBchkBitsVarAligned bits #[.builder b])

        let errorChecks : Array (Nat × Builder) :=
          #[
            (1, fullBuilder1023),
            (256, builder768),
            (124, builder900)
          ]
        for (bits, b) in errorChecks do
          expectSameOutcome s!"align/error/bits-{bits}/bits-used-{b.bits.size}"
            (runBchkBitsImmDirect bits #[.builder b])
            (runBchkBitsVarAligned bits #[.builder b])

        expectSameOutcome "align/underflow-empty"
          (runBchkBitsImmDirect 8 #[])
          (runBchkBitsVarAligned 8 #[])
        expectSameOutcome "align/type-top-null"
          (runBchkBitsImmDirect 8 #[.null])
          (runBchkBitsVarAligned 8 #[.null])
        expectSameOutcome "align/type-top-full-slice"
          (runBchkBitsImmDirect 8 #[.slice fullSliceA])
          (runBchkBitsVarAligned 8 #[.slice fullSliceA])
        expectSameOutcome "align/deep-stack-preserve-full-slice"
          (runBchkBitsImmDirect 8 #[.slice fullSliceB, .builder Builder.empty])
          (runBchkBitsVarAligned 8 #[.slice fullSliceB, .builder Builder.empty]) }
    ,
    { name := "unit/dispatch/non-bchkbitsimm-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runBchkBitsImmDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/bchk-var-neighbor"
          (runBchkBitsImmDispatchFallback bchkBitsVarInstr #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-neighbor"
          (runBchkBitsImmDispatchFallback (.cellOp .brefs) #[.slice fullSliceA])
          #[.slice fullSliceA, intV dispatchSentinel] }
  ]
  oracle := #[
    mkBchkBitsCase "ok/empty-builder/bits-1" 1 #[.builder Builder.empty],
    mkBchkBitsCase "ok/empty-builder/bits-2" 2 #[.builder Builder.empty],
    mkBchkBitsCase "ok/empty-builder/bits-8" 8 #[.builder Builder.empty],
    mkBchkBitsCase "ok/empty-builder/bits-64" 64 #[.builder Builder.empty],
    mkBchkBitsCase "ok/empty-builder/bits-255" 255 #[.builder Builder.empty],
    mkBchkBitsCase "ok/empty-builder/bits-256" 256 #[.builder Builder.empty],
    mkBchkBitsCase "ok/deep-stack-null-below" 8 #[.null, .builder Builder.empty],
    mkBchkBitsCase "ok/deep-stack-full-slice-below" 8 #[.slice fullSliceA, .builder Builder.empty],
    mkBchkBitsCase "ok/deep-stack-two-below" 8 #[.cell refLeafA, .slice fullSliceB, .builder Builder.empty],

    mkBchkBitsProgramCase "ok/program-build767-check256" #[] successBuild767Bits256Program,
    mkBchkBitsProgramCase "ok/program-build768-check255" #[] successBuild768Bits255Program,
    mkBchkBitsProgramCase "ok/program-build900-check123" #[] successBuild900Bits123Program,
    mkBchkBitsProgramCase "ok/program-build767-check1-with-slice-noise"
      #[.slice fullSliceA] (mkBchkBitsProgram build767Program 1),

    mkBchkBitsProgramCase "cellov/program-build768-check256" #[] cellovBuild768Bits256Program,
    mkBchkBitsProgramCase "cellov/program-build900-check124" #[] cellovBuild900Bits124Program,
    mkBchkBitsProgramCase "cellov/program-build1023-check1" #[] cellovBuild1023Bits1Program,
    mkBchkBitsProgramCase "cellov/program-build1023-check256" #[] cellovBuild1023Bits256Program,

    mkBchkBitsCase "underflow/empty" 8 #[],
    mkBchkBitsCase "type/top-null" 8 #[.null],
    mkBchkBitsCase "type/top-int" 8 #[intV 11],
    mkBchkBitsCase "type/top-cell" 8 #[.cell refLeafB],
    mkBchkBitsCase "type/top-full-slice" 8 #[.slice fullSliceA],
    mkBchkBitsCase "type/order-top-null-over-builder" 8 #[.builder Builder.empty, .null],

    mkBchkBitsCase "gas/exact-cost-succeeds" bchkBitsGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsSetGasExact), .tonEnvOp .setGasLimit, bchkBitsInstr bchkBitsGasProbeBits],
    mkBchkBitsCase "gas/exact-minus-one-out-of-gas" bchkBitsGasProbeBits #[.builder Builder.empty]
      #[.pushInt (.num bchkBitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bchkBitsInstr bchkBitsGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026021015
      count := 500
      gen := genBchkBitsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKBITS
