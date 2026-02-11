import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSTDADDR

/-
STSTDADDR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean` (`.tonEnvOp (.stStdAddr false)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa52` decode to `.tonEnvOp (.stStdAddr false)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.tonEnvOp (.stStdAddr false)` encode as `0xfa52`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`is_valid_std_msg_addr`, `exec_store_std_address`, opcode registration `0xfa52/0xfa53`).
  - Note: in current TON tree, STSTDADDR is implemented in `tonops.cpp` (not `cellops.cpp`).

Branch map used for this suite (`quiet=false`, i.e. STSTDADDR):
- Lean STSTDADDR path: 6 branch sites / 7 terminal outcomes
  (dispatch guard; `checkUnderflow 2`; pop top as builder; pop second as slice;
   std-address validity + capacity guard; success append or `cellOv` throw).
- C++ STSTDADDR path: 5 branch sites / 6 aligned outcomes
  (`check_underflow(2)`; `pop_builder`; `pop_cellslice`; `is_valid_std_msg_addr`;
   `can_extend_by`; success or `cell_ov`).

Key risk areas:
- stack order is `... slice builder` (builder on top);
- `isValidStdMsgAddr` is strict: exactly `267` remaining bits, no remaining refs, first 3 bits = `100`;
- valid boundary is `builder.bits.size ≤ 756` (since standard address contributes 267 bits);
- invalid std-address shape and builder-overflow both map to `cellOv` (non-quiet path);
- partial slices use remaining view (`toCellRemaining`) and must validate against remaining bits/refs.
-/

private def ststdaddrId : InstrId := { name := "STSTDADDR" }

private def ststdaddrInstr : Instr :=
  .tonEnvOp (.stStdAddr false)

private def mkStstdaddrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ststdaddrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ststdaddrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStstdaddrProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ststdaddrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStstdaddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ststdaddrInstr stack

private def runStstdaddrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 552)) stack

private def ststdaddrSetGasExact : Int :=
  computeExactGasBudget ststdaddrInstr

private def ststdaddrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ststdaddrInstr

private def mkStdAddrBits (workchain : Nat) (addr : Nat) : BitString :=
  natToBits 0b10 2 ++ #[false] ++ natToBits (workchain % 256) 8 ++ natToBits addr 256

private def mkStdAddrCell (workchain : Nat) (addr : Nat) : Cell :=
  Cell.mkOrdinary (mkStdAddrBits workchain addr) #[]

private def mkStdAddrSlice (workchain : Nat) (addr : Nat) : Slice :=
  Slice.ofCell (mkStdAddrCell workchain addr)

private def appendSliceRemaining (b : Builder) (s : Slice) : Builder :=
  let c := s.toCellRemaining
  { bits := b.bits ++ c.bits
    refs := b.refs ++ c.refs }

private def mkPrefix3BitsCell (prefix3 : Nat) (tailBits : Nat) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary (natToBits prefix3 3 ++ natToBits 0 tailBits) refs

private def stdAddrCellZero : Cell := mkStdAddrCell 0 0

private def stdAddrCellMaxWc : Cell := mkStdAddrCell 255 65535

private def stdAddrCellSample : Cell := mkStdAddrCell 17 0xABCD

private def stdAddrSliceZero : Slice := Slice.ofCell stdAddrCellZero

private def stdAddrSliceMaxWc : Slice := Slice.ofCell stdAddrCellMaxWc

private def stdAddrSliceSample : Slice := Slice.ofCell stdAddrCellSample

private def invalidPrefixSlice000 : Slice := Slice.ofCell (mkPrefix3BitsCell 0b000 264)

private def invalidAnycastSlice : Slice := Slice.ofCell (mkPrefix3BitsCell 0b101 264)

private def invalidShortSlice : Slice := Slice.ofCell (mkPrefix3BitsCell 0b100 263)

private def invalidLongSlice : Slice := Slice.ofCell (mkPrefix3BitsCell 0b100 265)

private def invalidRefSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkStdAddrBits 0 0) #[Cell.empty])

private def shiftedStdSlice : Slice :=
  (Slice.ofCell (Cell.mkOrdinary (natToBits 0b11 2 ++ mkStdAddrBits 7 42) #[])).advanceBits 2

private def spentRefStdSlice : Slice :=
  { (Slice.ofCell (Cell.mkOrdinary (mkStdAddrBits 9 77) #[Cell.empty])) with refPos := 1 }

private def builderRefs4 : Builder :=
  { bits := #[]
    refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }

private def appendOneEmptyCellRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneEmptyCellRefToTopBuilder

private def mkBuilderProgram (bits refs : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkStoreWithBuilderProgram (bits refs : Nat) (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[ststdaddrInstr]

private def ststdaddrProgramBits756 : Array Instr :=
  mkStoreWithBuilderProgram 756 0

private def ststdaddrProgramBits757Ov : Array Instr :=
  mkStoreWithBuilderProgram 757 0

private def ststdaddrProgramBits1023Ov : Array Instr :=
  mkStoreWithBuilderProgram 1023 0

private def ststdaddrProgramRefs4 : Array Instr :=
  mkStoreWithBuilderProgram 0 4

private def ststdaddrProgramBits756Refs4 : Array Instr :=
  mkStoreWithBuilderProgram 756 4

private def ststdaddrProgramBits757Refs4Ov : Array Instr :=
  mkStoreWithBuilderProgram 757 4

private def stdAddrWorkchainPool : Array Nat :=
  #[0, 1, 2, 17, 127, 128, 255]

private def stdAddrAddrPool : Array Nat :=
  #[0, 1, 2, 3, 7, 15, 31, 255, 256, 1024, 65535]

private def invalidPrefix3Pool : Array Nat :=
  #[0b000, 0b001, 0b010, 0b011, 0b101, 0b110, 0b111]

private def builderBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 256, 511, 700, 755, 756]

private def builderBitsOverflowPool : Array Nat :=
  #[757, 758, 800, 900, 1022, 1023]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickWorkchainMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickNatFromPool stdAddrWorkchainPool rng1
  else
    randNat rng1 0 255

private def pickAddrMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickNatFromPool stdAddrAddrPool rng1
  else
    randNat rng1 0 65535

private def pickStdAddrSlice (rng0 : StdGen) : Slice × StdGen :=
  let (wc, rng1) := pickWorkchainMixed rng0
  let (addr, rng2) := pickAddrMixed rng1
  (mkStdAddrSlice wc addr, rng2)

private def pickInvalidPrefixSlice (rng0 : StdGen) : Slice × StdGen :=
  let (prefix3, rng1) := pickNatFromPool invalidPrefix3Pool rng0
  (Slice.ofCell (mkPrefix3BitsCell prefix3 264), rng1)

private def pickBuilderBitsOk (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickNatFromPool builderBitsBoundaryPool rng1
  else
    randNat rng1 0 756

private def pickBuilderBitsOv (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 6 then
    pickNatFromPool builderBitsOverflowPool rng1
  else
    randNat rng1 757 1023

private def pickStstdaddrNoise (rng0 : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng0 0 3
  if k = 0 then
    (.null, rng1)
  else if k = 1 then
    let (u, rng2) := randNat rng1 0 127
    (intV (Int.ofNat u - 64), rng2)
  else if k = 2 then
    (.cell Cell.empty, rng1)
  else
    let (s, rng2) := pickStdAddrSlice rng1
    (.slice s, rng2)

private def genStstdaddrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (sValid, rng2) := pickStdAddrSlice rng1
  if shape = 0 then
    (mkStstdaddrCase "fuzz/ok/direct/top-only"
      #[.slice sValid, .builder Builder.empty], rng2)
  else if shape = 1 then
    let (noise, rng3) := pickStstdaddrNoise rng2
    (mkStstdaddrCase "fuzz/ok/direct/deep-stack"
      #[noise, .slice sValid, .builder Builder.empty], rng3)
  else if shape = 2 then
    (mkStstdaddrCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 3 then
    (mkStstdaddrCase "fuzz/underflow/one-slice" #[.slice sValid], rng2)
  else if shape = 4 then
    (mkStstdaddrCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng2)
  else if shape = 5 then
    (mkStstdaddrCase "fuzz/type/top-not-builder"
      #[.slice sValid, .null], rng2)
  else if shape = 6 then
    (mkStstdaddrCase "fuzz/type/second-not-slice"
      #[.null, .builder Builder.empty], rng2)
  else if shape = 7 then
    (mkStstdaddrCase "fuzz/type/reversed-order"
      #[.builder Builder.empty, .slice sValid], rng2)
  else if shape = 8 then
    let (sBadPrefix, rng3) := pickInvalidPrefixSlice rng2
    (mkStstdaddrCase "fuzz/cellov/invalid-prefix"
      #[.slice sBadPrefix, .builder Builder.empty], rng3)
  else if shape = 9 then
    (mkStstdaddrCase "fuzz/cellov/invalid-anycast"
      #[.slice invalidAnycastSlice, .builder Builder.empty], rng2)
  else if shape = 10 then
    (mkStstdaddrCase "fuzz/cellov/invalid-short"
      #[.slice invalidShortSlice, .builder Builder.empty], rng2)
  else if shape = 11 then
    (mkStstdaddrCase "fuzz/cellov/invalid-long"
      #[.slice invalidLongSlice, .builder Builder.empty], rng2)
  else if shape = 12 then
    let (wc, rng3) := pickWorkchainMixed rng2
    let (addr, rng4) := pickAddrMixed rng3
    let sBadRef := Slice.ofCell (Cell.mkOrdinary (mkStdAddrBits wc addr) #[Cell.empty])
    (mkStstdaddrCase "fuzz/cellov/invalid-ref"
      #[.slice sBadRef, .builder Builder.empty], rng4)
  else if shape = 13 then
    let (bits, rng3) := pickBuilderBitsOk rng2
    (mkStstdaddrProgramCase s!"fuzz/program/ok/bits-{bits}"
      #[.slice sValid]
      (mkStoreWithBuilderProgram bits 0), rng3)
  else if shape = 14 then
    let (bits, rng3) := pickBuilderBitsOv rng2
    (mkStstdaddrProgramCase s!"fuzz/program/cellov/bits-{bits}"
      #[.slice sValid]
      (mkStoreWithBuilderProgram bits 0), rng3)
  else if shape = 15 then
    (mkStstdaddrProgramCase "fuzz/program/ok/refs4"
      #[.slice sValid]
      ststdaddrProgramRefs4, rng2)
  else if shape = 16 then
    let (bits, rng3) := pickBuilderBitsOk rng2
    (mkStstdaddrProgramCase s!"fuzz/program/ok/refs4-bits-{bits}"
      #[.slice sValid]
      (mkStoreWithBuilderProgram bits 4), rng3)
  else if shape = 17 then
    (mkStstdaddrCase "fuzz/gas/exact"
      #[.slice sValid, .builder Builder.empty]
      #[.pushInt (.num ststdaddrSetGasExact), .tonEnvOp .setGasLimit, ststdaddrInstr], rng2)
  else if shape = 18 then
    (mkStstdaddrCase "fuzz/gas/minus-one"
      #[.slice sValid, .builder Builder.empty]
      #[.pushInt (.num ststdaddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, ststdaddrInstr], rng2)
  else if shape = 19 then
    let (noise, rng3) := pickStstdaddrNoise rng2
    let (bits, rng4) := pickBuilderBitsOk rng3
    (mkStstdaddrProgramCase s!"fuzz/program/ok/noise-bits-{bits}"
      #[noise, .slice sValid]
      (mkStoreWithBuilderProgram bits 0), rng4)
  else
    let (bits, rng3) := pickBuilderBitsOv rng2
    (mkStstdaddrProgramCase s!"fuzz/program/cellov/refs4-bits-{bits}"
      #[.slice sValid]
      (mkStoreWithBuilderProgram bits 4), rng3)

def suite : InstrSuite where
  id := ststdaddrId
  unit := #[
    { name := "unit/direct/success-order-and-remainder-append"
      run := do
        let sZero := stdAddrSliceZero
        let expectedZero := appendSliceRemaining Builder.empty sZero
        expectOkStack "ok/empty-builder-std-zero"
          (runStstdaddrDirect #[.slice sZero, .builder Builder.empty])
          #[.builder expectedZero]

        let prefBuilder : Builder := { bits := natToBits 5 3, refs := #[Cell.empty] }
        let sSample := stdAddrSliceSample
        let expectedSample := appendSliceRemaining prefBuilder sSample
        expectOkStack "ok/non-empty-builder-append-valid-stdaddr"
          (runStstdaddrDirect #[.slice sSample, .builder prefBuilder])
          #[.builder expectedSample]

        let expectedRefs4 := appendSliceRemaining builderRefs4 sZero
        expectOkStack "ok/refs4-builder-still-valid-append"
          (runStstdaddrDirect #[.slice sZero, .builder builderRefs4])
          #[.builder expectedRefs4]

        let expectedShifted := appendSliceRemaining Builder.empty shiftedStdSlice
        expectOkStack "ok/partial-slice-bitpos-remainder"
          (runStstdaddrDirect #[.slice shiftedStdSlice, .builder Builder.empty])
          #[.builder expectedShifted]

        let expectedSpentRef := appendSliceRemaining Builder.empty spentRefStdSlice
        expectOkStack "ok/partial-slice-refpos-remainder"
          (runStstdaddrDirect #[.slice spentRefStdSlice, .builder Builder.empty])
          #[.builder expectedSpentRef]

        let b756 : Builder := Builder.empty.storeBits (Array.replicate 756 false)
        let expected756 := appendSliceRemaining b756 sZero
        expectOkStack "ok/bits-boundary-756-plus-267"
          (runStstdaddrDirect #[.slice sZero, .builder b756])
          #[.builder expected756]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStstdaddrDirect #[.null, .slice sZero, .builder Builder.empty])
          #[.null, .builder expectedZero] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        let sZero := stdAddrSliceZero
        expectErr "underflow/empty" (runStstdaddrDirect #[]) .stkUnd
        expectErr "underflow/one-slice" (runStstdaddrDirect #[.slice sZero]) .stkUnd
        expectErr "underflow/one-builder" (runStstdaddrDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-null" (runStstdaddrDirect #[.null]) .stkUnd

        expectErr "type/top-not-builder-null"
          (runStstdaddrDirect #[.slice sZero, .null]) .typeChk
        expectErr "type/top-not-builder-int"
          (runStstdaddrDirect #[.slice sZero, intV 3]) .typeChk
        expectErr "type/second-not-slice-null"
          (runStstdaddrDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/second-not-slice-int"
          (runStstdaddrDirect #[intV 9, .builder Builder.empty]) .typeChk
        expectErr "type/reversed-order-misuse"
          (runStstdaddrDirect #[.builder Builder.empty, .slice sZero]) .typeChk
        expectErr "type/both-wrong-top-first"
          (runStstdaddrDirect #[intV 1, .null]) .typeChk }
    ,
    { name := "unit/direct/invalid-std-shape-yields-cellov"
      run := do
        expectErr "cellov/invalid-prefix-000"
          (runStstdaddrDirect #[.slice invalidPrefixSlice000, .builder Builder.empty]) .cellOv
        expectErr "cellov/invalid-anycast-101"
          (runStstdaddrDirect #[.slice invalidAnycastSlice, .builder Builder.empty]) .cellOv
        expectErr "cellov/invalid-short-266bits"
          (runStstdaddrDirect #[.slice invalidShortSlice, .builder Builder.empty]) .cellOv
        expectErr "cellov/invalid-long-268bits"
          (runStstdaddrDirect #[.slice invalidLongSlice, .builder Builder.empty]) .cellOv
        expectErr "cellov/invalid-refs-present"
          (runStstdaddrDirect #[.slice invalidRefSlice, .builder Builder.empty]) .cellOv
        expectErr "cellov/invalid-prefix-even-with-full-builder"
          (runStstdaddrDirect #[.slice invalidPrefixSlice000, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/direct/capacity-overflow-boundaries"
      run := do
        let sZero := stdAddrSliceZero
        let b757 : Builder := Builder.empty.storeBits (Array.replicate 757 false)
        expectErr "cellov/bits-757-plus-267"
          (runStstdaddrDirect #[.slice sZero, .builder b757]) .cellOv

        expectErr "cellov/full-builder-1023"
          (runStstdaddrDirect #[.slice sZero, .builder fullBuilder1023]) .cellOv

        let b757r4 : Builder :=
          { bits := Array.replicate 757 false
            refs := builderRefs4.refs }
        expectErr "cellov/bits-757-plus-267-with-refs4"
          (runStstdaddrDirect #[.slice sZero, .builder b757r4]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [ststdaddrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits 0xfa52 16 then
          pure ()
        else
          throw (IO.userError s!"ststdaddr canonical encode mismatch: got bits {canonicalOnly.bits}")

        let quietOnly ←
          match assembleCp0 [.tonEnvOp (.stStdAddr true)] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble quiet failed: {e}")
        if quietOnly.bits = natToBits 0xfa53 16 then
          pure ()
        else
          throw (IO.userError s!"ststdaddrq encode mismatch: got bits {quietOnly.bits}")

        let program : Array Instr :=
          #[ststdaddrInstr, .tonEnvOp (.stStdAddr true), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ststdaddr-fa52" s0 ststdaddrInstr 16
        let s2 ← expectDecodeStep "decode/ststdaddrq-fa53" s1 (.tonEnvOp (.stStdAddr true)) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-ststdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStstdaddrDispatchFallback #[.null])
          #[.null, intV 552] }
  ]
  oracle := #[
    mkStstdaddrCase "ok/empty-builder-std-zero"
      #[.slice stdAddrSliceZero, .builder Builder.empty],
    mkStstdaddrCase "ok/empty-builder-std-maxwc"
      #[.slice stdAddrSliceMaxWc, .builder Builder.empty],
    mkStstdaddrCase "ok/deep-stack-preserve-null"
      #[.null, .slice stdAddrSliceZero, .builder Builder.empty],
    mkStstdaddrCase "ok/deep-stack-preserve-int"
      #[intV 7, .slice stdAddrSliceSample, .builder Builder.empty],

    mkStstdaddrProgramCase "ok/program/bits-0"
      #[.slice stdAddrSliceZero]
      (mkStoreWithBuilderProgram 0 0),
    mkStstdaddrProgramCase "ok/program/bits-1"
      #[.slice stdAddrSliceZero]
      (mkStoreWithBuilderProgram 1 0 (.num 1)),
    mkStstdaddrProgramCase "ok/program/bits-255"
      #[.slice stdAddrSliceSample]
      (mkStoreWithBuilderProgram 255 0 (.num 1)),
    mkStstdaddrProgramCase "ok/program/bits-700"
      #[.slice stdAddrSliceMaxWc]
      (mkStoreWithBuilderProgram 700 0),
    mkStstdaddrProgramCase "ok/program/bits-756-boundary"
      #[.slice stdAddrSliceZero]
      ststdaddrProgramBits756,
    mkStstdaddrProgramCase "ok/program/refs4"
      #[.slice stdAddrSliceSample]
      ststdaddrProgramRefs4,
    mkStstdaddrProgramCase "ok/program/bits756-refs4"
      #[.slice stdAddrSliceMaxWc]
      ststdaddrProgramBits756Refs4,
    mkStstdaddrProgramCase "ok/program/noise-below-preserved"
      #[.null, .slice stdAddrSliceSample]
      (mkStoreWithBuilderProgram 5 0 (.num 1)),

    mkStstdaddrCase "cellov/invalid-prefix-000"
      #[.slice invalidPrefixSlice000, .builder Builder.empty],
    mkStstdaddrCase "cellov/invalid-anycast-101"
      #[.slice invalidAnycastSlice, .builder Builder.empty],
    mkStstdaddrCase "cellov/invalid-short-266bits"
      #[.slice invalidShortSlice, .builder Builder.empty],
    mkStstdaddrCase "cellov/invalid-long-268bits"
      #[.slice invalidLongSlice, .builder Builder.empty],
    mkStstdaddrCase "cellov/invalid-refs-present"
      #[.slice invalidRefSlice, .builder Builder.empty],

    mkStstdaddrCase "underflow/empty" #[],
    mkStstdaddrCase "underflow/one-slice" #[.slice stdAddrSliceZero],
    mkStstdaddrCase "underflow/one-builder" #[.builder Builder.empty],

    mkStstdaddrCase "type/top-not-builder-null"
      #[.slice stdAddrSliceZero, .null],
    mkStstdaddrCase "type/second-not-slice-null"
      #[.null, .builder Builder.empty],
    mkStstdaddrCase "type/reversed-order-misuse"
      #[.builder Builder.empty, .slice stdAddrSliceZero],

    mkStstdaddrCase "gas/exact-cost-succeeds"
      #[.slice stdAddrSliceZero, .builder Builder.empty]
      #[.pushInt (.num ststdaddrSetGasExact), .tonEnvOp .setGasLimit, ststdaddrInstr],
    mkStstdaddrCase "gas/exact-minus-one-out-of-gas"
      #[.slice stdAddrSliceZero, .builder Builder.empty]
      #[.pushInt (.num ststdaddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, ststdaddrInstr],

    mkStstdaddrProgramCase "cellov/program/bits-757-overflow"
      #[.slice stdAddrSliceZero]
      ststdaddrProgramBits757Ov,
    mkStstdaddrProgramCase "cellov/program/bits-1023-overflow"
      #[.slice stdAddrSliceZero]
      ststdaddrProgramBits1023Ov,
    mkStstdaddrProgramCase "cellov/program/bits-757-refs4-overflow"
      #[.slice stdAddrSliceZero]
      ststdaddrProgramBits757Refs4Ov
  ]
  fuzz := #[
    { seed := 2026021037
      count := 500
      gen := genStstdaddrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSTDADDR
