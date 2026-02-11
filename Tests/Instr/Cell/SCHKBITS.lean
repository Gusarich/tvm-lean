import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCHKBITS

/-
SCHKBITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/SchkBits.lean` (`.schkBits quiet`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popNatUpTo`, type/range behavior)
  - `TvmLean/Semantics/VM/Ops/Cells.lean` (`popSlice` type behavior)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SCHKBITS`/`SCHKBITSQ` opcodes)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode family `0xd741..0xd747`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_chk_op_args`, opcode registrations for SCHKBITS/SCHKBITSQ).

Branch map covered by this suite:
- dispatch guard for `.cellOp (.schkBits quiet)` vs fallback to `next`;
- `checkUnderflow 2` short-circuit before any pop;
- top-of-stack arg parsing (`popNatUpTo 1023`): type error and range error branches;
- second arg parsing (`popSlice`) after successful bits parse;
- payload predicate `s.haveBits bits`: success consume-all vs non-quiet `cellUnd`;
- decode/assembler neighborhood around SCHK/SCHKQ and adjacent opcodes.
-/

private def schkBitsId : InstrId := { name := "SCHKBITS" }

private def dispatchSentinel : Int := 743

private def schkBitsInstr : Instr :=
  .cellOp (.schkBits false)

private def schkBitsQInstr : Instr :=
  .cellOp (.schkBits true)

private def schkRefsInstr : Instr :=
  .cellOp (.schkRefs false)

private def schkBitRefsInstr : Instr :=
  .cellOp (.schkBitRefs false)

private def schkRefsQInstr : Instr :=
  .cellOp (.schkRefs true)

private def schkBitRefsQInstr : Instr :=
  .cellOp (.schkBitRefs true)

private def execInstrCellOpSchkBitsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpSchkBits op next
  | _ => next

private def mkSchkBitsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[schkBitsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkBitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSchkBitsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSchkBitsOnly schkBitsInstr stack

private def runSchkBitsQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSchkBitsOnly schkBitsQInstr stack

private def runSchkBitsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSchkBitsOnly instr (VM.push (intV dispatchSentinel)) stack

private def mkSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def zeroSlice (bits : Nat) : Slice :=
  mkSlice (Array.replicate bits false)

private def natStack (s : Slice) (bits : Nat) : Array Value :=
  #[.slice s, intV (Int.ofNat bits)]

private def refLeafA : Cell :=
  Cell.ofUInt 5 3

private def refLeafB : Cell :=
  Cell.ofUInt 9 4

private def refLeafC : Cell :=
  Cell.ofUInt 3 2

private def slice0 : Slice :=
  mkSlice #[]

private def slice1 : Slice :=
  mkSlice (natToBits 1 1)

private def slice3 : Slice :=
  mkSlice (natToBits 5 3)

private def slice6Refs2 : Slice :=
  mkSlice (natToBits 45 6) #[refLeafA, refLeafB]

private def slice8Offset2 : Slice :=
  { cell := Cell.mkOrdinary (natToBits 178 8) #[refLeafA]
    bitPos := 2
    refPos := 0 }

private def slice9Offset1Refs3 : Slice :=
  { cell := Cell.mkOrdinary (natToBits 341 9) #[refLeafA, refLeafB, refLeafC]
    bitPos := 1
    refPos := 2 }

private def slice255 : Slice := zeroSlice 255
private def slice300 : Slice := zeroSlice 300
private def slice512 : Slice := zeroSlice 512
private def slice767 : Slice := zeroSlice 767
private def slice900 : Slice := zeroSlice 900
private def slice1022 : Slice := zeroSlice 1022
private def slice1023 : Slice := zeroSlice 1023

private def schkBitsSetGasExact : Int :=
  computeExactGasBudget schkBitsInstr

private def schkBitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne schkBitsInstr

private def schkBitsLenBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 767, 768, 1022, 1023]

private def pickSchkBitsLenBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (schkBitsLenBoundaryPool.size - 1)
  (schkBitsLenBoundaryPool[idx]!, rng')

private def pickSchkBitsLenMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickSchkBitsLenBoundary rng1
  else
    randNat rng1 0 1023

private def pickSchkRefs (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let refs :=
    if pick = 0 then
      #[]
    else if pick = 1 then
      #[refLeafA]
    else if pick = 2 then
      #[refLeafA, refLeafB]
    else
      #[refLeafA, refLeafB, refLeafC]
  (refs, rng1)

private def pickSchkSlice (rng0 : StdGen) : Slice × StdGen := Id.run do
  let (len, rng1) := pickSchkBitsLenMixed rng0
  let (phase, rng2) := randNat rng1 0 1
  let (refs, rng3) := pickSchkRefs rng2
  (mkSlice (stripeBits len phase) refs, rng3)

private def pickSchkBitsAtMost (max : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 5
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (max, rng1)
  else if mode = 2 then
    (if max = 0 then 0 else max - 1, rng1)
  else
    randNat rng1 0 max

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    (intV 73, rng1)
  else if pick = 2 then
    (.cell refLeafC, rng1)
  else if pick = 3 then
    (.builder Builder.empty, rng1)
  else
    (.slice slice6Refs2, rng1)

private def genSchkBitsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    (mkSchkBitsCase "fuzz/ok/empty-bits0" (natStack slice0 0), rng1)
  else if shape = 1 then
    let (s, rng2) := pickSchkSlice rng1
    let bits := s.bitsRemaining
    (mkSchkBitsCase s!"fuzz/ok/exact/rem-{bits}" (natStack s bits), rng2)
  else if shape = 2 then
    let (s, rng2) := pickSchkSlice rng1
    let (bits, rng3) := pickSchkBitsAtMost s.bitsRemaining rng2
    (mkSchkBitsCase s!"fuzz/ok/rand/rem-{s.bitsRemaining}/bits-{bits}" (natStack s bits), rng3)
  else if shape = 3 then
    let (len, rng2) := randNat rng1 0 1022
    let (phase, rng3) := randNat rng2 0 1
    let (refs, rng4) := pickSchkRefs rng3
    let s := mkSlice (stripeBits len phase) refs
    let (bits, rng5) := randNat rng4 (len + 1) 1023
    (mkSchkBitsCase s!"fuzz/cellund/rem-{len}/bits-{bits}" (natStack s bits), rng5)
  else if shape = 4 then
    (mkSchkBitsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkSchkBitsCase "fuzz/underflow/one-item-slice" #[.slice slice3], rng1)
  else if shape = 6 then
    (mkSchkBitsCase "fuzz/type/top-null" #[.slice slice3, .null], rng1)
  else if shape = 7 then
    (mkSchkBitsCase "fuzz/type/slice-arg-null" #[.null, intV 1], rng1)
  else if shape = 8 then
    (mkSchkBitsCase "fuzz/range/negative" #[.slice slice6Refs2, intV (-1)], rng1)
  else if shape = 9 then
    let (n, rng2) := randNat rng1 1024 5000
    (mkSchkBitsCase s!"fuzz/range/high-{n}" #[.slice slice512, intV (Int.ofNat n)], rng2)
  else if shape = 10 then
    let (noise, rng2) := pickNoise rng1
    let (s, rng3) := pickSchkSlice rng2
    let (bits, rng4) := pickSchkBitsAtMost s.bitsRemaining rng3
    (mkSchkBitsCase s!"fuzz/ok/deep/rem-{s.bitsRemaining}/bits-{bits}" #[noise, .slice s, intV (Int.ofNat bits)], rng4)
  else if shape = 11 then
    let (noise, rng2) := pickNoise rng1
    let (len, rng3) := randNat rng2 0 1022
    let s := mkSlice (stripeBits len 1) #[refLeafA]
    let (bits, rng4) := randNat rng3 (len + 1) 1023
    (mkSchkBitsCase s!"fuzz/cellund/deep/rem-{len}/bits-{bits}" #[noise, .slice s, intV (Int.ofNat bits)], rng4)
  else if shape = 12 then
    (mkSchkBitsCase "fuzz/range/order-before-slice-type" #[.null, intV (-1)], rng1)
  else if shape = 13 then
    let (noise1, rng2) := pickNoise rng1
    let (noise2, rng3) := pickNoise rng2
    let (s, rng4) := pickSchkSlice rng3
    let (bits, rng5) := pickSchkBitsAtMost s.bitsRemaining rng4
    (mkSchkBitsCase s!"fuzz/ok/deep-two/rem-{s.bitsRemaining}/bits-{bits}"
      #[noise1, noise2, .slice s, intV (Int.ofNat bits)], rng5)
  else if shape = 14 then
    (mkSchkBitsCase "fuzz/gas/exact" (natStack slice3 0)
      #[.pushInt (.num schkBitsSetGasExact), .tonEnvOp .setGasLimit, schkBitsInstr], rng1)
  else
    (mkSchkBitsCase "fuzz/gas/exact-minus-one" (natStack slice3 0)
      #[.pushInt (.num schkBitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkBitsInstr], rng1)

def suite : InstrSuite where
  id := { name := "SCHKBITS" }
  unit := #[
    { name := "unit/direct/success-and-boundaries"
      run := do
        expectOkStack "ok/empty-bits0"
          (runSchkBitsDirect (natStack slice0 0))
          #[]
        expectOkStack "ok/one-bit-bits0"
          (runSchkBitsDirect (natStack slice1 0))
          #[]
        expectOkStack "ok/one-bit-bits1"
          (runSchkBitsDirect (natStack slice1 1))
          #[]
        expectOkStack "ok/exact-3"
          (runSchkBitsDirect (natStack slice3 3))
          #[]
        expectOkStack "ok/refs-ignored"
          (runSchkBitsDirect (natStack slice6Refs2 6))
          #[]
        expectOkStack "ok/offset-exact-6"
          (runSchkBitsDirect (natStack slice8Offset2 6))
          #[]
        expectOkStack "ok/offset-plus-refpos-exact-8"
          (runSchkBitsDirect (natStack slice9Offset1Refs3 8))
          #[]
        expectOkStack "ok/high-255"
          (runSchkBitsDirect (natStack slice255 255))
          #[]
        expectOkStack "ok/high-512"
          (runSchkBitsDirect (natStack slice512 512))
          #[]
        expectOkStack "ok/high-767"
          (runSchkBitsDirect (natStack slice767 767))
          #[]
        expectOkStack "ok/high-1023"
          (runSchkBitsDirect (natStack slice1023 1023))
          #[]
        expectOkStack "ok/deep-stack-preserve-two-below"
          (runSchkBitsDirect #[.null, .cell refLeafA, .slice slice6Refs2, intV 4])
          #[.null, .cell refLeafA] }
    ,
    { name := "unit/direct/cellund-failures"
      run := do
        expectErr "cellund/empty-plus-1"
          (runSchkBitsDirect (natStack slice0 1)) .cellUnd
        expectErr "cellund/exact-plus-1-on-3"
          (runSchkBitsDirect (natStack slice3 4)) .cellUnd
        expectErr "cellund/offset-plus-1-on-6"
          (runSchkBitsDirect (natStack slice8Offset2 7)) .cellUnd
        expectErr "cellund/512-plus-1"
          (runSchkBitsDirect (natStack slice512 513)) .cellUnd
        expectErr "cellund/767-plus-1"
          (runSchkBitsDirect (natStack slice767 768)) .cellUnd
        expectErr "cellund/1022-plus-1"
          (runSchkBitsDirect (natStack slice1022 1023)) .cellUnd
        expectErr "cellund/deep-stack"
          (runSchkBitsDirect #[.builder Builder.empty, .slice slice3, intV 7]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty"
          (runSchkBitsDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runSchkBitsDirect #[.slice slice3]) .stkUnd
        expectErr "underflow/one-item-int"
          (runSchkBitsDirect #[intV 1]) .stkUnd

        expectErr "type/top-not-int-null"
          (runSchkBitsDirect #[.slice slice3, .null]) .typeChk
        expectErr "type/top-not-int-cell"
          (runSchkBitsDirect #[.slice slice3, .cell refLeafA]) .typeChk
        expectErr "type/top-not-int-slice"
          (runSchkBitsDirect #[.slice slice3, .slice slice1]) .typeChk

        expectErr "range/top-nan"
          (runSchkBitsDirect #[.slice slice6Refs2, .int .nan]) .rangeChk
        expectErr "range/top-negative"
          (runSchkBitsDirect #[.slice slice6Refs2, intV (-1)]) .rangeChk
        expectErr "range/top-too-large"
          (runSchkBitsDirect #[.slice slice1023, intV 1024]) .rangeChk
        expectErr "range/order-before-slice-type"
          (runSchkBitsDirect #[.null, intV (-1)]) .rangeChk

        expectErr "type/slice-arg-null"
          (runSchkBitsDirect #[.null, intV 1]) .typeChk
        expectErr "type/slice-arg-builder"
          (runSchkBitsDirect #[.builder Builder.empty, intV 1]) .typeChk }
    ,
    { name := "unit/direct/quiet-neighbor-and-dispatch"
      run := do
        expectOkStack "quiet/success-returns-minus1"
          (runSchkBitsQDirect (natStack slice6Refs2 6))
          #[intV (-1)]
        expectOkStack "quiet/failure-returns-0"
          (runSchkBitsQDirect (natStack slice6Refs2 9))
          #[intV 0]
        expectOkStack "quiet/deep-stack-preserve-below"
          (runSchkBitsQDirect #[.null, .slice slice3, intV 2])
          #[.null, intV (-1)]
        expectErr "quiet/still-range-checks"
          (runSchkBitsQDirect #[.slice slice3, intV (-1)]) .rangeChk

        expectOkStack "dispatch/non-cellop"
          (runSchkBitsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop"
          (runSchkBitsDispatchFallback (.cellOp .sdepth) #[.slice slice3])
          #[.slice slice3, intV dispatchSentinel]
        expectOkStack "dispatch/schkrefs-neighbor"
          (runSchkBitsDispatchFallback schkRefsInstr #[.slice slice3, intV 1])
          #[.slice slice3, intV 1, intV dispatchSentinel]
        expectOkStack "dispatch/schkbitsq-is-handled-not-fallback"
          (runSchkBitsDispatchFallback schkBitsQInstr (natStack slice3 2))
          #[intV (-1)] }
    ,
    { name := "unit/opcode/decode-family-and-assembler-boundaries"
      run := do
        let program : Array Instr :=
          #[.cellOp (.split false), schkBitsInstr, schkRefsInstr, schkBitRefsInstr,
            schkBitsQInstr, schkRefsQInstr, schkBitRefsQInstr, .cellOp .pldRefVar, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/split-neighbor" s0 (.cellOp (.split false)) 16
        let s2 ← expectDecodeStep "decode/schkbits" s1 schkBitsInstr 16
        let s3 ← expectDecodeStep "decode/schkrefs" s2 schkRefsInstr 16
        let s4 ← expectDecodeStep "decode/schkbitrefs" s3 schkBitRefsInstr 16
        let s5 ← expectDecodeStep "decode/schkbitsq" s4 schkBitsQInstr 16
        let s6 ← expectDecodeStep "decode/schkrefsq" s5 schkRefsQInstr 16
        let s7 ← expectDecodeStep "decode/schkbitrefsq" s6 schkBitRefsQInstr 16
        let s8 ← expectDecodeStep "decode/pldrefvar-right-neighbor" s7 (.cellOp .pldRefVar) 16
        let s9 ← expectDecodeStep "decode/tail-add" s8 .add 8
        if s9.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s9.bitsRemaining} bits remaining")

        let schkCode ←
          match assembleCp0 [schkBitsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/schkbits failed: {e}")
        if schkCode.bits = natToBits 0xd741 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/schkbits: expected 0xd741, got bits {schkCode.bits}")
        if schkCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/schkbits: expected 16 bits, got {schkCode.bits.size}")

        let schkQCode ←
          match assembleCp0 [schkBitsQInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/schkbitsq failed: {e}")
        if schkQCode.bits = natToBits 0xd745 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/schkbitsq: expected 0xd745, got bits {schkQCode.bits}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd739 16
            ++ natToBits 0xd741 16
            ++ natToBits 0xd745 16
            ++ natToBits 0xd748 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-left-boundary-xctos" r0 .xctos 16
        let r2 ← expectDecodeStep "decode/raw-schkbits" r1 schkBitsInstr 16
        let r3 ← expectDecodeStep "decode/raw-schkbitsq" r2 schkBitsQInstr 16
        let r4 ← expectDecodeStep "decode/raw-right-boundary-pldrefvar" r3 (.cellOp .pldRefVar) 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
  ]
  oracle := #[
    mkSchkBitsCase "ok/empty-bits0" (natStack slice0 0),
    mkSchkBitsCase "ok/one-bit-bits0" (natStack slice1 0),
    mkSchkBitsCase "ok/one-bit-bits1" (natStack slice1 1),
    mkSchkBitsCase "ok/exact-3" (natStack slice3 3),
    mkSchkBitsCase "ok/refs-ignored-6" (natStack slice6Refs2 6),
    mkSchkBitsCase "ok/300-with-refs-bits-300" (natStack (mkSlice (Array.replicate 300 true) #[refLeafA, refLeafB]) 300),
    mkSchkBitsCase "ok/high-900" (natStack slice900 900),
    mkSchkBitsCase "ok/high-255" (natStack slice255 255),
    mkSchkBitsCase "ok/high-300" (natStack slice300 300),
    mkSchkBitsCase "ok/high-512" (natStack slice512 512),
    mkSchkBitsCase "ok/high-767" (natStack slice767 767),
    mkSchkBitsCase "ok/high-1023" (natStack slice1023 1023),
    mkSchkBitsCase "ok/deep-stack-null-below" #[.null, .slice slice3, intV 2],
    mkSchkBitsCase "ok/deep-stack-two-below" #[.cell refLeafA, .builder Builder.empty, .slice slice6Refs2, intV 4],

    mkSchkBitsCase "cellund/empty-plus-1" (natStack slice0 1),
    mkSchkBitsCase "cellund/exact-plus-1-on-3" (natStack slice3 4),
    mkSchkBitsCase "cellund/300-plus-1" (natStack slice300 301),
    mkSchkBitsCase "cellund/512-plus-1" (natStack slice512 513),
    mkSchkBitsCase "cellund/767-plus-1" (natStack slice767 768),
    mkSchkBitsCase "cellund/1022-plus-1" (natStack slice1022 1023),

    mkSchkBitsCase "underflow/empty" #[],
    mkSchkBitsCase "underflow/one-item-slice" #[.slice slice3],
    mkSchkBitsCase "underflow/one-item-int" #[intV 1],

    mkSchkBitsCase "type/top-not-int-null" #[.slice slice3, .null],
    mkSchkBitsCase "type/top-not-int-cell" #[.slice slice3, .cell refLeafA],
    mkSchkBitsCase "type/slice-arg-null" #[.null, intV 1],
    mkSchkBitsCase "type/slice-arg-builder" #[.builder Builder.empty, intV 1],

    mkSchkBitsCase "range/top-negative" #[.slice slice6Refs2, intV (-1)],
    mkSchkBitsCase "range/top-too-large-1024" #[.slice slice1023, intV 1024],
    mkSchkBitsCase "range/top-too-large-4096" #[.slice slice512, intV 4096],
    mkSchkBitsCase "range/order-before-slice-type" #[.null, intV (-1)],

    mkSchkBitsCase "gas/exact-cost-succeeds" (natStack slice3 0)
      #[.pushInt (.num schkBitsSetGasExact), .tonEnvOp .setGasLimit, schkBitsInstr],
    mkSchkBitsCase "gas/exact-minus-one-out-of-gas" (natStack slice3 0)
      #[.pushInt (.num schkBitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkBitsInstr]
  ]
  fuzz := #[
    { seed := 2026021019
      count := 500
      gen := genSchkBitsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCHKBITS
