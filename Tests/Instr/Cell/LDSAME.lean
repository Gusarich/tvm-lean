import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSAME

/-
LDSAME branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LdSame.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDSAME` encode: `0xd762`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd762` decode to `.cellOp .ldSame`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_same(..., "LDSAME", -1)`; `pop_smallint_range(1)` then `pop_cellslice`).

Branch map used for this suite:
- Lean LDSAME path: 7 branch sites / 12 terminal outcomes
  (opcode guard; `checkUnderflow 2`; selector pop (`popNatUpTo 1`) type/range/success;
   slice pop type/success; selector bit choice (`0` / `1`); `n > 0` advance split; success push order).
- C++ LDSAME path: aligned outcomes
  (`check_underflow(2)`; selector `pop_smallint_range(1)`; `pop_cellslice`;
   `count_leading(x)` for `x ∈ {0,1}`; conditional advance; pushes).

Key risk areas:
- stack order is `... slice b` (`b` on top);
- selector bounds (`b ∈ {0,1}`) must fail before slice type checks;
- both bit choices must match C++ (`0` counts leading zeroes, `1` counts leading ones);
- refs are preserved (only bit cursor moves), including empty-bit slices with refs.
-/

private def ldsameId : InstrId := { name := "LDSAME" }

private def ldsameInstr : Instr :=
  .cellOp .ldSame

private def execCellOpLdsameOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLdSame op next
  | _ => next

private def mkLdsameCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldsameInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldsameId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdsameProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldsameId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdsameDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpLdsameOnly ldsameInstr stack

private def runLdsameDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpLdsameOnly instr (VM.push (intV 762)) stack

private def ldsameSetGasExact : Int :=
  computeExactGasBudget ldsameInstr

private def ldsameSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldsameInstr

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3)

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 13 4)

private def mkLdsameSliceLeading (b : Bool) (n : Nat) (tail : BitString := #[]) : Slice :=
  mkSliceFromBits (Array.replicate n b ++ tail)

private def mkLdsameSlicePrefixStop (b : Bool) (n : Nat) (tail : BitString := #[]) : Slice :=
  mkSliceFromBits (Array.replicate n b ++ #[!b] ++ tail)

private def mkLdsameSliceImmediateMismatch (b : Bool) (tail : BitString := #[]) : Slice :=
  mkSliceFromBits (#[!b] ++ tail)

private def mkLdsameSliceWithRefs (bits : BitString) (refs : Array Cell := #[refLeafA]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkLdsameSliceLeadingWithRefs
    (b : Bool)
    (n : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[refLeafA]) : Slice :=
  mkLdsameSliceWithRefs (Array.replicate n b ++ tail) refs

private def mkLdsameStack (s : Slice) (bNat : Nat) : Array Value :=
  #[.slice s, intV bNat]

private def tailBits6 : BitString := natToBits 37 6

private def tailBits9 : BitString := natToBits 345 9

private def sliceEmpty : Slice :=
  mkSliceFromBits #[]

private def sliceZeroImmediateMismatch : Slice :=
  mkLdsameSliceImmediateMismatch false tailBits11

private def sliceOneImmediateMismatch : Slice :=
  mkLdsameSliceImmediateMismatch true tailBits11

private def sliceZeroPrefix4 : Slice :=
  mkLdsameSlicePrefixStop false 4 tailBits6

private def sliceOnePrefix5 : Slice :=
  mkLdsameSlicePrefixStop true 5 tailBits6

private def sliceAllZeroes1023 : Slice :=
  mkLdsameSliceLeading false 1023

private def sliceAllOnes1023 : Slice :=
  mkLdsameSliceLeading true 1023

private def refsOnlySlice : Slice :=
  mkLdsameSliceWithRefs #[] #[refLeafA, refLeafB]

private def refsLeadingZero4 : Slice :=
  mkLdsameSliceLeadingWithRefs false 4 #[true, false, true] #[refLeafA, refLeafB]

private def refsLeadingOne3 : Slice :=
  mkLdsameSliceLeadingWithRefs true 3 #[false, true] #[refLeafA]

private def leadLenPoolAny : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 1023]

private def leadLenPoolStop : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 1022]

private def pickFromPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickTailBitsUpTo (rng0 : StdGen) (maxWidth : Nat) : BitString × StdGen :=
  let widthCap := Nat.min maxWidth 16
  let (width, rng1) := randNat rng0 0 widthCap
  let maxVal : Nat := (1 <<< width) - 1
  let (v, rng2) := randNat rng1 0 maxVal
  (natToBits v width, rng2)

private def pickSelectorBit (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 1

private def pickRefs (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafB]
    else #[refLeafA, refLeafB]
  (refs, rng')

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 59
    else if pick = 2 then .cell Cell.empty
    else .builder Builder.empty
  (noise, rng')

private def genLdsameFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let (n, rng2) := pickFromPool rng1 leadLenPoolAny
    (mkLdsameCase s!"fuzz/ok/all-zeros/len-{n}" (mkLdsameStack (mkLdsameSliceLeading false n) 0), rng2)
  else if shape = 1 then
    let (n, rng2) := pickFromPool rng1 leadLenPoolAny
    (mkLdsameCase s!"fuzz/ok/all-ones/len-{n}" (mkLdsameStack (mkLdsameSliceLeading true n) 1), rng2)
  else if shape = 2 then
    let (n, rng2) := pickFromPool rng1 leadLenPoolStop
    let maxTail : Nat := 1023 - (n + 1)
    let (tail, rng3) := pickTailBitsUpTo rng2 maxTail
    (mkLdsameCase s!"fuzz/ok/b0/prefix-stop/len-{n}"
      (mkLdsameStack (mkLdsameSlicePrefixStop false n tail) 0), rng3)
  else if shape = 3 then
    let (n, rng2) := pickFromPool rng1 leadLenPoolStop
    let maxTail : Nat := 1023 - (n + 1)
    let (tail, rng3) := pickTailBitsUpTo rng2 maxTail
    (mkLdsameCase s!"fuzz/ok/b1/prefix-stop/len-{n}"
      (mkLdsameStack (mkLdsameSlicePrefixStop true n tail) 1), rng3)
  else if shape = 4 then
    let (tail, rng2) := pickTailBitsUpTo rng1 1022
    (mkLdsameCase s!"fuzz/ok/b0/immediate-mismatch/tail-{tail.size}"
      (mkLdsameStack (mkLdsameSliceImmediateMismatch false tail) 0), rng2)
  else if shape = 5 then
    let (tail, rng2) := pickTailBitsUpTo rng1 1022
    (mkLdsameCase s!"fuzz/ok/b1/immediate-mismatch/tail-{tail.size}"
      (mkLdsameStack (mkLdsameSliceImmediateMismatch true tail) 1), rng2)
  else if shape = 6 then
    (mkLdsameCase "fuzz/ok/b0-empty" (mkLdsameStack sliceEmpty 0), rng1)
  else if shape = 7 then
    (mkLdsameCase "fuzz/ok/b1-empty" (mkLdsameStack sliceEmpty 1), rng1)
  else if shape = 8 then
    let (bNat, rng2) := pickSelectorBit rng1
    let (refs, rng3) := pickRefs rng2
    (mkLdsameCase s!"fuzz/ok/refs-only/b-{bNat}/refs-{refs.size}"
      (mkLdsameStack (mkLdsameSliceWithRefs #[] refs) bNat), rng3)
  else if shape = 9 then
    let (bNat, rng2) := pickSelectorBit rng1
    let b : Bool := bNat = 1
    let (n, rng3) := randNat rng2 1 48
    let (tail, rng4) := pickTailBitsUpTo rng3 12
    let (refs, rng5) := pickRefs rng4
    (mkLdsameCase s!"fuzz/ok/refs-prefix/b-{bNat}/len-{n}/refs-{refs.size}"
      (mkLdsameStack (mkLdsameSliceLeadingWithRefs b n tail refs) bNat), rng5)
  else if shape = 10 then
    let (bNat, rng2) := pickSelectorBit rng1
    let b : Bool := bNat = 1
    let (n, rng3) := pickFromPool rng2 leadLenPoolStop
    let maxTail : Nat := 1023 - (n + 1)
    let (tail, rng4) := pickTailBitsUpTo rng3 maxTail
    let (noise, rng5) := pickNoise rng4
    (mkLdsameCase s!"fuzz/ok/deep-stack/b-{bNat}/len-{n}"
      #[noise, .slice (mkLdsameSlicePrefixStop b n tail), intV bNat], rng5)
  else if shape = 11 then
    (mkLdsameCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    let (bNat, rng2) := pickSelectorBit rng1
    (mkLdsameCase s!"fuzz/underflow/one-item-slice/b-{bNat}" #[.slice sliceEmpty], rng2)
  else if shape = 13 then
    (mkLdsameCase "fuzz/type/top-not-int" #[.slice sliceZeroPrefix4, .null], rng1)
  else if shape = 14 then
    (mkLdsameCase "fuzz/range/top-negative" #[.slice sliceOnePrefix5, intV (-1)], rng1)
  else if shape = 15 then
    (mkLdsameCase "fuzz/range/top-overflow-2" #[.slice sliceZeroPrefix4, intV 2], rng1)
  else if shape = 16 then
    (mkLdsameCase "fuzz/type/slice-after-valid-selector" #[.null, intV 1], rng1)
  else if shape = 17 then
    let (bNat, rng2) := pickSelectorBit rng1
    let b : Bool := bNat = 1
    let (n, rng3) := randNat rng2 0 64
    let (tail, rng4) := pickTailBitsUpTo rng3 16
    (mkLdsameCase "fuzz/gas/exact"
      (mkLdsameStack (mkLdsameSliceLeading b n tail) bNat)
      #[.pushInt (.num ldsameSetGasExact), .tonEnvOp .setGasLimit, ldsameInstr], rng4)
  else if shape = 18 then
    let (bNat, rng2) := pickSelectorBit rng1
    let b : Bool := bNat = 1
    let (n, rng3) := randNat rng2 0 64
    let (tail, rng4) := pickTailBitsUpTo rng3 16
    (mkLdsameCase "fuzz/gas/exact-minus-one"
      (mkLdsameStack (mkLdsameSliceLeading b n tail) bNat)
      #[.pushInt (.num ldsameSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldsameInstr], rng4)
  else
    (mkLdsameProgramCase "fuzz/range/top-nan-via-program"
      #[.slice sliceZeroPrefix4] #[.pushInt .nan, ldsameInstr], rng1)

def suite : InstrSuite where
  id := ldsameId
  unit := #[
    { name := "unit/direct/success-bit-choices-boundaries-and-order"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (0, sliceEmpty),
            (1, sliceEmpty),
            (0, sliceZeroImmediateMismatch),
            (1, sliceOneImmediateMismatch),
            (0, sliceZeroPrefix4),
            (1, sliceOnePrefix5),
            (0, mkLdsameSliceLeading false 63),
            (1, mkLdsameSliceLeading true 63),
            (0, sliceAllZeroes1023),
            (1, sliceAllOnes1023),
            (0, refsOnlySlice),
            (1, refsOnlySlice),
            (0, refsLeadingZero4),
            (1, refsLeadingOne3)
          ]
        for c in checks do
          let bNat := c.1
          let s := c.2
          let b : Bool := bNat = 1
          let n := s.countLeading b
          let rem := if n > 0 then s.advanceBits n else s
          expectOkStack s!"ok/b-{bNat}/bits-{s.bitsRemaining}"
            (runLdsameDirect (mkLdsameStack s bNat))
            #[intV n, .slice rem]

        let deep := mkLdsameSlicePrefixStop true 6 tailBits9
        let deepN := deep.countLeading true
        expectOkStack "ok/deep-stack-order-preserved"
          (runLdsameDirect #[.null, intV (-9), .slice deep, intV 1])
          #[.null, intV (-9), intV deepN, .slice (deep.advanceBits deepN)] }
    ,
    { name := "unit/direct/underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty" (runLdsameDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice" (runLdsameDirect #[.slice sliceEmpty]) .stkUnd
        expectErr "underflow/one-item-int" (runLdsameDirect #[intV 1]) .stkUnd

        expectErr "type/top-null" (runLdsameDirect #[.slice sliceEmpty, .null]) .typeChk
        expectErr "type/top-cell" (runLdsameDirect #[.slice sliceEmpty, .cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runLdsameDirect #[.slice sliceEmpty, .builder Builder.empty]) .typeChk

        expectErr "range/top-negative"
          (runLdsameDirect #[.slice sliceZeroPrefix4, intV (-1)]) .rangeChk
        expectErr "range/top-overflow-2"
          (runLdsameDirect #[.slice sliceZeroPrefix4, intV 2]) .rangeChk
        expectErr "range/top-nan"
          (runLdsameDirect #[.slice sliceZeroPrefix4, .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-type"
          (runLdsameDirect #[.null, intV 2]) .rangeChk
        expectErr "error-order/slice-type-after-valid-selector0"
          (runLdsameDirect #[.null, intV 0]) .typeChk
        expectErr "error-order/slice-type-after-valid-selector1"
          (runLdsameDirect #[.cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-and-invalid-fallback"
      run := do
        let program : Array Instr := #[ldsameInstr, .cellOp .ldOnes, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldsame" s0 ldsameInstr 16
        let s2 ← expectDecodeStep "decode/neighbor-ldones" s1 (.cellOp .ldOnes) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        let invalid := mkSliceFromBits (natToBits 0xd763 16)
        match decodeCp0WithBits invalid with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/invalid-0xd763: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/invalid-0xd763: expected failure, got {reprStr instr} ({bits} bits)") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runLdsameDispatchFallback .add #[.null])
          #[.null, intV 762]
        expectOkStack "dispatch/other-cellop"
          (runLdsameDispatchFallback (.cellOp .ldZeroes) #[intV (-3)])
          #[intV (-3), intV 762] }
  ]
  oracle := #[
    mkLdsameCase "ok/b0-empty" (mkLdsameStack sliceEmpty 0),
    mkLdsameCase "ok/b1-empty" (mkLdsameStack sliceEmpty 1),
    mkLdsameCase "ok/b0-immediate-mismatch" (mkLdsameStack sliceZeroImmediateMismatch 0),
    mkLdsameCase "ok/b1-immediate-mismatch" (mkLdsameStack sliceOneImmediateMismatch 1),
    mkLdsameCase "ok/b0-prefix1-stop" (mkLdsameStack (mkLdsameSlicePrefixStop false 1) 0),
    mkLdsameCase "ok/b1-prefix1-stop" (mkLdsameStack (mkLdsameSlicePrefixStop true 1) 1),
    mkLdsameCase "ok/b0-prefix4-tail6" (mkLdsameStack sliceZeroPrefix4 0),
    mkLdsameCase "ok/b1-prefix5-tail6" (mkLdsameStack sliceOnePrefix5 1),
    mkLdsameCase "ok/b0-prefix15-tail11"
      (mkLdsameStack (mkLdsameSlicePrefixStop false 15 tailBits11) 0),
    mkLdsameCase "ok/b1-prefix31-tail9"
      (mkLdsameStack (mkLdsameSlicePrefixStop true 31 tailBits9) 1),
    mkLdsameCase "ok/b0-all-zeroes-63" (mkLdsameStack (mkLdsameSliceLeading false 63) 0),
    mkLdsameCase "ok/b1-all-ones-63" (mkLdsameStack (mkLdsameSliceLeading true 63) 1),
    mkLdsameCase "ok/b0-all-zeroes-1023" (mkLdsameStack sliceAllZeroes1023 0),
    mkLdsameCase "ok/b1-all-ones-1023" (mkLdsameStack sliceAllOnes1023 1),
    mkLdsameCase "ok/b0-refs-only" (mkLdsameStack refsOnlySlice 0),
    mkLdsameCase "ok/b1-refs-only" (mkLdsameStack refsOnlySlice 1),
    mkLdsameCase "ok/b0-refs-leading-prefix" (mkLdsameStack refsLeadingZero4 0),
    mkLdsameCase "ok/b1-refs-leading-prefix" (mkLdsameStack refsLeadingOne3 1),
    mkLdsameCase "ok/deep-stack-null-below" #[.null, .slice sliceZeroPrefix4, intV 0],
    mkLdsameCase "ok/deep-stack-cell-below" #[.cell Cell.empty, .slice sliceOnePrefix5, intV 1],

    mkLdsameCase "underflow/empty" #[],
    mkLdsameCase "underflow/one-item-slice" #[.slice sliceEmpty],
    mkLdsameCase "underflow/one-item-int" #[intV 1],

    mkLdsameCase "type/top-null" #[.slice sliceEmpty, .null],
    mkLdsameCase "type/top-cell" #[.slice sliceEmpty, .cell Cell.empty],
    mkLdsameCase "type/top-builder" #[.slice sliceEmpty, .builder Builder.empty],
    mkLdsameCase "type/slice-after-valid-b0" #[.null, intV 0],
    mkLdsameCase "type/slice-after-valid-b1" #[.cell Cell.empty, intV 1],

    mkLdsameCase "range/top-negative" #[.slice sliceZeroPrefix4, intV (-1)],
    mkLdsameCase "range/top-overflow-2" #[.slice sliceOnePrefix5, intV 2],
    mkLdsameCase "range/b-before-slice-type" #[.null, intV 2],
    mkLdsameProgramCase "range/top-nan-via-program"
      #[.slice sliceZeroPrefix4] #[.pushInt .nan, ldsameInstr],

    mkLdsameProgramCase "gas/exact-cost-succeeds"
      #[.slice sliceZeroPrefix4, intV 0]
      #[.pushInt (.num ldsameSetGasExact), .tonEnvOp .setGasLimit, ldsameInstr],
    mkLdsameProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice sliceOnePrefix5, intV 1]
      #[.pushInt (.num ldsameSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldsameInstr]
  ]
  fuzz := #[
    { seed := 2026021044
      count := 320
      gen := genLdsameFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSAME
