import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDONES

/-
LDONES branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LdOnes.lean`
  - `TvmLean/Model/Cell/Primitives.lean` (`Slice.countLeading`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDONES` encode: `0xd761`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd761` decode to `.cellOp .ldOnes`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_same(..., "LDONES", 1)`; registered at opcode `0xd761`).

Branch map used for this suite:
- Lean LDONES path: 4 branch sites / 5 terminal outcomes
  (opcode guard; `popSlice` underflow/type; `n>0` advance split; success push order).
- C++ LDONES path: 4 branch sites / 5 aligned outcomes
  (`check_underflow(1)`; `pop_cellslice`; `n>0` advance split; success push order).

Key risk areas:
- result order must be `... n s'` (count first, then remainder slice);
- type/underflow checks happen before any data-dependent work;
- `n=0` must leave slice unchanged;
- refs are never consumed by LDONES (only bit cursor advances).
-/

private def ldonesId : InstrId := { name := "LDONES" }

private def ldonesInstr : Instr :=
  .cellOp .ldOnes

private def ldzeroesInstr : Instr :=
  .cellOp .ldZeroes

private def execCellOpLdOnesInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpLdOnes op next
  | _ => next

private def mkLdonesCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldonesInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldonesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdonesProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldonesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdonesDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpLdOnesInstr ldonesInstr stack

private def runLdonesDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpLdOnesInstr .add (VM.push (intV 761)) stack

private def ldonesSetGasExact : Int :=
  computeExactGasBudget ldonesInstr

private def ldonesSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldonesInstr

private def tailBits7 : BitString := natToBits 93 7

private def tailBits11 : BitString := natToBits 1337 11

private def mkSliceHeadZero (tail : BitString := #[]) : Slice :=
  mkSliceFromBits (#[false] ++ tail)

private def mkSliceLeadingOnes (ones : Nat) (appendZero : Bool := false) (tail : BitString := #[]) : Slice :=
  let bits : BitString :=
    Array.replicate ones true ++ (if appendZero then #[false] else #[]) ++ tail
  mkSliceFromBits bits

private def mkSliceWithRefs (bits : BitString) (refCount : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits (Array.replicate refCount Cell.empty))

private def sliceEmpty : Slice :=
  mkSliceFromBits #[]

private def sliceHeadZeroTail7 : Slice :=
  mkSliceHeadZero tailBits7

private def sliceSingleOne : Slice :=
  mkSliceLeadingOnes 1

private def slicePrefix3Stop : Slice :=
  mkSliceFromBits #[true, true, true, false, true, false]

private def slicePrefix8Tail : Slice :=
  mkSliceLeadingOnes 8 true tailBits7

private def sliceAllOnes17 : Slice :=
  mkSliceLeadingOnes 17

private def sliceAllOnes1023 : Slice :=
  mkSliceLeadingOnes 1023

private def sliceRefOnly2 : Slice :=
  mkSliceWithRefs #[] 2

private def sliceRefLeading3 : Slice :=
  mkSliceWithRefs #[true, true, true, false, true] 1

private def sliceDeepOrder : Slice :=
  mkSliceFromBits #[true, false, true, true]

private def onesLensAny : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 1023]

private def onesLensWithStop : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 1022]

private def pickFromNatPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 1 16
  let maxVal : Nat := (1 <<< width) - 1
  let (value, rng2) := randNat rng1 0 maxVal
  (natToBits value width, rng2)

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (k, rng') := randNat rng 0 3
  let v : Value :=
    if k = 0 then .null
    else if k = 1 then intV 19
    else if k = 2 then .cell Cell.empty
    else .builder Builder.empty
  (v, rng')

private def genLdonesFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    (mkLdonesCase "fuzz/ok/empty-slice" #[.slice sliceEmpty], rng1)
  else if shape = 1 then
    let (tail, rng2) := pickTailBits rng1
    (mkLdonesCase s!"fuzz/ok/head-zero/tail-{tail.size}" #[.slice (mkSliceHeadZero tail)], rng2)
  else if shape = 2 then
    let (ones, rng2) := pickFromNatPool rng1 onesLensAny
    (mkLdonesCase s!"fuzz/ok/all-ones/len-{ones}" #[.slice (mkSliceLeadingOnes ones)], rng2)
  else if shape = 3 then
    let (ones, rng2) := pickFromNatPool rng1 onesLensWithStop
    let (tail, rng3) := pickTailBits rng2
    let maxTail : Nat := 1023 - (ones + 1)
    let tail' := tail.take maxTail
    (mkLdonesCase s!"fuzz/ok/prefix-ones-stop-zero/ones-{ones}/tail-{tail.size}"
      #[.slice (mkSliceLeadingOnes ones true tail')], rng3)
  else if shape = 4 then
    let (tail, rng2) := pickTailBits rng1
    let (noise, rng3) := pickNoise rng2
    (mkLdonesCase s!"fuzz/ok/deep/head-zero/tail-{tail.size}"
      #[noise, .slice (mkSliceHeadZero tail)], rng3)
  else if shape = 5 then
    let (ones, rng2) := pickFromNatPool rng1 onesLensWithStop
    let (noise, rng3) := pickNoise rng2
    let maxTail : Nat := 1023 - (ones + 1)
    let tail := tailBits7.take maxTail
    (mkLdonesCase s!"fuzz/ok/deep/prefix-ones/ones-{ones}"
      #[noise, .slice (mkSliceLeadingOnes ones true tail)], rng3)
  else if shape = 6 then
    let (refs, rng2) := randNat rng1 1 4
    (mkLdonesCase s!"fuzz/ok/ref-only/refs-{refs}" #[.slice (mkSliceWithRefs #[] refs)], rng2)
  else if shape = 7 then
    let (refs, rng2) := randNat rng1 1 4
    let (ones, rng3) := pickFromNatPool rng2 onesLensWithStop
    (mkLdonesCase s!"fuzz/ok/ref-leading-ones/ones-{ones}/refs-{refs}"
      #[.slice (mkSliceWithRefs (Array.replicate ones true ++ #[false]) refs)], rng3)
  else if shape = 8 then
    (mkLdonesCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 9 then
    (mkLdonesCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 10 then
    (mkLdonesCase "fuzz/type/top-int" #[intV 0], rng1)
  else if shape = 11 then
    (mkLdonesCase "fuzz/type/top-cell" #[.cell Cell.empty], rng1)
  else if shape = 12 then
    (mkLdonesCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 13 then
    (mkLdonesCase "fuzz/type/deep-top-not-slice"
      #[.slice slicePrefix3Stop, .null], rng1)
  else
    (mkLdonesProgramCase "fuzz/type/program-nan-top"
      #[] #[.pushInt .nan, ldonesInstr], rng1)

def suite : InstrSuite where
  id := ldonesId
  unit := #[
    { name := "unit/direct/success-order-and-boundaries"
      run := do
        expectOkStack "ok/empty-slice"
          (runLdonesDirect #[.slice sliceEmpty])
          #[intV 0, .slice sliceEmpty]

        expectOkStack "ok/head-zero-no-advance"
          (runLdonesDirect #[.slice sliceHeadZeroTail7])
          #[intV 0, .slice sliceHeadZeroTail7]

        expectOkStack "ok/single-one-consumed"
          (runLdonesDirect #[.slice sliceSingleOne])
          #[intV 1, .slice (sliceSingleOne.advanceBits 1)]

        expectOkStack "ok/prefix-three-stops-at-zero"
          (runLdonesDirect #[.slice slicePrefix3Stop])
          #[intV 3, .slice (slicePrefix3Stop.advanceBits 3)]

        expectOkStack "ok/prefix-eight-with-tail"
          (runLdonesDirect #[.slice slicePrefix8Tail])
          #[intV 8, .slice (slicePrefix8Tail.advanceBits 8)]

        expectOkStack "ok/all-ones-17"
          (runLdonesDirect #[.slice sliceAllOnes17])
          #[intV 17, .slice (sliceAllOnes17.advanceBits 17)]

        expectOkStack "ok/all-ones-1023"
          (runLdonesDirect #[.slice sliceAllOnes1023])
          #[intV 1023, .slice (sliceAllOnes1023.advanceBits 1023)]

        expectOkStack "ok/ref-only-slice-no-shape-failure"
          (runLdonesDirect #[.slice sliceRefOnly2])
          #[intV 0, .slice sliceRefOnly2]

        expectOkStack "ok/refs-preserved-while-advancing"
          (runLdonesDirect #[.slice sliceRefLeading3])
          #[intV 3, .slice (sliceRefLeading3.advanceBits 3)]

        expectOkStack "ok/deep-stack-order-preserved"
          (runLdonesDirect #[.null, intV 77, .slice sliceDeepOrder])
          #[.null, intV 77, intV 1, .slice (sliceDeepOrder.advanceBits 1)] }
    ,
    { name := "unit/direct/underflow-type-and-no-range-branch"
      run := do
        expectErr "underflow/empty" (runLdonesDirect #[]) .stkUnd

        expectErr "type/top-null" (runLdonesDirect #[.null]) .typeChk
        expectErr "type/top-int" (runLdonesDirect #[intV 0]) .typeChk
        expectErr "type/top-nan-not-range" (runLdonesDirect #[.int .nan]) .typeChk
        expectErr "type/top-cell" (runLdonesDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runLdonesDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdonesDirect #[.slice slicePrefix3Stop, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[ldonesInstr, ldzeroesInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldones" s0 ldonesInstr 16
        let s2 ← expectDecodeStep "decode/ldzeroes-neighbor" s1 ldzeroesInstr 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-ldones-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdonesDispatchFallback #[.null])
          #[.null, intV 761] }
  ]
  oracle := #[
    mkLdonesCase "ok/empty-slice" #[.slice sliceEmpty],
    mkLdonesCase "ok/head-zero-tail7" #[.slice sliceHeadZeroTail7],
    mkLdonesCase "ok/single-one" #[.slice sliceSingleOne],
    mkLdonesCase "ok/prefix3-stop-zero" #[.slice slicePrefix3Stop],
    mkLdonesCase "ok/prefix8-tail7" #[.slice slicePrefix8Tail],
    mkLdonesCase "ok/all-ones-17" #[.slice sliceAllOnes17],
    mkLdonesCase "ok/all-ones-1023" #[.slice sliceAllOnes1023],
    mkLdonesCase "ok/ref-only-two-refs" #[.slice sliceRefOnly2],
    mkLdonesCase "ok/ref-leading-three" #[.slice sliceRefLeading3],
    mkLdonesCase "ok/with-tail11-head-zero" #[.slice (mkSliceHeadZero tailBits11)],
    mkLdonesCase "ok/deep-stack-null-below" #[.null, .slice slicePrefix8Tail],
    mkLdonesCase "ok/deep-stack-cell-below" #[.cell Cell.empty, .slice slicePrefix3Stop],

    mkLdonesCase "underflow/empty" #[],
    mkLdonesCase "type/top-null" #[.null],
    mkLdonesCase "type/top-int" #[intV 0],
    mkLdonesCase "type/top-cell" #[.cell Cell.empty],
    mkLdonesCase "type/top-builder" #[.builder Builder.empty],
    mkLdonesCase "type/deep-top-not-slice" #[.slice slicePrefix3Stop, .null],
    mkLdonesProgramCase "type/program-nan-top" #[] #[.pushInt .nan, ldonesInstr],

    mkLdonesCase "gas/exact-cost-succeeds" #[.slice slicePrefix8Tail]
      #[.pushInt (.num ldonesSetGasExact), .tonEnvOp .setGasLimit, ldonesInstr],
    mkLdonesCase "gas/exact-minus-one-out-of-gas" #[.slice slicePrefix8Tail]
      #[.pushInt (.num ldonesSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldonesInstr],

    mkLdonesCase "ok/ref-only-four-refs" #[.slice (mkSliceWithRefs #[] 4)],
    mkLdonesCase "ok/ref-leading-ones-four-refs"
      #[.slice (mkSliceWithRefs #[true, true, true, true, false] 4)]
  ]
  fuzz := #[
    { seed := 2026021031
      count := 320
      gen := genLdonesFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDONES
