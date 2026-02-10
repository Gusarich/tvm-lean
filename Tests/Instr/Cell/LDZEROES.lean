import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDZEROES

/-
LDZEROES branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LdZeroes.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (dispatch chain for `.cellOp`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDZEROES` encode: `0xd760`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd760` decode to `.cellOp .ldZeroes`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_same(..., x=0)` for `LDZEROES`).

Branch map used for this suite:
- Lean LDZEROES path: 6 branch sites / 7 terminal outcomes
  (instr guard; cell-op guard; pop-slice underflow/type/success; `n>0` advance split;
   success push order `n` then remainder).
- C++ LDZEROES path: aligned outcomes
  (`check_underflow(1)`; `pop_cellslice`; `count_leading(0)`; conditional advance; pushes).

Notable property:
- LDZEROES has no explicit range/cell-shape rejection branch; failure surface is only
  stack underflow/type at `popSlice`.
-/

private def ldzeroesId : InstrId := { name := "LDZEROES" }

private def ldzeroesInstr : Instr := .cellOp .ldZeroes

private def execInstrCellOpLdZeroesOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLdZeroes op next
  | _ => next

private def mkLdzeroesCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldzeroesInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldzeroesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdzeroesProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldzeroesId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdzeroesDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLdZeroesOnly ldzeroesInstr stack

private def runLdzeroesDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLdZeroesOnly instr (VM.push (intV 434)) stack

private def ldzeroesSetGasExact : Int :=
  computeExactGasBudget ldzeroesInstr

private def ldzeroesSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldzeroesInstr

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3)

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 13 4)

private def mkLdzeroesSlice (zeros : Nat) (tail : BitString := #[]) : Slice :=
  mkSliceFromBits (Array.replicate zeros false ++ tail)

private def mkLdzeroesSliceWithRefs
    (zeros : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[refLeafA]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (Array.replicate zeros false ++ tail) refs)

private def tailBits6 : BitString := natToBits 37 6

private def tailBits11 : BitString := natToBits 1337 11

private def tailBits13 : BitString := natToBits 4242 13

private def refsOnlySlice : Slice :=
  mkLdzeroesSliceWithRefs 0 #[] #[refLeafA, refLeafB]

private def refsZeroPrefixSlice : Slice :=
  mkLdzeroesSliceWithRefs 4 #[true, false, true] #[refLeafA, refLeafB]

private def refsAllZero32Slice : Slice :=
  mkLdzeroesSliceWithRefs 32 #[] #[refLeafA]

private def ldzeroesZeroPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 511, 1023]

private def pickZeroLen (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ldzeroesZeroPool.size - 1)
  (ldzeroesZeroPool[idx]!, rng')

private def pickTailBitsUpTo (rng0 : StdGen) (maxWidth : Nat) : BitString × StdGen :=
  let widthCap := Nat.min maxWidth 16
  let (width, rng1) := randNat rng0 0 widthCap
  let maxVal : Nat := (1 <<< width) - 1
  let (v, rng2) := randNat rng1 0 maxVal
  (natToBits v width, rng2)

private def pickRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafB]
    else #[refLeafA, refLeafB]
  (refs, rng')

private def genLdzeroesFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    let (zeros, rng2) := pickZeroLen rng1
    (mkLdzeroesCase s!"fuzz/ok/all-zeros-{zeros}" #[.slice (mkLdzeroesSlice zeros)], rng2)
  else if shape = 1 then
    let (zeros0, rng2) := pickZeroLen rng1
    let zeros := if zeros0 = 1023 then 1022 else zeros0
    let (tail, rng3) := pickTailBitsUpTo rng2 (1022 - zeros)
    let s := mkLdzeroesSlice zeros (#[true] ++ tail)
    (mkLdzeroesCase s!"fuzz/ok/prefix-zeros-{zeros}-then-one" #[.slice s], rng3)
  else if shape = 2 then
    let (tail, rng2) := pickTailBitsUpTo rng1 32
    (mkLdzeroesCase s!"fuzz/ok/no-leading-zero/tail-{tail.size}"
      #[.slice (mkSliceFromBits (#[true] ++ tail))], rng2)
  else if shape = 3 then
    let (refs, rng2) := pickRefPack rng1
    (mkLdzeroesCase s!"fuzz/ok/refs-only/refs-{refs.size}"
      #[.slice (mkLdzeroesSliceWithRefs 0 #[] refs)], rng2)
  else if shape = 4 then
    let (zeros, rng2) := randNat rng1 1 64
    let (tail, rng3) := pickTailBitsUpTo rng2 8
    let (refs, rng4) := pickRefPack rng3
    (mkLdzeroesCase s!"fuzz/ok/refs-prefix/zeros-{zeros}/refs-{refs.size}"
      #[.slice (mkLdzeroesSliceWithRefs zeros tail refs)], rng4)
  else if shape = 5 then
    let (zeros, rng2) := randNat rng1 0 48
    let (tail, rng3) := pickTailBitsUpTo rng2 12
    (mkLdzeroesCase s!"fuzz/ok/deep-stack/zeros-{zeros}"
      #[.null, intV 77, .slice (mkLdzeroesSlice zeros tail)], rng3)
  else if shape = 6 then
    (mkLdzeroesCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkLdzeroesCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 8 then
    (mkLdzeroesCase "fuzz/type/top-int" #[intV 12], rng1)
  else if shape = 9 then
    (mkLdzeroesCase "fuzz/type/top-cell" #[.cell Cell.empty], rng1)
  else if shape = 10 then
    (mkLdzeroesCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 11 then
    (mkLdzeroesCase "fuzz/type/deep-top-not-slice"
      #[.slice (mkLdzeroesSlice 1 #[true]), .null], rng1)
  else if shape = 12 then
    let (zeros, rng2) := randNat rng1 0 64
    let (tail, rng3) := pickTailBitsUpTo rng2 16
    (mkLdzeroesCase "fuzz/gas/exact"
      #[.slice (mkLdzeroesSlice zeros tail)]
      #[.pushInt (.num ldzeroesSetGasExact), .tonEnvOp .setGasLimit, ldzeroesInstr], rng3)
  else if shape = 13 then
    let (zeros, rng2) := randNat rng1 0 64
    let (tail, rng3) := pickTailBitsUpTo rng2 16
    (mkLdzeroesCase "fuzz/gas/exact-minus-one"
      #[.slice (mkLdzeroesSlice zeros tail)]
      #[.pushInt (.num ldzeroesSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldzeroesInstr], rng3)
  else
    (mkLdzeroesCase "fuzz/ok/max-zeros" #[.slice (mkLdzeroesSlice 1023)], rng1)

def suite : InstrSuite where
  id := ldzeroesId
  unit := #[
    { name := "unit/direct/success-order-and-prefix-consumption"
      run := do
        let checks : Array (Nat × BitString) :=
          #[
            (0, #[]),
            (1, #[]),
            (2, #[]),
            (3, #[true]),
            (7, tailBits6),
            (15, #[]),
            (255, #[]),
            (1023, #[])
          ]
        for c in checks do
          let zeros := c.1
          let tail := c.2
          let input := mkLdzeroesSlice zeros tail
          let rem := if zeros > 0 then input.advanceBits zeros else input
          expectOkStack s!"ok/zeros-{zeros}/tail-{tail.size}"
            (runLdzeroesDirect #[.slice input])
            #[intV zeros, .slice rem]

        let startsOne := mkSliceFromBits (#[true] ++ tailBits13)
        expectOkStack "ok/no-leading-zero-no-advance"
          (runLdzeroesDirect #[.slice startsOne])
          #[intV 0, .slice startsOne]

        let refsInput := refsZeroPrefixSlice
        expectOkStack "ok/refs-are-preserved"
          (runLdzeroesDirect #[.slice refsInput])
          #[intV 4, .slice (refsInput.advanceBits 4)]

        expectOkStack "ok/refs-only-no-bits"
          (runLdzeroesDirect #[.slice refsOnlySlice])
          #[intV 0, .slice refsOnlySlice]

        let shiftedInput := (mkLdzeroesSlice 8 #[true, false, true]).advanceBits 3
        expectOkStack "ok/shifted-slice-view-prefix"
          (runLdzeroesDirect #[.slice shiftedInput])
          #[intV 5, .slice (shiftedInput.advanceBits 5)]

        let shiftedRefsInput :=
          (mkLdzeroesSliceWithRefs 6 #[true, false] #[refLeafA, refLeafB]).advanceBits 2
        expectOkStack "ok/shifted-slice-view-with-refs"
          (runLdzeroesDirect #[.slice shiftedRefsInput])
          #[intV 4, .slice (shiftedRefsInput.advanceBits 4)]

        let deepInput := mkLdzeroesSlice 5 tailBits6
        expectOkStack "ok/deep-stack-order"
          (runLdzeroesDirect #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, intV 5, .slice (deepInput.advanceBits 5)] }
    ,
    { name := "unit/direct/underflow-type-failure-surface"
      run := do
        expectErr "underflow/empty" (runLdzeroesDirect #[]) .stkUnd
        expectErr "type/top-null" (runLdzeroesDirect #[.null]) .typeChk
        expectErr "type/top-int" (runLdzeroesDirect #[intV 1]) .typeChk
        expectErr "type/top-nan" (runLdzeroesDirect #[.int .nan]) .typeChk
        expectErr "type/top-cell" (runLdzeroesDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runLdzeroesDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdzeroesDirect #[.slice (mkLdzeroesSlice 1 #[true]), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let program : Array Instr := #[ldzeroesInstr, .cellOp .ldOnes, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldzeroes" s0 ldzeroesInstr 16
        let s2 ← expectDecodeStep "decode/adjacent-ldones" s1 (.cellOp .ldOnes) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runLdzeroesDispatchFallback .add #[.null])
          #[.null, intV 434]
        expectOkStack "dispatch/other-cellop"
          (runLdzeroesDispatchFallback (.cellOp .ldOnes) #[intV (-3)])
          #[intV (-3), intV 434] }
  ]
  oracle := #[
    -- Branch: `popSlice` success + `n = 0` (no cursor advance).
    mkLdzeroesCase "ok/empty-slice" #[.slice (mkLdzeroesSlice 0)],
    mkLdzeroesCase "ok/single-one-no-advance" #[.slice (mkSliceFromBits #[true])],
    mkLdzeroesCase "ok/no-leading-zero-alt-tail"
      #[.slice (mkSliceFromBits (#[true] ++ tailBits13))],
    mkLdzeroesCase "ok/no-leading-zero-then-many-zeros"
      #[.slice (mkSliceFromBits (#[true] ++ Array.replicate 48 false))],
    mkLdzeroesCase "ok/refs-only-no-bits" #[.slice refsOnlySlice],

    -- Branch: `popSlice` success + `n > 0` (advance by counted zero prefix).
    mkLdzeroesCase "ok/single-zero" #[.slice (mkLdzeroesSlice 1)],
    mkLdzeroesCase "ok/two-zeros-then-one" #[.slice (mkLdzeroesSlice 2 #[true])],
    mkLdzeroesCase "ok/three-zeros-tail6" #[.slice (mkLdzeroesSlice 3 tailBits6)],
    mkLdzeroesCase "ok/five-zeros-tail11" #[.slice (mkLdzeroesSlice 5 tailBits11)],
    mkLdzeroesCase "ok/all-zeros-15" #[.slice (mkLdzeroesSlice 15)],
    mkLdzeroesCase "ok/all-zeros-31" #[.slice (mkLdzeroesSlice 31)],
    mkLdzeroesCase "ok/all-zeros-255" #[.slice (mkLdzeroesSlice 255)],
    mkLdzeroesCase "ok/all-zeros-511" #[.slice (mkLdzeroesSlice 511)],
    mkLdzeroesCase "ok/all-zeros-1023" #[.slice (mkLdzeroesSlice 1023)],
    mkLdzeroesCase "ok/max-prefix-1022-then-one" #[.slice (mkLdzeroesSlice 1022 #[true])],
    mkLdzeroesCase "ok/prefix-8-then-one-tail"
      #[.slice (mkLdzeroesSlice 8 #[true, false, true])],
    mkLdzeroesCase "ok/deep-stack-null-below" #[.null, .slice (mkLdzeroesSlice 4 #[true, false])],
    mkLdzeroesCase "ok/deep-stack-two-below"
      #[intV (-7), .null, .slice (mkLdzeroesSlice 6 tailBits6)],
    mkLdzeroesCase "ok/refs-zero-prefix" #[.slice refsZeroPrefixSlice],
    mkLdzeroesCase "ok/refs-all-zeros-32" #[.slice refsAllZero32Slice],
    mkLdzeroesCase "ok/refs-prefix-6-then-one"
      #[.slice (mkLdzeroesSliceWithRefs 6 #[true, false] #[refLeafA, refLeafB])],

    -- Branch: failure surface of `popSlice` (underflow + type checks only).
    mkLdzeroesCase "underflow/empty" #[],
    mkLdzeroesCase "type/top-null" #[.null],
    mkLdzeroesCase "type/top-int" #[intV 7],
    mkLdzeroesProgramCase "type/program-nan-top" #[] #[.pushInt .nan, ldzeroesInstr],
    mkLdzeroesCase "type/top-cell" #[.cell Cell.empty],
    mkLdzeroesCase "type/top-builder" #[.builder Builder.empty],
    mkLdzeroesCase "type/deep-top-not-slice" #[.slice (mkLdzeroesSlice 1 #[true]), .null],

    -- Branch: exact opcode-cost gas boundary.
    mkLdzeroesProgramCase "gas/exact-cost-succeeds"
      #[.slice (mkLdzeroesSlice 7 tailBits6)]
      #[.pushInt (.num ldzeroesSetGasExact), .tonEnvOp .setGasLimit, ldzeroesInstr],
    mkLdzeroesProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkLdzeroesSlice 7 tailBits6)]
      #[.pushInt (.num ldzeroesSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldzeroesInstr]
  ]
  fuzz := #[
    { seed := 2026021011
      count := 320
      gen := genLdzeroesFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDZEROES
