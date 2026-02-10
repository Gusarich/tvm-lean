import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSLICEX

/-
LDSLICEX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadSliceX.lean` (`.loadSliceX prefetch quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.loadSliceX` encode: `0xd718 + args`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd718..0xd71b` decode to `.loadSliceX prefetch quiet`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_slice` + `exec_load_slice_common`, non-prefetch/non-quiet mode args=`0`).

Branch map used for this suite (`LDSLICEX` = prefetch=false, quiet=false):
- `checkUnderflow 2` before any pop;
- width pop via `popNatUpTo 1023` (`typeChk` for non-int, `rangeChk` for NaN/negative/>1023);
- `popSlice` type guard only after width succeeds;
- `haveBits width` split: success pushes `[subslice, remainder]`, failure throws `cellUnd`;
- dispatch fallback for non-`.loadSliceX`.

Key C++ alignment for args=`0`:
- `check_underflow(2)`;
- `pop_smallint_range(1023)` then `pop_cellslice()`;
- `!have(bits)` -> `cell_und`;
- success push order is fetched subslice first, then mutated remainder.
-/

private def ldslicexId : InstrId := { name := "LDSLICEX" }

private def ldslicexInstr : Instr := .loadSliceX false false

private def ldslicexOpcode : Nat := 0xd718

private def dispatchSentinel : Int := 442

private def mkLdslicexCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldslicexInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldslicexId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdslicexProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkLdslicexCase name stack program gasLimits fuel

private def runLdslicexDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadSliceX ldslicexInstr stack

private def runLdslicexDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadSliceX instr (VM.push (intV dispatchSentinel)) stack

private def ldslicexSetGasExact : Int :=
  computeExactGasBudget ldslicexInstr

private def ldslicexSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldslicexInstr

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 13 4) #[]

private def tailBits6 : BitString := natToBits 37 6

private def tailBits11 : BitString := natToBits 1337 11

private def tailBits17 : BitString := natToBits 99877 17

private def mkPatternBits (bitCount : Nat) : BitString := Id.run do
  let mut bits : BitString := #[]
  for idx in [0:bitCount] do
    let bit := ((idx % 2) == 0) || ((idx % 5) == 1)
    bits := bits.push bit
  return bits

private def mkPatternSlice (bitCount : Nat) : Slice :=
  mkSliceFromBits (mkPatternBits bitCount)

private def mkPatternSliceWithRefs (bitCount : Nat) (refs : Array Cell) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkPatternBits bitCount) refs)

private def expectedLoadedSlice (source : Slice) (width : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (source.readBits width) #[])

private def expectedSuccessStack
    (below : Array Value)
    (source : Slice)
    (width : Nat) : Array Value :=
  below ++ #[.slice (expectedLoadedSlice source width), .slice (source.advanceBits width)]

private def widthBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 768, 1022, 1023]

private def pickWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (widthBoundaryPool.size - 1)
  (widthBoundaryPool[idx]!, rng')

private def pickWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickWidthBoundary rng1
  else
    randNat rng1 0 1023

private def randBitString (bitCount : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:bitCount] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def mkRandomSlice
    (bitCount : Nat)
    (refs : Array Cell := #[])
    (rng0 : StdGen) : Slice × StdGen :=
  let (bits, rng1) := randBitString bitCount rng0
  let slice :=
    if refs.isEmpty then
      mkSliceFromBits bits
    else
      Slice.ofCell (Cell.mkOrdinary bits refs)
  (slice, rng1)

private def pickRefsPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let refs :=
    if pick = 0 then #[] else if pick = 1 then #[refLeafA] else if pick = 2 then #[refLeafB] else #[refLeafA, refLeafB]
  (refs, rng')

private def pickNoiseValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let noise : Value :=
    if pick = 0 then .null else if pick = 1 then intV 77 else if pick = 2 then .cell refLeafA else .cell refLeafB
  (noise, rng')

private def genLdslicexFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  if shape = 0 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdslicexCase s!"fuzz/ok/exact-width-{width}" #[.slice slice, intV width], rng3)
  else if shape = 1 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 64 (1023 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    (mkLdslicexCase s!"fuzz/ok/with-tail/width-{width}/extra-{extra}" #[.slice slice, intV width], rng4)
  else if shape = 2 then
    let (bitCount, rng2) := randNat rng1 0 128
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdslicexCase s!"fuzz/ok/width-zero/bits-{bitCount}" #[.slice slice, intV 0], rng3)
  else if shape = 3 then
    let (width, rng2) := pickWidthMixed rng1
    let (refs, rng3) := pickRefsPack rng2
    let extraCap := Nat.min 32 (1023 - width)
    let (extra, rng4) := randNat rng3 0 extraCap
    let (slice, rng5) := mkRandomSlice (width + extra) refs rng4
    (mkLdslicexCase s!"fuzz/ok/refs/width-{width}/refs-{refs.size}" #[.slice slice, intV width], rng5)
  else if shape = 4 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 32 (1023 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkLdslicexCase s!"fuzz/ok/deep-noise/width-{width}" #[noise, .slice slice, intV width], rng5)
  else if shape = 5 then
    let (availableBits, rng2) := randNat rng1 0 1022
    let width := availableBits + 1
    let (slice, rng3) := mkRandomSlice availableBits #[] rng2
    (mkLdslicexCase s!"fuzz/cellund/short-by-one/bits-{availableBits}" #[.slice slice, intV width], rng3)
  else if shape = 6 then
    let (width, rng2) := randNat rng1 1 1023
    (mkLdslicexCase s!"fuzz/cellund/empty-slice/width-{width}" #[.slice (mkSliceFromBits #[]), intV width], rng2)
  else if shape = 7 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdslicexCase s!"fuzz/range/negative-width/width-{width}" #[.slice slice, intV (-1)], rng3)
  else if shape = 8 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (delta, rng4) := randNat rng3 1 2048
    let tooLargeWidth : Int := Int.ofNat (1023 + delta)
    (mkLdslicexCase s!"fuzz/range/too-large-width-{tooLargeWidth}" #[.slice slice, intV tooLargeWidth], rng4)
  else if shape = 9 then
    let (width, rng2) := randNat rng1 0 64
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdslicexProgramCase "fuzz/range/width-nan-via-program"
      #[.slice slice]
      #[.pushInt .nan, ldslicexInstr], rng3)
  else if shape = 10 then
    (mkLdslicexCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 11 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkLdslicexCase "fuzz/underflow/one-item-slice" #[.slice (mkSliceFromBits #[])], rng2)
    else
      (mkLdslicexCase "fuzz/underflow/one-item-width" #[intV 0], rng2)
  else if shape = 12 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (badPick, rng4) := randNat rng3 0 2
    let badWidth : Value :=
      if badPick = 0 then .null else if badPick = 1 then .cell refLeafA else .slice (mkSliceFromBits #[])
    (mkLdslicexCase "fuzz/type/width-not-int" #[.slice slice, badWidth], rng4)
  else if shape = 13 then
    let (width, rng2) := pickWidthMixed rng1
    let (badPick, rng3) := randNat rng2 0 2
    let badSlice : Value :=
      if badPick = 0 then .null else if badPick = 1 then intV 9 else .cell refLeafB
    (mkLdslicexCase s!"fuzz/type/slice-not-slice/width-{width}" #[badSlice, intV width], rng3)
  else if shape = 14 then
    let (badPick, rng2) := randNat rng1 0 1
    let badSlice : Value := if badPick = 0 then .null else .cell refLeafA
    (mkLdslicexCase "fuzz/error-order/range-before-slice-type" #[badSlice, intV 2048], rng2)
  else if shape = 15 then
    let (bitCount, rng2) := randNat rng1 0 64
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdslicexCase "fuzz/gas/exact"
      #[.slice slice, intV 0]
      #[.pushInt (.num ldslicexSetGasExact), .tonEnvOp .setGasLimit, ldslicexInstr], rng3)
  else
    let (bitCount, rng2) := randNat rng1 0 64
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdslicexCase "fuzz/gas/exact-minus-one"
      #[.slice slice, intV 0]
      #[.pushInt (.num ldslicexSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldslicexInstr], rng3)

private def oracleSlice0 : Slice := mkSliceFromBits #[]

private def oracleSlice1 : Slice := mkPatternSlice 1

private def oracleSlice4 : Slice := mkPatternSlice 4

private def oracleSlice5 : Slice := mkPatternSlice 5

private def oracleSlice8 : Slice := mkPatternSlice 8

private def oracleSlice13 : Slice := mkPatternSlice 13

private def oracleSlice31 : Slice := mkPatternSlice 31

private def oracleSlice255 : Slice := mkPatternSlice 255

private def oracleSlice512 : Slice := mkPatternSlice 512

private def oracleSlice768 : Slice := mkPatternSlice 768

private def oracleSlice1022 : Slice := mkPatternSlice 1022

private def oracleSlice1023 : Slice := mkPatternSlice 1023

private def oracleSliceWithRefs6 : Slice := mkPatternSliceWithRefs 6 #[refLeafA, refLeafB]

private def oracleSliceWithRefs9 : Slice := mkPatternSliceWithRefs 9 #[refLeafA]

private def oracleSlice8Tail11 : Slice := mkSliceFromBits (mkPatternBits 8 ++ tailBits11)

private def oracleSlice512Tail17 : Slice := mkSliceFromBits (mkPatternBits 512 ++ tailBits17)

def suite : InstrSuite where
  id := ldslicexId
  unit := #[
    { name := "unit/direct/success-widths-order-deep-stack"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (0, mkPatternSlice 11),
            (1, mkPatternSlice 1),
            (3, mkPatternSlice 8),
            (8, mkSliceFromBits (mkPatternBits 8 ++ tailBits6)),
            (512, mkPatternSlice 700),
            (1023, mkPatternSlice 1023)
          ]
        for check in checks do
          let width := check.1
          let source := check.2
          expectOkStack s!"ok/width-{width}/bits-{source.bitsRemaining}"
            (runLdslicexDirect #[.slice source, intV width])
            (expectedSuccessStack #[] source width)

        let zeroWithRefs := mkPatternSliceWithRefs 9 #[refLeafA, refLeafB]
        expectOkStack "ok/width0-remainder-preserves-refs"
          (runLdslicexDirect #[.slice zeroWithRefs, intV 0])
          (expectedSuccessStack #[] zeroWithRefs 0)

        let deepSource := mkPatternSliceWithRefs 16 #[refLeafA, refLeafB]
        let deepPrefix : Array Value := #[.null, intV 99, .cell refLeafA]
        expectOkStack "ok/deep-stack-order-preserved"
          (runLdslicexDirect (deepPrefix ++ #[.slice deepSource, intV 4]))
          (expectedSuccessStack deepPrefix deepSource 4)

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 40) #[refLeafA, refLeafB]
        let partialSlice : Slice := { cell := partialCell, bitPos := 7, refPos := 1 }
        expectOkStack "ok/uses-slice-cursor-remainder"
          (runLdslicexDirect #[.slice partialSlice, intV 12])
          (expectedSuccessStack #[] partialSlice 12) }
    ,
    { name := "unit/direct/cellund-when-width-exceeds-bits"
      run := do
        expectErr "cellund/empty-width1"
          (runLdslicexDirect #[.slice (mkSliceFromBits #[]), intV 1]) .cellUnd
        expectErr "cellund/short-4-vs5"
          (runLdslicexDirect #[.slice (mkPatternSlice 4), intV 5]) .cellUnd
        expectErr "cellund/short-1022-vs1023"
          (runLdslicexDirect #[.slice (mkPatternSlice 1022), intV 1023]) .cellUnd
        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 24) #[refLeafA]
        let partialSlice : Slice := { cell := partialCell, bitPos := 15, refPos := 0 }
        expectErr "cellund/partial-slice-short"
          (runLdslicexDirect #[.slice partialSlice, intV 10]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-bounds-and-error-order"
      run := do
        expectErr "underflow/empty" (runLdslicexDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runLdslicexDirect #[.slice (mkPatternSlice 3)]) .stkUnd
        expectErr "underflow/one-item-width"
          (runLdslicexDirect #[intV 7]) .stkUnd
        expectErr "underflow/one-item-null"
          (runLdslicexDirect #[.null]) .stkUnd

        expectErr "type/width-not-int-null"
          (runLdslicexDirect #[.slice (mkPatternSlice 3), .null]) .typeChk
        expectErr "type/width-not-int-cell"
          (runLdslicexDirect #[.slice (mkPatternSlice 3), .cell refLeafA]) .typeChk
        expectErr "type/slice-not-slice-after-valid-width"
          (runLdslicexDirect #[.null, intV 0]) .typeChk

        expectErr "range/width-negative"
          (runLdslicexDirect #[.slice (mkPatternSlice 3), intV (-1)]) .rangeChk
        expectErr "range/width-too-large"
          (runLdslicexDirect #[.slice (mkPatternSlice 3), intV 1024]) .rangeChk
        expectErr "range/width-nan"
          (runLdslicexDirect #[.slice (mkPatternSlice 3), .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-type"
          (runLdslicexDirect #[.null, intV 2048]) .rangeChk
        expectErr "error-order/width-type-before-slice-type"
          (runLdslicexDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[
          ldslicexInstr,
          .loadSliceX true false,
          .loadSliceX false true,
          .loadSliceX true true,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldslicex" s0 ldslicexInstr 16
        let s2 ← expectDecodeStep "decode/pldslicex-neighbor" s1 (.loadSliceX true false) 16
        let s3 ← expectDecodeStep "decode/ldslicexq-neighbor" s2 (.loadSliceX false true) 16
        let s4 ← expectDecodeStep "decode/pldslicexq-neighbor" s3 (.loadSliceX true true) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [ldslicexInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits ldslicexOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldslicex: expected 0xd718 16-bit encoding, got bit-length {singleCode.bits.size}")

        let rawSlice := mkSliceFromBits (natToBits ldslicexOpcode 16)
        let rawRest ← expectDecodeStep "decode/raw-0xd718" rawSlice ldslicexInstr 16
        if rawRest.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {rawRest.bitsRemaining} bits remaining")

        let fixedCode ←
          match assembleCp0 [.loadSliceFixed false false 1] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble fixed failed: {e}")
        let fixedSlice := Slice.ofCell fixedCode
        let fixedRest ← expectDecodeStep "decode/loadslicefixed-neighbor" fixedSlice (.loadSliceFixed false false 1) 24
        if fixedRest.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/fixed-end: expected exhausted slice, got {fixedRest.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-loadslicex-add"
          (runLdslicexDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-loadslicex-fixed-neighbor"
          (runLdslicexDispatchFallback (.loadSliceFixed false false 8) #[intV 9])
          #[intV 9, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdslicexCase "ok/width0-empty-slice" #[.slice oracleSlice0, intV 0],
    mkLdslicexCase "ok/width0-nonempty-slice" #[.slice oracleSlice13, intV 0],
    mkLdslicexCase "ok/width1-exact" #[.slice oracleSlice1, intV 1],
    mkLdslicexCase "ok/width3-of-5" #[.slice oracleSlice5, intV 3],
    mkLdslicexCase "ok/width8-exact" #[.slice oracleSlice8, intV 8],
    mkLdslicexCase "ok/width8-with-tail" #[.slice oracleSlice8Tail11, intV 8],
    mkLdslicexCase "ok/width31-exact" #[.slice oracleSlice31, intV 31],
    mkLdslicexCase "ok/width255-exact" #[.slice oracleSlice255, intV 255],
    mkLdslicexCase "ok/width512-exact" #[.slice oracleSlice512, intV 512],
    mkLdslicexCase "ok/width512-with-tail" #[.slice oracleSlice512Tail17, intV 512],
    mkLdslicexCase "ok/width768-exact" #[.slice oracleSlice768, intV 768],
    mkLdslicexCase "ok/width1022-exact" #[.slice oracleSlice1022, intV 1022],
    mkLdslicexCase "ok/width1023-exact" #[.slice oracleSlice1023, intV 1023],
    mkLdslicexCase "ok/refs-in-input-slice" #[.slice oracleSliceWithRefs9, intV 4],
    mkLdslicexCase "ok/deep-stack-preserve-noise"
      #[.null, .cell refLeafB, .slice oracleSlice13, intV 5],

    mkLdslicexCase "cellund/empty-width1" #[.slice oracleSlice0, intV 1],
    mkLdslicexCase "cellund/short-4-vs5" #[.slice oracleSlice4, intV 5],
    mkLdslicexCase "cellund/short-1022-vs1023" #[.slice oracleSlice1022, intV 1023],
    mkLdslicexCase "cellund/refs-short-6-vs7" #[.slice oracleSliceWithRefs6, intV 7],

    mkLdslicexCase "range/width-negative" #[.slice oracleSlice13, intV (-1)],
    mkLdslicexCase "range/width-too-large-1024" #[.slice oracleSlice13, intV 1024],
    mkLdslicexCase "range/width-too-large-4096" #[.slice oracleSlice13, intV 4096],
    mkLdslicexProgramCase "range/width-nan-via-program"
      #[.slice oracleSlice13]
      #[.pushInt .nan, ldslicexInstr],

    mkLdslicexCase "underflow/empty" #[],
    mkLdslicexCase "underflow/one-item-slice" #[.slice oracleSlice13],
    mkLdslicexCase "underflow/one-item-width" #[intV 0],

    mkLdslicexCase "type/width-top-null" #[.slice oracleSlice13, .null],
    mkLdslicexCase "type/width-top-cell" #[.slice oracleSlice13, .cell refLeafA],
    mkLdslicexCase "type/slice-not-slice-after-valid-width" #[.null, intV 0],

    mkLdslicexCase "error-order/range-before-slice-type" #[.null, intV 2048],
    mkLdslicexCase "error-order/width-type-before-slice-type" #[.null, .null],

    mkLdslicexCase "gas/exact-cost-succeeds"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num ldslicexSetGasExact), .tonEnvOp .setGasLimit, ldslicexInstr],
    mkLdslicexCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num ldslicexSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldslicexInstr]
  ]
  fuzz := #[
    { seed := 2026021014
      count := 320
      gen := genLdslicexFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSLICEX
