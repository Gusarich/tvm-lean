import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSLICEXQ

/-
LDSLICEXQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadSliceX.lean` (`.loadSliceX prefetch quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.loadSliceX` encode: `0xd718 + args`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd718..0xd71b` decode to `.loadSliceX prefetch quiet`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_slice` + `exec_load_slice_common`).

Branch map for this suite (`LDSLICEXQ` = prefetch=false, quiet=true):
- `checkUnderflow 2` before any pop;
- width pop via `popNatUpTo 1023` (`typeChk` for non-int, `rangeChk` for NaN/negative/>1023);
- `popSlice` type guard only after width succeeds;
- `haveBits width` split:
  - success: push `[subslice, remainder, -1]`;
  - failure: no exception, push `[original slice, 0]`;
- dispatch fallback for non-`.loadSliceX`.

Key C++ alignment for args=`2` (quiet non-prefetch):
- `check_underflow(2)`;
- `pop_smallint_range(1023)` then `pop_cellslice()`;
- `!have(bits)` returns quiet status `0` and restores original slice;
- success pushes fetched subslice first, then mutated remainder, then `-1`.
-/

private def ldslicexqId : InstrId := { name := "LDSLICEXQ" }

private def ldslicexqInstr : Instr := .loadSliceX false true

private def ldslicexqOpcode : Nat := 0xd71a

private def dispatchSentinel : Int := 541

private def mkLdslicexqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldslicexqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldslicexqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdslicexqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkLdslicexqCase name stack program gasLimits fuel

private def runLdslicexqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadSliceX ldslicexqInstr stack

private def runLdslicexqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadSliceX instr (VM.push (intV dispatchSentinel)) stack

private def ldslicexqSetGasExact : Int :=
  computeExactGasBudget ldslicexqInstr

private def ldslicexqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldslicexqInstr

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 13 4) #[]

private def tailBits6 : BitString := natToBits 37 6

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
  below ++ #[.slice (expectedLoadedSlice source width), .slice (source.advanceBits width), intV (-1)]

private def expectedFailureStack
    (below : Array Value)
    (source : Slice) : Array Value :=
  below ++ #[.slice source, intV 0]

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

private def pickRefsPackNonEmpty (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA] else if pick = 1 then #[refLeafB] else #[refLeafA, refLeafB]
  (refs, rng')

private def pickNoiseValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let noise : Value :=
    if pick = 0 then .null else if pick = 1 then intV 77 else if pick = 2 then .cell refLeafA else .cell refLeafB
  (noise, rng')

private def genLdslicexqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  if shape = 0 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdslicexqCase s!"fuzz/ok/exact-width-{width}" #[.slice slice, intV width], rng3)
  else if shape = 1 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 64 (1023 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    (mkLdslicexqCase s!"fuzz/ok/with-tail/width-{width}/extra-{extra}" #[.slice slice, intV width], rng4)
  else if shape = 2 then
    let (bitCount, rng2) := randNat rng1 0 128
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdslicexqCase s!"fuzz/ok/width-zero/bits-{bitCount}" #[.slice slice, intV 0], rng3)
  else if shape = 3 then
    let (width, rng2) := pickWidthMixed rng1
    let (refs, rng3) := pickRefsPack rng2
    let extraCap := Nat.min 32 (1023 - width)
    let (extra, rng4) := randNat rng3 0 extraCap
    let (slice, rng5) := mkRandomSlice (width + extra) refs rng4
    (mkLdslicexqCase s!"fuzz/ok/refs/width-{width}/refs-{refs.size}" #[.slice slice, intV width], rng5)
  else if shape = 4 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 32 (1023 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkLdslicexqCase s!"fuzz/ok/deep-noise/width-{width}" #[noise, .slice slice, intV width], rng5)
  else if shape = 5 then
    let (availableBits, rng2) := randNat rng1 0 1022
    let width := availableBits + 1
    let (slice, rng3) := mkRandomSlice availableBits #[] rng2
    (mkLdslicexqCase s!"fuzz/fail/short-by-one/bits-{availableBits}" #[.slice slice, intV width], rng3)
  else if shape = 6 then
    let (width, rng2) := randNat rng1 1 1023
    (mkLdslicexqCase s!"fuzz/fail/empty-slice/width-{width}" #[.slice (mkSliceFromBits #[]), intV width], rng2)
  else if shape = 7 then
    let (width0, rng2) := pickWidthMixed rng1
    let width := if width0 = 0 then 1 else width0
    let (refs, rng3) := pickRefsPackNonEmpty rng2
    let (availableBits, rng4) := randNat rng3 0 (width - 1)
    let (slice, rng5) := mkRandomSlice availableBits refs rng4
    (mkLdslicexqCase s!"fuzz/fail/refs-short/w-{width}-a-{availableBits}-r-{refs.size}"
      #[.slice slice, intV width], rng5)
  else if shape = 8 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdslicexqCase s!"fuzz/range/negative-width/width-{width}" #[.slice slice, intV (-1)], rng3)
  else if shape = 9 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (delta, rng4) := randNat rng3 1 2048
    let tooLargeWidth : Int := Int.ofNat (1023 + delta)
    (mkLdslicexqCase s!"fuzz/range/too-large-width-{tooLargeWidth}" #[.slice slice, intV tooLargeWidth], rng4)
  else if shape = 10 then
    let (bitCount, rng2) := randNat rng1 0 64
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdslicexqProgramCase "fuzz/range/width-nan-via-program"
      #[.slice slice]
      #[.pushInt .nan, ldslicexqInstr], rng3)
  else if shape = 11 then
    (mkLdslicexqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkLdslicexqCase "fuzz/underflow/one-item-slice" #[.slice (mkSliceFromBits #[])], rng2)
    else
      (mkLdslicexqCase "fuzz/underflow/one-item-width" #[intV 0], rng2)
  else if shape = 13 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (badPick, rng4) := randNat rng3 0 2
    let badWidth : Value :=
      if badPick = 0 then .null else if badPick = 1 then .cell refLeafA else .slice (mkSliceFromBits #[])
    (mkLdslicexqCase "fuzz/type/width-not-int" #[.slice slice, badWidth], rng4)
  else if shape = 14 then
    let (width, rng2) := pickWidthMixed rng1
    let (badPick, rng3) := randNat rng2 0 2
    let badSlice : Value :=
      if badPick = 0 then .null else if badPick = 1 then intV 9 else .cell refLeafB
    (mkLdslicexqCase s!"fuzz/type/slice-not-slice/width-{width}" #[badSlice, intV width], rng3)
  else if shape = 15 then
    let (badPick, rng2) := randNat rng1 0 1
    let badSlice : Value := if badPick = 0 then .null else .cell refLeafA
    (mkLdslicexqCase "fuzz/error-order/range-before-slice-type" #[badSlice, intV 2048], rng2)
  else if shape = 16 then
    let (badPick, rng2) := randNat rng1 0 1
    let badSlice : Value := if badPick = 0 then .null else .cell refLeafA
    let badWidth : Value := if badPick = 0 then .null else .cell refLeafB
    (mkLdslicexqCase "fuzz/error-order/width-type-before-slice-type" #[badSlice, badWidth], rng2)
  else if shape = 17 then
    let (bitCount, rng2) := randNat rng1 0 64
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdslicexqCase "fuzz/gas/exact"
      #[.slice slice, intV 0]
      #[.pushInt (.num ldslicexqSetGasExact), .tonEnvOp .setGasLimit, ldslicexqInstr], rng3)
  else
    let (bitCount, rng2) := randNat rng1 0 64
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdslicexqCase "fuzz/gas/exact-minus-one"
      #[.slice slice, intV 0]
      #[.pushInt (.num ldslicexqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldslicexqInstr], rng3)

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
  id := ldslicexqId
  unit := #[
    { name := "unit/direct/quiet-success-stack-order-and-status-minus1"
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
            (runLdslicexqDirect #[.slice source, intV width])
            (expectedSuccessStack #[] source width)

        let zeroWithRefs := mkPatternSliceWithRefs 9 #[refLeafA, refLeafB]
        expectOkStack "ok/width0-remainder-preserves-refs"
          (runLdslicexqDirect #[.slice zeroWithRefs, intV 0])
          (expectedSuccessStack #[] zeroWithRefs 0)

        let deepSource := mkPatternSliceWithRefs 16 #[refLeafA, refLeafB]
        let deepPrefix : Array Value := #[.null, intV 99, .cell refLeafA]
        expectOkStack "ok/deep-stack-order-preserved"
          (runLdslicexqDirect (deepPrefix ++ #[.slice deepSource, intV 4]))
          (expectedSuccessStack deepPrefix deepSource 4)

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 40) #[refLeafA, refLeafB]
        let partialSlice : Slice := { cell := partialCell, bitPos := 7, refPos := 1 }
        expectOkStack "ok/uses-slice-cursor-remainder"
          (runLdslicexqDirect #[.slice partialSlice, intV 12])
          (expectedSuccessStack #[] partialSlice 12) }
    ,
    { name := "unit/direct/quiet-failure-preserves-original-slice-and-status0"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkSliceFromBits #[]),
            (5, mkPatternSlice 4),
            (64, mkPatternSlice 12),
            (1023, mkPatternSlice 1022)
          ]
        for check in checks do
          let width := check.1
          let source := check.2
          expectOkStack s!"fail/w-{width}/a-{source.bitsRemaining}"
            (runLdslicexqDirect #[.slice source, intV width])
            (expectedFailureStack #[] source)

        let refsInput := mkPatternSliceWithRefs 6 #[refLeafA, refLeafB]
        expectOkStack "fail/refs/w-7-a-6-r-2"
          (runLdslicexqDirect #[.slice refsInput, intV 7])
          (expectedFailureStack #[] refsInput)

        let deep := mkPatternSlice 10
        expectOkStack "fail/deep-stack-preserve-below"
          (runLdslicexqDirect #[intV 77, .slice deep, intV 64])
          (expectedFailureStack #[intV 77] deep)

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 24) #[refLeafA]
        let partialSlice : Slice := { cell := partialCell, bitPos := 15, refPos := 0 }
        expectOkStack "fail/partial-slice-short"
          (runLdslicexqDirect #[.slice partialSlice, intV 10])
          (expectedFailureStack #[] partialSlice) }
    ,
    { name := "unit/direct/underflow-type-bounds-and-error-order"
      run := do
        expectErr "underflow/empty" (runLdslicexqDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runLdslicexqDirect #[.slice (mkPatternSlice 3)]) .stkUnd
        expectErr "underflow/one-item-width"
          (runLdslicexqDirect #[intV 7]) .stkUnd
        expectErr "underflow/one-item-null"
          (runLdslicexqDirect #[.null]) .stkUnd

        expectErr "type/width-not-int-null"
          (runLdslicexqDirect #[.slice (mkPatternSlice 3), .null]) .typeChk
        expectErr "type/width-not-int-cell"
          (runLdslicexqDirect #[.slice (mkPatternSlice 3), .cell refLeafA]) .typeChk
        expectErr "type/slice-not-slice-after-valid-width"
          (runLdslicexqDirect #[.null, intV 0]) .typeChk

        expectErr "range/width-negative"
          (runLdslicexqDirect #[.slice (mkPatternSlice 3), intV (-1)]) .rangeChk
        expectErr "range/width-too-large"
          (runLdslicexqDirect #[.slice (mkPatternSlice 3), intV 1024]) .rangeChk
        expectErr "range/width-nan"
          (runLdslicexqDirect #[.slice (mkPatternSlice 3), .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-type"
          (runLdslicexqDirect #[.null, intV 2048]) .rangeChk
        expectErr "error-order/width-type-before-slice-type"
          (runLdslicexqDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[
          ldslicexqInstr,
          .loadSliceX false false,
          .loadSliceX true false,
          .loadSliceX true true,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldslicexq" s0 ldslicexqInstr 16
        let s2 ← expectDecodeStep "decode/ldslicex-neighbor" s1 (.loadSliceX false false) 16
        let s3 ← expectDecodeStep "decode/pldslicex-neighbor" s2 (.loadSliceX true false) 16
        let s4 ← expectDecodeStep "decode/pldslicexq-neighbor" s3 (.loadSliceX true true) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [ldslicexqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits ldslicexqOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldslicexq: expected 0xd71a 16-bit encoding, got bit-length {singleCode.bits.size}")

        let rawSlice := mkSliceFromBits (natToBits ldslicexqOpcode 16 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-0xd71a" rawSlice ldslicexqInstr 16
        let raw2 ← expectDecodeStep "decode/raw-tail-add" raw1 .add 8
        if raw2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {raw2.bitsRemaining} bits remaining")

        let fixedCode ←
          match assembleCp0 [.loadSliceFixed false true 1] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble fixed failed: {e}")
        let fixedSlice := Slice.ofCell fixedCode
        let fixedRest ← expectDecodeStep "decode/loadslicefixedq-neighbor" fixedSlice (.loadSliceFixed false true 1) 24
        if fixedRest.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/fixed-end: expected exhausted slice, got {fixedRest.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-loadslicex-add"
          (runLdslicexqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-loadslicex-fixed-neighbor"
          (runLdslicexqDispatchFallback (.loadSliceFixed false true 8) #[intV 9])
          #[intV 9, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdslicexqCase "ok/width0-empty-slice" #[.slice oracleSlice0, intV 0],
    mkLdslicexqCase "ok/width0-nonempty-slice" #[.slice oracleSlice13, intV 0],
    mkLdslicexqCase "ok/width1-exact" #[.slice oracleSlice1, intV 1],
    mkLdslicexqCase "ok/width3-of-5" #[.slice oracleSlice5, intV 3],
    mkLdslicexqCase "ok/width8-exact" #[.slice oracleSlice8, intV 8],
    mkLdslicexqCase "ok/width8-with-tail" #[.slice oracleSlice8Tail11, intV 8],
    mkLdslicexqCase "ok/width31-exact" #[.slice oracleSlice31, intV 31],
    mkLdslicexqCase "ok/width255-exact" #[.slice oracleSlice255, intV 255],
    mkLdslicexqCase "ok/width512-exact" #[.slice oracleSlice512, intV 512],
    mkLdslicexqCase "ok/width512-with-tail" #[.slice oracleSlice512Tail17, intV 512],
    mkLdslicexqCase "ok/width768-exact" #[.slice oracleSlice768, intV 768],
    mkLdslicexqCase "ok/width1022-exact" #[.slice oracleSlice1022, intV 1022],
    mkLdslicexqCase "ok/width1023-exact" #[.slice oracleSlice1023, intV 1023],
    mkLdslicexqCase "ok/refs-in-input-slice" #[.slice oracleSliceWithRefs9, intV 4],
    mkLdslicexqCase "ok/deep-stack-preserve-noise"
      #[.null, .cell refLeafB, .slice oracleSlice13, intV 5],

    mkLdslicexqCase "fail/empty-width1" #[.slice oracleSlice0, intV 1],
    mkLdslicexqCase "fail/short-4-vs5" #[.slice oracleSlice4, intV 5],
    mkLdslicexqCase "fail/short-5-vs9" #[.slice oracleSlice5, intV 9],
    mkLdslicexqCase "fail/short-1022-vs1023" #[.slice oracleSlice1022, intV 1023],
    mkLdslicexqCase "fail/refs-short-6-vs7" #[.slice oracleSliceWithRefs6, intV 7],
    mkLdslicexqCase "fail/deep-stack-preserve-noise"
      #[intV 33, .slice oracleSlice8, intV 16],
    mkLdslicexqCase "fail/width1023-vs768" #[.slice oracleSlice768, intV 1023],

    mkLdslicexqCase "range/width-negative" #[.slice oracleSlice13, intV (-1)],
    mkLdslicexqCase "range/width-too-large-1024" #[.slice oracleSlice13, intV 1024],
    mkLdslicexqCase "range/width-too-large-4096" #[.slice oracleSlice13, intV 4096],
    mkLdslicexqProgramCase "range/width-nan-via-program"
      #[.slice oracleSlice13]
      #[.pushInt .nan, ldslicexqInstr],

    mkLdslicexqCase "underflow/empty" #[],
    mkLdslicexqCase "underflow/one-item-slice" #[.slice oracleSlice13],
    mkLdslicexqCase "underflow/one-item-width" #[intV 0],

    mkLdslicexqCase "type/width-top-null" #[.slice oracleSlice13, .null],
    mkLdslicexqCase "type/width-top-cell" #[.slice oracleSlice13, .cell refLeafA],
    mkLdslicexqCase "type/slice-not-slice-after-valid-width" #[.null, intV 0],

    mkLdslicexqCase "error-order/range-before-slice-type" #[.null, intV 2048],
    mkLdslicexqCase "error-order/width-type-before-slice-type" #[.null, .null],

    mkLdslicexqCase "gas/exact-cost-succeeds"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num ldslicexqSetGasExact), .tonEnvOp .setGasLimit, ldslicexqInstr],
    mkLdslicexqCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num ldslicexqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldslicexqInstr]
  ]
  fuzz := #[
    { seed := 2026021037
      count := 320
      gen := genLdslicexqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSLICEXQ
