import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDSKIPFIRST

/-
SDSKIPFIRST branch-mapping notes (Lean execution path):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sdskipfirst.lean` (`.sdskipfirst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdskipfirst` -> `0xd721`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd721` decode to `.sdskipfirst`)

Branch map used for this suite:
- dispatch guard: `.sdskipfirst` vs fallback to `next`;
- stack gate: `checkUnderflow 2` before any pops;
- width pop via `popNatUpTo 1023`:
  non-int -> `typeChk`, NaN/negative/>1023 -> `rangeChk`;
- slice pop only after width succeeds (`typeChk` for non-slice);
- main split: `haveBits width` -> push `advanceBits width`; else `cellUnd`.
-/

private def sdskipfirstId : InstrId := { name := "SDSKIPFIRST" }

private def sdskipfirstInstr : Instr := .sdskipfirst

private def sdskipfirstOpcode : Nat := 0xd721

private def dispatchSentinel : Int := 721

private def mkSdskipfirstCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdskipfirstInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdskipfirstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSdskipfirstProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkSdskipfirstCase name stack program gasLimits fuel

private def runSdskipfirstDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdskipfirst sdskipfirstInstr stack

private def runSdskipfirstDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellSdskipfirst
    instr
    (VM.push (intV dispatchSentinel))
    stack

private def sdskipfirstSetGasExact : Int :=
  computeExactGasBudget sdskipfirstInstr

private def sdskipfirstSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdskipfirstInstr

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 11 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 6 3) #[refLeafA]

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 3 = 1) || ((idx.1 + phase) % 5 = 0)

private def mkPatternSlice (bitCount : Nat) (phase : Nat := 0) : Slice :=
  mkSliceFromBits (stripeBits bitCount phase)

private def mkPatternSliceWithRefs
    (bitCount : Nat)
    (refs : Array Cell)
    (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stripeBits bitCount phase) refs)

private def expectedSuccessStack
    (below : Array Value)
    (source : Slice)
    (width : Nat) : Array Value :=
  below ++ #[.slice (source.advanceBits width)]

private def runSdskipfirstModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 2 then
    throw .stkUnd
  let top := stack.back!
  let afterWidthPop := stack.pop
  let bits : Nat ←
    match top with
    | .int .nan => throw .rangeChk
    | .int (.num n) =>
        if n < 0 then
          throw .rangeChk
        let u := n.toNat
        if u > 1023 then
          throw .rangeChk
        pure u
    | _ => throw .typeChk
  let nextTop := afterWidthPop.back!
  let below := afterWidthPop.pop
  match nextTop with
  | .slice s =>
      if s.haveBits bits then
        pure (below.push (.slice (s.advanceBits bits)))
      else
        throw .cellUnd
  | _ => throw .typeChk

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
    if pick = 0 then #[]
    else if pick = 1 then #[refLeafA]
    else if pick = 2 then #[refLeafB]
    else #[refLeafA, refLeafB]
  (refs, rng')

private def pickNoiseValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 4
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell refLeafA
    else if pick = 3 then .cell refLeafB
    else .builder Builder.empty
  (noise, rng')

private def pickBadWidthValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let bad : Value :=
    if pick = 0 then .null
    else if pick = 1 then .cell refLeafA
    else .slice (mkSliceFromBits #[])
  (bad, rng')

private def pickBadSliceValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let bad : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 9
    else if pick = 2 then .cell refLeafC
    else .builder Builder.empty
  (bad, rng')

private def genSdskipfirstFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkSdskipfirstCase s!"fuzz/ok/exact-width-{width}" #[.slice slice, intV width], rng3)
  else if shape = 1 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 64 (1023 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    (mkSdskipfirstCase s!"fuzz/ok/with-tail/width-{width}/extra-{extra}" #[.slice slice, intV width], rng4)
  else if shape = 2 then
    let (bitCount, rng2) := randNat rng1 0 1023
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkSdskipfirstCase s!"fuzz/ok/width-zero/bits-{bitCount}" #[.slice slice, intV 0], rng3)
  else if shape = 3 then
    let (width, rng2) := pickWidthMixed rng1
    let (refs, rng3) := pickRefsPack rng2
    let extraCap := Nat.min 32 (1023 - width)
    let (extra, rng4) := randNat rng3 0 extraCap
    let (slice, rng5) := mkRandomSlice (width + extra) refs rng4
    (mkSdskipfirstCase s!"fuzz/ok/refs/width-{width}/refs-{refs.size}" #[.slice slice, intV width], rng5)
  else if shape = 4 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 32 (1023 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkSdskipfirstCase s!"fuzz/ok/deep-noise/width-{width}" #[noise, .slice slice, intV width], rng5)
  else if shape = 5 then
    let (availableBits, rng2) := randNat rng1 0 1022
    let width := availableBits + 1
    let (slice, rng3) := mkRandomSlice availableBits #[] rng2
    (mkSdskipfirstCase s!"fuzz/cellund/short-by-one/bits-{availableBits}" #[.slice slice, intV width], rng3)
  else if shape = 6 then
    let (width, rng2) := randNat rng1 1 1023
    (mkSdskipfirstCase s!"fuzz/cellund/empty-slice/width-{width}" #[.slice (mkSliceFromBits #[]), intV width], rng2)
  else if shape = 7 then
    let (width, rng2) := randNat rng1 1 1023
    let maxDelta := Nat.min width 24
    let (delta, rng3) := randNat rng2 1 maxDelta
    let avail := width - delta
    let (slice, rng4) := mkRandomSlice avail #[] rng3
    (mkSdskipfirstCase s!"fuzz/cellund/random-short/avail-{avail}/width-{width}" #[.slice slice, intV width], rng4)
  else if shape = 8 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkSdskipfirstCase s!"fuzz/range/negative-width/width-{width}" #[.slice slice, intV (-1)], rng3)
  else if shape = 9 then
    let (bitCount, rng2) := randNat rng1 0 128
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    let (delta, rng4) := randNat rng3 1 4096
    let tooLarge : Int := Int.ofNat (1023 + delta)
    (mkSdskipfirstCase s!"fuzz/range/too-large-width-{tooLarge}" #[.slice slice, intV tooLarge], rng4)
  else if shape = 10 then
    let (bitCount, rng2) := randNat rng1 0 128
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkSdskipfirstProgramCase "fuzz/range/width-nan-via-program"
      #[.slice slice]
      #[.pushInt .nan, sdskipfirstInstr], rng3)
  else if shape = 11 then
    (mkSdskipfirstCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkSdskipfirstCase "fuzz/underflow/one-item-slice" #[.slice (mkSliceFromBits #[])], rng2)
    else
      (mkSdskipfirstCase "fuzz/underflow/one-item-width" #[intV 0], rng2)
  else if shape = 13 then
    let (bitCount, rng2) := randNat rng1 0 64
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    let (badWidth, rng4) := pickBadWidthValue rng3
    (mkSdskipfirstCase "fuzz/type/width-not-int" #[.slice slice, badWidth], rng4)
  else if shape = 14 then
    let (width, rng2) := pickWidthMixed rng1
    let (badSlice, rng3) := pickBadSliceValue rng2
    (mkSdskipfirstCase s!"fuzz/type/slice-not-slice/width-{width}" #[badSlice, intV width], rng3)
  else if shape = 15 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    (mkSdskipfirstCase "fuzz/error-order/range-before-slice-type" #[badSlice, intV 4096], rng2)
  else if shape = 16 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    (mkSdskipfirstCase "fuzz/error-order/width-type-before-slice-type" #[badSlice, .null], rng2)
  else if shape = 17 then
    let (bitCount, rng2) := randNat rng1 0 96
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkSdskipfirstCase "fuzz/gas/exact"
      #[.slice slice, intV 0]
      #[.pushInt (.num sdskipfirstSetGasExact), .tonEnvOp .setGasLimit, sdskipfirstInstr], rng3)
  else
    let (bitCount, rng2) := randNat rng1 0 96
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkSdskipfirstCase "fuzz/gas/exact-minus-one"
      #[.slice slice, intV 0]
      #[.pushInt (.num sdskipfirstSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdskipfirstInstr], rng3)

private def oracleSlice0 : Slice := mkPatternSlice 0
private def oracleSlice1 : Slice := mkPatternSlice 1
private def oracleSlice4 : Slice := mkPatternSlice 4
private def oracleSlice5 : Slice := mkPatternSlice 5
private def oracleSlice8 : Slice := mkPatternSlice 8
private def oracleSlice13 : Slice := mkPatternSlice 13
private def oracleSlice31 : Slice := mkPatternSlice 31
private def oracleSlice63 : Slice := mkPatternSlice 63
private def oracleSlice255 : Slice := mkPatternSlice 255
private def oracleSlice768 : Slice := mkPatternSlice 768
private def oracleSlice1022 : Slice := mkPatternSlice 1022
private def oracleSlice1023 : Slice := mkPatternSlice 1023

private def oracleSliceWithRefs9 : Slice := mkPatternSliceWithRefs 9 #[refLeafA, refLeafB]
private def oracleSlice8Tail11 : Slice := mkSliceFromBits (stripeBits 8 0 ++ natToBits 1337 11)

private def partialCell : Cell := Cell.mkOrdinary (stripeBits 40 1) #[refLeafA, refLeafB, refLeafC]
private def partialSlice : Slice := { cell := partialCell, bitPos := 7, refPos := 1 }

private def shortPartialCell : Cell := Cell.mkOrdinary (stripeBits 24 0) #[refLeafA]
private def shortPartialSlice : Slice := { cell := shortPartialCell, bitPos := 15, refPos := 0 }

def suite : InstrSuite where
  id := { name := "SDSKIPFIRST" }
  unit := #[
    { name := "unit/direct/success-widths-cursor-and-deep-stack-order"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (0, mkPatternSlice 0),
            (0, mkPatternSlice 19),
            (1, mkPatternSlice 1),
            (3, mkPatternSlice 8),
            (8, mkPatternSlice 16),
            (63, mkPatternSlice 63),
            (255, mkPatternSlice 300),
            (1022, mkPatternSlice 1023),
            (1023, mkPatternSlice 1023)
          ]
        for check in checks do
          let width := check.1
          let source := check.2
          expectOkStack s!"ok/width-{width}/bits-{source.bitsRemaining}"
            (runSdskipfirstDirect #[.slice source, intV width])
            (expectedSuccessStack #[] source width)

        let withRefs := mkPatternSliceWithRefs 9 #[refLeafA, refLeafB]
        expectOkStack "ok/width0-preserves-cursor-and-refs"
          (runSdskipfirstDirect #[.slice withRefs, intV 0])
          (expectedSuccessStack #[] withRefs 0)

        let deepPrefix : Array Value := #[.null, intV 99, .cell refLeafA]
        let deepSource := mkPatternSliceWithRefs 18 #[refLeafA, refLeafB]
        expectOkStack "ok/deep-stack-preserved"
          (runSdskipfirstDirect (deepPrefix ++ #[.slice deepSource, intV 5]))
          (expectedSuccessStack deepPrefix deepSource 5)

        expectOkStack "ok/partial-slice-cursor"
          (runSdskipfirstDirect #[.slice partialSlice, intV 12])
          (expectedSuccessStack #[] partialSlice 12) }
    ,
    { name := "unit/direct/cellund-when-width-exceeds-bits"
      run := do
        expectErr "cellund/empty-width1"
          (runSdskipfirstDirect #[.slice (mkSliceFromBits #[]), intV 1]) .cellUnd
        expectErr "cellund/short-4-vs5"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 4), intV 5]) .cellUnd
        expectErr "cellund/short-1022-vs1023"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 1022), intV 1023]) .cellUnd
        expectErr "cellund/partial-short"
          (runSdskipfirstDirect #[.slice shortPartialSlice, intV 10]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-error-order"
      run := do
        expectErr "underflow/empty" (runSdskipfirstDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 5)]) .stkUnd
        expectErr "underflow/one-item-width"
          (runSdskipfirstDirect #[intV 4]) .stkUnd
        expectErr "underflow/one-item-null"
          (runSdskipfirstDirect #[.null]) .stkUnd

        expectErr "type/width-not-int-null"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 5), .null]) .typeChk
        expectErr "type/width-not-int-cell"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 5), .cell refLeafA]) .typeChk
        expectErr "type/width-not-int-slice"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 5), .slice (mkPatternSlice 0)]) .typeChk
        expectErr "type/slice-not-slice-after-valid-width"
          (runSdskipfirstDirect #[.null, intV 0]) .typeChk

        expectErr "range/width-negative"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 5), intV (-1)]) .rangeChk
        expectErr "range/width-too-large"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 5), intV 1024]) .rangeChk
        expectErr "range/width-nan"
          (runSdskipfirstDirect #[.slice (mkPatternSlice 5), .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-type"
          (runSdskipfirstDirect #[.null, intV 2048]) .rangeChk
        expectErr "error-order/width-type-before-slice-type"
          (runSdskipfirstDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/model/alignment-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/width0", #[.slice oracleSlice13, intV 0]),
            ("ok/exact", #[.slice oracleSlice63, intV 63]),
            ("ok/with-tail", #[.slice oracleSlice8Tail11, intV 8]),
            ("ok/partial", #[.slice partialSlice, intV 12]),
            ("ok/deep", #[.null, intV 9, .slice oracleSlice31, intV 5]),
            ("err/cellund", #[.slice oracleSlice4, intV 5]),
            ("err/range-negative", #[.slice oracleSlice31, intV (-1)]),
            ("err/type-width", #[.slice oracleSlice31, .null]),
            ("err/type-slice", #[.null, intV 0]),
            ("err/underflow", #[.slice oracleSlice31])
          ]
        for sample in samples do
          let label := sample.1
          let stack := sample.2
          expectSameOutcome s!"model/{label}"
            (runSdskipfirstDirect stack)
            (runSdskipfirstModel stack) }
    ,
    { name := "unit/opcode/decode-assemble-boundaries"
      run := do
        let program : Array Instr := #[
          .sdcutfirst,
          sdskipfirstInstr,
          .sdcutlast,
          .sdskiplast,
          (.cellOp .sdSubstr),
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdcutfirst-neighbor" s0 .sdcutfirst 16
        let s2 ← expectDecodeStep "decode/sdskipfirst" s1 sdskipfirstInstr 16
        let s3 ← expectDecodeStep "decode/sdcutlast-neighbor" s2 .sdcutlast 16
        let s4 ← expectDecodeStep "decode/sdskiplast-neighbor" s3 .sdskiplast 16
        let s5 ← expectDecodeStep "decode/sdsubstr-neighbor" s4 (.cellOp .sdSubstr) 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [sdskipfirstInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits sdskipfirstOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"opcode/sdskipfirst: expected 0xd721 16-bit encoding, got bit-length {singleCode.bits.size}")

        let rawSlice := mkSliceFromBits (natToBits sdskipfirstOpcode 16 ++ natToBits 0xa5 8)
        let rawRest ← expectDecodeStep "decode/raw-0xd721" rawSlice sdskipfirstInstr 16
        if rawRest.readBits 8 = natToBits 0xa5 8 then
          pure ()
        else
          throw (IO.userError "decode/raw-0xd721 did not preserve trailing payload") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-sdskipfirst-add"
          (runSdskipfirstDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-sdskipfirst-sdcutfirst"
          (runSdskipfirstDispatchFallback .sdcutfirst #[intV 9])
          #[intV 9, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdskipfirstCase "ok/width0-empty-slice" #[.slice oracleSlice0, intV 0],
    mkSdskipfirstCase "ok/width0-nonempty-slice" #[.slice oracleSlice13, intV 0],
    mkSdskipfirstCase "ok/width1-exact" #[.slice oracleSlice1, intV 1],
    mkSdskipfirstCase "ok/width3-of-5" #[.slice oracleSlice5, intV 3],
    mkSdskipfirstCase "ok/width8-with-tail" #[.slice oracleSlice8Tail11, intV 8],
    mkSdskipfirstCase "ok/width63-exact" #[.slice oracleSlice63, intV 63],
    mkSdskipfirstCase "ok/width255-exact" #[.slice oracleSlice255, intV 255],
    mkSdskipfirstCase "ok/width512-of-768" #[.slice oracleSlice768, intV 512],
    mkSdskipfirstCase "ok/width1022-of-1023" #[.slice oracleSlice1023, intV 1022],
    mkSdskipfirstCase "ok/width1023-exact" #[.slice oracleSlice1023, intV 1023],
    mkSdskipfirstCase "ok/refs-in-input-slice" #[.slice oracleSliceWithRefs9, intV 4],
    mkSdskipfirstCase "ok/deep-stack-preserve-noise"
      #[.null, .cell refLeafB, .slice oracleSlice31, intV 5],

    mkSdskipfirstCase "cellund/empty-width1" #[.slice oracleSlice0, intV 1],
    mkSdskipfirstCase "cellund/short-4-vs5" #[.slice oracleSlice4, intV 5],
    mkSdskipfirstCase "cellund/short-1022-vs1023" #[.slice oracleSlice1022, intV 1023],

    mkSdskipfirstCase "range/width-negative" #[.slice oracleSlice31, intV (-1)],
    mkSdskipfirstCase "range/width-too-large-1024" #[.slice oracleSlice31, intV 1024],
    mkSdskipfirstProgramCase "range/width-nan-via-program"
      #[.slice oracleSlice31]
      #[.pushInt .nan, sdskipfirstInstr],

    mkSdskipfirstCase "underflow/empty" #[],
    mkSdskipfirstCase "underflow/one-item-slice" #[.slice oracleSlice31],
    mkSdskipfirstCase "type/width-top-null" #[.slice oracleSlice31, .null],
    mkSdskipfirstCase "type/slice-not-slice-after-valid-width" #[.null, intV 0],
    mkSdskipfirstCase "error-order/range-before-slice-type" #[.null, intV 2048],

    mkSdskipfirstCase "gas/exact-cost-succeeds"
      #[.slice oracleSlice8, intV 0]
      #[.pushInt (.num sdskipfirstSetGasExact), .tonEnvOp .setGasLimit, sdskipfirstInstr],
    mkSdskipfirstCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSlice8, intV 0]
      #[.pushInt (.num sdskipfirstSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdskipfirstInstr]
  ]
  fuzz := #[
    { seed := 2026021021
      count := 240
      gen := genSdskipfirstFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDSKIPFIRST
