import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDUX

/-!
PLDUX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadIntVar.lean`
    (`.loadIntVar unsigned=true prefetch=true quiet=false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadIntVar` encode: `0xd700 + args3`, so PLDUX = `0xd703`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd700..0xd707` decode to `.loadIntVar unsigned prefetch quiet`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_var`, `exec_load_int_common`, mode=`3` for PLDUX).

Branch map covered by this suite:
- `checkUnderflow 2` before any pop;
- width pop via `popNatUpTo 256` (type/range paths from `popInt` and bounds);
- slice pop type check only after width checks succeed;
- success contract in prefetch mode: push loaded unsigned int only (no remainder);
- insufficient bits path throws `cellUnd` in non-quiet mode;
- opcode decode/dispatch checks for PLDUX family and boundaries.
-/

private def plduxId : InstrId := { name := "PLDUX" }

private def plduxInstr : Instr := .loadIntVar true true false

private def plduxOpcode : Nat := 0xd703

private def dispatchSentinel : Int := 713

private def mkPlduxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[plduxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := plduxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPlduxProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkPlduxCase name stack program gasLimits fuel

private def runPlduxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar plduxInstr stack

private def runPlduxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadIntVar instr (VM.push (intV dispatchSentinel)) stack

private def plduxSetGasExact : Int :=
  computeExactGasBudget plduxInstr

private def plduxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne plduxInstr

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

private def expectedUnsigned (source : Slice) (width : Nat) : Int :=
  Int.ofNat (bitsToNat (source.readBits width))

private def expectedSuccessStack
    (below : Array Value)
    (source : Slice)
    (width : Nat) : Array Value :=
  below ++ #[intV (expectedUnsigned source width)]

private def widthBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 192, 255, 256]

private def pickWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (widthBoundaryPool.size - 1)
  (widthBoundaryPool[idx]!, rng')

private def pickWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickWidthBoundary rng1
  else
    randNat rng1 0 256

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
  let (pick, rng') := randNat rng 0 4
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell refLeafA
    else if pick = 3 then .cell refLeafB
    else .builder Builder.empty
  (noise, rng')

private def genPlduxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkPlduxCase s!"fuzz/ok/exact-width-{width}" #[.slice slice, intV width], rng3)
  else if shape = 1 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 64 (256 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    (mkPlduxCase s!"fuzz/ok/with-tail/width-{width}/extra-{extra}" #[.slice slice, intV width], rng4)
  else if shape = 2 then
    let (bitCount, rng2) := randNat rng1 0 256
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkPlduxCase s!"fuzz/ok/width-zero/bits-{bitCount}" #[.slice slice, intV 0], rng3)
  else if shape = 3 then
    let (width, rng2) := pickWidthMixed rng1
    let (refs, rng3) := pickRefsPack rng2
    let extraCap := Nat.min 32 (256 - width)
    let (extra, rng4) := randNat rng3 0 extraCap
    let (slice, rng5) := mkRandomSlice (width + extra) refs rng4
    (mkPlduxCase s!"fuzz/ok/refs/width-{width}/refs-{refs.size}" #[.slice slice, intV width], rng5)
  else if shape = 4 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 16 (256 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkPlduxCase s!"fuzz/ok/deep-noise/width-{width}" #[noise, .slice slice, intV width], rng5)
  else if shape = 5 then
    let (availableBits, rng2) := randNat rng1 0 255
    let width := availableBits + 1
    let (slice, rng3) := mkRandomSlice availableBits #[] rng2
    (mkPlduxCase s!"fuzz/cellund/short-by-one/bits-{availableBits}" #[.slice slice, intV width], rng3)
  else if shape = 6 then
    let (width, rng2) := randNat rng1 1 256
    (mkPlduxCase s!"fuzz/cellund/empty-slice/width-{width}" #[.slice (mkSliceFromBits #[]), intV width], rng2)
  else if shape = 7 then
    let (availableBits, rng2) := randNat rng1 0 248
    let maxDelta := Nat.min 8 (256 - availableBits)
    let (delta, rng3) := randNat rng2 1 maxDelta
    let width := availableBits + delta
    let (slice, rng4) := mkRandomSlice availableBits #[] rng3
    (mkPlduxCase s!"fuzz/cellund/random-short/avail-{availableBits}/width-{width}" #[.slice slice, intV width], rng4)
  else if shape = 8 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkPlduxCase s!"fuzz/range/negative-width/width-{width}" #[.slice slice, intV (-1)], rng3)
  else if shape = 9 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (delta, rng4) := randNat rng3 1 2048
    let tooLargeWidth : Int := Int.ofNat (256 + delta)
    (mkPlduxCase s!"fuzz/range/too-large-width-{tooLargeWidth}" #[.slice slice, intV tooLargeWidth], rng4)
  else if shape = 10 then
    let (width, rng2) := randNat rng1 0 128
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkPlduxProgramCase "fuzz/range/width-nan-via-program"
      #[.slice slice]
      #[.pushInt .nan, plduxInstr], rng3)
  else if shape = 11 then
    (mkPlduxCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkPlduxCase "fuzz/underflow/one-item-slice" #[.slice (mkSliceFromBits #[])], rng2)
    else
      (mkPlduxCase "fuzz/underflow/one-item-width" #[intV 0], rng2)
  else if shape = 13 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (badPick, rng4) := randNat rng3 0 2
    let badWidth : Value :=
      if badPick = 0 then .null else if badPick = 1 then .cell refLeafA else .slice (mkSliceFromBits #[])
    (mkPlduxCase "fuzz/type/width-not-int" #[.slice slice, badWidth], rng4)
  else if shape = 14 then
    let (width, rng2) := pickWidthMixed rng1
    let (badPick, rng3) := randNat rng2 0 3
    let badSlice : Value :=
      if badPick = 0 then .null else if badPick = 1 then intV 9 else if badPick = 2 then .cell refLeafB else .builder Builder.empty
    (mkPlduxCase s!"fuzz/type/slice-not-slice/width-{width}" #[badSlice, intV width], rng3)
  else if shape = 15 then
    let (badPick, rng2) := randNat rng1 0 2
    let badSlice : Value := if badPick = 0 then .null else if badPick = 1 then .cell refLeafA else .builder Builder.empty
    (mkPlduxCase "fuzz/error-order/range-before-slice-type" #[badSlice, intV 4096], rng2)
  else if shape = 16 then
    let (badPick, rng2) := randNat rng1 0 2
    let badSlice : Value := if badPick = 0 then .null else if badPick = 1 then .cell refLeafB else .builder Builder.empty
    (mkPlduxCase "fuzz/error-order/width-type-before-slice-type" #[badSlice, .null], rng2)
  else if shape = 17 then
    let (bitCount, rng2) := randNat rng1 0 96
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkPlduxCase "fuzz/gas/exact"
      #[.slice slice, intV 0]
      #[.pushInt (.num plduxSetGasExact), .tonEnvOp .setGasLimit, plduxInstr], rng3)
  else if shape = 18 then
    let (bitCount, rng2) := randNat rng1 0 96
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkPlduxCase "fuzz/gas/exact-minus-one"
      #[.slice slice, intV 0]
      #[.pushInt (.num plduxSetGasExactMinusOne), .tonEnvOp .setGasLimit, plduxInstr], rng3)
  else
    let maxSlice : Slice := mkSliceFromBits (Array.replicate 256 true)
    (mkPlduxCase "fuzz/ok/max-unsigned-256" #[.slice maxSlice, intV 256], rng1)

private def oracleSlice0 : Slice := mkPatternSlice 0
private def oracleSlice1 : Slice := mkPatternSlice 1
private def oracleSlice4 : Slice := mkPatternSlice 4
private def oracleSlice5 : Slice := mkPatternSlice 5
private def oracleSlice8 : Slice := mkPatternSlice 8
private def oracleSlice13 : Slice := mkPatternSlice 13
private def oracleSlice31 : Slice := mkPatternSlice 31
private def oracleSlice64 : Slice := mkPatternSlice 64
private def oracleSlice127 : Slice := mkPatternSlice 127
private def oracleSlice128 : Slice := mkPatternSlice 128
private def oracleSlice255 : Slice := mkPatternSlice 255
private def oracleSlice256 : Slice := mkPatternSlice 256

private def oracleSliceWithRefs6 : Slice := mkPatternSliceWithRefs 6 #[refLeafA, refLeafB]
private def oracleSliceWithRefs9 : Slice := mkPatternSliceWithRefs 9 #[refLeafA]

private def oracleSlice8Tail11 : Slice := mkSliceFromBits (mkPatternBits 8 ++ tailBits11)
private def oracleSlice128Tail17 : Slice := mkSliceFromBits (mkPatternBits 128 ++ tailBits17)
private def oracleSlice256Tail6 : Slice := mkSliceFromBits (mkPatternBits 256 ++ tailBits6)

private def partialCell : Cell := Cell.mkOrdinary (mkPatternBits 40) #[refLeafA, refLeafB]
private def partialSlice : Slice := { cell := partialCell, bitPos := 7, refPos := 1 }

private def shortPartialCell : Cell := Cell.mkOrdinary (mkPatternBits 24) #[refLeafA]
private def shortPartialSlice : Slice := { cell := shortPartialCell, bitPos := 15, refPos := 0 }

private def loadIntFixedWord24 (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) +
      (if prefetch then 2 else 0) +
        (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

def suite : InstrSuite where
  id := plduxId
  unit := #[
    { name := "unit/direct/prefetch-success-pushes-int-only"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (0, mkPatternSlice 11),
            (1, mkPatternSlice 1),
            (3, mkPatternSlice 8),
            (8, mkSliceFromBits (mkPatternBits 8 ++ tailBits6)),
            (64, mkPatternSlice 96),
            (255, mkPatternSlice 255),
            (256, mkSliceFromBits (mkPatternBits 256 ++ tailBits11)),
            (256, mkSliceFromBits (Array.replicate 256 true))
          ]
        for check in checks do
          let width := check.1
          let source := check.2
          expectOkStack s!"ok/width-{width}/bits-{source.bitsRemaining}"
            (runPlduxDirect #[.slice source, intV width])
            (expectedSuccessStack #[] source width)

        let zeroWithRefs := mkPatternSliceWithRefs 9 #[refLeafA, refLeafB]
        expectOkStack "ok/width0-with-refs-still-zero"
          (runPlduxDirect #[.slice zeroWithRefs, intV 0])
          (expectedSuccessStack #[] zeroWithRefs 0)

        let deepSource := mkPatternSliceWithRefs 18 #[refLeafA, refLeafB]
        let deepPrefix : Array Value := #[.null, intV 99, .cell refLeafA]
        expectOkStack "ok/deep-stack-order-preserved"
          (runPlduxDirect (deepPrefix ++ #[.slice deepSource, intV 5]))
          (expectedSuccessStack deepPrefix deepSource 5)

        expectOkStack "ok/partial-slice-cursor"
          (runPlduxDirect #[.slice partialSlice, intV 12])
          (expectedSuccessStack #[] partialSlice 12) }
    ,
    { name := "unit/direct/cellund-when-width-exceeds-bits"
      run := do
        expectErr "cellund/empty-width1"
          (runPlduxDirect #[.slice (mkSliceFromBits #[]), intV 1]) .cellUnd
        expectErr "cellund/short-4-vs5"
          (runPlduxDirect #[.slice (mkPatternSlice 4), intV 5]) .cellUnd
        expectErr "cellund/short-255-vs256"
          (runPlduxDirect #[.slice (mkPatternSlice 255), intV 256]) .cellUnd
        let refsShort := mkPatternSliceWithRefs 6 #[refLeafA, refLeafB]
        expectErr "cellund/refs-short-6-vs7"
          (runPlduxDirect #[.slice refsShort, intV 7]) .cellUnd
        expectErr "cellund/partial-slice-short"
          (runPlduxDirect #[.slice shortPartialSlice, intV 10]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-error-order"
      run := do
        expectErr "underflow/empty" (runPlduxDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runPlduxDirect #[.slice (mkPatternSlice 3)]) .stkUnd
        expectErr "underflow/one-item-width"
          (runPlduxDirect #[intV 7]) .stkUnd
        expectErr "underflow/one-item-null"
          (runPlduxDirect #[.null]) .stkUnd

        expectErr "type/width-not-int-null"
          (runPlduxDirect #[.slice (mkPatternSlice 3), .null]) .typeChk
        expectErr "type/width-not-int-cell"
          (runPlduxDirect #[.slice (mkPatternSlice 3), .cell refLeafA]) .typeChk
        expectErr "type/slice-not-slice-after-valid-width"
          (runPlduxDirect #[.null, intV 0]) .typeChk
        expectErr "type/slice-not-slice-cell-after-valid-width"
          (runPlduxDirect #[.cell refLeafB, intV 1]) .typeChk

        expectErr "range/width-negative"
          (runPlduxDirect #[.slice (mkPatternSlice 3), intV (-1)]) .rangeChk
        expectErr "range/width-too-large-257"
          (runPlduxDirect #[.slice (mkPatternSlice 3), intV 257]) .rangeChk
        expectErr "range/width-too-large-1024"
          (runPlduxDirect #[.slice (mkPatternSlice 3), intV 1024]) .rangeChk
        expectErr "range/width-nan"
          (runPlduxDirect #[.slice (mkPatternSlice 3), .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-type"
          (runPlduxDirect #[.null, intV 2048]) .rangeChk
        expectErr "error-order/width-type-before-slice-type"
          (runPlduxDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[
          .loadIntVar false false false,
          .loadIntVar true false false,
          .loadIntVar false true false,
          plduxInstr,
          .loadIntVar false false true,
          .loadIntVar true false true,
          .loadIntVar false true true,
          .loadIntVar true true true,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldix" s0 (.loadIntVar false false false) 16
        let s2 ← expectDecodeStep "decode/ldux-neighbor" s1 (.loadIntVar true false false) 16
        let s3 ← expectDecodeStep "decode/pldix-neighbor" s2 (.loadIntVar false true false) 16
        let s4 ← expectDecodeStep "decode/pldux" s3 plduxInstr 16
        let s5 ← expectDecodeStep "decode/ldixq-neighbor" s4 (.loadIntVar false false true) 16
        let s6 ← expectDecodeStep "decode/lduxq-neighbor" s5 (.loadIntVar true false true) 16
        let s7 ← expectDecodeStep "decode/pldixq-neighbor" s6 (.loadIntVar false true true) 16
        let s8 ← expectDecodeStep "decode/plduxq-neighbor" s7 (.loadIntVar true true true) 16
        let s9 ← expectDecodeStep "decode/tail-add" s8 .add 8
        if s9.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s9.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [plduxInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits plduxOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldux: expected 0xd703 16-bit encoding, got bit-length {singleCode.bits.size}")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawFamilyBits : BitString :=
          natToBits 0xd700 16 ++ natToBits 0xd701 16 ++ natToBits 0xd702 16 ++ natToBits 0xd703 16 ++
            natToBits 0xd704 16 ++ natToBits 0xd705 16 ++ natToBits 0xd706 16 ++ natToBits 0xd707 16 ++ addCode.bits
        let rawFamily := mkSliceFromBits rawFamilyBits
        let r1 ← expectDecodeStep "decode/raw-0xd700" rawFamily (.loadIntVar false false false) 16
        let r2 ← expectDecodeStep "decode/raw-0xd701" r1 (.loadIntVar true false false) 16
        let r3 ← expectDecodeStep "decode/raw-0xd702" r2 (.loadIntVar false true false) 16
        let r4 ← expectDecodeStep "decode/raw-0xd703" r3 plduxInstr 16
        let r5 ← expectDecodeStep "decode/raw-0xd704" r4 (.loadIntVar false false true) 16
        let r6 ← expectDecodeStep "decode/raw-0xd705" r5 (.loadIntVar true false true) 16
        let r7 ← expectDecodeStep "decode/raw-0xd706" r6 (.loadIntVar false true true) 16
        let r8 ← expectDecodeStep "decode/raw-0xd707" r7 (.loadIntVar true true true) 16
        let r9 ← expectDecodeStep "decode/raw-tail-add" r8 .add 8
        if r9.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-family-end: expected exhausted slice, got {r9.bitsRemaining} bits remaining")

        let fixedNeighborWord : Nat := loadIntFixedWord24 true true false 8
        let rawBoundaryBits : BitString :=
          natToBits 0xd707 16 ++ natToBits fixedNeighborWord 24 ++ addCode.bits
        let b0 := mkSliceFromBits rawBoundaryBits
        let b1 ← expectDecodeStep "decode/raw-boundary-0xd707-plduxq" b0 (.loadIntVar true true true) 16
        let b2 ← expectDecodeStep "decode/raw-boundary-loadint-fixed" b1 (.loadInt true true false 8) 24
        let b3 ← expectDecodeStep "decode/raw-boundary-tail-add" b2 .add 8
        if b3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-boundary-end: expected exhausted slice, got {b3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-loadintvar-add"
          (runPlduxDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-loadintvar-fixed-neighbor"
          (runPlduxDispatchFallback (.loadInt true true false 8) #[intV 9])
          #[intV 9, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPlduxCase "ok/width0-empty-slice" #[.slice oracleSlice0, intV 0],
    mkPlduxCase "ok/width0-nonempty-slice" #[.slice oracleSlice13, intV 0],
    mkPlduxCase "ok/width1-exact" #[.slice oracleSlice1, intV 1],
    mkPlduxCase "ok/width3-of-5" #[.slice oracleSlice5, intV 3],
    mkPlduxCase "ok/width8-exact" #[.slice oracleSlice8, intV 8],
    mkPlduxCase "ok/width8-with-tail" #[.slice oracleSlice8Tail11, intV 8],
    mkPlduxCase "ok/width31-exact" #[.slice oracleSlice31, intV 31],
    mkPlduxCase "ok/width64-exact" #[.slice oracleSlice64, intV 64],
    mkPlduxCase "ok/width127-exact" #[.slice oracleSlice127, intV 127],
    mkPlduxCase "ok/width128-with-tail" #[.slice oracleSlice128Tail17, intV 128],
    mkPlduxCase "ok/width255-exact" #[.slice oracleSlice255, intV 255],
    mkPlduxCase "ok/width256-exact" #[.slice oracleSlice256, intV 256],
    mkPlduxCase "ok/width256-with-tail" #[.slice oracleSlice256Tail6, intV 256],
    mkPlduxCase "ok/refs-in-input-slice" #[.slice oracleSliceWithRefs9, intV 4],
    mkPlduxCase "ok/deep-stack-preserve-noise"
      #[.null, .cell refLeafB, .slice oracleSlice13, intV 5],

    mkPlduxCase "cellund/empty-width1" #[.slice oracleSlice0, intV 1],
    mkPlduxCase "cellund/short-4-vs5" #[.slice oracleSlice4, intV 5],
    mkPlduxCase "cellund/short-255-vs256" #[.slice oracleSlice255, intV 256],
    mkPlduxCase "cellund/refs-short-6-vs7" #[.slice oracleSliceWithRefs6, intV 7],

    mkPlduxCase "range/width-negative" #[.slice oracleSlice13, intV (-1)],
    mkPlduxCase "range/width-too-large-257" #[.slice oracleSlice13, intV 257],
    mkPlduxCase "range/width-too-large-1024" #[.slice oracleSlice13, intV 1024],
    mkPlduxProgramCase "range/width-nan-via-program"
      #[.slice oracleSlice13]
      #[.pushInt .nan, plduxInstr],

    mkPlduxCase "underflow/empty" #[],
    mkPlduxCase "underflow/one-item-slice" #[.slice oracleSlice13],
    mkPlduxCase "underflow/one-item-width" #[intV 0],

    mkPlduxCase "type/width-top-null" #[.slice oracleSlice13, .null],
    mkPlduxCase "type/width-top-cell" #[.slice oracleSlice13, .cell refLeafA],
    mkPlduxCase "type/slice-not-slice-after-valid-width" #[.null, intV 0],
    mkPlduxCase "error-order/range-before-slice-type" #[.null, intV 2048],
    mkPlduxCase "error-order/width-type-before-slice-type" #[.null, .null],

    mkPlduxCase "gas/exact-cost-succeeds"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num plduxSetGasExact), .tonEnvOp .setGasLimit, plduxInstr],
    mkPlduxCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num plduxSetGasExactMinusOne), .tonEnvOp .setGasLimit, plduxInstr]
  ]
  fuzz := #[
    { seed := 2026021017
      count := 500
      gen := genPlduxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDUX
