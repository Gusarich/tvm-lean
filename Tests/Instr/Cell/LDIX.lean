import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDIX

/-- LDIX branch-mapping notes (Lean + C++ authority).

Lean analyzed files:
- `TvmLean/Semantics/Exec/Cell/LoadIntVar.lean`
  (`.loadIntVar unsigned=false prefetch=false quiet=false`)
- `TvmLean/Model/Instr/Asm/Cp0.lean`
  (`.loadIntVar` encode: `0xd700 + args3`, so LDIX = `0xd700`)
- `TvmLean/Model/Instr/Codepage/Cp0.lean`
  (`0xd700..0xd707` decode to `.loadIntVar unsigned prefetch quiet`)
- `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
  (shared fixed-form core behavior used as a direct proxy on shared domain `bits ∈ [1, 256]`)

C++ authority:
- `~/Coding/ton/crypto/vm/cellops.cpp`
  (`exec_load_int_var`, `exec_load_int_common`, mode=`0` for LDIX).

Branch map covered by this suite:
- `checkUnderflow 2` before any pop;
- width pop via `popNatUpTo 257` (type/range from `popInt`, including NaN);
- slice pop type check only after width checks succeed;
- success contract in non-prefetch mode: push signed int then remainder slice;
- insufficient bits path throws `cellUnd` in non-quiet mode;
- opcode decode/dispatch checks for LDIX family + `0xd6ff/0xd700/0xd708` boundary;
- assembler constraints (`.loadIntVar` assembleable, `.loadInt ...` fixed family rejected by assembler).
-/

private def ldixId : InstrId := { name := "LDIX" }

private def ldixInstr : Instr := .loadIntVar false false false

private def ldixOpcode : Nat := 0xd700

private def dispatchSentinel : Int := 701

private def mkLdixCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldixInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldixId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdixProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkLdixCase name stack program gasLimits fuel

private def runLdixDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar ldixInstr stack

private def runLdixFixed2Direct (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (.loadInt false false false bits) stack

private def runLdixDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadIntVar instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (ldixRes fixedRes : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match ldixRes, fixedRes with
    | .ok lv, .ok fv => lv == fv
    | .error le, .error fe => le == fe
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got ldix={reprStr ldixRes}, fixed={reprStr fixedRes}")

private def ldixSetGasExact : Int :=
  computeExactGasBudget ldixInstr

private def ldixSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldixInstr

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

private def expectedSigned (source : Slice) (width : Nat) : Int :=
  bitsToIntSignedTwos (source.readBits width)

private def expectedSuccessStack
    (below : Array Value)
    (source : Slice)
    (width : Nat) : Array Value :=
  below ++ #[intV (expectedSigned source width), .slice (source.advanceBits width)]

private def widthBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 192, 255, 256, 257]

private def pickWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (widthBoundaryPool.size - 1)
  (widthBoundaryPool[idx]!, rng')

private def pickWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickWidthBoundary rng1
  else
    randNat rng1 0 257

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

private def signedMin257Bits : BitString :=
  #[true] ++ Array.replicate 256 false

private def signedMax257Bits : BitString :=
  #[false] ++ Array.replicate 256 true

private def signedNegOne257Bits : BitString :=
  Array.replicate 257 true

private def genLdixFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  if shape = 0 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdixCase s!"fuzz/ok/exact-width-{width}" #[.slice slice, intV width], rng3)
  else if shape = 1 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 64 (257 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    (mkLdixCase s!"fuzz/ok/with-tail/width-{width}/extra-{extra}" #[.slice slice, intV width], rng4)
  else if shape = 2 then
    let (bitCount, rng2) := randNat rng1 0 257
    let (slice, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdixCase s!"fuzz/ok/width-zero/bits-{bitCount}" #[.slice slice, intV 0], rng3)
  else if shape = 3 then
    let (width, rng2) := pickWidthMixed rng1
    let (refs, rng3) := pickRefsPack rng2
    let extraCap := Nat.min 32 (257 - width)
    let (extra, rng4) := randNat rng3 0 extraCap
    let (slice, rng5) := mkRandomSlice (width + extra) refs rng4
    (mkLdixCase s!"fuzz/ok/refs/width-{width}/refs-{refs.size}" #[.slice slice, intV width], rng5)
  else if shape = 4 then
    let (width, rng2) := pickWidthMixed rng1
    let extraCap := Nat.min 16 (257 - width)
    let (extra, rng3) := randNat rng2 0 extraCap
    let (slice, rng4) := mkRandomSlice (width + extra) #[] rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkLdixCase s!"fuzz/ok/deep-noise/width-{width}" #[noise, .slice slice, intV width], rng5)
  else if shape = 5 then
    let (availableBits, rng2) := randNat rng1 0 256
    let width := availableBits + 1
    let (slice, rng3) := mkRandomSlice availableBits #[] rng2
    (mkLdixCase s!"fuzz/cellund/short-by-one/bits-{availableBits}" #[.slice slice, intV width], rng3)
  else if shape = 6 then
    let (width, rng2) := randNat rng1 1 257
    (mkLdixCase s!"fuzz/cellund/empty-slice/width-{width}" #[.slice (mkSliceFromBits #[]), intV width], rng2)
  else if shape = 7 then
    let (width, rng2) := randNat rng1 1 257
    let maxDelta := Nat.min 16 width
    let (delta, rng3) := randNat rng2 1 maxDelta
    let availableBits := width - delta
    let (slice, rng4) := mkRandomSlice availableBits #[] rng3
    (mkLdixCase s!"fuzz/cellund/random-short/avail-{availableBits}/width-{width}" #[.slice slice, intV width], rng4)
  else if shape = 8 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdixCase s!"fuzz/range/negative-width/width-{width}" #[.slice slice, intV (-1)], rng3)
  else if shape = 9 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (delta, rng4) := randNat rng3 1 2048
    let tooLargeWidth : Int := Int.ofNat (257 + delta)
    (mkLdixCase s!"fuzz/range/too-large-width-{tooLargeWidth}" #[.slice slice, intV tooLargeWidth], rng4)
  else if shape = 10 then
    let (width, rng2) := randNat rng1 0 129
    let (slice, rng3) := mkRandomSlice width #[] rng2
    (mkLdixProgramCase "fuzz/range/width-nan-via-program"
      #[.slice slice]
      #[.pushInt .nan, ldixInstr], rng3)
  else if shape = 11 then
    (mkLdixCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkLdixCase "fuzz/underflow/one-item-slice" #[.slice (mkSliceFromBits #[])], rng2)
    else
      (mkLdixCase "fuzz/underflow/one-item-width" #[intV 0], rng2)
  else if shape = 13 then
    let (width, rng2) := pickWidthMixed rng1
    let (slice, rng3) := mkRandomSlice width #[] rng2
    let (badPick, rng4) := randNat rng3 0 2
    let badWidth : Value :=
      if badPick = 0 then .null else if badPick = 1 then .cell refLeafA else .slice (mkSliceFromBits #[])
    (mkLdixCase "fuzz/type/width-not-int" #[.slice slice, badWidth], rng4)
  else if shape = 14 then
    let (width, rng2) := pickWidthMixed rng1
    let (badPick, rng3) := randNat rng2 0 3
    let badSlice : Value :=
      if badPick = 0 then .null else if badPick = 1 then intV 9 else if badPick = 2 then .cell refLeafB else .builder Builder.empty
    (mkLdixCase s!"fuzz/type/slice-not-slice/width-{width}" #[badSlice, intV width], rng3)
  else if shape = 15 then
    let (badPick, rng2) := randNat rng1 0 2
    let badSlice : Value := if badPick = 0 then .null else if badPick = 1 then .cell refLeafA else .builder Builder.empty
    (mkLdixCase "fuzz/error-order/range-before-slice-type" #[badSlice, intV 4096], rng2)
  else if shape = 16 then
    let (badSlicePick, rng2) := randNat rng1 0 2
    let badSlice : Value :=
      if badSlicePick = 0 then .null else if badSlicePick = 1 then .cell refLeafA else .builder Builder.empty
    let (badWidthPick, rng3) := randNat rng2 0 2
    let badWidth : Value :=
      if badWidthPick = 0 then .null else if badWidthPick = 1 then .cell refLeafB else .slice (mkSliceFromBits #[])
    (mkLdixCase "fuzz/error-order/width-type-before-slice-type" #[badSlice, badWidth], rng3)
  else if shape = 17 then
    (mkLdixCase "fuzz/gas/exact"
      #[.slice (mkSliceFromBits (mkPatternBits 8 ++ tailBits11)), intV 8]
      #[.pushInt (.num ldixSetGasExact), .tonEnvOp .setGasLimit, ldixInstr], rng1)
  else if shape = 18 then
    (mkLdixCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSliceFromBits (mkPatternBits 8 ++ tailBits11)), intV 8]
      #[.pushInt (.num ldixSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixInstr], rng1)
  else if shape = 19 then
    let (pick, rng2) := randNat rng1 0 2
    let edgeSlice :=
      if pick = 0 then mkSliceFromBits signedMin257Bits
      else if pick = 1 then mkSliceFromBits signedMax257Bits
      else mkSliceFromBits (signedNegOne257Bits ++ tailBits6)
    (mkLdixCase s!"fuzz/ok/signed257-edge-{pick}" #[.slice edgeSlice, intV 257], rng2)
  else
    let (extra, rng2) := randNat rng1 0 32
    let edge := mkSliceFromBits (mkPatternBits 257 ++ mkPatternBits extra)
    (mkLdixCase s!"fuzz/ok/width257-with-tail-extra-{extra}" #[.slice edge, intV 257], rng2)

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
private def oracleSlice257 : Slice := mkPatternSlice 257

private def oracleSliceWithRefs6 : Slice := mkPatternSliceWithRefs 6 #[refLeafA, refLeafB]
private def oracleSliceWithRefs9 : Slice := mkPatternSliceWithRefs 9 #[refLeafA]

private def oracleSlice8Tail11 : Slice := mkSliceFromBits (mkPatternBits 8 ++ tailBits11)
private def oracleSlice128Tail17 : Slice := mkSliceFromBits (mkPatternBits 128 ++ tailBits17)
private def oracleSlice257Tail6 : Slice := mkSliceFromBits (mkPatternBits 257 ++ tailBits6)

private def oracleSlice257Min : Slice := mkSliceFromBits signedMin257Bits
private def oracleSlice257Max : Slice := mkSliceFromBits signedMax257Bits
private def oracleSlice257NegOneTail6 : Slice := mkSliceFromBits (signedNegOne257Bits ++ tailBits6)

private def partialCell : Cell := Cell.mkOrdinary (mkPatternBits 56) #[refLeafA, refLeafB]
private def partialSlice : Slice := { cell := partialCell, bitPos := 9, refPos := 1 }

private def shortPartialCell : Cell := Cell.mkOrdinary (mkPatternBits 24) #[refLeafA]
private def shortPartialSlice : Slice := { cell := shortPartialCell, bitPos := 15, refPos := 0 }

private def loadIntFixedWord24 (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

def suite : InstrSuite where
  id := ldixId
  unit := #[
    { name := "unit/direct/non-prefetch-success-pushes-signed-int-and-remainder"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (0, mkPatternSlice 11),
            (1, mkSliceFromBits (#[false] ++ tailBits6)),
            (1, mkSliceFromBits (#[true] ++ tailBits6)),
            (8, mkSliceFromBits (natToBits 127 8 ++ tailBits6)),
            (8, mkSliceFromBits (natToBits 128 8 ++ tailBits6)),
            (16, mkSliceFromBits (natToBits 32769 16 ++ tailBits11)),
            (64, mkPatternSlice 96),
            (255, mkPatternSlice 255),
            (256, mkSliceFromBits (mkPatternBits 256 ++ tailBits11)),
            (257, mkPatternSlice 257),
            (257, mkSliceFromBits (signedNegOne257Bits ++ tailBits6))
          ]
        for check in checks do
          let width := check.1
          let source := check.2
          expectOkStack s!"ok/width-{width}/bits-{source.bitsRemaining}"
            (runLdixDirect #[.slice source, intV width])
            (expectedSuccessStack #[] source width)

        expectOkStack "ok/width257-min-int257"
          (runLdixDirect #[.slice oracleSlice257Min, intV 257])
          #[intV minInt257, .slice (oracleSlice257Min.advanceBits 257)]
        expectOkStack "ok/width257-max-int257"
          (runLdixDirect #[.slice oracleSlice257Max, intV 257])
          #[intV maxInt257, .slice (oracleSlice257Max.advanceBits 257)]

        let zeroWithRefs := mkPatternSliceWithRefs 9 #[refLeafA, refLeafB]
        expectOkStack "ok/width0-with-refs-still-zero"
          (runLdixDirect #[.slice zeroWithRefs, intV 0])
          (expectedSuccessStack #[] zeroWithRefs 0)

        let deepSource := mkPatternSliceWithRefs 18 #[refLeafA, refLeafB]
        let deepPrefix : Array Value := #[.null, intV 99, .cell refLeafA]
        expectOkStack "ok/deep-stack-order-preserved"
          (runLdixDirect (deepPrefix ++ #[.slice deepSource, intV 5]))
          (expectedSuccessStack deepPrefix deepSource 5)

        expectOkStack "ok/partial-slice-cursor"
          (runLdixDirect #[.slice partialSlice, intV 12])
          (expectedSuccessStack #[] partialSlice 12) }
    ,
    { name := "unit/direct/cellund-when-width-exceeds-bits"
      run := do
        expectErr "cellund/empty-width1"
          (runLdixDirect #[.slice (mkSliceFromBits #[]), intV 1]) .cellUnd
        expectErr "cellund/short-4-vs5"
          (runLdixDirect #[.slice (mkPatternSlice 4), intV 5]) .cellUnd
        expectErr "cellund/short-255-vs256"
          (runLdixDirect #[.slice (mkPatternSlice 255), intV 256]) .cellUnd
        expectErr "cellund/short-256-vs257"
          (runLdixDirect #[.slice (mkPatternSlice 256), intV 257]) .cellUnd
        let refsShort := mkPatternSliceWithRefs 6 #[refLeafA, refLeafB]
        expectErr "cellund/refs-short-6-vs7"
          (runLdixDirect #[.slice refsShort, intV 7]) .cellUnd
        expectErr "cellund/partial-slice-short"
          (runLdixDirect #[.slice shortPartialSlice, intV 10]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-error-order"
      run := do
        expectErr "underflow/empty" (runLdixDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runLdixDirect #[.slice (mkPatternSlice 3)]) .stkUnd
        expectErr "underflow/one-item-width"
          (runLdixDirect #[intV 7]) .stkUnd
        expectErr "underflow/one-item-null"
          (runLdixDirect #[.null]) .stkUnd

        expectErr "type/width-not-int-null"
          (runLdixDirect #[.slice (mkPatternSlice 3), .null]) .typeChk
        expectErr "type/width-not-int-cell"
          (runLdixDirect #[.slice (mkPatternSlice 3), .cell refLeafA]) .typeChk
        expectErr "type/slice-not-slice-after-valid-width"
          (runLdixDirect #[.null, intV 0]) .typeChk
        expectErr "type/slice-not-slice-cell-after-valid-width"
          (runLdixDirect #[.cell refLeafB, intV 1]) .typeChk
        expectErr "type/slice-not-slice-after-width257"
          (runLdixDirect #[.builder Builder.empty, intV 257]) .typeChk

        expectErr "range/width-negative"
          (runLdixDirect #[.slice (mkPatternSlice 3), intV (-1)]) .rangeChk
        expectErr "range/width-too-large-258"
          (runLdixDirect #[.slice (mkPatternSlice 3), intV 258]) .rangeChk
        expectErr "range/width-too-large-4096"
          (runLdixDirect #[.slice (mkPatternSlice 3), intV 4096]) .rangeChk
        expectErr "range/width-nan"
          (runLdixDirect #[.slice (mkPatternSlice 3), .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-type"
          (runLdixDirect #[.null, intV 4096]) .rangeChk
        expectErr "error-order/width-type-before-slice-type"
          (runLdixDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[
          ldixInstr,
          .loadIntVar true false false,
          .loadIntVar false true false,
          .loadIntVar true true false,
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
        let s1 ← expectDecodeStep "decode/ldix" s0 ldixInstr 16
        let s2 ← expectDecodeStep "decode/ldux-neighbor" s1 (.loadIntVar true false false) 16
        let s3 ← expectDecodeStep "decode/pldix-neighbor" s2 (.loadIntVar false true false) 16
        let s4 ← expectDecodeStep "decode/pldux-neighbor" s3 (.loadIntVar true true false) 16
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
          match assembleCp0 [ldixInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits ldixOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldix: expected 0xd700 16-bit encoding, got bit-length {singleCode.bits.size}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldix: expected 16 bits, got {singleCode.bits.size}")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawFamilyBits : BitString :=
          natToBits 0xd700 16 ++ natToBits 0xd701 16 ++ natToBits 0xd702 16 ++ natToBits 0xd703 16 ++
            natToBits 0xd704 16 ++ natToBits 0xd705 16 ++ natToBits 0xd706 16 ++ natToBits 0xd707 16 ++ addCode.bits
        let rawFamily := mkSliceFromBits rawFamilyBits
        let r1 ← expectDecodeStep "decode/raw-0xd700-ldix" rawFamily ldixInstr 16
        let r2 ← expectDecodeStep "decode/raw-0xd701" r1 (.loadIntVar true false false) 16
        let r3 ← expectDecodeStep "decode/raw-0xd702" r2 (.loadIntVar false true false) 16
        let r4 ← expectDecodeStep "decode/raw-0xd703" r3 (.loadIntVar true true false) 16
        let r5 ← expectDecodeStep "decode/raw-0xd704" r4 (.loadIntVar false false true) 16
        let r6 ← expectDecodeStep "decode/raw-0xd705" r5 (.loadIntVar true false true) 16
        let r7 ← expectDecodeStep "decode/raw-0xd706" r6 (.loadIntVar false true true) 16
        let r8 ← expectDecodeStep "decode/raw-0xd707" r7 (.loadIntVar true true true) 16
        let r9 ← expectDecodeStep "decode/raw-tail-add" r8 .add 8
        if r9.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-family-end: expected exhausted slice, got {r9.bitsRemaining} bits remaining")

        let rawPrefixBoundaryBits : BitString :=
          natToBits 0xd6ff 16 ++ natToBits ldixOpcode 16 ++ addCode.bits
        let p0 := mkSliceFromBits rawPrefixBoundaryBits
        let p1 ← expectDecodeStep "decode/raw-boundary-0xd6ff-ldslice256" p0 (.loadSliceFixed false false 256) 16
        let p2 ← expectDecodeStep "decode/raw-boundary-0xd700-ldix" p1 ldixInstr 16
        let p3 ← expectDecodeStep "decode/raw-boundary-tail-add" p2 .add 8
        if p3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-prefix-boundary-end: expected exhausted slice, got {p3.bitsRemaining} bits remaining")

        let fixedNeighborWord : Nat := loadIntFixedWord24 false false false 8
        let rawFixedBoundaryBits : BitString :=
          natToBits 0xd707 16 ++ natToBits fixedNeighborWord 24 ++ addCode.bits
        let b0 := mkSliceFromBits rawFixedBoundaryBits
        let b1 ← expectDecodeStep "decode/raw-fixed-boundary-0xd707-plduxq" b0 (.loadIntVar true true true) 16
        let b2 ← expectDecodeStep "decode/raw-fixed-boundary-0xd708-loadint" b1 (.loadInt false false false 8) 24
        let b3 ← expectDecodeStep "decode/raw-fixed-boundary-tail-add" b2 .add 8
        if b3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-fixed-boundary-end: expected exhausted slice, got {b3.bitsRemaining} bits remaining")

        match assembleCp0 [.loadInt false false false 8] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/loadInt-fixed-8: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/loadInt-fixed-8: expected invOpcode, got success")

        match assembleCp0 [.loadInt false false false 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/loadInt-fixed-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/loadInt-fixed-256: expected invOpcode, got success")

        match assembleCp0 [.loadInt false false false 257] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/loadInt-fixed-257: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/loadInt-fixed-257: expected invOpcode, got success") }
    ,
    { name := "unit/proxy/fixed2-loadint-aligns-on-shared-domain"
      run := do
        let okChecks : Array (Nat × Slice) :=
          #[
            (1, mkSliceFromBits (#[true] ++ tailBits6)),
            (8, mkSliceFromBits (natToBits 0xa5 8 ++ tailBits11)),
            (32, mkPatternSlice 48),
            (256, mkSliceFromBits (mkPatternBits 256 ++ tailBits6))
          ]
        for (bits, input) in okChecks do
          expectSameOutcome s!"align/ok/bits-{bits}"
            (runLdixDirect #[.slice input, intV bits])
            (runLdixFixed2Direct bits #[.slice input])

        let insuff : Array (Nat × Nat) := #[(1, 0), (8, 7), (256, 255)]
        for (bits, available) in insuff do
          let slice := mkSliceFromBits (mkPatternBits available)
          expectSameOutcome s!"align/cellund/bits-{bits}/avail-{available}"
            (runLdixDirect #[.slice slice, intV bits])
            (runLdixFixed2Direct bits #[.slice slice])

        expectSameOutcome "align/underflow-empty"
          (runLdixDirect #[])
          (runLdixFixed2Direct 8 #[])
        expectSameOutcome "align/type-top-null"
          (runLdixDirect #[.null, intV 8])
          (runLdixFixed2Direct 8 #[.null]) }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-loadintvar-add"
          (runLdixDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-loadintvar-fixed-neighbor"
          (runLdixDispatchFallback (.loadInt false false false 8) #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/non-loadintvar-slice-neighbor"
          (runLdixDispatchFallback (.loadSliceX false false) #[.cell refLeafA])
          #[.cell refLeafA, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdixCase "ok/width0-empty-slice" #[.slice oracleSlice0, intV 0],
    mkLdixCase "ok/width0-nonempty-slice" #[.slice oracleSlice13, intV 0],
    mkLdixCase "ok/width1-exact" #[.slice oracleSlice1, intV 1],
    mkLdixCase "ok/width1-negative" #[.slice (mkSliceFromBits #[true]), intV 1],
    mkLdixCase "ok/width3-of-5" #[.slice oracleSlice5, intV 3],
    mkLdixCase "ok/width8-positive-127" #[.slice (mkSliceFromBits (natToBits 127 8)), intV 8],
    mkLdixCase "ok/width8-negative-128" #[.slice (mkSliceFromBits (natToBits 128 8)), intV 8],
    mkLdixCase "ok/width8-with-tail" #[.slice oracleSlice8Tail11, intV 8],
    mkLdixCase "ok/width31-exact" #[.slice oracleSlice31, intV 31],
    mkLdixCase "ok/width64-exact" #[.slice oracleSlice64, intV 64],
    mkLdixCase "ok/width127-exact" #[.slice oracleSlice127, intV 127],
    mkLdixCase "ok/width128-with-tail" #[.slice oracleSlice128Tail17, intV 128],
    mkLdixCase "ok/width255-exact" #[.slice oracleSlice255, intV 255],
    mkLdixCase "ok/width256-exact" #[.slice oracleSlice256, intV 256],
    mkLdixCase "ok/width257-exact" #[.slice oracleSlice257, intV 257],
    mkLdixCase "ok/width257-with-tail" #[.slice oracleSlice257Tail6, intV 257],
    mkLdixCase "ok/width257-min-int257" #[.slice oracleSlice257Min, intV 257],
    mkLdixCase "ok/width257-max-int257" #[.slice oracleSlice257Max, intV 257],
    mkLdixCase "ok/width257-negone-with-tail" #[.slice oracleSlice257NegOneTail6, intV 257],
    mkLdixCase "ok/refs-in-input-slice" #[.slice oracleSliceWithRefs9, intV 4],
    mkLdixCase "ok/deep-stack-preserve-noise"
      #[.null, .cell refLeafB, .slice oracleSlice13, intV 5],

    mkLdixCase "cellund/empty-width1" #[.slice oracleSlice0, intV 1],
    mkLdixCase "cellund/short-4-vs5" #[.slice oracleSlice4, intV 5],
    mkLdixCase "cellund/short-255-vs256" #[.slice oracleSlice255, intV 256],
    mkLdixCase "cellund/short-256-vs257" #[.slice oracleSlice256, intV 257],
    mkLdixCase "cellund/refs-short-6-vs7" #[.slice oracleSliceWithRefs6, intV 7],

    mkLdixCase "range/width-negative" #[.slice oracleSlice13, intV (-1)],
    mkLdixCase "range/width-too-large-258" #[.slice oracleSlice13, intV 258],
    mkLdixCase "range/width-too-large-4096" #[.slice oracleSlice13, intV 4096],
    mkLdixProgramCase "range/width-nan-via-program"
      #[.slice oracleSlice13]
      #[.pushInt .nan, ldixInstr],

    mkLdixCase "underflow/empty" #[],
    mkLdixCase "underflow/one-item-slice" #[.slice oracleSlice13],
    mkLdixCase "underflow/one-item-width" #[intV 0],

    mkLdixCase "type/width-top-null" #[.slice oracleSlice13, .null],
    mkLdixCase "type/width-top-cell" #[.slice oracleSlice13, .cell refLeafA],
    mkLdixCase "type/slice-not-slice-after-valid-width" #[.null, intV 0],
    mkLdixCase "error-order/range-before-slice-type" #[.null, intV 4096],
    mkLdixCase "error-order/width-type-before-slice-type" #[.null, .null],

    mkLdixCase "gas/exact-cost-succeeds"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num ldixSetGasExact), .tonEnvOp .setGasLimit, ldixInstr],
    mkLdixCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSlice13, intV 5]
      #[.pushInt (.num ldixSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixInstr]
  ]
  fuzz := #[
    { seed := 2026021091
      count := 320
      gen := genLdixFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDIX
