import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDIXQ

/-
LDIXQ branch-mapping notes (signed, non-prefetch, quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadIntVar.lean` (`.loadIntVar false false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xd700 + args3`, args=`4` for `LDIXQ`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd700..0xd707` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_var`, `exec_load_int_common`, mode=`4`).

Branch contracts targeted by this suite:
- success stack shape in non-prefetch+quiet mode is `[int, remainder-slice, -1]`;
- quiet insufficient-bits path restores original slice and pushes `0`;
- error ordering: `checkUnderflow 2` then width pop (`typeChk`/`rangeChk`) then slice pop (`typeChk`);
- opcode/decode: `LDIXQ` is `0xd704`, with boundary against fixed family (`0xd708>>3`);
- dispatch fallback: non-`.loadIntVar` instructions must pass through `next`.

Oracle harness constraint:
- partial-cursor slices (`bitPos/refPos ≠ 0`) are not token-encodable for oracle;
  partial-slice branches are covered in direct unit tests only.
-/

private def ldixqId : InstrId := { name := "LDIXQ" }

private def ldixqInstr : Instr := .loadIntVar false false true

private def ldixInstr : Instr := .loadIntVar false false false

private def ldixqOpcode : Nat := 0xd704

private def dispatchSentinel : Int := 607

private def mkLdixqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldixqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldixqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdixqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkLdixqCase name stack program gasLimits fuel

private def runLdixqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar ldixqInstr stack

private def runLdixqDirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar instr stack

private def runLdixqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadIntVar instr (VM.push (intV dispatchSentinel)) stack

private def mkPatternBits (bitCount : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := bitCount) fun i => ((i.1 + phase) % 3 = 1) || ((i.1 + phase) % 5 = 0)

private def mkSliceWithRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSignedSlice
    (width : Nat)
    (n : Int)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  let payload :=
    match intToBitsTwos n width with
    | .ok bs => bs
    | .error e => panic! s!"mkSignedSlice: intToBitsTwos failed width={width} n={n}: {e}"
  mkSliceWithRefs (payload ++ tail) refs

private def mkAvailSlice
    (availBits : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithRefs (mkPatternBits availBits phase) refs

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 11 4) #[]

private def sampleNeg201 : Int := -(intPow2 200) + 654321

private def minInt256 : Int := -(intPow2 255)

private def maxInt256 : Int := intPow2 255 - 1

private def maxInt255 : Int := intPow2 254 - 1

private def expectedSuccessStack (below : Array Value) (n : Int) (rem : Slice) : Array Value :=
  below ++ #[intV n, .slice rem, intV (-1)]

private def expectedQuietFailStack (below : Array Value) (original : Slice) : Array Value :=
  below ++ #[.slice original, intV 0]

private def loadIntVarWord (unsigned : Bool) (prefetch : Bool) (quiet : Bool) : Nat :=
  let args3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  0xd700 + args3

private def loadIntFixedWord (unsigned : Bool) (prefetch : Bool) (quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def ldixqSetGasExact : Int :=
  computeExactGasBudget ldixqInstr

private def ldixqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldixqInstr

private def widthBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257]

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
  (mkSliceWithRefs bits refs, rng1)

private def pickSignedForWidth (bits : Nat) (rng0 : StdGen) : Int × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    let lo := minSignedBits bits
    let hi := maxSignedBits bits
    let (mode, rng1) := randNat rng0 0 7
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (1, rng1)
    else if mode = 2 then
      (-1, rng1)
    else if mode = 3 then
      (lo, rng1)
    else if mode = 4 then
      (hi, rng1)
    else if mode = 5 then
      (if hi > lo then hi - 1 else hi, rng1)
    else if mode = 6 then
      (if lo < hi then lo + 1 else lo, rng1)
    else
      let (randBits, rng2) := randBitString bits rng1
      (bitsToIntSignedTwos randBits, rng2)

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (tailLen, rng1) := randNat rng0 0 18
  randBitString tailLen rng1

private def pickRefsPackNonEmpty (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafB]
    else #[refLeafA, refLeafB]
  (refs, rng')

private def pickNoiseValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let v : Value :=
    if pick = 0 then
      .null
    else if pick = 1 then
      intV 77
    else if pick = 2 then
      .cell refLeafA
    else
      .builder Builder.empty
  (v, rng')

private def pickBadWidthValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let v : Value :=
    if pick = 0 then
      .null
    else if pick = 1 then
      .cell refLeafA
    else
      .slice (mkSliceFromBits #[])
  (v, rng')

private def pickBadSliceValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let v : Value :=
    if pick = 0 then
      .null
    else if pick = 1 then
      intV 17
    else
      .builder Builder.empty
  (v, rng')

private def genLdixqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  if shape = 0 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickSignedForWidth width rng2
    (mkLdixqCase s!"fuzz/ok/exact-width-{width}" #[.slice (mkSignedSlice width x), intV width], rng3)
  else if shape = 1 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickSignedForWidth width rng2
    let (tail, rng4) := pickTailBits rng3
    (mkLdixqCase s!"fuzz/ok/with-tail/width-{width}" #[.slice (mkSignedSlice width x tail), intV width], rng4)
  else if shape = 2 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickSignedForWidth width rng2
    let (tail, rng4) := pickTailBits rng3
    let (refs, rng5) := pickRefsPackNonEmpty rng4
    (mkLdixqCase s!"fuzz/ok/refs-{refs.size}/width-{width}" #[.slice (mkSignedSlice width x tail refs), intV width], rng5)
  else if shape = 3 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickSignedForWidth width rng2
    let (tail, rng4) := pickTailBits rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkLdixqCase s!"fuzz/ok/deep-stack/width-{width}" #[noise, .slice (mkSignedSlice width x tail), intV width], rng5)
  else if shape = 4 then
    let (bitCount, rng2) := randNat rng1 0 257
    let (s, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLdixqCase s!"fuzz/ok/width-zero/bits-{bitCount}" #[.slice s, intV 0], rng3)
  else if shape = 5 then
    (mkLdixqCase "fuzz/ok/width257-min"
      #[.slice (mkSignedSlice 257 minInt257 tailBits7), intV 257], rng1)
  else if shape = 6 then
    (mkLdixqCase "fuzz/ok/width257-max"
      #[.slice (mkSignedSlice 257 maxInt257 tailBits7), intV 257], rng1)
  else if shape = 7 then
    let (width, rng2) := randNat rng1 1 257
    let avail := width - 1
    let (s, rng3) := mkRandomSlice avail #[] rng2
    (mkLdixqCase s!"fuzz/fail/short-by-one/width-{width}" #[.slice s, intV width], rng3)
  else if shape = 8 then
    let (width, rng2) := randNat rng1 1 257
    let maxDelta := Nat.min width 16
    let (delta, rng3) := randNat rng2 1 maxDelta
    let avail := width - delta
    let (refs, rng4) := pickRefsPackNonEmpty rng3
    let (s, rng5) := mkRandomSlice avail refs rng4
    (mkLdixqCase s!"fuzz/fail/short-delta-{delta}/width-{width}" #[.slice s, intV width], rng5)
  else if shape = 9 then
    let (width, rng2) := randNat rng1 1 257
    let (refs, rng3) := pickRefsPackNonEmpty rng2
    (mkLdixqCase s!"fuzz/fail/refs-only-no-bits/width-{width}" #[.slice (mkSliceWithRefs #[] refs), intV width], rng3)
  else if shape = 10 then
    let (width, rng2) := randNat rng1 1 257
    let (avail, rng3) := randNat rng2 0 (width - 1)
    let (noise, rng4) := pickNoiseValue rng3
    let (s, rng5) := mkRandomSlice avail #[] rng4
    (mkLdixqCase s!"fuzz/fail/deep-stack/w-{width}-a-{avail}" #[noise, .slice s, intV width], rng5)
  else if shape = 11 then
    (mkLdixqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkLdixqCase "fuzz/underflow/one-item-slice" #[.slice (mkSignedSlice 8 1)], rng2)
    else
      (mkLdixqCase "fuzz/underflow/one-item-width" #[intV 8], rng2)
  else if shape = 13 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickSignedForWidth width rng2
    let (badWidth, rng4) := pickBadWidthValue rng3
    (mkLdixqCase s!"fuzz/type/width-not-int/width-{width}" #[.slice (mkSignedSlice width x), badWidth], rng4)
  else if shape = 14 then
    let (width, rng2) := pickWidthMixed rng1
    let (badSlice, rng3) := pickBadSliceValue rng2
    (mkLdixqCase s!"fuzz/type/slice-not-slice/width-{width}" #[badSlice, intV width], rng3)
  else if shape = 15 then
    let (width, rng2) := pickWidthMixed rng1
    (mkLdixqCase s!"fuzz/range/negative-width-{width}" #[.slice (mkSignedSlice width 0), intV (-1)], rng2)
  else if shape = 16 then
    let (delta, rng2) := randNat rng1 1 2048
    let tooLarge : Int := Int.ofNat (257 + delta)
    (mkLdixqCase s!"fuzz/range/too-large-width-{tooLarge}" #[.slice (mkSignedSlice 8 1), intV tooLarge], rng2)
  else if shape = 17 then
    (mkLdixqProgramCase "fuzz/range/width-nan-via-program"
      #[.slice (mkSignedSlice 8 1)]
      #[.pushInt .nan, ldixqInstr], rng1)
  else if shape = 18 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    let (delta, rng3) := randNat rng2 1 2048
    let tooLarge : Int := Int.ofNat (257 + delta)
    (mkLdixqCase s!"fuzz/error-order/range-before-slice-type/w-{tooLarge}" #[badSlice, intV tooLarge], rng3)
  else if shape = 19 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    let (badWidth, rng3) := pickBadWidthValue rng2
    (mkLdixqCase "fuzz/error-order/width-type-before-slice-type" #[badSlice, badWidth], rng3)
  else if shape = 20 then
    (mkLdixqCase "fuzz/gas/exact"
      #[.slice (mkSignedSlice 8 (-7) tailBits11), intV 8]
      #[.pushInt (.num ldixqSetGasExact), .tonEnvOp .setGasLimit, ldixqInstr], rng1)
  else if shape = 21 then
    (mkLdixqCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSignedSlice 8 (-7) tailBits11), intV 8]
      #[.pushInt (.num ldixqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixqInstr], rng1)
  else if shape = 22 then
    let (avail, rng2) := randNat rng1 0 256
    let (s, rng3) := mkRandomSlice avail #[] rng2
    (mkLdixqProgramCase s!"fuzz/nonquiet/short-cellund/avail-{avail}"
      #[.slice s, intV 257]
      #[ldixInstr], rng3)
  else
    let (width0, rng2) := pickWidthBoundary rng1
    let width := if width0 = 0 then 1 else width0
    let (refs, rng3) := pickRefsPackNonEmpty rng2
    let (s, rng4) := mkRandomSlice (width - 1) refs rng3
    (mkLdixqCase s!"fuzz/fail/boundary-width-{width}" #[.slice s, intV width], rng4)

def suite : InstrSuite where
  id := ldixqId
  unit := #[
    { name := "unit/direct/nonprefetch-quiet-success-stack-int-rem-status"
      run := do
        let checks : Array (Nat × Int × BitString) :=
          #[
            (0, 0, #[]),
            (0, 0, tailBits7),
            (1, -1, #[]),
            (1, 0, tailBits7),
            (8, -85, tailBits5),
            (8, 127, #[]),
            (8, -128, #[]),
            (16, -12345, tailBits3),
            (64, -(intPow2 63) + 12345, tailBits11),
            (127, intPow2 126 - 7, #[]),
            (201, sampleNeg201, #[]),
            (255, maxInt255, tailBits13),
            (256, minInt256, #[]),
            (256, maxInt256, tailBits5),
            (257, minInt257, #[]),
            (257, maxInt257, tailBits5)
          ]
        for (width, n, tail) in checks do
          let input := mkSignedSlice width n tail
          let rem := input.advanceBits width
          expectOkStack s!"ok/width-{width}/n-{n}/tail-{tail.size}"
            (runLdixqDirect #[.slice input, intV width])
            (expectedSuccessStack #[] n rem)

        let refsInput := mkSignedSlice 8 (-86) tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-in-source-remainder-preserved"
          (runLdixqDirect #[.slice refsInput, intV 8])
          (expectedSuccessStack #[] (-86) (refsInput.advanceBits 8))

        let deepInput := mkSignedSlice 16 (-21555) tailBits11
        let below : Array Value := #[.null, .cell refLeafA]
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdixqDirect (below ++ #[.slice deepInput, intV 16]))
          (expectedSuccessStack below (-21555) (deepInput.advanceBits 16))

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 48) #[refLeafA, refLeafB]
        let partialSlice : Slice := { cell := partialCell, bitPos := 9, refPos := 1 }
        let width : Nat := 12
        let expected : Int := bitsToIntSignedTwos (partialSlice.readBits width)
        expectOkStack "ok/partial-slice-cursor"
          (runLdixqDirect #[.slice partialSlice, intV width])
          (expectedSuccessStack #[] expected (partialSlice.advanceBits width)) }
    ,
    { name := "unit/direct/quiet-insufficient-bits-restores-slice-and-status0"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkSliceFromBits #[]),
            (8, mkAvailSlice 7 0),
            (64, mkAvailSlice 63 1),
            (127, mkAvailSlice 126 0),
            (255, mkAvailSlice 254 1),
            (256, mkAvailSlice 255 0),
            (257, mkAvailSlice 256 1)
          ]
        for (width, source) in checks do
          expectOkStack s!"fail/width-{width}/avail-{source.bitsRemaining}"
            (runLdixqDirect #[.slice source, intV width])
            (expectedQuietFailStack #[] source)

        let refsOnly := mkSliceWithRefs #[] #[refLeafA, refLeafB]
        expectOkStack "fail/refs-only-no-bits"
          (runLdixqDirect #[.slice refsOnly, intV 16])
          (expectedQuietFailStack #[] refsOnly)

        let deepBelow : Array Value := #[intV 77, .cell refLeafA]
        let short := mkAvailSlice 5 1
        expectOkStack "fail/deep-stack-preserve-below"
          (runLdixqDirect (deepBelow ++ #[.slice short, intV 8]))
          (expectedQuietFailStack deepBelow short)

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 30) #[refLeafA]
        let partialSlice : Slice := { cell := partialCell, bitPos := 14, refPos := 0 }
        expectOkStack "fail/partial-slice-short"
          (runLdixqDirect #[.slice partialSlice, intV 17])
          (expectedQuietFailStack #[] partialSlice)

        expectErr "nonquiet/short-throws-cellund"
          (runLdixqDirectInstr ldixInstr #[.slice (mkAvailSlice 31 0), intV 32]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runLdixqDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice" (runLdixqDirect #[.slice (mkSignedSlice 8 1)]) .stkUnd
        expectErr "underflow/one-item-width" (runLdixqDirect #[intV 8]) .stkUnd
        expectErr "underflow/one-item-null" (runLdixqDirect #[.null]) .stkUnd

        expectErr "type/width-top-null"
          (runLdixqDirect #[.slice (mkSignedSlice 8 1), .null]) .typeChk
        expectErr "type/width-top-cell"
          (runLdixqDirect #[.slice (mkSignedSlice 8 1), .cell refLeafA]) .typeChk
        expectErr "type/width-top-slice"
          (runLdixqDirect #[.slice (mkSignedSlice 8 1), .slice (mkSliceFromBits #[])]) .typeChk

        expectErr "range/width-negative"
          (runLdixqDirect #[.slice (mkSignedSlice 8 1), intV (-1)]) .rangeChk
        expectErr "range/width-too-large-258"
          (runLdixqDirect #[.slice (mkSignedSlice 8 1), intV 258]) .rangeChk
        expectErr "range/width-too-large-4096"
          (runLdixqDirect #[.slice (mkSignedSlice 8 1), intV 4096]) .rangeChk
        expectErr "range/width-nan"
          (runLdixqDirect #[.slice (mkSignedSlice 8 1), .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-pop"
          (runLdixqDirect #[.null, intV 300]) .rangeChk
        expectErr "error-order/width-type-before-slice-pop"
          (runLdixqDirect #[.null, .null]) .typeChk
        expectErr "type/slice-pop-after-valid-width"
          (runLdixqDirect #[.null, intV 0]) .typeChk }
    ,
    { name := "unit/opcode-decode-assembler-and-family-boundaries"
      run := do
        let program : Array Instr := #[
          .loadIntVar false false false,
          .loadIntVar true false false,
          .loadIntVar false true false,
          .loadIntVar true true false,
          ldixqInstr,
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
        let s2 ← expectDecodeStep "decode/ldux" s1 (.loadIntVar true false false) 16
        let s3 ← expectDecodeStep "decode/pldix" s2 (.loadIntVar false true false) 16
        let s4 ← expectDecodeStep "decode/pldux" s3 (.loadIntVar true true false) 16
        let s5 ← expectDecodeStep "decode/ldixq" s4 ldixqInstr 16
        let s6 ← expectDecodeStep "decode/lduxq" s5 (.loadIntVar true false true) 16
        let s7 ← expectDecodeStep "decode/pldixq" s6 (.loadIntVar false true true) 16
        let s8 ← expectDecodeStep "decode/plduxq" s7 (.loadIntVar true true true) 16
        let s9 ← expectDecodeStep "decode/tail-add" s8 .add 8
        if s9.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s9.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [ldixqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits ldixqOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldixq: expected 0xd704 encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldixq: expected 16-bit encoding, got {singleCode.bits.size}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")

        let rawBoundary : Cell :=
          Cell.mkOrdinary
            (natToBits ldixqOpcode 16 ++ natToBits (loadIntFixedWord false false false 1) 24 ++ addCell.bits) #[]
        let rb0 := Slice.ofCell rawBoundary
        let rb1 ← expectDecodeStep "decode/raw-ldixq" rb0 ldixqInstr 16
        let rb2 ← expectDecodeStep "decode/raw-fixed-boundary-ldi1" rb1 (.loadInt false false false 1) 24
        let rb3 ← expectDecodeStep "decode/raw-tail-add" rb2 .add 8
        if rb3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-boundary-end: expected exhausted slice, got {rb3.bitsRemaining} bits remaining")

        let rawNeighbors : Cell :=
          Cell.mkOrdinary
            (natToBits (loadIntVarWord false false false) 16 ++ natToBits ldixqOpcode 16
              ++ natToBits (loadIntVarWord false true true) 16 ++ addCell.bits) #[]
        let rn0 := Slice.ofCell rawNeighbors
        let rn1 ← expectDecodeStep "decode/raw-ldix-neighbor" rn0 (.loadIntVar false false false) 16
        let rn2 ← expectDecodeStep "decode/raw-ldixq-neighbor" rn1 ldixqInstr 16
        let rn3 ← expectDecodeStep "decode/raw-pldixq-neighbor" rn2 (.loadIntVar false true true) 16
        let rn4 ← expectDecodeStep "decode/raw-neighbor-tail-add" rn3 .add 8
        if rn4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-neighbor-end: expected exhausted slice, got {rn4.bitsRemaining} bits remaining")

        match assembleCp0 [.loadInt false true true 8] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/loadInt-fixed-ptq: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/loadInt-fixed-ptq: expected invOpcode, got success")

        match assembleCp0 [.loadInt false false false 1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/loadInt-fixed-ldi1: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/loadInt-fixed-ldi1: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/fallback-for-non-loadintvar"
      run := do
        expectOkStack "dispatch/add"
          (runLdixqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/fixed-loadint-family"
          (runLdixqDispatchFallback (.loadInt false true true 8) #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/loadslicex-neighbor"
          (runLdixqDispatchFallback (.loadSliceX true true) #[.cell refLeafA])
          #[.cell refLeafA, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdixqCase "ok/width0-empty" #[.slice (mkSliceFromBits #[]), intV 0],
    mkLdixqCase "ok/width0-nonempty" #[.slice (mkAvailSlice 17 1), intV 0],
    mkLdixqCase "ok/width1-neg1" #[.slice (mkSignedSlice 1 (-1)), intV 1],
    mkLdixqCase "ok/width1-zero-with-tail" #[.slice (mkSignedSlice 1 0 tailBits7), intV 1],
    mkLdixqCase "ok/width8-neg85" #[.slice (mkSignedSlice 8 (-85) tailBits5), intV 8],
    mkLdixqCase "ok/width8-max127" #[.slice (mkSignedSlice 8 127), intV 8],
    mkLdixqCase "ok/width8-min128" #[.slice (mkSignedSlice 8 (-128)), intV 8],
    mkLdixqCase "ok/width16-neg12345" #[.slice (mkSignedSlice 16 (-12345) tailBits3), intV 16],
    mkLdixqCase "ok/width32-deadbeef-signed" #[.slice (mkSignedSlice 32 (-559038737) tailBits11), intV 32],
    mkLdixqCase "ok/width64-near-min" #[.slice (mkSignedSlice 64 (-(intPow2 63) + 12345) tailBits13), intV 64],
    mkLdixqCase "ok/width127-high-positive" #[.slice (mkSignedSlice 127 (intPow2 126 - 7)), intV 127],
    mkLdixqCase "ok/width201-sample-neg" #[.slice (mkSignedSlice 201 sampleNeg201), intV 201],
    mkLdixqCase "ok/width255-near-max" #[.slice (mkSignedSlice 255 (maxInt255 - 1)), intV 255],
    mkLdixqCase "ok/width256-min" #[.slice (mkSignedSlice 256 minInt256), intV 256],
    mkLdixqCase "ok/width256-max" #[.slice (mkSignedSlice 256 maxInt256), intV 256],
    mkLdixqCase "ok/width257-minInt257" #[.slice (mkSignedSlice 257 minInt257), intV 257],
    mkLdixqCase "ok/width257-maxInt257" #[.slice (mkSignedSlice 257 maxInt257), intV 257],
    mkLdixqCase "ok/deep-stack-below-preserved"
      #[.null, .cell refLeafA, .slice (mkSignedSlice 8 (-42) tailBits5), intV 8],

    mkLdixqCase "fail/width1-empty" #[.slice (mkSliceFromBits #[]), intV 1],
    mkLdixqCase "fail/width8-short7" #[.slice (mkAvailSlice 7 0), intV 8],
    mkLdixqCase "fail/width64-short63" #[.slice (mkAvailSlice 63 1), intV 64],
    mkLdixqCase "fail/width127-short126" #[.slice (mkAvailSlice 126 0), intV 127],
    mkLdixqCase "fail/width255-short254" #[.slice (mkAvailSlice 254 1), intV 255],
    mkLdixqCase "fail/width256-short255" #[.slice (mkAvailSlice 255 0), intV 256],
    mkLdixqCase "fail/width257-short256" #[.slice (mkAvailSlice 256 1), intV 257],
    mkLdixqCase "fail/refs-only-no-bits" #[.slice (mkSliceWithRefs #[] #[refLeafA, refLeafB]), intV 16],
    mkLdixqCase "fail/deep-stack-below-preserved"
      #[intV 77, .slice (mkAvailSlice 5 0), intV 8],

    mkLdixqCase "range/width-negative" #[.slice (mkSignedSlice 8 1), intV (-1)],
    mkLdixqCase "range/width-too-large-258" #[.slice (mkSignedSlice 8 1), intV 258],
    mkLdixqCase "range/width-too-large-4096" #[.slice (mkSignedSlice 8 1), intV 4096],
    mkLdixqProgramCase "range/width-nan-via-program"
      #[.slice (mkSignedSlice 8 1)]
      #[.pushInt .nan, ldixqInstr],

    mkLdixqCase "underflow/empty" #[],
    mkLdixqCase "underflow/one-item-slice" #[.slice (mkSignedSlice 8 1)],
    mkLdixqCase "type/width-top-null" #[.slice (mkSignedSlice 8 1), .null],
    mkLdixqCase "type/slice-not-slice-after-valid-width" #[.null, intV 0],

    mkLdixqCase "error-order/range-before-slice-pop" #[.null, intV 300],
    mkLdixqCase "error-order/width-type-before-slice-pop" #[.null, .null],

    mkLdixqCase "gas/exact-cost-succeeds"
      #[.slice (mkSignedSlice 8 (-7) tailBits11), intV 8]
      #[.pushInt (.num ldixqSetGasExact), .tonEnvOp .setGasLimit, ldixqInstr],
    mkLdixqCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSignedSlice 8 (-7) tailBits11), intV 8]
      #[.pushInt (.num ldixqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixqInstr]
  ]
  fuzz := #[
    { seed := 2026021109
      count := 500
      gen := genLdixqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDIXQ
