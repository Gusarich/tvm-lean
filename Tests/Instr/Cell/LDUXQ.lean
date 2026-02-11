import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDUXQ

/-
LDUXQ branch-mapping notes (unsigned, non-prefetch, quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadIntVar.lean` (`.loadIntVar true false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xd700 + args3`, args=`5` for `LDUXQ`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd700..0xd707` var-width decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_var`, `exec_load_int_common`, mode=`5`).

Branch contracts targeted by this suite:
- success stack shape in non-prefetch+quiet mode is exactly `[int, slice, -1]`;
- quiet insufficient-bits path re-pushes original slice then status `0`;
- error ordering: `checkUnderflow 2` then width pop (`typeChk`/`rangeChk`) then slice pop (`typeChk`);
- opcode/decode: `LDUXQ` is `0xd705`, with boundaries against var neighbors and fixed-width family (`0xd708>>3`);
- assembler constraints: var-form `loadIntVar` assembles; fixed-form `.loadInt ...` remains rejected in Lean asm.

Oracle/fuzz harness constraint:
- token encoder supports only full-cell slices (`bitPos=0`, `refPos=0`) in oracle/fuzz cases.
  Partial-cursor behavior is validated in direct unit tests only.
-/

private def lduxqId : InstrId := { name := "LDUXQ" }

private def lduxqInstr : Instr := .loadIntVar true false true

private def lduxqOpcode : Nat := 0xd705

private def dispatchSentinel : Int := 619

private def mkLduxqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lduxqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lduxqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLduxqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkLduxqCase name stack program gasLimits fuel

private def runLduxqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar lduxqInstr stack

private def runLduxqDirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar instr stack

private def runLduxqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadIntVar instr (VM.push (intV dispatchSentinel)) stack

private def mkPatternBits (bitCount : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := bitCount) fun i => ((i.1 + phase) % 3 = 1) || ((i.1 + phase) % 5 = 0)

private def mkSliceWithRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkUnsignedSlice
    (width : Nat)
    (n : Int)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithRefs (natToBits n.toNat width ++ tail) refs

private def mkAvailSlice
    (availBits : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithRefs (mkPatternBits availBits phase) refs

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 11 4) #[]

private def maxUInt255 : Int := intPow2 255 - 1

private def maxUInt256 : Int := intPow2 256 - 1

private def sampleWide201 : Int := intPow2 200 + 654321

private def expectedSuccessStack (below : Array Value) (s : Slice) (n : Int) (width : Nat) : Array Value :=
  below ++ #[intV n, .slice (s.advanceBits width), intV (-1)]

private def expectedQuietFailStack (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[.slice s, intV 0]

private def loadIntVarWord (unsigned : Bool) (prefetch : Bool) (quiet : Bool) : Nat :=
  let args3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  0xd700 + args3

private def loadIntFixedWord (unsigned : Bool) (prefetch : Bool) (quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def lduxqSetGasExact : Int :=
  computeExactGasBudget lduxqInstr

private def lduxqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lduxqInstr

private def widthBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

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
  (mkSliceWithRefs bits refs, rng1)

private def pickUnsignedForWidth (bits : Nat) (rng0 : StdGen) : Int × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    let maxv := intPow2 bits - 1
    let (mode, rng1) := randNat rng0 0 5
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (1, rng1)
    else if mode = 2 then
      (maxv, rng1)
    else if mode = 3 then
      (if maxv > 0 then maxv - 1 else 0, rng1)
    else if mode = 4 then
      (intPow2 (bits - 1), rng1)
    else
      let (randBits, rng2) := randBitString bits rng1
      (Int.ofNat (bitsToNat randBits), rng2)

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (tailLen, rng1) := randNat rng0 0 16
  randBitString tailLen rng1

private def pickRefsPackNonEmpty (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafB]
    else #[refLeafA, refLeafB]
  (refs, rng')

private def pickNoiseValue (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let v : Value :=
    if pick = 0 then
      .null
    else if pick = 1 then
      intV 77
    else
      .cell refLeafA
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

private def genLduxqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  if shape = 0 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickUnsignedForWidth width rng2
    (mkLduxqCase s!"fuzz/ok/exact-width-{width}" #[.slice (mkUnsignedSlice width x), intV width], rng3)
  else if shape = 1 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickUnsignedForWidth width rng2
    let (tail, rng4) := pickTailBits rng3
    (mkLduxqCase s!"fuzz/ok/with-tail/width-{width}" #[.slice (mkUnsignedSlice width x tail), intV width], rng4)
  else if shape = 2 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickUnsignedForWidth width rng2
    let (tail, rng4) := pickTailBits rng3
    let (refs, rng5) := pickRefsPackNonEmpty rng4
    (mkLduxqCase s!"fuzz/ok/refs-tail/width-{width}/r-{refs.size}"
      #[.slice (mkUnsignedSlice width x tail refs), intV width], rng5)
  else if shape = 3 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickUnsignedForWidth width rng2
    let (tail, rng4) := pickTailBits rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkLduxqCase s!"fuzz/ok/deep-stack/width-{width}" #[noise, .slice (mkUnsignedSlice width x tail), intV width], rng5)
  else if shape = 4 then
    let (bitCount, rng2) := randNat rng1 0 256
    let (s, rng3) := mkRandomSlice bitCount #[] rng2
    (mkLduxqCase s!"fuzz/ok/width-zero/bits-{bitCount}" #[.slice s, intV 0], rng3)
  else if shape = 5 then
    let (width, rng2) := randNat rng1 1 256
    let avail := width - 1
    let (s, rng3) := mkRandomSlice avail #[] rng2
    (mkLduxqCase s!"fuzz/fail/short-by-one/width-{width}" #[.slice s, intV width], rng3)
  else if shape = 6 then
    let (width, rng2) := randNat rng1 1 256
    let maxDelta := Nat.min width 16
    let (delta, rng3) := randNat rng2 1 maxDelta
    let avail := width - delta
    let (refs, rng4) := pickRefsPackNonEmpty rng3
    let (s, rng5) := mkRandomSlice avail refs rng4
    (mkLduxqCase s!"fuzz/fail/short-delta-{delta}/width-{width}" #[.slice s, intV width], rng5)
  else if shape = 7 then
    let (width, rng2) := randNat rng1 1 256
    let (refs, rng3) := pickRefsPackNonEmpty rng2
    (mkLduxqCase s!"fuzz/fail/refs-only-no-bits/width-{width}" #[.slice (mkSliceWithRefs #[] refs), intV width], rng3)
  else if shape = 8 then
    let (width, rng2) := pickWidthMixed rng1
    (mkLduxqCase s!"fuzz/range/negative-width-{width}" #[.slice (mkUnsignedSlice width 0), intV (-1)], rng2)
  else if shape = 9 then
    let (delta, rng2) := randNat rng1 1 2048
    let tooLarge : Int := Int.ofNat (256 + delta)
    (mkLduxqCase s!"fuzz/range/too-large-width-{tooLarge}" #[.slice (mkUnsignedSlice 8 1), intV tooLarge], rng2)
  else if shape = 10 then
    (mkLduxqProgramCase "fuzz/range/width-nan-via-program"
      #[.slice (mkUnsignedSlice 8 1)]
      #[.pushInt .nan, lduxqInstr], rng1)
  else if shape = 11 then
    (mkLduxqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkLduxqCase "fuzz/underflow/one-item-slice" #[.slice (mkUnsignedSlice 8 1)], rng2)
    else
      (mkLduxqCase "fuzz/underflow/one-item-width" #[intV 8], rng2)
  else if shape = 13 then
    let (width, rng2) := pickWidthMixed rng1
    let (x, rng3) := pickUnsignedForWidth width rng2
    let (badWidth, rng4) := pickBadWidthValue rng3
    (mkLduxqCase s!"fuzz/type/width-not-int/width-{width}" #[.slice (mkUnsignedSlice width x), badWidth], rng4)
  else if shape = 14 then
    let (width, rng2) := pickWidthMixed rng1
    let (badSlice, rng3) := pickBadSliceValue rng2
    (mkLduxqCase s!"fuzz/type/slice-not-slice/width-{width}" #[badSlice, intV width], rng3)
  else if shape = 15 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    let (delta, rng3) := randNat rng2 1 2048
    let tooLarge : Int := Int.ofNat (256 + delta)
    (mkLduxqCase s!"fuzz/error-order/range-before-slice-type/w-{tooLarge}" #[badSlice, intV tooLarge], rng3)
  else if shape = 16 then
    let (badSlice, rng2) := pickBadSliceValue rng1
    let (badWidth, rng3) := pickBadWidthValue rng2
    (mkLduxqCase "fuzz/error-order/width-type-before-slice-type" #[badSlice, badWidth], rng3)
  else if shape = 17 then
    (mkLduxqCase "fuzz/gas/exact"
      #[.slice (mkUnsignedSlice 8 7 tailBits11), intV 8]
      #[.pushInt (.num lduxqSetGasExact), .tonEnvOp .setGasLimit, lduxqInstr], rng1)
  else
    (mkLduxqCase "fuzz/gas/exact-minus-one"
      #[.slice (mkUnsignedSlice 8 7 tailBits11), intV 8]
      #[.pushInt (.num lduxqSetGasExactMinusOne), .tonEnvOp .setGasLimit, lduxqInstr], rng1)

def suite : InstrSuite where
  id := lduxqId
  unit := #[
    { name := "unit/direct/non-prefetch-quiet-success-stack-int-slice-minus1"
      run := do
        let checks : Array (Nat × Int × BitString) :=
          #[
            (0, 0, #[]),
            (0, 0, tailBits7),
            (1, 0, #[]),
            (1, 1, tailBits7),
            (8, 165, tailBits5),
            (8, 255, #[]),
            (16, 48879, tailBits3),
            (64, intPow2 63 + 12345, tailBits11),
            (127, intPow2 126 + 7, #[]),
            (201, sampleWide201, #[]),
            (255, maxUInt255, tailBits13),
            (256, maxUInt256, #[])
          ]
        for (width, n, tail) in checks do
          let input := mkUnsignedSlice width n tail
          expectOkStack s!"ok/width-{width}/n-{n}/tail-{tail.size}"
            (runLduxqDirect #[.slice input, intV width])
            (expectedSuccessStack #[] input n width)

        let refsInput := mkUnsignedSlice 8 170 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-in-source-remainder-preserved"
          (runLduxqDirect #[.slice refsInput, intV 8])
          (expectedSuccessStack #[] refsInput 170 8)

        let deepInput := mkUnsignedSlice 16 43981 tailBits11
        let below : Array Value := #[.null, .cell refLeafA]
        expectOkStack "ok/deep-stack-preserve-below"
          (runLduxqDirect (below ++ #[.slice deepInput, intV 16]))
          (expectedSuccessStack below deepInput 43981 16)

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 48) #[refLeafA, refLeafB]
        let partialSlice : Slice := { cell := partialCell, bitPos := 9, refPos := 1 }
        let width : Nat := 12
        let expected : Int := Int.ofNat (bitsToNat (partialSlice.readBits width))
        expectOkStack "ok/partial-slice-cursor"
          (runLduxqDirect #[.slice partialSlice, intV width])
          (expectedSuccessStack #[] partialSlice expected width) }
    ,
    { name := "unit/direct/quiet-insufficient-bits-restores-slice-then-status0"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkSliceFromBits #[]),
            (8, mkAvailSlice 7 0),
            (64, mkAvailSlice 63 1),
            (127, mkAvailSlice 126 0),
            (255, mkAvailSlice 254 1),
            (256, mkAvailSlice 255 0)
          ]
        for (width, source) in checks do
          expectOkStack s!"fail/width-{width}/avail-{source.bitsRemaining}"
            (runLduxqDirect #[.slice source, intV width])
            (expectedQuietFailStack #[] source)

        let refsOnly := mkSliceWithRefs #[] #[refLeafA, refLeafB]
        expectOkStack "fail/refs-only-no-bits"
          (runLduxqDirect #[.slice refsOnly, intV 16])
          (expectedQuietFailStack #[] refsOnly)

        let deepBelow : Array Value := #[intV 77, .cell refLeafA]
        let short := mkAvailSlice 5 1
        expectOkStack "fail/deep-stack-preserve-below"
          (runLduxqDirect (deepBelow ++ #[.slice short, intV 8]))
          (expectedQuietFailStack deepBelow short)

        let partialCell : Cell := Cell.mkOrdinary (mkPatternBits 30) #[refLeafA]
        let partialSlice : Slice := { cell := partialCell, bitPos := 14, refPos := 0 }
        expectOkStack "fail/partial-slice-short"
          (runLduxqDirect #[.slice partialSlice, intV 17])
          (expectedQuietFailStack #[] partialSlice)

        expectErr "nonquiet/short-throws-cellund"
          (runLduxqDirectInstr (.loadIntVar true false false) #[.slice (mkAvailSlice 7 0), intV 8]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runLduxqDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice" (runLduxqDirect #[.slice (mkUnsignedSlice 8 1)]) .stkUnd
        expectErr "underflow/one-item-width" (runLduxqDirect #[intV 8]) .stkUnd
        expectErr "underflow/one-item-null" (runLduxqDirect #[.null]) .stkUnd

        expectErr "type/width-top-null"
          (runLduxqDirect #[.slice (mkUnsignedSlice 8 1), .null]) .typeChk
        expectErr "type/width-top-cell"
          (runLduxqDirect #[.slice (mkUnsignedSlice 8 1), .cell refLeafA]) .typeChk
        expectErr "type/width-top-slice"
          (runLduxqDirect #[.slice (mkUnsignedSlice 8 1), .slice (mkSliceFromBits #[])]) .typeChk

        expectErr "range/width-negative"
          (runLduxqDirect #[.slice (mkUnsignedSlice 8 1), intV (-1)]) .rangeChk
        expectErr "range/width-too-large-257"
          (runLduxqDirect #[.slice (mkUnsignedSlice 8 1), intV 257]) .rangeChk
        expectErr "range/width-too-large-4096"
          (runLduxqDirect #[.slice (mkUnsignedSlice 8 1), intV 4096]) .rangeChk
        expectErr "range/width-nan"
          (runLduxqDirect #[.slice (mkUnsignedSlice 8 1), .int .nan]) .rangeChk

        expectErr "error-order/range-before-slice-pop"
          (runLduxqDirect #[.null, intV 300]) .rangeChk
        expectErr "error-order/width-type-before-slice-pop"
          (runLduxqDirect #[.null, .null]) .typeChk
        expectErr "type/slice-pop-after-valid-width"
          (runLduxqDirect #[.null, intV 0]) .typeChk }
    ,
    { name := "unit/opcode-decode-assembler-and-family-boundaries"
      run := do
        let program : Array Instr := #[
          .loadIntVar false false false,
          .loadIntVar true false false,
          .loadIntVar false true false,
          .loadIntVar true true false,
          .loadIntVar false false true,
          lduxqInstr,
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
        let s5 ← expectDecodeStep "decode/ldixq" s4 (.loadIntVar false false true) 16
        let s6 ← expectDecodeStep "decode/lduxq" s5 lduxqInstr 16
        let s7 ← expectDecodeStep "decode/pldixq" s6 (.loadIntVar false true true) 16
        let s8 ← expectDecodeStep "decode/plduxq" s7 (.loadIntVar true true true) 16
        let s9 ← expectDecodeStep "decode/tail-add" s8 .add 8
        if s9.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s9.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [lduxqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits lduxqOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/lduxq: expected 0xd705 encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/lduxq: expected 16-bit encoding, got {singleCode.bits.size}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")

        let rawBoundary : Cell :=
          Cell.mkOrdinary
            (natToBits lduxqOpcode 16 ++ natToBits (loadIntFixedWord false false false 1) 24 ++ addCell.bits) #[]
        let rb0 := Slice.ofCell rawBoundary
        let rb1 ← expectDecodeStep "decode/raw-lduxq" rb0 lduxqInstr 16
        let rb2 ← expectDecodeStep "decode/raw-fixed-boundary-ldi1" rb1 (.loadInt false false false 1) 24
        let rb3 ← expectDecodeStep "decode/raw-tail-add" rb2 .add 8
        if rb3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-boundary-end: expected exhausted slice, got {rb3.bitsRemaining} bits remaining")

        let rawNeighbors : Cell :=
          Cell.mkOrdinary
            (natToBits (loadIntVarWord false false true) 16 ++
             natToBits lduxqOpcode 16 ++
             natToBits (loadIntVarWord true true true) 16 ++
             addCell.bits) #[]
        let rn0 := Slice.ofCell rawNeighbors
        let rn1 ← expectDecodeStep "decode/raw-ldixq-neighbor" rn0 (.loadIntVar false false true) 16
        let rn2 ← expectDecodeStep "decode/raw-lduxq-neighbor" rn1 lduxqInstr 16
        let rn3 ← expectDecodeStep "decode/raw-plduxq-neighbor" rn2 (.loadIntVar true true true) 16
        let rn4 ← expectDecodeStep "decode/raw-neighbor-tail-add" rn3 .add 8
        if rn4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-neighbor-end: expected exhausted slice, got {rn4.bitsRemaining} bits remaining")

        let rawPlduzBoundary : Cell :=
          Cell.mkOrdinary
            (natToBits lduxqOpcode 16 ++ natToBits 0xd710 16 ++ addCell.bits) #[]
        let rz0 := Slice.ofCell rawPlduzBoundary
        let rz1 ← expectDecodeStep "decode/raw-lduxq-before-plduz" rz0 lduxqInstr 16
        let rz2 ← expectDecodeStep "decode/raw-plduz-boundary" rz1 (.cellExt (.plduz 0)) 16
        let rz3 ← expectDecodeStep "decode/raw-plduz-tail-add" rz2 .add 8
        if rz3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-plduz-boundary-end: expected exhausted slice, got {rz3.bitsRemaining} bits remaining")

        match assembleCp0 [.loadInt true false true 8] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/loadInt-fixed: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/loadInt-fixed: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/fallback-for-non-loadintvar"
      run := do
        expectOkStack "dispatch/add"
          (runLduxqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/fixed-loadint-family"
          (runLduxqDispatchFallback (.loadInt true false true 8) #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/loadslicex-neighbor"
          (runLduxqDispatchFallback (.loadSliceX false true) #[.cell refLeafA])
          #[.cell refLeafA, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLduxqCase "ok/width0-empty" #[.slice (mkSliceFromBits #[]), intV 0],
    mkLduxqCase "ok/width0-nonempty-tail" #[.slice (mkUnsignedSlice 0 0 tailBits7), intV 0],
    mkLduxqCase "ok/width1-zero" #[.slice (mkUnsignedSlice 1 0), intV 1],
    mkLduxqCase "ok/width1-one-with-tail" #[.slice (mkUnsignedSlice 1 1 tailBits7), intV 1],
    mkLduxqCase "ok/width8-mid" #[.slice (mkUnsignedSlice 8 165 tailBits5), intV 8],
    mkLduxqCase "ok/width8-max" #[.slice (mkUnsignedSlice 8 255), intV 8],
    mkLduxqCase "ok/width16-beef" #[.slice (mkUnsignedSlice 16 48879 tailBits3), intV 16],
    mkLduxqCase "ok/width32-deadbeef" #[.slice (mkUnsignedSlice 32 3735928559 tailBits11), intV 32],
    mkLduxqCase "ok/width64-high" #[.slice (mkUnsignedSlice 64 (intPow2 63 + 12345) tailBits13), intV 64],
    mkLduxqCase "ok/width127" #[.slice (mkUnsignedSlice 127 (intPow2 126 + 7)), intV 127],
    mkLduxqCase "ok/width201-sample" #[.slice (mkUnsignedSlice 201 sampleWide201), intV 201],
    mkLduxqCase "ok/width255-near-max" #[.slice (mkUnsignedSlice 255 (maxUInt255 - 1)), intV 255],
    mkLduxqCase "ok/width256-max" #[.slice (mkUnsignedSlice 256 maxUInt256), intV 256],
    mkLduxqCase "ok/deep-stack-below-preserved"
      #[.null, .cell refLeafA, .slice (mkUnsignedSlice 8 42 tailBits5), intV 8],
    mkLduxqCase "ok/refs-present-tail" #[.slice (mkUnsignedSlice 8 170 tailBits5 #[refLeafA, refLeafB]), intV 8],
    mkLduxqCase "ok/width256-with-refs-tail"
      #[.slice (mkUnsignedSlice 256 (maxUInt256 - 7) tailBits3 #[refLeafA]), intV 256],

    mkLduxqCase "fail/width1-empty" #[.slice (mkSliceFromBits #[]), intV 1],
    mkLduxqCase "fail/width8-short7" #[.slice (mkAvailSlice 7 0), intV 8],
    mkLduxqCase "fail/width64-short63" #[.slice (mkAvailSlice 63 1), intV 64],
    mkLduxqCase "fail/width127-short126" #[.slice (mkAvailSlice 126 0), intV 127],
    mkLduxqCase "fail/width255-short254" #[.slice (mkAvailSlice 254 1), intV 255],
    mkLduxqCase "fail/width256-short255" #[.slice (mkAvailSlice 255 0), intV 256],
    mkLduxqCase "fail/refs-only-no-bits" #[.slice (mkSliceWithRefs #[] #[refLeafA, refLeafB]), intV 16],
    mkLduxqCase "fail/deep-stack-below-preserved"
      #[intV 77, .slice (mkAvailSlice 5 0), intV 8],
    mkLduxqCase "fail/width32-short0" #[.slice (mkAvailSlice 0 1), intV 32],

    mkLduxqCase "range/width-negative" #[.slice (mkUnsignedSlice 8 1), intV (-1)],
    mkLduxqCase "range/width-too-large-257" #[.slice (mkUnsignedSlice 8 1), intV 257],
    mkLduxqCase "range/width-too-large-4096" #[.slice (mkUnsignedSlice 8 1), intV 4096],
    mkLduxqProgramCase "range/width-nan-via-program"
      #[.slice (mkUnsignedSlice 8 1)]
      #[.pushInt .nan, lduxqInstr],

    mkLduxqCase "underflow/empty" #[],
    mkLduxqCase "underflow/one-item-slice" #[.slice (mkUnsignedSlice 8 1)],
    mkLduxqCase "underflow/one-item-width" #[intV 8],

    mkLduxqCase "type/width-top-null" #[.slice (mkUnsignedSlice 8 1), .null],
    mkLduxqCase "type/width-top-cell" #[.slice (mkUnsignedSlice 8 1), .cell refLeafA],
    mkLduxqCase "type/width-top-slice" #[.slice (mkUnsignedSlice 8 1), .slice (mkSliceFromBits #[])],
    mkLduxqCase "type/slice-not-slice-after-valid-width" #[.null, intV 0],

    mkLduxqCase "error-order/range-before-slice-pop" #[.null, intV 300],
    mkLduxqCase "error-order/width-type-before-slice-pop" #[.null, .null],

    mkLduxqCase "gas/exact-cost-succeeds"
      #[.slice (mkUnsignedSlice 8 7 tailBits11), intV 8]
      #[.pushInt (.num lduxqSetGasExact), .tonEnvOp .setGasLimit, lduxqInstr],
    mkLduxqCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkUnsignedSlice 8 7 tailBits11), intV 8]
      #[.pushInt (.num lduxqSetGasExactMinusOne), .tonEnvOp .setGasLimit, lduxqInstr]
  ]
  fuzz := #[
    { seed := 2026021073
      count := 320
      gen := genLduxqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDUXQ
