import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDILE8Q

/-!
PLDILE8Q branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt false 8 true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=14 for PLDILE8Q)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- quiet insufficient-bits path (`haveBits 64 = false`) in prefetch mode returns `[0]`
  without pushing remainder slice;
- success path: little-endian 8-byte signed decode + prefetch/quiet stack contract (`[int, -1]`);
- opcode family decode around `0xd75e`, plus boundary against non-family `0xd760`;
- handler dispatch fallback for non-`.loadLeInt` instructions.

Oracle harness constraint:
- partial-cursor slices (`bitPos/refPos ≠ 0`) are not encodable in oracle token format;
  partial-slice branches are covered in direct unit tests and fuzz only uses full-cell slices.
-/

private def pldile8qId : InstrId := { name := "PLDILE8Q" }

private def pldile8qInstr : Instr :=
  .cellOp (.loadLeInt false 8 true true)

private def pldile8qWord : Nat := 0xd75e

private def dispatchSentinel : Int := 853

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkPldile8qCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldile8qInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldile8qId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldile8qDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly pldile8qInstr stack

private def runPldile8qDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero8 : Array UInt8 := #[
  u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00
]
private def bytesOne8 : Array UInt8 := #[
  u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00
]
private def bytesMinusOne8 : Array UInt8 := #[
  u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff
]
private def bytesMaxPos8 : Array UInt8 := #[
  u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0x7f
]
private def bytesMinNeg8 : Array UInt8 := #[
  u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80
]
private def bytes0123456789abcdef : Array UInt8 := #[
  u8 0xef, u8 0xcd, u8 0xab, u8 0x89, u8 0x67, u8 0x45, u8 0x23, u8 0x01
]
private def bytesFedcba9876543210 : Array UInt8 := #[
  u8 0x10, u8 0x32, u8 0x54, u8 0x76, u8 0x98, u8 0xba, u8 0xdc, u8 0xfe
]
private def bytesAltPos8 : Array UInt8 := #[
  u8 0x11, u8 0x22, u8 0x33, u8 0x44, u8 0x55, u8 0x66, u8 0x10, u8 0x01
]
private def bytesAltNeg8 : Array UInt8 := #[
  u8 0xaa, u8 0xbb, u8 0xcc, u8 0xdd, u8 0xee, u8 0xff, u8 0x00, u8 0x80
]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero8,
    bytesOne8,
    bytesMinusOne8,
    bytesMaxPos8,
    bytesMinNeg8,
    bytes0123456789abcdef,
    bytesFedcba9876543210,
    bytesAltPos8,
    bytesAltNeg8
  ]

private def mkSliceFromLeBytes
    (bytes : Array UInt8)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (bytesToBitsBE bytes ++ tail) refs

private def expectedSignedFromBytes (bytes : Array UInt8) : Int :=
  natToIntSignedTwos (bytesToNatLE bytes) 64

private def expectedSignedFromSlice (s : Slice) : Int :=
  expectedSignedFromBytes (bitStringToBytesBE (s.readBits 64))

private def expectedSuccessStack (below : Array Value) (x : Int) : Array Value :=
  below ++ #[intV x, intV (-1)]

private def expectedQuietFailStack (below : Array Value) : Array Value :=
  below ++ #[intV 0]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 140 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 13, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 78 1) #[refLeafA]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 18, refPos := 0 }

private def pldile8qSetGasExact : Int :=
  computeExactGasBudget pldile8qInstr

private def pldile8qSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pldile8qInstr

private def randBytes8 (rng0 : StdGen) : Array UInt8 × StdGen := Id.run do
  let mut out : Array UInt8 := #[]
  let mut rng := rng0
  for _ in [0:8] do
    let (n, rng') := randNat rng 0 255
    out := out.push (u8 n)
    rng := rng'
  return (out, rng)

private def pickBoundaryBytes (rng : StdGen) : Nat × Array UInt8 × StdGen :=
  let (idx, rng') := randNat rng 0 (boundaryBytesPool.size - 1)
  (idx, boundaryBytesPool[idx]!, rng')

private def pickTailBits (rng0 : StdGen) (maxLen : Nat := 24) : BitString × StdGen :=
  let (len, rng1) := randNat rng0 0 maxLen
  randBitString len rng1

private def pickRefPack (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafB]
    else #[refLeafA, refLeafB]
  (refs, rng1)

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV (-7)
    else if pick = 2 then .cell refLeafA
    else .builder Builder.empty
  (v, rng1)

private def genPldile8qFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkPldile8qCase s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes8 rng1
    (mkPldile8qCase "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkPldile8qCase s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkPldile8qCase s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkPldile8qCase s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    (mkPldile8qCase "fuzz/ok/boundary-max-positive"
      #[.slice (mkSliceFromLeBytes bytesMaxPos8)], rng1)
  else if shape = 6 then
    (mkPldile8qCase "fuzz/ok/boundary-min-negative"
      #[.slice (mkSliceFromLeBytes bytesMinNeg8)], rng1)
  else if shape = 7 then
    (mkPldile8qCase "fuzz/quiet/avail0"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 8 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    (mkPldile8qCase s!"fuzz/quiet/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 9 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkPldile8qCase s!"fuzz/quiet/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 10 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (noise, rng4) := pickNoise rng3
    (mkPldile8qCase s!"fuzz/quiet/deep-stack-short-{avail}"
      #[noise, .slice (mkSliceWithBitsRefs bits)], rng4)
  else if shape = 11 then
    (mkPldile8qCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    (mkPldile8qCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 13 then
    let (n, rng2) := randNat rng1 0 255
    (mkPldile8qCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 14 then
    (mkPldile8qCase "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 15 then
    let (bytes, rng2) := randBytes8 rng1
    let (noise, rng3) := pickNoise rng2
    (mkPldile8qCase "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), noise], rng3)
  else if shape = 16 then
    (mkPldile8qCase "fuzz/gas/exact"
      #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldile8qSetGasExact), .tonEnvOp .setGasLimit, pldile8qInstr], rng1)
  else
    (mkPldile8qCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldile8qSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldile8qInstr], rng1)

def suite : InstrSuite where
  id := pldile8qId
  unit := #[
    { name := "unit/direct/success-le-signed-and-prefetch-quiet-stack-contract"
      run := do
        let checks : Array (String × Array UInt8 × BitString) :=
          #[
            ("zero", bytesZero8, #[]),
            ("one", bytesOne8, #[]),
            ("minus1", bytesMinusOne8, #[]),
            ("max-pos", bytesMaxPos8, #[]),
            ("min-neg", bytesMinNeg8, #[]),
            ("0123456789abcdef", bytes0123456789abcdef, #[]),
            ("fedcba9876543210", bytesFedcba9876543210, #[]),
            ("tail3", bytes0123456789abcdef, tailBits3),
            ("tail11", bytesFedcba9876543210, tailBits11)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runPldile8qDirect #[.slice input])
            (expectedSuccessStack #[] (expectedSignedFromBytes bytes))

        let refsInput := mkSliceFromLeBytes bytesAltPos8 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-still-prefetch-int-and-status"
          (runPldile8qDirect #[.slice refsInput])
          (expectedSuccessStack #[] (expectedSignedFromBytes bytesAltPos8))

        let deepInput := mkSliceFromLeBytes bytesAltNeg8 tailBits13
        let below : Array Value := #[.null, intV 77]
        expectOkStack "ok/deep-stack-preserved"
          (runPldile8qDirect (below ++ #[.slice deepInput]))
          (expectedSuccessStack below (expectedSignedFromBytes bytesAltNeg8))

        expectOkStack "ok/partial-slice-offset"
          (runPldile8qDirect #[.slice partialCursorSlice])
          (expectedSuccessStack #[] (expectedSignedFromSlice partialCursorSlice)) }
    ,
    { name := "unit/direct/quiet-insufficient-bits-returns-status0-without-slice"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31, 63]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectOkStack s!"quiet/avail-{avail}"
            (runPldile8qDirect #[.slice s])
            (expectedQuietFailStack #[])

        expectOkStack "quiet/refs-only-no-bits"
          (runPldile8qDirect #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])])
          (expectedQuietFailStack #[])

        let below : Array Value := #[intV (-3), .cell refLeafA]
        let short := mkSliceWithBitsRefs (stripeBits 42 1)
        expectOkStack "quiet/deep-stack-preserved"
          (runPldile8qDirect (below ++ #[.slice short]))
          (expectedQuietFailStack below)

        expectOkStack "quiet/partial-cursor-short"
          (runPldile8qDirect #[.slice shortCursorSlice])
          (expectedQuietFailStack #[]) }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldile8qDirect #[]) .stkUnd
        expectErr "type/top-null" (runPldile8qDirect #[.null]) .typeChk
        expectErr "type/top-int" (runPldile8qDirect #[intV 9]) .typeChk
        expectErr "type/top-cell" (runPldile8qDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldile8qDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldile8qDirect #[.slice (mkSliceFromLeBytes bytesOne8), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldile8qDirect #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-and-assembler-boundaries"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits pldile8qWord 16 ++
             natToBits 0xd75f 16 ++
             natToBits 0xd75c 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-pldile8q" s1 pldile8qInstr 16
        let s3 ← expectDecodeStep "decode/raw-neighbor-pldule8q" s2 (.cellOp (.loadLeInt true 8 true true)) 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-pldile4q" s3 (.cellOp (.loadLeInt false 4 true true)) 16
        let s5 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s4 (.cellOp .ldZeroes) 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [pldile8qInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldile8q-single failed: {e}")
        if singleCode.bits = natToBits pldile8qWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldile8q: expected 0xd75e encoding, got bits {singleCode.bits}")

        let asmCode ←
          match assembleCp0 [pldile8qInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldile8q failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-pldile8q" a0 pldile8qInstr 16
        let a2 ← expectDecodeStep "decode/asm-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellOp (.loadLeInt false 5 true true)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-loadleint-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runPldile8qDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-ldzeroes"
          (runPldile8qDispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne8 tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne8 tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runPldile8qDispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldile8qCase "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero8)],
    mkPldile8qCase "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne8)],
    mkPldile8qCase "ok/minus-one/exact" #[.slice (mkSliceFromLeBytes bytesMinusOne8)],
    mkPldile8qCase "ok/max-positive/exact" #[.slice (mkSliceFromLeBytes bytesMaxPos8)],
    mkPldile8qCase "ok/min-negative/exact" #[.slice (mkSliceFromLeBytes bytesMinNeg8)],
    mkPldile8qCase "ok/random-0123456789abcdef/exact" #[.slice (mkSliceFromLeBytes bytes0123456789abcdef)],
    mkPldile8qCase "ok/random-fedcba9876543210/exact" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210)],
    mkPldile8qCase "ok/alt-positive/exact" #[.slice (mkSliceFromLeBytes bytesAltPos8)],
    mkPldile8qCase "ok/alt-negative/exact" #[.slice (mkSliceFromLeBytes bytesAltNeg8)],
    mkPldile8qCase "ok/tail3" #[.slice (mkSliceFromLeBytes bytes0123456789abcdef tailBits3)],
    mkPldile8qCase "ok/tail7" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits7)],
    mkPldile8qCase "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltNeg8 tailBits11)],
    mkPldile8qCase "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltPos8 tailBits13)],
    mkPldile8qCase "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne8 tailBits5 #[refLeafA])],
    mkPldile8qCase "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesMinNeg8 tailBits7 #[refLeafA, refLeafB])],
    mkPldile8qCase "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxPos8 tailBits3)],
    mkPldile8qCase "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)],

    mkPldile8qCase "quiet/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkPldile8qCase "quiet/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkPldile8qCase "quiet/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkPldile8qCase "quiet/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkPldile8qCase "quiet/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkPldile8qCase "quiet/avail63" #[.slice (mkSliceWithBitsRefs (stripeBits 63 0))],
    mkPldile8qCase "quiet/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldile8qCase "quiet/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],
    mkPldile8qCase "quiet/deep-stack-below-preserved" #[intV 77, .null, .slice (mkSliceWithBitsRefs (stripeBits 42 1))],

    mkPldile8qCase "underflow/empty" #[],
    mkPldile8qCase "type/top-null" #[.null],
    mkPldile8qCase "type/top-int" #[intV 0],
    mkPldile8qCase "type/top-cell" #[.cell Cell.empty],
    mkPldile8qCase "type/top-builder" #[.builder Builder.empty],
    mkPldile8qCase "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne8), .null],
    mkPldile8qCase "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3],

    mkPldile8qCase "gas/exact-cost-succeeds" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldile8qSetGasExact), .tonEnvOp .setGasLimit, pldile8qInstr],
    mkPldile8qCase "gas/exact-minus-one-out-of-gas" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldile8qSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldile8qInstr]
  ]
  fuzz := #[
    { seed := 2026021094
      count := 320
      gen := genPldile8qFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDILE8Q
