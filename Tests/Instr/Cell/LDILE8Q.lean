import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDILE8Q

/-!
LDILE8Q branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt false 8 false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=10 for LDILE8Q)

Branch contracts covered by this suite:
- stack underflow/type from initial `popSlice`;
- quiet insufficient-bits path (`haveBits 64 = false`) in non-prefetch mode re-pushes original
  slice and then status `0`;
- success path: little-endian signed 8-byte decode, then push remainder slice, then status `-1`;
- opcode-family decode around `0xd75a`, including family boundaries and assembler byte-range guard;
- dispatch fallback for non-`.loadLeInt` instructions.

Oracle harness constraint:
- token encoder supports only full-cell slices (`bitPos = 0`, `refPos = 0`) in oracle cases.
  Partial-cursor slice coverage is kept in direct unit tests; oracle/fuzz inputs stay full-cell.
-/

private def ldile8qId : InstrId := { name := "LDILE8Q" }

private def ldile8qInstr : Instr :=
  .cellOp (.loadLeInt false 8 false true)

private def ldile8qWord : Nat := 0xd75a

private def dispatchSentinel : Int := 857

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkLdile8qCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldile8qInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldile8qId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdile8qDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly ldile8qInstr stack

private def runLdile8qDirectInstr (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly instr stack

private def runLdile8qDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero8 : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesOne8 : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesMinusOne8 : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff]

private def bytesMaxPos8 : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0x7f]

private def bytesMinNeg8 : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytesNearMaxMinusOne8 : Array UInt8 :=
  #[u8 0xfe, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0x7f]

private def bytesNearMinPlusOne8 : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytes0123456789abcdef : Array UInt8 :=
  #[u8 0xef, u8 0xcd, u8 0xab, u8 0x89, u8 0x67, u8 0x45, u8 0x23, u8 0x01]

private def bytesFedcba9876543210 : Array UInt8 :=
  #[u8 0x10, u8 0x32, u8 0x54, u8 0x76, u8 0x98, u8 0xba, u8 0xdc, u8 0xfe]

private def bytesAltPos8 : Array UInt8 :=
  #[u8 0x55, u8 0xaa, u8 0x10, u8 0x01, u8 0x22, u8 0x33, u8 0x44, u8 0x12]

private def bytesAltNeg8 : Array UInt8 :=
  #[u8 0xaa, u8 0x55, u8 0x20, u8 0x90, u8 0x44, u8 0x33, u8 0x22, u8 0x91]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero8,
    bytesOne8,
    bytesMinusOne8,
    bytesMaxPos8,
    bytesMinNeg8,
    bytesNearMaxMinusOne8,
    bytesNearMinPlusOne8,
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

private def expectedSuccessStack (below : Array Value) (s : Slice) (x : Int) : Array Value :=
  below ++ #[intV x, .slice (s.advanceBits 64), intV (-1)]

private def expectedQuietFailStack (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[.slice s, intV 0]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 152 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 17, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 96 1) #[refLeafA]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 37, refPos := 0 }

private def ldile8qSetGasExact : Int :=
  computeExactGasBudget ldile8qInstr

private def ldile8qSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldile8qInstr

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

private def genLdile8qFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkLdile8qCase s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes8 rng1
    (mkLdile8qCase "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkLdile8qCase s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkLdile8qCase s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkLdile8qCase s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    (mkLdile8qCase "fuzz/ok/boundary-max-positive"
      #[.slice (mkSliceFromLeBytes bytesMaxPos8)], rng1)
  else if shape = 6 then
    (mkLdile8qCase "fuzz/ok/boundary-min-negative"
      #[.slice (mkSliceFromLeBytes bytesMinNeg8)], rng1)
  else if shape = 7 then
    (mkLdile8qCase "fuzz/quiet/avail0"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 8 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    (mkLdile8qCase s!"fuzz/quiet/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 9 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkLdile8qCase s!"fuzz/quiet/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 10 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (noise, rng4) := pickNoise rng3
    (mkLdile8qCase s!"fuzz/quiet/deep-stack-short-{avail}"
      #[noise, .slice (mkSliceWithBitsRefs bits)], rng4)
  else if shape = 11 then
    (mkLdile8qCase "fuzz/quiet/refs-only-no-bits"
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])], rng1)
  else if shape = 12 then
    (mkLdile8qCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 13 then
    (mkLdile8qCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 14 then
    let (n, rng2) := randNat rng1 0 255
    (mkLdile8qCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 15 then
    (mkLdile8qCase "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 16 then
    (mkLdile8qCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 17 then
    let (bytes, rng2) := randBytes8 rng1
    (mkLdile8qCase "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), .null], rng2)
  else if shape = 18 then
    (mkLdile8qCase "fuzz/type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3], rng1)
  else if shape = 19 then
    (mkLdile8qCase "fuzz/gas/exact"
      #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num ldile8qSetGasExact), .tonEnvOp .setGasLimit, ldile8qInstr], rng1)
  else
    (mkLdile8qCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num ldile8qSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldile8qInstr], rng1)

def suite : InstrSuite where
  id := ldile8qId
  unit := #[
    { name := "unit/direct/quiet-success-signed-little-endian-non-prefetch-stack-contract"
      run := do
        let checks : Array (String × Array UInt8 × BitString) :=
          #[
            ("zero", bytesZero8, #[]),
            ("one", bytesOne8, #[]),
            ("minus1", bytesMinusOne8, #[]),
            ("max-pos", bytesMaxPos8, #[]),
            ("min-neg", bytesMinNeg8, #[]),
            ("near-max-minus1", bytesNearMaxMinusOne8, #[]),
            ("near-min-plus1", bytesNearMinPlusOne8, #[]),
            ("0123456789abcdef", bytes0123456789abcdef, #[]),
            ("fedcba9876543210", bytesFedcba9876543210, #[]),
            ("tail3", bytes0123456789abcdef, tailBits3),
            ("tail11", bytesFedcba9876543210, tailBits11)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runLdile8qDirect #[.slice input])
            (expectedSuccessStack #[] input (expectedSignedFromBytes bytes))

        let refsInput := mkSliceFromLeBytes bytesAltPos8 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-remainder-preserved"
          (runLdile8qDirect #[.slice refsInput])
          (expectedSuccessStack #[] refsInput (expectedSignedFromBytes bytesAltPos8))

        let deepInput := mkSliceFromLeBytes bytesAltNeg8 tailBits13
        let below : Array Value := #[.null, intV 77]
        expectOkStack "ok/deep-stack-preserved"
          (runLdile8qDirect (below ++ #[.slice deepInput]))
          (expectedSuccessStack below deepInput (expectedSignedFromBytes bytesAltNeg8))

        expectOkStack "ok/partial-slice-offset"
          (runLdile8qDirect #[.slice partialCursorSlice])
          (expectedSuccessStack #[] partialCursorSlice (expectedSignedFromSlice partialCursorSlice)) }
    ,
    { name := "unit/direct/quiet-insufficient-bits-repushes-slice-then-status0"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31, 48, 63]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectOkStack s!"quiet/avail-{avail}"
            (runLdile8qDirect #[.slice s])
            (expectedQuietFailStack #[] s)

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectOkStack "quiet/refs-only-no-bits"
          (runLdile8qDirect #[.slice refsOnly])
          (expectedQuietFailStack #[] refsOnly)

        let below : Array Value := #[intV (-3), .cell refLeafA]
        let short := mkSliceWithBitsRefs (stripeBits 42 1)
        expectOkStack "quiet/deep-stack-preserved"
          (runLdile8qDirect (below ++ #[.slice short]))
          (expectedQuietFailStack below short)

        expectOkStack "quiet/partial-cursor-short"
          (runLdile8qDirect #[.slice shortCursorSlice])
          (expectedQuietFailStack #[] shortCursorSlice)

        expectErr "nonquiet/short-throws-cellund"
          (runLdile8qDirectInstr (.cellOp (.loadLeInt false 8 false false))
            #[.slice (mkSliceWithBitsRefs (stripeBits 63 0))]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runLdile8qDirect #[]) .stkUnd
        expectErr "type/top-null" (runLdile8qDirect #[.null]) .typeChk
        expectErr "type/top-int" (runLdile8qDirect #[intV 9]) .typeChk
        expectErr "type/top-cell" (runLdile8qDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runLdile8qDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdile8qDirect #[.slice (mkSliceFromLeBytes bytesOne8), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runLdile8qDirect #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-and-assembler-boundaries"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits 0xd750 16 ++
             natToBits ldile8qWord 16 ++
             natToBits 0xd75b 16 ++
             natToBits 0xd75e 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-family-start-ldile4" s1 (.cellOp (.loadLeInt false 4 false false)) 16
        let s3 ← expectDecodeStep "decode/raw-ldile8q" s2 ldile8qInstr 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-ldule8q" s3 (.cellOp (.loadLeInt true 8 false true)) 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-pldile8q" s4 (.cellOp (.loadLeInt false 8 true true)) 16
        let s6 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s5 (.cellOp .ldZeroes) 16
        let s7 ← expectDecodeStep "decode/raw-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [ldile8qInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/ldile8q-single failed: {e}")
        if singleCode.bits = natToBits ldile8qWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldile8q: expected 0xd75a encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldile8q: expected 16-bit encoding, got {singleCode.bits.size}")

        let asmCode ←
          match assembleCp0 [ldile8qInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/ldile8q failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-ldile8q" a0 ldile8qInstr 16
        let a2 ← expectDecodeStep "decode/asm-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellOp (.loadLeInt false 5 false true)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-loadleint-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runLdile8qDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-ldzeroes"
          (runLdile8qDispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne8 tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne8 tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runLdile8qDispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdile8qCase "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero8)],
    mkLdile8qCase "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne8)],
    mkLdile8qCase "ok/minus-one/exact" #[.slice (mkSliceFromLeBytes bytesMinusOne8)],
    mkLdile8qCase "ok/max-positive/exact" #[.slice (mkSliceFromLeBytes bytesMaxPos8)],
    mkLdile8qCase "ok/min-negative/exact" #[.slice (mkSliceFromLeBytes bytesMinNeg8)],
    mkLdile8qCase "ok/near-max-minus1/exact" #[.slice (mkSliceFromLeBytes bytesNearMaxMinusOne8)],
    mkLdile8qCase "ok/near-min-plus1/exact" #[.slice (mkSliceFromLeBytes bytesNearMinPlusOne8)],
    mkLdile8qCase "ok/random-0123456789abcdef/exact" #[.slice (mkSliceFromLeBytes bytes0123456789abcdef)],
    mkLdile8qCase "ok/random-fedcba9876543210/exact" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210)],
    mkLdile8qCase "ok/alt-positive/exact" #[.slice (mkSliceFromLeBytes bytesAltPos8)],
    mkLdile8qCase "ok/alt-negative/exact" #[.slice (mkSliceFromLeBytes bytesAltNeg8)],
    mkLdile8qCase "ok/tail3" #[.slice (mkSliceFromLeBytes bytes0123456789abcdef tailBits3)],
    mkLdile8qCase "ok/tail7" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits7)],
    mkLdile8qCase "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltNeg8 tailBits11)],
    mkLdile8qCase "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltPos8 tailBits13)],
    mkLdile8qCase "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne8 tailBits5 #[refLeafA])],
    mkLdile8qCase "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesMinNeg8 tailBits7 #[refLeafA, refLeafB])],
    mkLdile8qCase "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxPos8 tailBits3)],
    mkLdile8qCase "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)],

    mkLdile8qCase "quiet/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkLdile8qCase "quiet/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkLdile8qCase "quiet/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkLdile8qCase "quiet/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkLdile8qCase "quiet/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkLdile8qCase "quiet/avail48" #[.slice (mkSliceWithBitsRefs (stripeBits 48 0))],
    mkLdile8qCase "quiet/avail63" #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkLdile8qCase "quiet/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkLdile8qCase "quiet/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],
    mkLdile8qCase "quiet/deep-stack-below-preserved" #[intV 77, .null, .slice (mkSliceWithBitsRefs (stripeBits 42 1))],

    mkLdile8qCase "underflow/empty" #[],
    mkLdile8qCase "type/top-null" #[.null],
    mkLdile8qCase "type/top-int" #[intV 0],
    mkLdile8qCase "type/top-cell" #[.cell Cell.empty],
    mkLdile8qCase "type/top-builder" #[.builder Builder.empty],
    mkLdile8qCase "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne8), .null],
    mkLdile8qCase "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3],

    mkLdile8qCase "gas/exact-cost-succeeds" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num ldile8qSetGasExact), .tonEnvOp .setGasLimit, ldile8qInstr],
    mkLdile8qCase "gas/exact-minus-one-out-of-gas" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num ldile8qSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldile8qInstr]
  ]
  fuzz := #[
    { seed := 2026021108
      count := 320
      gen := genLdile8qFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDILE8Q
