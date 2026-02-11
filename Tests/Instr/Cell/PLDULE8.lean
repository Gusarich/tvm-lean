import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDULE8

/-!
PLDULE8 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt true 8 true false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=7 for PLDULE8)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- error ordering: top-of-stack type failures happen before short-slice checks;
- insufficient bits (`haveBits 64 = false`) -> `cellUnd` (non-quiet mode);
- success path: little-endian 8-byte unsigned decode with prefetch stack contract
  (`PLD*` pushes int only; no remainder slice push);
- opcode family decode around `0xd757`, assembler byte-range guard (`bytes ∈ {4,8}`),
  and dispatch fallback for non-`.loadLeInt` handlers.

Harness constraint:
- oracle token encoding supports only full-cell slices; non-zero cursor slices are
  therefore covered in direct unit tests (not oracle/fuzz).
-/

private def pldule8Id : InstrId := { name := "PLDULE8" }

private def pldule8Instr : Instr :=
  .cellOp (.loadLeInt true 8 true false)

private def pldule8Word : Nat := 0xd757

private def dispatchSentinel : Int := 857

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkPldule8Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldule8Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldule8Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldule8Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly pldule8Instr stack

private def runPldule8DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesOne : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesMaxU64 : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff]

private def bytesHighBit : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytesMaxSignedPos : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0x7f]

private def bytesNearHighBitPlusOne : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytes0123456789ABCDEF : Array UInt8 :=
  #[u8 0xef, u8 0xcd, u8 0xab, u8 0x89, u8 0x67, u8 0x45, u8 0x23, u8 0x01]

private def bytesFEDCBA9876543210 : Array UInt8 :=
  #[u8 0x10, u8 0x32, u8 0x54, u8 0x76, u8 0x98, u8 0xba, u8 0xdc, u8 0xfe]

private def bytesAltLo : Array UInt8 :=
  #[u8 0x55, u8 0xaa, u8 0x10, u8 0x01, u8 0x22, u8 0x33, u8 0x44, u8 0x12]

private def bytesAltHi : Array UInt8 :=
  #[u8 0xaa, u8 0x55, u8 0x20, u8 0x90, u8 0x44, u8 0x33, u8 0x22, u8 0x91]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero,
    bytesOne,
    bytesMaxU64,
    bytesHighBit,
    bytesMaxSignedPos,
    bytesNearHighBitPlusOne,
    bytes0123456789ABCDEF,
    bytesFEDCBA9876543210,
    bytesAltLo,
    bytesAltHi
  ]

private def tailBits23 : BitString := natToBits 345678 23

private def mkSliceFromLeBytes
    (bytes : Array UInt8)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (bytesToBitsBE bytes ++ tail) refs

private def expectedUnsignedFromBytes (bytes : Array UInt8) : Int :=
  Int.ofNat (bytesToNatLE bytes)

private def expectedUnsignedFromSlice (s : Slice) : Int :=
  expectedUnsignedFromBytes (bitStringToBytesBE (s.readBits 64))

private def expectedSuccessStack (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[intV (expectedUnsignedFromSlice s)]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 152 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 17, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 96 1) #[refLeafA]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 37, refPos := 0 }

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

private def genPldule8FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkPldule8Case s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes8 rng1
    (mkPldule8Case "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkPldule8Case s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkPldule8Case s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkPldule8Case s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    (mkPldule8Case "fuzz/ok/boundary-max-u64"
      #[.slice (mkSliceFromLeBytes bytesMaxU64)], rng1)
  else if shape = 6 then
    (mkPldule8Case "fuzz/ok/boundary-high-bit"
      #[.slice (mkSliceFromLeBytes bytesHighBit)], rng1)
  else if shape = 7 then
    (mkPldule8Case "fuzz/ok/boundary-max-signed-pos"
      #[.slice (mkSliceFromLeBytes bytesMaxSignedPos)], rng1)
  else if shape = 8 then
    (mkPldule8Case "fuzz/ok/boundary-near-high-bit-plus1"
      #[.slice (mkSliceFromLeBytes bytesNearHighBitPlusOne)], rng1)
  else if shape = 9 then
    (mkPldule8Case "fuzz/ok/boundary-fedcba9876543210"
      #[.slice (mkSliceFromLeBytes bytesFEDCBA9876543210)], rng1)
  else if shape = 10 then
    (mkPldule8Case "fuzz/cellund/empty-slice"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 11 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    (mkPldule8Case s!"fuzz/cellund/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 12 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkPldule8Case s!"fuzz/cellund/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 13 then
    (mkPldule8Case "fuzz/cellund/refs-only-no-bits"
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])], rng1)
  else if shape = 14 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (noise, rng4) := pickNoise rng3
    (mkPldule8Case s!"fuzz/cellund/deep-stack-short-{avail}"
      #[noise, .slice (mkSliceWithBitsRefs bits)], rng4)
  else if shape = 15 then
    (mkPldule8Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 16 then
    (mkPldule8Case "fuzz/type/top-null" #[.null], rng1)
  else if shape = 17 then
    let (n, rng2) := randNat rng1 0 255
    (mkPldule8Case s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 18 then
    (mkPldule8Case "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 19 then
    (mkPldule8Case "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 20 then
    let (bytes, rng2) := randBytes8 rng1
    let (noise, rng3) := pickNoise rng2
    (mkPldule8Case "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), noise], rng3)
  else if shape = 21 then
    (mkPldule8Case "fuzz/error-order/type-before-cellund"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3], rng1)
  else
    (mkPldule8Case "fuzz/error-order/cellund-before-below-type"
      #[.null, .slice (mkSliceWithBitsRefs (stripeBits 8 1))], rng1)

def suite : InstrSuite where
  id := pldule8Id
  unit := #[
    { name := "unit/direct/success-le-unsigned-and-prefetch-contract"
      run := do
        let checks : Array (String × Array UInt8 × BitString) :=
          #[
            ("zero", bytesZero, #[]),
            ("one", bytesOne, #[]),
            ("max-u64", bytesMaxU64, #[]),
            ("high-bit", bytesHighBit, #[]),
            ("max-signed-pos", bytesMaxSignedPos, #[]),
            ("near-high-bit-plus1", bytesNearHighBitPlusOne, #[]),
            ("0123456789abcdef", bytes0123456789ABCDEF, #[]),
            ("fedcba9876543210", bytesFEDCBA9876543210, #[]),
            ("tail3", bytes0123456789ABCDEF, tailBits3),
            ("tail11", bytesFEDCBA9876543210, tailBits11),
            ("tail23", bytesAltHi, tailBits23)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runPldule8Direct #[.slice input])
            #[intV (expectedUnsignedFromBytes bytes)]

        let refsInput := mkSliceFromLeBytes bytesAltLo tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-still-int-only"
          (runPldule8Direct #[.slice refsInput])
          (expectedSuccessStack #[] refsInput)

        let deepInput := mkSliceFromLeBytes bytesAltHi tailBits13
        let below : Array Value := #[.null, intV 77]
        expectOkStack "ok/deep-stack-preserved"
          (runPldule8Direct (below ++ #[.slice deepInput]))
          (expectedSuccessStack below deepInput)

        expectOkStack "ok/partial-slice-offset"
          (runPldule8Direct #[.slice partialCursorSlice])
          (expectedSuccessStack #[] partialCursorSlice) }
    ,
    { name := "unit/direct/insufficient-bits-cellund"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31, 48, 63]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectErr s!"cellund/avail-{avail}"
            (runPldule8Direct #[.slice s]) .cellUnd

        expectErr "cellund/refs-only-no-bits"
          (runPldule8Direct #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])]) .cellUnd

        expectErr "cellund/short-cursor-avail59"
          (runPldule8Direct #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldule8Direct #[]) .stkUnd
        expectErr "type/top-null" (runPldule8Direct #[.null]) .typeChk
        expectErr "type/top-int" (runPldule8Direct #[intV 9]) .typeChk
        expectErr "type/top-cell" (runPldule8Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldule8Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldule8Direct #[.slice (mkSliceFromLeBytes bytesOne), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldule8Direct #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk
        expectErr "cellund/order-short-slice-over-invalid-below"
          (runPldule8Direct #[.null, .slice (mkSliceWithBitsRefs (stripeBits 8 1))]) .cellUnd }
    ,
    { name := "unit/direct/rangechk-unreachable-for-runtime-path"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runPldule8Direct #[.slice (mkSliceFromLeBytes bytesOne)]),
            ("cellund", runPldule8Direct #[.slice (mkSliceWithBitsRefs (stripeBits 31 0))]),
            ("underflow", runPldule8Direct #[]),
            ("type", runPldule8Direct #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for PLDULE8 runtime path")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-family-and-assembler-boundaries"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits 0xd750 16 ++
             natToBits 0xd753 16 ++
             natToBits 0xd756 16 ++
             natToBits pldule8Word 16 ++
             natToBits 0xd75f 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-family-start-ldile4" s1 (.cellOp (.loadLeInt false 4 false false)) 16
        let s3 ← expectDecodeStep "decode/raw-neighbor-ldule8" s2 (.cellOp (.loadLeInt true 8 false false)) 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-pldile8" s3 (.cellOp (.loadLeInt false 8 true false)) 16
        let s5 ← expectDecodeStep "decode/raw-pldule8" s4 pldule8Instr 16
        let s6 ← expectDecodeStep "decode/raw-neighbor-pldule8q" s5 (.cellOp (.loadLeInt true 8 true true)) 16
        let s7 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s6 (.cellOp .ldZeroes) 16
        let s8 ← expectDecodeStep "decode/raw-tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [pldule8Instr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldule8-single failed: {e}")
        if singleCode.bits = natToBits pldule8Word 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldule8: expected 0xd757 encoding, got bits {singleCode.bits}")

        let asmCode ←
          match assembleCp0 [pldule8Instr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldule8 failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-pldule8" a0 pldule8Instr 16
        let a2 ← expectDecodeStep "decode/asm-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellOp (.loadLeInt true 5 true false)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes-5: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes-5: expected rangeChk, got success")

        match assembleCp0 [.cellOp (.loadLeInt true 0 true false)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes-0: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-loadleint-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runPldule8DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-ldzeroes"
          (runPldule8DispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runPldule8DispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldule8Case "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero)],
    mkPldule8Case "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne)],
    mkPldule8Case "ok/max-u64/exact" #[.slice (mkSliceFromLeBytes bytesMaxU64)],
    mkPldule8Case "ok/high-bit/exact" #[.slice (mkSliceFromLeBytes bytesHighBit)],
    mkPldule8Case "ok/max-signed-pos/exact" #[.slice (mkSliceFromLeBytes bytesMaxSignedPos)],
    mkPldule8Case "ok/near-high-bit-plus1/exact" #[.slice (mkSliceFromLeBytes bytesNearHighBitPlusOne)],
    mkPldule8Case "ok/random-0123456789abcdef/exact" #[.slice (mkSliceFromLeBytes bytes0123456789ABCDEF)],
    mkPldule8Case "ok/random-fedcba9876543210/exact" #[.slice (mkSliceFromLeBytes bytesFEDCBA9876543210)],
    mkPldule8Case "ok/alt-lo/exact" #[.slice (mkSliceFromLeBytes bytesAltLo)],
    mkPldule8Case "ok/alt-hi/exact" #[.slice (mkSliceFromLeBytes bytesAltHi)],
    mkPldule8Case "ok/tail3" #[.slice (mkSliceFromLeBytes bytes0123456789ABCDEF tailBits3)],
    mkPldule8Case "ok/tail7" #[.slice (mkSliceFromLeBytes bytesFEDCBA9876543210 tailBits7)],
    mkPldule8Case "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltHi tailBits11)],
    mkPldule8Case "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltLo tailBits13)],
    mkPldule8Case "ok/tail23" #[.slice (mkSliceFromLeBytes bytesNearHighBitPlusOne tailBits23)],
    mkPldule8Case "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne tailBits5 #[refLeafA])],
    mkPldule8Case "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesHighBit tailBits7 #[refLeafA, refLeafB])],
    mkPldule8Case "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxU64 tailBits3)],
    mkPldule8Case "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesFEDCBA9876543210 tailBits11)],
    mkPldule8Case "ok/deep-stack-cell-below" #[.cell refLeafA, .slice (mkSliceFromLeBytes bytesAltHi tailBits5)],

    mkPldule8Case "cellund/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkPldule8Case "cellund/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkPldule8Case "cellund/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkPldule8Case "cellund/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkPldule8Case "cellund/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkPldule8Case "cellund/avail48" #[.slice (mkSliceWithBitsRefs (stripeBits 48 0))],
    mkPldule8Case "cellund/avail63" #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkPldule8Case "cellund/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldule8Case "cellund/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],
    mkPldule8Case "cellund/order-short-slice-over-invalid-below"
      #[.null, .slice (mkSliceWithBitsRefs (stripeBits 8 1))],

    mkPldule8Case "underflow/empty" #[],
    mkPldule8Case "type/top-null" #[.null],
    mkPldule8Case "type/top-int" #[intV 0],
    mkPldule8Case "type/top-cell" #[.cell Cell.empty],
    mkPldule8Case "type/top-builder" #[.builder Builder.empty],
    mkPldule8Case "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne), .null],
    mkPldule8Case "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]
  ]
  fuzz := #[
    { seed := 2026021277
      count := 320
      gen := genPldule8FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDULE8
