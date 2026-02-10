import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDILE8

/-
PLDILE8 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt false 8 true false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=6 for PLDILE8)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- insufficient bits (`haveBits 64 = false`) -> `cellUnd` for non-quiet mode;
- success path: little-endian 8-byte decode + signed two's-complement conversion, prefetch contract
  (`PLD*` pushes int only; no remainder slice push);
- opcode family decode around `0xd756` and dispatch fallthrough for non-`.loadLeInt` handlers;
- assembler byte-length guard (`bytes ∈ {4,8}` only).

Harness constraint:
- oracle token encoding supports only full-cell slices; non-zero cursor slices cannot be serialized.
  Cursor-offset branches are therefore covered in direct unit tests (not oracle/fuzz).
-/

private def pldile8Id : InstrId := { name := "PLDILE8" }

private def pldile8Instr : Instr :=
  .cellOp (.loadLeInt false 8 true false)

private def pldile8Word : Nat := 0xd756

private def dispatchSentinel : Int := 842

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkPldile8Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldile8Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldile8Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldile8Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly pldile8Instr stack

private def runPldile8DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesOne : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesMinusOne : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff]

private def bytesMaxPos : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0x7f]

private def bytesMinNeg : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytesNearMaxMinusOne : Array UInt8 :=
  #[u8 0xfe, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0x7f]

private def bytesNearMinPlusOne : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytes0123456789ABCDEF : Array UInt8 :=
  #[u8 0xef, u8 0xcd, u8 0xab, u8 0x89, u8 0x67, u8 0x45, u8 0x23, u8 0x01]

private def bytesFEDCBA9876543210 : Array UInt8 :=
  #[u8 0x10, u8 0x32, u8 0x54, u8 0x76, u8 0x98, u8 0xba, u8 0xdc, u8 0xfe]

private def bytesAltPos : Array UInt8 :=
  #[u8 0x55, u8 0xaa, u8 0x10, u8 0x01, u8 0x22, u8 0x33, u8 0x44, u8 0x12]

private def bytesAltNeg : Array UInt8 :=
  #[u8 0xaa, u8 0x55, u8 0x20, u8 0x90, u8 0x44, u8 0x33, u8 0x22, u8 0x91]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero,
    bytesOne,
    bytesMinusOne,
    bytesMaxPos,
    bytesMinNeg,
    bytesNearMaxMinusOne,
    bytesNearMinPlusOne,
    bytes0123456789ABCDEF,
    bytesFEDCBA9876543210,
    bytesAltPos,
    bytesAltNeg
  ]

private def tailBits3 : BitString := natToBits 5 3
private def tailBits5 : BitString := natToBits 21 5
private def tailBits7 : BitString := natToBits 93 7
private def tailBits11 : BitString := natToBits 1337 11
private def tailBits13 : BitString := natToBits 4242 13

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]

private def bytesToBitsBE (bs : Array UInt8) : BitString :=
  bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSliceFromLeBytes
    (bytes : Array UInt8)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (bytesToBitsBE bytes ++ tail) refs

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def expectedSignedFromBytes (bytes : Array UInt8) : Int :=
  natToIntSignedTwos (bytesToNatLE bytes) 64

private def expectedSignedFromSlice (s : Slice) : Int :=
  expectedSignedFromBytes (bitStringToBytesBE (s.readBits 64))

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 152 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 17, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 96 1) #[refLeafA]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 37, refPos := 0 }

private def randBitString (count : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

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

private def genPldile8FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkPldile8Case s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes8 rng1
    (mkPldile8Case "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkPldile8Case s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkPldile8Case s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkPldile8Case s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    (mkPldile8Case "fuzz/ok/boundary-max-positive"
      #[.slice (mkSliceFromLeBytes bytesMaxPos)], rng1)
  else if shape = 6 then
    (mkPldile8Case "fuzz/ok/boundary-min-negative"
      #[.slice (mkSliceFromLeBytes bytesMinNeg)], rng1)
  else if shape = 7 then
    (mkPldile8Case "fuzz/ok/boundary-near-max-minus1"
      #[.slice (mkSliceFromLeBytes bytesNearMaxMinusOne)], rng1)
  else if shape = 8 then
    (mkPldile8Case "fuzz/cellund/empty-slice"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 9 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    (mkPldile8Case s!"fuzz/cellund/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 10 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkPldile8Case s!"fuzz/cellund/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 11 then
    (mkPldile8Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 12 then
    (mkPldile8Case "fuzz/type/top-null" #[.null], rng1)
  else if shape = 13 then
    let (n, rng2) := randNat rng1 0 255
    (mkPldile8Case s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 14 then
    (mkPldile8Case "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 15 then
    (mkPldile8Case "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 16 then
    let (bytes, rng2) := randBytes8 rng1
    (mkPldile8Case "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), .null], rng2)
  else if shape = 17 then
    (mkPldile8Case "fuzz/type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3], rng1)
  else if shape = 18 then
    (mkPldile8Case "fuzz/cellund/short63-refs2"
      #[.slice (mkSliceWithBitsRefs (stripeBits 63 1) #[refLeafA, refLeafB])], rng1)
  else
    (mkPldile8Case "fuzz/cellund/avail48"
      #[.slice (mkSliceWithBitsRefs (stripeBits 48 0))], rng1)

def suite : InstrSuite where
  id := pldile8Id
  unit := #[
    { name := "unit/direct/success-le-signed-and-prefetch-contract"
      run := do
        let checks : Array (String × Array UInt8 × BitString) :=
          #[
            ("zero", bytesZero, #[]),
            ("one", bytesOne, #[]),
            ("minus1", bytesMinusOne, #[]),
            ("max-pos", bytesMaxPos, #[]),
            ("min-neg", bytesMinNeg, #[]),
            ("near-max-minus1", bytesNearMaxMinusOne, #[]),
            ("near-min-plus1", bytesNearMinPlusOne, #[]),
            ("0123456789abcdef", bytes0123456789ABCDEF, #[]),
            ("fedcba9876543210", bytesFEDCBA9876543210, #[]),
            ("tail3", bytes0123456789ABCDEF, tailBits3),
            ("tail11", bytesFEDCBA9876543210, tailBits11)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runPldile8Direct #[.slice input])
            #[intV (expectedSignedFromBytes bytes)]

        let refsInput := mkSliceFromLeBytes bytesAltPos tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-still-int-only"
          (runPldile8Direct #[.slice refsInput])
          #[intV (expectedSignedFromBytes bytesAltPos)]

        let deepInput := mkSliceFromLeBytes bytesAltNeg tailBits13
        expectOkStack "ok/deep-stack-preserved"
          (runPldile8Direct #[.null, intV 77, .slice deepInput])
          #[.null, intV 77, intV (expectedSignedFromBytes bytesAltNeg)]

        expectOkStack "ok/partial-slice-offset"
          (runPldile8Direct #[.slice partialCursorSlice])
          #[intV (expectedSignedFromSlice partialCursorSlice)] }
    ,
    { name := "unit/direct/insufficient-bits-cellund"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31, 48, 63]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectErr s!"cellund/avail-{avail}"
            (runPldile8Direct #[.slice s]) .cellUnd

        expectErr "cellund/refs-only-no-bits"
          (runPldile8Direct #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])]) .cellUnd

        expectErr "cellund/short-cursor-avail59"
          (runPldile8Direct #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldile8Direct #[]) .stkUnd
        expectErr "type/top-null" (runPldile8Direct #[.null]) .typeChk
        expectErr "type/top-int" (runPldile8Direct #[intV 9]) .typeChk
        expectErr "type/top-cell" (runPldile8Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldile8Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldile8Direct #[.slice (mkSliceFromLeBytes bytesOne), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldile8Direct #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-and-assembler-path"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits 0xd750 16 ++
             natToBits pldile8Word 16 ++
             natToBits 0xd75e 16 ++
             natToBits 0xd75f 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-family-start-ldile4" s1 (.cellOp (.loadLeInt false 4 false false)) 16
        let s3 ← expectDecodeStep "decode/raw-pldile8" s2 pldile8Instr 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-pldile8q" s3 (.cellOp (.loadLeInt false 8 true true)) 16
        let s5 ← expectDecodeStep "decode/raw-family-end-pldule8q" s4 (.cellOp (.loadLeInt true 8 true true)) 16
        let s6 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s5 (.cellOp .ldZeroes) 16
        let s7 ← expectDecodeStep "decode/raw-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let asmCode ←
          match assembleCp0 [pldile8Instr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldile8 failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-pldile8" a0 pldile8Instr 16
        let a2 ← expectDecodeStep "decode/asm-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellOp (.loadLeInt false 5 true false)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-loadleint-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runPldile8DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop"
          (runPldile8DispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runPldile8DispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldile8Case "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero)],
    mkPldile8Case "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne)],
    mkPldile8Case "ok/minus-one/exact" #[.slice (mkSliceFromLeBytes bytesMinusOne)],
    mkPldile8Case "ok/max-positive/exact" #[.slice (mkSliceFromLeBytes bytesMaxPos)],
    mkPldile8Case "ok/min-negative/exact" #[.slice (mkSliceFromLeBytes bytesMinNeg)],
    mkPldile8Case "ok/near-max-minus1/exact" #[.slice (mkSliceFromLeBytes bytesNearMaxMinusOne)],
    mkPldile8Case "ok/near-min-plus1/exact" #[.slice (mkSliceFromLeBytes bytesNearMinPlusOne)],
    mkPldile8Case "ok/random-0123456789abcdef/exact" #[.slice (mkSliceFromLeBytes bytes0123456789ABCDEF)],
    mkPldile8Case "ok/random-fedcba9876543210/exact" #[.slice (mkSliceFromLeBytes bytesFEDCBA9876543210)],
    mkPldile8Case "ok/alt-positive/exact" #[.slice (mkSliceFromLeBytes bytesAltPos)],
    mkPldile8Case "ok/alt-negative/exact" #[.slice (mkSliceFromLeBytes bytesAltNeg)],
    mkPldile8Case "ok/tail3" #[.slice (mkSliceFromLeBytes bytes0123456789ABCDEF tailBits3)],
    mkPldile8Case "ok/tail7" #[.slice (mkSliceFromLeBytes bytesFEDCBA9876543210 tailBits7)],
    mkPldile8Case "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltNeg tailBits11)],
    mkPldile8Case "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltPos tailBits13)],
    mkPldile8Case "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne tailBits5 #[refLeafA])],
    mkPldile8Case "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesMinNeg tailBits7 #[refLeafA, refLeafB])],
    mkPldile8Case "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxPos tailBits3)],
    mkPldile8Case "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesFEDCBA9876543210 tailBits11)],

    mkPldile8Case "cellund/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkPldile8Case "cellund/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkPldile8Case "cellund/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkPldile8Case "cellund/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkPldile8Case "cellund/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkPldile8Case "cellund/avail48" #[.slice (mkSliceWithBitsRefs (stripeBits 48 0))],
    mkPldile8Case "cellund/avail63" #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkPldile8Case "cellund/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldile8Case "cellund/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],

    mkPldile8Case "underflow/empty" #[],
    mkPldile8Case "type/top-null" #[.null],
    mkPldile8Case "type/top-int" #[intV 0],
    mkPldile8Case "type/top-cell" #[.cell Cell.empty],
    mkPldile8Case "type/top-builder" #[.builder Builder.empty],
    mkPldile8Case "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne), .null],
    mkPldile8Case "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]
  ]
  fuzz := #[
    { seed := 2026021062
      count := 320
      gen := genPldile8FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDILE8
