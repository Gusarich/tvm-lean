import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDULE4

/-!
PLDULE4 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt true 4 true false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=`5` for PLDULE4)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- error ordering: top-of-stack type failures happen before short-slice checks;
- insufficient bits (`haveBits 32 = false`) -> `cellUnd` (non-quiet mode);
- success path: little-endian 4-byte unsigned decode, prefetch contract
  (`PLD*` pushes int only; no remainder slice push);
- opcode family decode around `0xd755`, assembler range-check for invalid byte widths,
  and dispatch fallback for non-`.loadLeInt` handlers.
-/

private def pldule4Id : InstrId := { name := "PLDULE4" }

private def pldule4Instr : Instr :=
  .cellOp (.loadLeInt true 4 true false)

private def pldule4Word : Nat := 0xd755

private def dispatchSentinel : Int := 853

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkPldule4Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldule4Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldule4Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldule4Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly pldule4Instr stack

private def runPldule4DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero : Array UInt8 := #[u8 0x00, u8 0x00, u8 0x00, u8 0x00]
private def bytesOne : Array UInt8 := #[u8 0x01, u8 0x00, u8 0x00, u8 0x00]
private def bytesMaxU32 : Array UInt8 := #[u8 0xff, u8 0xff, u8 0xff, u8 0xff]
private def bytesHighBit : Array UInt8 := #[u8 0x00, u8 0x00, u8 0x00, u8 0x80]
private def bytesMaxSignedPos : Array UInt8 := #[u8 0xff, u8 0xff, u8 0xff, u8 0x7f]
private def bytes12345678 : Array UInt8 := #[u8 0x78, u8 0x56, u8 0x34, u8 0x12]
private def bytesF6543210 : Array UInt8 := #[u8 0x10, u8 0x32, u8 0x54, u8 0xf6]
private def bytesAltLo : Array UInt8 := #[u8 0x55, u8 0xaa, u8 0x10, u8 0x01]
private def bytesAltHi : Array UInt8 := #[u8 0xaa, u8 0x55, u8 0x20, u8 0x90]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero,
    bytesOne,
    bytesMaxU32,
    bytesHighBit,
    bytesMaxSignedPos,
    bytes12345678,
    bytesF6543210,
    bytesAltLo,
    bytesAltHi
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

private def expectedUnsignedFromBytes (bytes : Array UInt8) : Int :=
  Int.ofNat (bytesToNatLE bytes)

private def expectedUnsignedFromSlice (s : Slice) : Int :=
  expectedUnsignedFromBytes (bitStringToBytesBE (s.readBits 32))

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 80 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 5, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 40 1) #[refLeafA]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 10, refPos := 0 }

private def randBitString (count : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def randBytes4 (rng0 : StdGen) : Array UInt8 × StdGen := Id.run do
  let mut out : Array UInt8 := #[]
  let mut rng := rng0
  for _ in [0:4] do
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

private def genPldule4FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkPldule4Case s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes4 rng1
    (mkPldule4Case "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkPldule4Case s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkPldule4Case s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 12
    (mkPldule4Case s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[.null, .slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 5 then
    (mkPldule4Case "fuzz/ok/boundary-max-u32"
      #[.slice (mkSliceFromLeBytes bytesMaxU32)], rng1)
  else if shape = 6 then
    (mkPldule4Case "fuzz/ok/boundary-high-bit"
      #[.slice (mkSliceFromLeBytes bytesHighBit)], rng1)
  else if shape = 7 then
    (mkPldule4Case "fuzz/cellund/empty-slice"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 8 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    (mkPldule4Case s!"fuzz/cellund/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 9 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkPldule4Case s!"fuzz/cellund/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 10 then
    (mkPldule4Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 11 then
    (mkPldule4Case "fuzz/type/top-null" #[.null], rng1)
  else if shape = 12 then
    let (n, rng2) := randNat rng1 0 255
    (mkPldule4Case s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 13 then
    (mkPldule4Case "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 14 then
    (mkPldule4Case "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 15 then
    let (bytes, rng2) := randBytes4 rng1
    (mkPldule4Case "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), .null], rng2)
  else if shape = 16 then
    (mkPldule4Case "fuzz/error-order/type-before-cellund"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3], rng1)
  else
    (mkPldule4Case "fuzz/error-order/cellund-before-below-type"
      #[.null, .slice (mkSliceWithBitsRefs (stripeBits 8 1))], rng1)

def suite : InstrSuite where
  id := pldule4Id
  unit := #[
    { name := "unit/direct/success-le-unsigned-and-prefetch-contract"
      run := do
        let checks : Array (String × Array UInt8 × BitString) :=
          #[
            ("zero", bytesZero, #[]),
            ("one", bytesOne, #[]),
            ("max-u32", bytesMaxU32, #[]),
            ("high-bit", bytesHighBit, #[]),
            ("max-signed-pos", bytesMaxSignedPos, #[]),
            ("12345678", bytes12345678, #[]),
            ("f6543210", bytesF6543210, #[]),
            ("tail3", bytes12345678, tailBits3),
            ("tail11", bytesF6543210, tailBits11),
            ("tail13", bytesAltHi, tailBits13)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runPldule4Direct #[.slice input])
            #[intV (expectedUnsignedFromBytes bytes)]

        let refsInput := mkSliceFromLeBytes bytesAltLo tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-still-int-only"
          (runPldule4Direct #[.slice refsInput])
          #[intV (expectedUnsignedFromBytes bytesAltLo)]

        let deepInput := mkSliceFromLeBytes bytesAltHi tailBits13
        expectOkStack "ok/deep-stack-preserved"
          (runPldule4Direct #[.null, intV 77, .slice deepInput])
          #[.null, intV 77, intV (expectedUnsignedFromBytes bytesAltHi)]

        expectOkStack "ok/partial-slice-offset"
          (runPldule4Direct #[.slice partialCursorSlice])
          #[intV (expectedUnsignedFromSlice partialCursorSlice)] }
    ,
    { name := "unit/direct/insufficient-bits-cellund"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectErr s!"cellund/avail-{avail}"
            (runPldule4Direct #[.slice s]) .cellUnd

        expectErr "cellund/refs-only-no-bits"
          (runPldule4Direct #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])]) .cellUnd

        expectErr "cellund/short-partial-cursor-avail30"
          (runPldule4Direct #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldule4Direct #[]) .stkUnd
        expectErr "type/top-null" (runPldule4Direct #[.null]) .typeChk
        expectErr "type/top-int" (runPldule4Direct #[intV 9]) .typeChk
        expectErr "type/top-cell" (runPldule4Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldule4Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldule4Direct #[.slice (mkSliceFromLeBytes bytesOne), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldule4Direct #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk
        expectErr "cellund/order-short-slice-over-invalid-below"
          (runPldule4Direct #[.null, .slice (mkSliceWithBitsRefs (stripeBits 8 1))]) .cellUnd }
    ,
    { name := "unit/opcode/decode-family-and-assembler-path"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits pldule4Word 16 ++
             natToBits 0xd754 16 ++
             natToBits 0xd757 16 ++
             natToBits 0xd75d 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-pldule4" s1 pldule4Instr 16
        let s3 ← expectDecodeStep "decode/raw-neighbor-pldile4" s2 (.cellOp (.loadLeInt false 4 true false)) 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-pldule8" s3 (.cellOp (.loadLeInt true 8 true false)) 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-pldule4q" s4 (.cellOp (.loadLeInt true 4 true true)) 16
        let s6 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s5 (.cellOp .ldZeroes) 16
        let s7 ← expectDecodeStep "decode/raw-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let asmCode ←
          match assembleCp0 [pldule4Instr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldule4 failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-pldule4" a0 pldule4Instr 16
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
          (runPldule4DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop"
          (runPldule4DispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runPldule4DispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldule4Case "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero)],
    mkPldule4Case "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne)],
    mkPldule4Case "ok/max-u32/exact" #[.slice (mkSliceFromLeBytes bytesMaxU32)],
    mkPldule4Case "ok/high-bit/exact" #[.slice (mkSliceFromLeBytes bytesHighBit)],
    mkPldule4Case "ok/max-signed-pos/exact" #[.slice (mkSliceFromLeBytes bytesMaxSignedPos)],
    mkPldule4Case "ok/random-12345678/exact" #[.slice (mkSliceFromLeBytes bytes12345678)],
    mkPldule4Case "ok/random-f6543210/exact" #[.slice (mkSliceFromLeBytes bytesF6543210)],
    mkPldule4Case "ok/alt-lo/exact" #[.slice (mkSliceFromLeBytes bytesAltLo)],
    mkPldule4Case "ok/alt-hi/exact" #[.slice (mkSliceFromLeBytes bytesAltHi)],
    mkPldule4Case "ok/tail3" #[.slice (mkSliceFromLeBytes bytes12345678 tailBits3)],
    mkPldule4Case "ok/tail7" #[.slice (mkSliceFromLeBytes bytesF6543210 tailBits7)],
    mkPldule4Case "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltHi tailBits11)],
    mkPldule4Case "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltLo tailBits13)],
    mkPldule4Case "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne tailBits5 #[refLeafA])],
    mkPldule4Case "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesHighBit tailBits7 #[refLeafA, refLeafB])],
    mkPldule4Case "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxU32 tailBits3)],
    mkPldule4Case "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesF6543210 tailBits11)],
    mkPldule4Case "ok/deep-stack-cell-below" #[.cell refLeafA, .slice (mkSliceFromLeBytes bytesAltHi tailBits5)],

    mkPldule4Case "cellund/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkPldule4Case "cellund/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkPldule4Case "cellund/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkPldule4Case "cellund/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkPldule4Case "cellund/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkPldule4Case "cellund/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldule4Case "cellund/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],

    mkPldule4Case "underflow/empty" #[],
    mkPldule4Case "type/top-null" #[.null],
    mkPldule4Case "type/top-int" #[intV 0],
    mkPldule4Case "type/top-cell" #[.cell Cell.empty],
    mkPldule4Case "type/top-builder" #[.builder Builder.empty],
    mkPldule4Case "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne), .null],
    mkPldule4Case "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]
  ]
  fuzz := #[
    { seed := 2026021061
      count := 320
      gen := genPldule4FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDULE4
