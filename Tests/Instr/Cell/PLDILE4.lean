import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDILE4

/-!
PLDILE4 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt false 4 true false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=4 for PLDILE4)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- insufficient bits (`haveBits 32 = false`) -> `cellUnd` for non-quiet mode;
- success path: little-endian 4-byte decode + signed two's-complement conversion, prefetch contract
  (`PLD*` pushes int only; no remainder slice push);
- opcode family decode around `0xd754` and dispatch fallthrough for non-`.loadLeInt` handlers.
-/

private def pldile4Id : InstrId := { name := "PLDILE4" }

private def pldile4Instr : Instr :=
  .cellOp (.loadLeInt false 4 true false)

private def pldile4Word : Nat := 0xd754

private def dispatchSentinel : Int := 841

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkPldile4Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldile4Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldile4Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldile4Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly pldile4Instr stack

private def runPldile4DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero : Array UInt8 := #[u8 0x00, u8 0x00, u8 0x00, u8 0x00]
private def bytesOne : Array UInt8 := #[u8 0x01, u8 0x00, u8 0x00, u8 0x00]
private def bytesMinusOne : Array UInt8 := #[u8 0xff, u8 0xff, u8 0xff, u8 0xff]
private def bytesMaxPos : Array UInt8 := #[u8 0xff, u8 0xff, u8 0xff, u8 0x7f]
private def bytesMinNeg : Array UInt8 := #[u8 0x00, u8 0x00, u8 0x00, u8 0x80]
private def bytes12345678 : Array UInt8 := #[u8 0x78, u8 0x56, u8 0x34, u8 0x12]
private def bytesF6543210 : Array UInt8 := #[u8 0x10, u8 0x32, u8 0x54, u8 0xf6]
private def bytesAltPos : Array UInt8 := #[u8 0x55, u8 0xaa, u8 0x10, u8 0x01]
private def bytesAltNeg : Array UInt8 := #[u8 0xaa, u8 0x55, u8 0x20, u8 0x90]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero,
    bytesOne,
    bytesMinusOne,
    bytesMaxPos,
    bytesMinNeg,
    bytes12345678,
    bytesF6543210,
    bytesAltPos,
    bytesAltNeg
  ]

private def mkSliceFromLeBytes
    (bytes : Array UInt8)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (bytesToBitsBE bytes ++ tail) refs

private def expectedSignedFromBytes (bytes : Array UInt8) : Int :=
  natToIntSignedTwos (bytesToNatLE bytes) 32

private def expectedSignedFromSlice (s : Slice) : Int :=
  expectedSignedFromBytes (bitStringToBytesBE (s.readBits 32))

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 80 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 5, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 40 1) #[refLeafA]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 10, refPos := 0 }

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

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV (-7)
    else if pick = 2 then .cell refLeafA
    else .builder Builder.empty
  (v, rng1)

private def genPldile4FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkPldile4Case s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes4 rng1
    (mkPldile4Case "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkPldile4Case s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkPldile4Case s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkPldile4Case s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    (mkPldile4Case "fuzz/ok/boundary-max-positive"
      #[.slice (mkSliceFromLeBytes bytesMaxPos)], rng1)
  else if shape = 6 then
    (mkPldile4Case "fuzz/ok/boundary-min-negative"
      #[.slice (mkSliceFromLeBytes bytesMinNeg)], rng1)
  else if shape = 7 then
    (mkPldile4Case "fuzz/cellund/empty-slice"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 8 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    (mkPldile4Case s!"fuzz/cellund/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 9 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkPldile4Case s!"fuzz/cellund/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 10 then
    (mkPldile4Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 11 then
    (mkPldile4Case "fuzz/type/top-null" #[.null], rng1)
  else if shape = 12 then
    let (n, rng2) := randNat rng1 0 255
    (mkPldile4Case s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 13 then
    (mkPldile4Case "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 14 then
    (mkPldile4Case "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else
    let (bytes, rng2) := randBytes4 rng1
    (mkPldile4Case "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), .null], rng2)

def suite : InstrSuite where
  id := pldile4Id
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
            ("12345678", bytes12345678, #[]),
            ("f6543210", bytesF6543210, #[]),
            ("tail3", bytes12345678, tailBits3),
            ("tail11", bytesF6543210, tailBits11)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runPldile4Direct #[.slice input])
            #[intV (expectedSignedFromBytes bytes)]

        let refsInput := mkSliceFromLeBytes bytesAltPos tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-still-int-only"
          (runPldile4Direct #[.slice refsInput])
          #[intV (expectedSignedFromBytes bytesAltPos)]

        let deepInput := mkSliceFromLeBytes bytesAltNeg tailBits13
        expectOkStack "ok/deep-stack-preserved"
          (runPldile4Direct #[.null, intV 77, .slice deepInput])
          #[.null, intV 77, intV (expectedSignedFromBytes bytesAltNeg)]

        expectOkStack "ok/partial-slice-offset"
          (runPldile4Direct #[.slice partialCursorSlice])
          #[intV (expectedSignedFromSlice partialCursorSlice)] }
    ,
    { name := "unit/direct/insufficient-bits-cellund"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectErr s!"cellund/avail-{avail}"
            (runPldile4Direct #[.slice s]) .cellUnd

        expectErr "cellund/refs-only-no-bits"
          (runPldile4Direct #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])]) .cellUnd

        expectErr "cellund/short-partial-cursor-avail30"
          (runPldile4Direct #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldile4Direct #[]) .stkUnd
        expectErr "type/top-null" (runPldile4Direct #[.null]) .typeChk
        expectErr "type/top-int" (runPldile4Direct #[intV 9]) .typeChk
        expectErr "type/top-cell" (runPldile4Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldile4Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldile4Direct #[.slice (mkSliceFromLeBytes bytesOne), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldile4Direct #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-and-assembler-path"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits pldile4Word 16 ++
             natToBits 0xd757 16 ++
             natToBits 0xd75c 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-pldile4" s1 pldile4Instr 16
        let s3 ← expectDecodeStep "decode/raw-neighbor-pldule8" s2 (.cellOp (.loadLeInt true 8 true false)) 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-pldile4q" s3 (.cellOp (.loadLeInt false 4 true true)) 16
        let s5 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s4 (.cellOp .ldZeroes) 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let asmCode ←
          match assembleCp0 [pldile4Instr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldile4 failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-pldile4" a0 pldile4Instr 16
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
          (runPldile4DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop"
          (runPldile4DispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runPldile4DispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldile4Case "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero)],
    mkPldile4Case "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne)],
    mkPldile4Case "ok/minus-one/exact" #[.slice (mkSliceFromLeBytes bytesMinusOne)],
    mkPldile4Case "ok/max-positive/exact" #[.slice (mkSliceFromLeBytes bytesMaxPos)],
    mkPldile4Case "ok/min-negative/exact" #[.slice (mkSliceFromLeBytes bytesMinNeg)],
    mkPldile4Case "ok/random-12345678/exact" #[.slice (mkSliceFromLeBytes bytes12345678)],
    mkPldile4Case "ok/random-f6543210/exact" #[.slice (mkSliceFromLeBytes bytesF6543210)],
    mkPldile4Case "ok/alt-positive/exact" #[.slice (mkSliceFromLeBytes bytesAltPos)],
    mkPldile4Case "ok/alt-negative/exact" #[.slice (mkSliceFromLeBytes bytesAltNeg)],
    mkPldile4Case "ok/tail3" #[.slice (mkSliceFromLeBytes bytes12345678 tailBits3)],
    mkPldile4Case "ok/tail7" #[.slice (mkSliceFromLeBytes bytesF6543210 tailBits7)],
    mkPldile4Case "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltNeg tailBits11)],
    mkPldile4Case "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltPos tailBits13)],
    mkPldile4Case "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne tailBits5 #[refLeafA])],
    mkPldile4Case "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesMinNeg tailBits7 #[refLeafA, refLeafB])],
    mkPldile4Case "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxPos tailBits3)],
    mkPldile4Case "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesF6543210 tailBits11)],

    mkPldile4Case "cellund/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkPldile4Case "cellund/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkPldile4Case "cellund/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkPldile4Case "cellund/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkPldile4Case "cellund/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkPldile4Case "cellund/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldile4Case "cellund/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],

    mkPldile4Case "underflow/empty" #[],
    mkPldile4Case "type/top-null" #[.null],
    mkPldile4Case "type/top-int" #[intV 0],
    mkPldile4Case "type/top-cell" #[.cell Cell.empty],
    mkPldile4Case "type/top-builder" #[.builder Builder.empty],
    mkPldile4Case "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne), .null],
    mkPldile4Case "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]
  ]
  fuzz := #[
    { seed := 2026021058
      count := 500
      gen := genPldile4FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDILE4
