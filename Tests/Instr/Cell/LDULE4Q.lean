import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDULE4Q

/-!
LDULE4Q branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt true 4 false true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=9 for LDULE4Q)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- quiet insufficient-bits branch (`haveBits 32 = false`) in non-prefetch mode:
  push original slice, then push `0`;
- success branch: little-endian 4-byte unsigned decode, then push
  `[int, remainder-slice, -1]`;
- decode/assembler mapping for opcode `0xd759` with family boundaries;
- handler dispatch fallback for non-`.loadLeInt` instructions.

Oracle harness constraint:
- partial-cursor slices (`bitPos/refPos ≠ 0`) are not token-encodable for oracle;
  partial-slice branches are covered in direct unit tests only.
-/

private def ldule4qId : InstrId := { name := "LDULE4Q" }

private def ldule4qInstr : Instr :=
  .cellOp (.loadLeInt true 4 false true)

private def ldule4qWord : Nat := 0xd759

private def dispatchSentinel : Int := 867

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkLdule4qCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldule4qInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldule4qId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdule4qDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly ldule4qInstr stack

private def runLdule4qDirectInstr (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly instr stack

private def runLdule4qDispatchFallback (instr : Instr) (stack : Array Value) :
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

private def expectedSuccessStack
    (below : Array Value)
    (x : Int)
    (rem : Slice) : Array Value :=
  below ++ #[intV x, .slice rem, intV (-1)]

private def expectedQuietFailStack
    (below : Array Value)
    (original : Slice) : Array Value :=
  below ++ #[.slice original, intV 0]

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

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV (-7)
    else if pick = 2 then .cell refLeafA
    else .builder Builder.empty
  (v, rng1)

private def genLdule4qFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkLdule4qCase s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes4 rng1
    (mkLdule4qCase "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkLdule4qCase s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkLdule4qCase s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkLdule4qCase s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    (mkLdule4qCase "fuzz/ok/boundary-max-u32"
      #[.slice (mkSliceFromLeBytes bytesMaxU32)], rng1)
  else if shape = 6 then
    (mkLdule4qCase "fuzz/ok/boundary-high-bit"
      #[.slice (mkSliceFromLeBytes bytesHighBit)], rng1)
  else if shape = 7 then
    (mkLdule4qCase "fuzz/quiet-fail/empty-slice"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 8 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    (mkLdule4qCase s!"fuzz/quiet-fail/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 9 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkLdule4qCase s!"fuzz/quiet-fail/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 10 then
    (mkLdule4qCase "fuzz/quiet-fail/refs-only-no-bits"
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])], rng1)
  else if shape = 11 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    let (noise, rng4) := pickNoise rng3
    (mkLdule4qCase s!"fuzz/quiet-fail/deep-stack-short-{avail}"
      #[noise, .slice (mkSliceWithBitsRefs bits)], rng4)
  else if shape = 12 then
    (mkLdule4qCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 13 then
    (mkLdule4qCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 14 then
    let (n, rng2) := randNat rng1 0 255
    (mkLdule4qCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 15 then
    (mkLdule4qCase "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 16 then
    (mkLdule4qCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 17 then
    let (bytes, rng2) := randBytes4 rng1
    (mkLdule4qCase "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), .null], rng2)
  else if shape = 18 then
    (mkLdule4qCase "fuzz/type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3], rng1)
  else if shape = 19 then
    let (bits, rng2) := randBitString 31 rng1
    (mkLdule4qCase "fuzz/quiet-fail/near-boundary-31"
      #[.slice (mkSliceWithBitsRefs bits)], rng2)
  else
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 3
    (mkLdule4qCase s!"fuzz/ok/near-boundary-32/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)

def suite : InstrSuite where
  id := ldule4qId
  unit := #[
    { name := "unit/direct/quiet-success-unsigned-le-nonprefetch-stack-contract"
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
            ("tail11", bytesF6543210, tailBits11)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          let rem := input.advanceBits 32
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runLdule4qDirect #[.slice input])
            (expectedSuccessStack #[] (expectedUnsignedFromBytes bytes) rem)

        let refsInput := mkSliceFromLeBytes bytesAltLo tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-remainder-preserved"
          (runLdule4qDirect #[.slice refsInput])
          (expectedSuccessStack #[] (expectedUnsignedFromBytes bytesAltLo) (refsInput.advanceBits 32))

        let deepInput := mkSliceFromLeBytes bytesAltHi tailBits13
        let below : Array Value := #[.null, intV 77]
        expectOkStack "ok/deep-stack-preserved"
          (runLdule4qDirect (below ++ #[.slice deepInput]))
          (expectedSuccessStack below (expectedUnsignedFromBytes bytesAltHi) (deepInput.advanceBits 32))

        expectOkStack "ok/partial-slice-offset"
          (runLdule4qDirect #[.slice partialCursorSlice])
          (expectedSuccessStack #[] (expectedUnsignedFromSlice partialCursorSlice) (partialCursorSlice.advanceBits 32)) }
    ,
    { name := "unit/direct/quiet-insufficient-bits-restores-slice-and-status0"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectOkStack s!"quiet-fail/avail-{avail}"
            (runLdule4qDirect #[.slice s])
            (expectedQuietFailStack #[] s)

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectOkStack "quiet-fail/refs-only-no-bits"
          (runLdule4qDirect #[.slice refsOnly])
          (expectedQuietFailStack #[] refsOnly)

        expectOkStack "quiet-fail/short-partial-cursor-avail30"
          (runLdule4qDirect #[.slice shortCursorSlice])
          (expectedQuietFailStack #[] shortCursorSlice)

        let below : Array Value := #[intV 55, .cell refLeafA]
        let short := mkSliceWithBitsRefs (stripeBits 9 1)
        expectOkStack "quiet-fail/deep-stack-preserved"
          (runLdule4qDirect (below ++ #[.slice short]))
          (expectedQuietFailStack below short)

        expectErr "nonquiet/short-throws-cellund"
          (runLdule4qDirectInstr (.cellOp (.loadLeInt true 4 false false))
            #[.slice (mkSliceWithBitsRefs (stripeBits 31 0))]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runLdule4qDirect #[]) .stkUnd
        expectErr "type/top-null" (runLdule4qDirect #[.null]) .typeChk
        expectErr "type/top-int" (runLdule4qDirect #[intV 9]) .typeChk
        expectErr "type/top-cell" (runLdule4qDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runLdule4qDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdule4qDirect #[.slice (mkSliceFromLeBytes bytesOne), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-quiet-short-slice"
          (runLdule4qDirect #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk

        let short := mkSliceWithBitsRefs (stripeBits 8 1)
        expectOkStack "quiet-fail/order-short-slice-over-invalid-below"
          (runLdule4qDirect #[.null, .slice short])
          (expectedQuietFailStack #[.null] short) }
    ,
    { name := "unit/opcode/decode-family-boundaries-and-assembler"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits 0xd758 16 ++
             natToBits ldule4qWord 16 ++
             natToBits 0xd75a 16 ++
             natToBits 0xd75d 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-neighbor-ldile4q" s1 (.cellOp (.loadLeInt false 4 false true)) 16
        let s3 ← expectDecodeStep "decode/raw-ldule4q" s2 ldule4qInstr 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-ldile8q" s3 (.cellOp (.loadLeInt false 8 false true)) 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-pldule4q" s4 (.cellOp (.loadLeInt true 4 true true)) 16
        let s6 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s5 (.cellOp .ldZeroes) 16
        let s7 ← expectDecodeStep "decode/raw-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let asmCode ←
          match assembleCp0 [ldule4qInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/ldule4q failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-ldule4q" a0 ldule4qInstr 16
        let a2 ← expectDecodeStep "decode/asm-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [ldule4qInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/single-ldule4q failed: {e}")
        if singleCode.bits = natToBits ldule4qWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldule4q: expected 0xd759 encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldule4q: expected 16-bit encoding, got {singleCode.bits.size}")

        match assembleCp0 [.cellOp (.loadLeInt true 5 false true)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes-5: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes-5: expected rangeChk, got success")

        match assembleCp0 [.cellOp (.loadLeInt true 0 false true)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes-0: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-loadleint-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runLdule4qDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-ldzeroes"
          (runLdule4qDispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runLdule4qDispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdule4qCase "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero)],
    mkLdule4qCase "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne)],
    mkLdule4qCase "ok/max-u32/exact" #[.slice (mkSliceFromLeBytes bytesMaxU32)],
    mkLdule4qCase "ok/high-bit/exact" #[.slice (mkSliceFromLeBytes bytesHighBit)],
    mkLdule4qCase "ok/max-signed-pos/exact" #[.slice (mkSliceFromLeBytes bytesMaxSignedPos)],
    mkLdule4qCase "ok/random-12345678/exact" #[.slice (mkSliceFromLeBytes bytes12345678)],
    mkLdule4qCase "ok/random-f6543210/exact" #[.slice (mkSliceFromLeBytes bytesF6543210)],
    mkLdule4qCase "ok/alt-lo/exact" #[.slice (mkSliceFromLeBytes bytesAltLo)],
    mkLdule4qCase "ok/alt-hi/exact" #[.slice (mkSliceFromLeBytes bytesAltHi)],
    mkLdule4qCase "ok/tail3" #[.slice (mkSliceFromLeBytes bytes12345678 tailBits3)],
    mkLdule4qCase "ok/tail5" #[.slice (mkSliceFromLeBytes bytesAltLo tailBits5)],
    mkLdule4qCase "ok/tail7" #[.slice (mkSliceFromLeBytes bytesF6543210 tailBits7)],
    mkLdule4qCase "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltHi tailBits11)],
    mkLdule4qCase "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltLo tailBits13)],
    mkLdule4qCase "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne tailBits5 #[refLeafA])],
    mkLdule4qCase "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesHighBit tailBits7 #[refLeafA, refLeafB])],
    mkLdule4qCase "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxU32 tailBits3)],
    mkLdule4qCase "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesF6543210 tailBits11)],
    mkLdule4qCase "ok/deep-stack-cell-below" #[.cell refLeafA, .slice (mkSliceFromLeBytes bytesAltHi tailBits5)],

    mkLdule4qCase "quiet-fail/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkLdule4qCase "quiet-fail/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkLdule4qCase "quiet-fail/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkLdule4qCase "quiet-fail/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkLdule4qCase "quiet-fail/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkLdule4qCase "quiet-fail/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkLdule4qCase "quiet-fail/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],
    mkLdule4qCase "quiet-fail/deep-stack-below-preserved"
      #[intV 88, .slice (mkSliceWithBitsRefs (stripeBits 11 0))],
    mkLdule4qCase "quiet-fail/refs-short30-two"
      #[.slice (mkSliceWithBitsRefs (stripeBits 30 1) #[refLeafA, refLeafB])],
    mkLdule4qCase "quiet-fail/order-short-slice-over-invalid-below"
      #[.null, .slice (mkSliceWithBitsRefs (stripeBits 8 1))],

    mkLdule4qCase "underflow/empty" #[],
    mkLdule4qCase "type/top-null" #[.null],
    mkLdule4qCase "type/top-int" #[intV 0],
    mkLdule4qCase "type/top-cell" #[.cell Cell.empty],
    mkLdule4qCase "type/top-builder" #[.builder Builder.empty],
    mkLdule4qCase "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne), .null],
    mkLdule4qCase "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]
  ]
  fuzz := #[
    { seed := 2026021120
      count := 320
      gen := genLdule4qFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDULE4Q
