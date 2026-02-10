import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDULE8Q

/-!
PLDULE8Q branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt true 8 true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=15 for PLDULE8Q)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- quiet insufficient-bits path (`haveBits 64 = false`) in prefetch mode returns `[0]`
  without pushing a remainder slice;
- success path: little-endian 8-byte unsigned decode + prefetch/quiet stack contract (`[int, -1]`);
- error ordering: top-of-stack type-check fires before any slice-content checks; quiet short-slice
  handling preserves below-stack values without inspecting their types;
- opcode family decode around `0xd75f`, family boundaries, and assembler range checks;
- dispatch fallback for non-`.loadLeInt` handlers.

Oracle harness constraint:
- partial-cursor slices (`bitPos/refPos ≠ 0`) are not token-encodable for oracle/fuzz;
  those branches are covered in direct unit tests.
-/

private def pldule8qId : InstrId := { name := "PLDULE8Q" }

private def pldule8qInstr : Instr :=
  .cellOp (.loadLeInt true 8 true true)

private def pldule8qWord : Nat := 0xd75f

private def dispatchSentinel : Int := 871

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkPldule8qCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldule8qInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldule8qId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldule8qDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly pldule8qInstr stack

private def runPldule8qDirectInstr (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly instr stack

private def runPldule8qDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero8 : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesOne8 : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00]

private def bytesMaxU64 : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff]

private def bytesHighBit8 : Array UInt8 :=
  #[u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytesMaxSignedPos8 : Array UInt8 :=
  #[u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0x7f]

private def bytesNearMaxMinusOne8 : Array UInt8 :=
  #[u8 0xfe, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff, u8 0xff]

private def bytesHighBitPlusOne8 : Array UInt8 :=
  #[u8 0x01, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x00, u8 0x80]

private def bytes0123456789abcdef : Array UInt8 :=
  #[u8 0xef, u8 0xcd, u8 0xab, u8 0x89, u8 0x67, u8 0x45, u8 0x23, u8 0x01]

private def bytesFedcba9876543210 : Array UInt8 :=
  #[u8 0x10, u8 0x32, u8 0x54, u8 0x76, u8 0x98, u8 0xba, u8 0xdc, u8 0xfe]

private def bytesAltLo8 : Array UInt8 :=
  #[u8 0x55, u8 0xaa, u8 0x10, u8 0x01, u8 0x22, u8 0x33, u8 0x44, u8 0x12]

private def bytesAltHi8 : Array UInt8 :=
  #[u8 0xaa, u8 0x55, u8 0x20, u8 0x90, u8 0x44, u8 0x33, u8 0x22, u8 0x91]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero8,
    bytesOne8,
    bytesMaxU64,
    bytesHighBit8,
    bytesMaxSignedPos8,
    bytesNearMaxMinusOne8,
    bytesHighBitPlusOne8,
    bytes0123456789abcdef,
    bytesFedcba9876543210,
    bytesAltLo8,
    bytesAltHi8
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
  expectedUnsignedFromBytes (bitStringToBytesBE (s.readBits 64))

private def expectedSuccessStack (below : Array Value) (x : Int) : Array Value :=
  below ++ #[intV x, intV (-1)]

private def expectedQuietFailStack (below : Array Value) : Array Value :=
  below ++ #[intV 0]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 152 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 17, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 96 1) #[refLeafA]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 37, refPos := 0 }

private def pldule8qSetGasExact : Int :=
  computeExactGasBudget pldule8qInstr

private def pldule8qSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pldule8qInstr

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

private def genPldule8qFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkPldule8qCase s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes8 rng1
    (mkPldule8qCase "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkPldule8qCase s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkPldule8qCase s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes8 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkPldule8qCase s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    (mkPldule8qCase "fuzz/ok/boundary-max-u64"
      #[.slice (mkSliceFromLeBytes bytesMaxU64)], rng1)
  else if shape = 6 then
    (mkPldule8qCase "fuzz/ok/boundary-high-bit"
      #[.slice (mkSliceFromLeBytes bytesHighBit8)], rng1)
  else if shape = 7 then
    (mkPldule8qCase "fuzz/quiet/avail0"
      #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 8 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    (mkPldule8qCase s!"fuzz/quiet/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 9 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkPldule8qCase s!"fuzz/quiet/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 10 then
    let (avail, rng2) := randNat rng1 0 63
    let (bits, rng3) := randBitString avail rng2
    let (noise, rng4) := pickNoise rng3
    (mkPldule8qCase s!"fuzz/quiet/deep-stack-short-{avail}"
      #[noise, .slice (mkSliceWithBitsRefs bits)], rng4)
  else if shape = 11 then
    (mkPldule8qCase "fuzz/quiet/refs-only-no-bits"
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])], rng1)
  else if shape = 12 then
    (mkPldule8qCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 13 then
    (mkPldule8qCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 14 then
    let (n, rng2) := randNat rng1 0 255
    (mkPldule8qCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 15 then
    (mkPldule8qCase "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 16 then
    (mkPldule8qCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 17 then
    let (bytes, rng2) := randBytes8 rng1
    (mkPldule8qCase "fuzz/type/deep-top-not-slice"
      #[.slice (mkSliceFromLeBytes bytes), .null], rng2)
  else if shape = 18 then
    (mkPldule8qCase "fuzz/type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3], rng1)
  else if shape = 19 then
    (mkPldule8qCase "fuzz/gas/exact"
      #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldule8qSetGasExact), .tonEnvOp .setGasLimit, pldule8qInstr], rng1)
  else
    (mkPldule8qCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldule8qSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldule8qInstr], rng1)

def suite : InstrSuite where
  id := pldule8qId
  unit := #[
    { name := "unit/direct/quiet-success-unsigned-little-endian-prefetch-stack-contract"
      run := do
        let checks : Array (String × Array UInt8 × BitString) :=
          #[
            ("zero", bytesZero8, #[]),
            ("one", bytesOne8, #[]),
            ("max-u64", bytesMaxU64, #[]),
            ("high-bit", bytesHighBit8, #[]),
            ("max-signed-pos", bytesMaxSignedPos8, #[]),
            ("near-max-minus1", bytesNearMaxMinusOne8, #[]),
            ("high-bit-plus1", bytesHighBitPlusOne8, #[]),
            ("0123456789abcdef", bytes0123456789abcdef, #[]),
            ("fedcba9876543210", bytesFedcba9876543210, #[]),
            ("tail3", bytes0123456789abcdef, tailBits3),
            ("tail11", bytesFedcba9876543210, tailBits11)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runPldule8qDirect #[.slice input])
            (expectedSuccessStack #[] (expectedUnsignedFromBytes bytes))

        let refsInput := mkSliceFromLeBytes bytesAltLo8 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-still-prefetch-int-and-status"
          (runPldule8qDirect #[.slice refsInput])
          (expectedSuccessStack #[] (expectedUnsignedFromBytes bytesAltLo8))

        let deepInput := mkSliceFromLeBytes bytesAltHi8 tailBits13
        let below : Array Value := #[.null, intV 77]
        expectOkStack "ok/deep-stack-preserved"
          (runPldule8qDirect (below ++ #[.slice deepInput]))
          (expectedSuccessStack below (expectedUnsignedFromBytes bytesAltHi8))

        expectOkStack "ok/partial-slice-offset"
          (runPldule8qDirect #[.slice partialCursorSlice])
          (expectedSuccessStack #[] (expectedUnsignedFromSlice partialCursorSlice)) }
    ,
    { name := "unit/direct/quiet-insufficient-bits-returns-status0-without-slice"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31, 48, 63]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectOkStack s!"quiet/avail-{avail}"
            (runPldule8qDirect #[.slice s])
            (expectedQuietFailStack #[])

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectOkStack "quiet/refs-only-no-bits"
          (runPldule8qDirect #[.slice refsOnly])
          (expectedQuietFailStack #[])

        let below : Array Value := #[intV (-3), .cell refLeafA]
        let short := mkSliceWithBitsRefs (stripeBits 42 1)
        expectOkStack "quiet/deep-stack-preserved"
          (runPldule8qDirect (below ++ #[.slice short]))
          (expectedQuietFailStack below)

        let shortOrder := mkSliceWithBitsRefs (stripeBits 8 1)
        expectOkStack "quiet/order-short-slice-before-invalid-below"
          (runPldule8qDirect #[.null, .slice shortOrder])
          (expectedQuietFailStack #[.null])

        expectOkStack "quiet/partial-cursor-short"
          (runPldule8qDirect #[.slice shortCursorSlice])
          (expectedQuietFailStack #[])

        expectErr "nonquiet/short-throws-cellund"
          (runPldule8qDirectInstr (.cellOp (.loadLeInt true 8 true false))
            #[.slice (mkSliceWithBitsRefs (stripeBits 63 0))]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldule8qDirect #[]) .stkUnd
        expectErr "type/top-null" (runPldule8qDirect #[.null]) .typeChk
        expectErr "type/top-int" (runPldule8qDirect #[intV 9]) .typeChk
        expectErr "type/top-cell" (runPldule8qDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldule8qDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldule8qDirect #[.slice (mkSliceFromLeBytes bytesOne8), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldule8qDirect #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-and-assembler-boundaries"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits 0xd750 16 ++
             natToBits 0xd75b 16 ++
             natToBits 0xd75d 16 ++
             natToBits 0xd75e 16 ++
             natToBits pldule8qWord 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-family-start-ldile4" s1 (.cellOp (.loadLeInt false 4 false false)) 16
        let s3 ← expectDecodeStep "decode/raw-neighbor-ldule8q" s2 (.cellOp (.loadLeInt true 8 false true)) 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-pldule4q" s3 (.cellOp (.loadLeInt true 4 true true)) 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-pldile8q" s4 (.cellOp (.loadLeInt false 8 true true)) 16
        let s6 ← expectDecodeStep "decode/raw-pldule8q" s5 pldule8qInstr 16
        let s7 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s6 (.cellOp .ldZeroes) 16
        let s8 ← expectDecodeStep "decode/raw-tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [pldule8qInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldule8q-single failed: {e}")
        if singleCode.bits = natToBits pldule8qWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldule8q: expected 0xd75f encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldule8q: expected 16-bit encoding, got {singleCode.bits.size}")

        let asmCode ←
          match assembleCp0 [pldule8qInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldule8q failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-pldule8q" a0 pldule8qInstr 16
        let a2 ← expectDecodeStep "decode/asm-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellOp (.loadLeInt true 5 true true)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes-5: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes-5: expected rangeChk, got success")

        match assembleCp0 [.cellOp (.loadLeInt true 0 true true)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes-0: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-loadleint-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runPldule8qDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-ldzeroes"
          (runPldule8qDispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne8 tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne8 tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runPldule8qDispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldule8qCase "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero8)],
    mkPldule8qCase "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne8)],
    mkPldule8qCase "ok/max-u64/exact" #[.slice (mkSliceFromLeBytes bytesMaxU64)],
    mkPldule8qCase "ok/high-bit/exact" #[.slice (mkSliceFromLeBytes bytesHighBit8)],
    mkPldule8qCase "ok/near-max-minus1/exact" #[.slice (mkSliceFromLeBytes bytesNearMaxMinusOne8)],
    mkPldule8qCase "ok/high-bit-plus1/exact" #[.slice (mkSliceFromLeBytes bytesHighBitPlusOne8)],
    mkPldule8qCase "ok/random-0123456789abcdef/exact" #[.slice (mkSliceFromLeBytes bytes0123456789abcdef)],
    mkPldule8qCase "ok/random-fedcba9876543210/exact" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210)],
    mkPldule8qCase "ok/alt-lo/exact" #[.slice (mkSliceFromLeBytes bytesAltLo8)],
    mkPldule8qCase "ok/tail3" #[.slice (mkSliceFromLeBytes bytes0123456789abcdef tailBits3)],
    mkPldule8qCase "ok/tail11" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)],
    mkPldule8qCase "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne8 tailBits5 #[refLeafA])],
    mkPldule8qCase "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesHighBit8 tailBits7 #[refLeafA, refLeafB])],
    mkPldule8qCase "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMaxU64 tailBits3)],
    mkPldule8qCase "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)],

    mkPldule8qCase "quiet/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkPldule8qCase "quiet/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkPldule8qCase "quiet/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkPldule8qCase "quiet/avail63" #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkPldule8qCase "quiet/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldule8qCase "quiet/deep-stack-below-preserved" #[intV 77, .null, .slice (mkSliceWithBitsRefs (stripeBits 42 1))],

    mkPldule8qCase "underflow/empty" #[],
    mkPldule8qCase "type/top-null" #[.null],
    mkPldule8qCase "type/top-int" #[intV 0],
    mkPldule8qCase "type/top-cell" #[.cell Cell.empty],
    mkPldule8qCase "type/top-builder" #[.builder Builder.empty],
    mkPldule8qCase "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne8), .null],
    mkPldule8qCase "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3],

    mkPldule8qCase "gas/exact-cost-succeeds" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldule8qSetGasExact), .tonEnvOp .setGasLimit, pldule8qInstr],
    mkPldule8qCase "gas/exact-minus-one-out-of-gas" #[.slice (mkSliceFromLeBytes bytesFedcba9876543210 tailBits11)]
      #[.pushInt (.num pldule8qSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldule8qInstr]
  ]
  fuzz := #[
    { seed := 2026021176
      count := 320
      gen := genPldule8qFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDULE8Q
