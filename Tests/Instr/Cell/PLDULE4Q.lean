import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDULE4Q

/-
PLDULE4Q branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/LoadLeInt.lean` (`.loadLeInt true 4 true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CellInstr.loadLeInt` encode path, `bytes ∈ {4,8}`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd750..0xd75f` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_load_le_int`, args=`13` for PLDULE4Q)

Branch map covered by this suite:
- stack underflow/type from initial `popSlice`;
- insufficient bits (`haveBits 32 = false`) in quiet+prefetch mode returns status `0`
  and does not re-push a remainder slice;
- success path: little-endian 4-byte unsigned decode + prefetch contract
  (`PLD*` pushes int only, then quiet status `-1`);
- opcode family boundary/decode around `0xd75d`, assembler range checks for invalid byte-widths,
  and dispatch fallback for non-`.loadLeInt` handlers.
-/

private def pldule4qId : InstrId := { name := "PLDULE4Q" }

private def pldule4qInstr : Instr :=
  .cellOp (.loadLeInt true 4 true true)

private def pldule4qWord : Nat := 0xd75d

private def dispatchSentinel : Int := 863

private def execInstrCellOpLoadLeIntOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpLoadLeInt op next
  | _ => next

private def mkPldule4qCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldule4qInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldule4qId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldule4qDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly pldule4qInstr stack

private def runPldule4qDirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpLoadLeIntOnly instr stack

private def runPldule4qDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpLoadLeIntOnly instr (VM.push (intV dispatchSentinel)) stack

private def pldule4qSetGasExact : Int :=
  computeExactGasBudget pldule4qInstr

private def pldule4qSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pldule4qInstr

private def u8 (n : Nat) : UInt8 := UInt8.ofNat n

private def bytesZero : Array UInt8 := #[u8 0x00, u8 0x00, u8 0x00, u8 0x00]
private def bytesOne : Array UInt8 := #[u8 0x01, u8 0x00, u8 0x00, u8 0x00]
private def bytesMax : Array UInt8 := #[u8 0xff, u8 0xff, u8 0xff, u8 0xff]
private def bytesSignBit : Array UInt8 := #[u8 0x00, u8 0x00, u8 0x00, u8 0x80]
private def bytes12345678 : Array UInt8 := #[u8 0x78, u8 0x56, u8 0x34, u8 0x12]
private def bytesF6543210 : Array UInt8 := #[u8 0x10, u8 0x32, u8 0x54, u8 0xf6]
private def bytesAltA : Array UInt8 := #[u8 0x0f, u8 0xf0, u8 0x55, u8 0xaa]
private def bytesAltB : Array UInt8 := #[u8 0xc3, u8 0x3c, u8 0x5a, u8 0xa5]

private def boundaryBytesPool : Array (Array UInt8) :=
  #[
    bytesZero,
    bytesOne,
    bytesMax,
    bytesSignBit,
    bytes12345678,
    bytesF6543210,
    bytesAltA,
    bytesAltB
  ]

private def tailBits19 : BitString := natToBits 299593 19

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def mkSliceFromLeBytes
    (bytes : Array UInt8)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (bytesToBitsBE bytes ++ tail) refs

private def expectedUnsignedFromBytes (bytes : Array UInt8) : Int :=
  Int.ofNat (bytesToNatLE bytes)

private def expectedUnsignedFromSlice (s : Slice) : Int :=
  expectedUnsignedFromBytes (bitStringToBytesBE (s.readBits 32))

private def expectedSuccessStack (below : Array Value) (n : Int) : Array Value :=
  below ++ #[intV n, intV (-1)]

private def expectedQuietFailStack (below : Array Value) : Array Value :=
  below ++ #[intV 0]

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
    else if pick = 1 then intV 91
    else if pick = 2 then .cell refLeafA
    else .builder Builder.empty
  (v, rng1)

private def genPldule4qFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (idx, bytes, rng2) := pickBoundaryBytes rng1
    (mkPldule4qCase s!"fuzz/ok/exact-boundary-{idx}"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 1 then
    let (bytes, rng2) := randBytes4 rng1
    (mkPldule4qCase "fuzz/ok/exact-random"
      #[.slice (mkSliceFromLeBytes bytes)], rng2)
  else if shape = 2 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 24
    (mkPldule4qCase s!"fuzz/ok/with-tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 3 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 16
    let (refs, rng4) := pickRefPack rng3
    (mkPldule4qCase s!"fuzz/ok/refs-{refs.size}/tail-{tail.size}"
      #[.slice (mkSliceFromLeBytes bytes tail refs)], rng4)
  else if shape = 4 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 12
    let (noise, rng4) := pickNoise rng3
    (mkPldule4qCase s!"fuzz/ok/deep-stack/tail-{tail.size}"
      #[noise, .slice (mkSliceFromLeBytes bytes tail)], rng4)
  else if shape = 5 then
    let (bytes, rng2) := randBytes4 rng1
    let (tail, rng3) := pickTailBits rng2 9
    (mkPldule4qCase s!"fuzz/ok/deep-tail-{tail.size}"
      #[.null, .slice (mkSliceFromLeBytes bytes tail)], rng3)
  else if shape = 6 then
    (mkPldule4qCase "fuzz/fail/empty-slice" #[.slice (mkSliceWithBitsRefs #[])], rng1)
  else if shape = 7 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    (mkPldule4qCase s!"fuzz/fail/short-{avail}"
      #[.slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 8 then
    let (avail, rng2) := randNat rng1 0 31
    let (bits, rng3) := randBitString avail rng2
    let (refs, rng4) := pickRefPack rng3
    (mkPldule4qCase s!"fuzz/fail/short-refs-{avail}/r-{refs.size}"
      #[.slice (mkSliceWithBitsRefs bits refs)], rng4)
  else if shape = 9 then
    (mkPldule4qCase "fuzz/fail/short-fixed30" #[.slice (mkSliceWithBitsRefs (stripeBits 30 1))], rng1)
  else if shape = 10 then
    (mkPldule4qCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 11 then
    (mkPldule4qCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 12 then
    let (n, rng2) := randNat rng1 0 65535
    (mkPldule4qCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n)], rng2)
  else if shape = 13 then
    (mkPldule4qCase "fuzz/type/top-cell" #[.cell refLeafA], rng1)
  else if shape = 14 then
    (mkPldule4qCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 15 then
    (mkPldule4qCase "fuzz/error-order/top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), .null], rng1)
  else if shape = 16 then
    (mkPldule4qCase "fuzz/gas/exact"
      #[.slice (mkSliceFromLeBytes bytes12345678 tailBits11)]
      #[.pushInt (.num pldule4qSetGasExact), .tonEnvOp .setGasLimit, pldule4qInstr], rng1)
  else
    (mkPldule4qCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSliceFromLeBytes bytes12345678 tailBits11)]
      #[.pushInt (.num pldule4qSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldule4qInstr], rng1)

def suite : InstrSuite where
  id := pldule4qId
  unit := #[
    { name := "unit/direct/success-quiet-prefetch-unsigned-stack-shape"
      run := do
        let checks : Array (String × Array UInt8 × BitString) :=
          #[
            ("zero", bytesZero, #[]),
            ("one", bytesOne, #[]),
            ("max-u32", bytesMax, #[]),
            ("sign-bit-set", bytesSignBit, #[]),
            ("12345678", bytes12345678, #[]),
            ("f6543210", bytesF6543210, #[]),
            ("tail3", bytes12345678, tailBits3),
            ("tail11", bytesF6543210, tailBits11),
            ("tail19", bytesAltA, tailBits19)
          ]
        for (label, bytes, tail) in checks do
          let input := mkSliceFromLeBytes bytes tail
          expectOkStack s!"ok/{label}/tail-{tail.size}"
            (runPldule4qDirect #[.slice input])
            (expectedSuccessStack #[] (expectedUnsignedFromBytes bytes))

        let refsInput := mkSliceFromLeBytes bytesAltB tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-present-still-int-then-minus1"
          (runPldule4qDirect #[.slice refsInput])
          (expectedSuccessStack #[] (expectedUnsignedFromBytes bytesAltB))

        let deepInput := mkSliceFromLeBytes bytesAltA tailBits13
        let below : Array Value := #[.null, intV 77]
        expectOkStack "ok/deep-stack-preserved"
          (runPldule4qDirect (below ++ #[.slice deepInput]))
          (expectedSuccessStack below (expectedUnsignedFromBytes bytesAltA))

        expectOkStack "ok/partial-slice-offset"
          (runPldule4qDirect #[.slice partialCursorSlice])
          (expectedSuccessStack #[] (expectedUnsignedFromSlice partialCursorSlice)) }
    ,
    { name := "unit/direct/quiet-insufficient-bits-returns-status0-only"
      run := do
        let insuff : Array Nat := #[0, 1, 7, 16, 31]
        for avail in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectOkStack s!"fail/avail-{avail}"
            (runPldule4qDirect #[.slice s])
            (expectedQuietFailStack #[])

        expectOkStack "fail/refs-only-no-bits"
          (runPldule4qDirect #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])])
          (expectedQuietFailStack #[])

        let deepBelow : Array Value := #[intV 55, .cell refLeafA]
        let short := mkSliceWithBitsRefs (stripeBits 5 1)
        expectOkStack "fail/deep-stack-preserve-below"
          (runPldule4qDirect (deepBelow ++ #[.slice short]))
          (expectedQuietFailStack deepBelow)

        expectOkStack "fail/partial-cursor-short"
          (runPldule4qDirect #[.slice shortCursorSlice])
          (expectedQuietFailStack #[])

        expectErr "nonquiet/short-throws-cellund"
          (runPldule4qDirectInstr (.cellOp (.loadLeInt true 4 true false)) #[.slice short]) .cellUnd }
    ,
    { name := "unit/direct/popSlice-underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldule4qDirect #[]) .stkUnd
        expectErr "type/top-null" (runPldule4qDirect #[.null]) .typeChk
        expectErr "type/top-int" (runPldule4qDirect #[intV 9]) .typeChk
        expectErr "type/top-cell" (runPldule4qDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldule4qDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldule4qDirect #[.slice (mkSliceFromLeBytes bytesOne), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldule4qDirect #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-boundaries-and-assembler-path"
      run := do
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd74f 16 ++
             natToBits 0xd75c 16 ++
             natToBits pldule4qWord 16 ++
             natToBits 0xd75e 16 ++
             natToBits 0xd75f 16 ++
             natToBits 0xd760 16 ++
             natToBits 0xa0 8) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-left-boundary-pldrefidx3" s0 (.pldRefIdx 3) 16
        let s2 ← expectDecodeStep "decode/raw-neighbor-pldile4q" s1 (.cellOp (.loadLeInt false 4 true true)) 16
        let s3 ← expectDecodeStep "decode/raw-pldule4q" s2 pldule4qInstr 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-pldile8q" s3 (.cellOp (.loadLeInt false 8 true true)) 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-pldule8q" s4 (.cellOp (.loadLeInt true 8 true true)) 16
        let s6 ← expectDecodeStep "decode/raw-right-boundary-ldzeroes" s5 (.cellOp .ldZeroes) 16
        let s7 ← expectDecodeStep "decode/raw-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let asmCode ←
          match assembleCp0 [pldule4qInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/pldule4q failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-pldule4q" a0 pldule4qInstr 16
        let a2 ← expectDecodeStep "decode/asm-tail-add" a1 .add 8
        if a2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a2.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [pldule4qInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/single failed: {e}")
        if singleCode.bits = natToBits pldule4qWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldule4q: expected 0xd75d encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/pldule4q: expected 16-bit encoding, got {singleCode.bits.size}")

        match assembleCp0 [.cellOp (.loadLeInt true 5 true true)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/invalid-bytes: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/invalid-bytes: expected rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-loadleint-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runPldule4qDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-ldzeroes"
          (runPldule4qDispatchFallback (.cellOp .ldZeroes) #[.slice (mkSliceFromLeBytes bytesOne tailBits3)])
          #[.slice (mkSliceFromLeBytes bytesOne tailBits3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-pldrefvar"
          (runPldule4qDispatchFallback (.cellOp .pldRefVar) #[intV (-11)])
          #[intV (-11), intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldule4qCase "ok/zero/exact" #[.slice (mkSliceFromLeBytes bytesZero)],
    mkPldule4qCase "ok/one/exact" #[.slice (mkSliceFromLeBytes bytesOne)],
    mkPldule4qCase "ok/max-u32/exact" #[.slice (mkSliceFromLeBytes bytesMax)],
    mkPldule4qCase "ok/sign-bit-set/exact" #[.slice (mkSliceFromLeBytes bytesSignBit)],
    mkPldule4qCase "ok/random-12345678/exact" #[.slice (mkSliceFromLeBytes bytes12345678)],
    mkPldule4qCase "ok/random-f6543210/exact" #[.slice (mkSliceFromLeBytes bytesF6543210)],
    mkPldule4qCase "ok/alt-a/exact" #[.slice (mkSliceFromLeBytes bytesAltA)],
    mkPldule4qCase "ok/alt-b/exact" #[.slice (mkSliceFromLeBytes bytesAltB)],
    mkPldule4qCase "ok/tail3" #[.slice (mkSliceFromLeBytes bytes12345678 tailBits3)],
    mkPldule4qCase "ok/tail7" #[.slice (mkSliceFromLeBytes bytesF6543210 tailBits7)],
    mkPldule4qCase "ok/tail11" #[.slice (mkSliceFromLeBytes bytesAltA tailBits11)],
    mkPldule4qCase "ok/tail13" #[.slice (mkSliceFromLeBytes bytesAltB tailBits13)],
    mkPldule4qCase "ok/tail19" #[.slice (mkSliceFromLeBytes bytesAltA tailBits19)],
    mkPldule4qCase "ok/refs1" #[.slice (mkSliceFromLeBytes bytesOne tailBits5 #[refLeafA])],
    mkPldule4qCase "ok/refs2-tail7" #[.slice (mkSliceFromLeBytes bytesSignBit tailBits7 #[refLeafA, refLeafB])],
    mkPldule4qCase "ok/deep-stack-null-below" #[.null, .slice (mkSliceFromLeBytes bytesMax tailBits3)],
    mkPldule4qCase "ok/deep-stack-two-below" #[intV (-5), .null, .slice (mkSliceFromLeBytes bytesF6543210 tailBits11)],

    mkPldule4qCase "fail/avail0" #[.slice (mkSliceWithBitsRefs #[])],
    mkPldule4qCase "fail/avail1" #[.slice (mkSliceWithBitsRefs (stripeBits 1 0))],
    mkPldule4qCase "fail/avail7" #[.slice (mkSliceWithBitsRefs (stripeBits 7 1))],
    mkPldule4qCase "fail/avail16" #[.slice (mkSliceWithBitsRefs (stripeBits 16 0))],
    mkPldule4qCase "fail/avail31" #[.slice (mkSliceWithBitsRefs (stripeBits 31 1))],
    mkPldule4qCase "fail/refs-only" #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldule4qCase "fail/refs-short20" #[.slice (mkSliceWithBitsRefs (stripeBits 20 0) #[refLeafA])],
    mkPldule4qCase "fail/deep-stack-below-preserved" #[intV 77, .slice (mkSliceWithBitsRefs (stripeBits 5 1))],

    mkPldule4qCase "underflow/empty" #[],
    mkPldule4qCase "type/top-null" #[.null],
    mkPldule4qCase "type/top-int" #[intV 0],
    mkPldule4qCase "type/top-cell" #[.cell Cell.empty],
    mkPldule4qCase "type/top-builder" #[.builder Builder.empty],
    mkPldule4qCase "type/deep-top-not-slice" #[.slice (mkSliceFromLeBytes bytesOne), .null],
    mkPldule4qCase "type/order-top-not-slice-over-short-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0)), intV 3],

    mkPldule4qCase "gas/exact-cost-succeeds"
      #[.slice (mkSliceFromLeBytes bytes12345678 tailBits11)]
      #[.pushInt (.num pldule4qSetGasExact), .tonEnvOp .setGasLimit, pldule4qInstr],
    mkPldule4qCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSliceFromLeBytes bytes12345678 tailBits11)]
      #[.pushInt (.num pldule4qSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldule4qInstr]
  ]
  fuzz := #[
    { seed := 2026021064
      count := 320
      gen := genPldule4qFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDULE4Q
