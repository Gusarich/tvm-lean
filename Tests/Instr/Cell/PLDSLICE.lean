import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDSLICE

/-
PLDSLICE branch-mapping notes (fixed-width, prefetch, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadSliceFixed.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_slice_fixed2`, `exec_load_slice_common`, mode=`1`).

Branch map used for this suite (`PLDSLICE` = prefetch=true, quiet=false):
- success (`have(bits)`): push only loaded prefix subslice (no remainder, no status);
- failure (`!have(bits)`): throw `cellUnd` (non-quiet path);
- underflow/type at `popSlice` happen before `have(bits)` split;
- opcode boundaries and decode/dispatch around `{P}LDSLICE{Q}` fixed family
  (`0xd71c>>2` + flags2 + bits8), including boundary with `0xd71b` (`PLDSLICEXQ`).
-/

private def pldsliceId : InstrId := { name := "PLDSLICE" }

private def dispatchSentinel : Int := 934

private def pldsliceInstr (bits : Nat) : Instr :=
  .loadSliceFixed true false bits

private def mkPldsliceCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[pldsliceInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldsliceId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldsliceDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadSliceFixed (pldsliceInstr bits) stack

private def runPldsliceDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadSliceFixed instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkPldsliceInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def expectedLoaded (s : Slice) (bits : Nat) : Slice :=
  mkSliceFromBits (s.readBits bits)

private def ldsliceShortWord (bits : Nat) : Nat :=
  0xd600 + (bits - 1)

private def pldsliceWord (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags2 : Nat := 0x1
  let args10 : Nat := (flags2 <<< 8) + bits8
  let prefix14 : Nat := (0xd71c >>> 2)
  (prefix14 <<< 10) + args10

private def tailBits3 : BitString := natToBits 5 3
private def tailBits5 : BitString := natToBits 21 5
private def tailBits7 : BitString := natToBits 93 7
private def tailBits11 : BitString := natToBits 1337 11
private def tailBits13 : BitString := natToBits 4242 13

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 40 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 7, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 24 1) #[refLeafC]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 20, refPos := 0 }

private def pldsliceGasProbeBits : Nat := 8

private def pldsliceSetGasExact : Int :=
  computeExactGasBudget (pldsliceInstr pldsliceGasProbeBits)

private def pldsliceSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (pldsliceInstr pldsliceGasProbeBits)

private def pldsliceBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickPldsliceBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pldsliceBitsBoundaryPool.size - 1)
  (pldsliceBitsBoundaryPool[idx]!, rng')

private def pickPldsliceBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickPldsliceBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafA, refLeafB]
    else #[refLeafA, refLeafB, refLeafC]
  (refs, rng')

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell Cell.empty
    else .builder Builder.empty
  (v, rng')

private def genPldsliceFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (bits, rng2) := pickPldsliceBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkPldsliceCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkPldsliceInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkPldsliceCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkPldsliceInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkPldsliceCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkPldsliceInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkPldsliceCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkPldsliceInput bits tail phase)], rng5)
  else if shape = 4 then
    let avail := bits - 1
    (mkPldsliceCase s!"fuzz/cellund/by1/bits-{bits}/avail-{avail}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits avail phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let avail := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkPldsliceCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{avail}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits avail phase) refs)], rng5)
  else if shape = 6 then
    (mkPldsliceCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkPldsliceCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkPldsliceCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng3)
  else if shape = 9 then
    (mkPldsliceCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 10 then
    (mkPldsliceCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 11 then
    (mkPldsliceCase s!"fuzz/type/top-cell/bits-{bits}" bits #[.cell Cell.empty], rng3)
  else if shape = 12 then
    (mkPldsliceCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)
  else if shape = 13 then
    (mkPldsliceCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkPldsliceInput bits tailBits3 phase), .null], rng3)
  else if shape = 14 then
    (mkPldsliceCase "fuzz/gas/exact" pldsliceGasProbeBits
      #[.slice (mkPldsliceInput pldsliceGasProbeBits tailBits11 1)]
      #[.pushInt (.num pldsliceSetGasExact), .tonEnvOp .setGasLimit, pldsliceInstr pldsliceGasProbeBits], rng3)
  else
    (mkPldsliceCase "fuzz/gas/exact-minus-one" pldsliceGasProbeBits
      #[.slice (mkPldsliceInput pldsliceGasProbeBits tailBits11 1)]
      #[.pushInt (.num pldsliceSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldsliceInstr pldsliceGasProbeBits], rng3)

def suite : InstrSuite where
  id := pldsliceId
  unit := #[
    { name := "unit/direct/prefetch-success-pushes-loaded-only"
      run := do
        let checks : Array (Nat × BitString × Nat) :=
          #[
            (1, #[], 0),
            (1, tailBits7, 1),
            (8, #[], 1),
            (8, tailBits11, 0),
            (255, #[], 0),
            (255, #[true], 1),
            (256, #[], 1),
            (256, tailBits3, 0)
          ]
        for (bits, tail, phase) in checks do
          let input := mkPldsliceInput bits tail phase
          expectOkStack s!"ok/bits-{bits}/tail-{tail.size}"
            (runPldsliceDirect bits #[.slice input])
            #[.slice (expectedLoaded input bits)]

        let refsInput := mkPldsliceInput 8 tailBits5 1 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-in-source-loaded-has-no-refs"
          (runPldsliceDirect 8 #[.slice refsInput])
          #[.slice (expectedLoaded refsInput 8)]

        let deepInput := mkPldsliceInput 32 tailBits7 0
        expectOkStack "ok/deep-stack-preserved-no-remainder-push"
          (runPldsliceDirect 32 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, .slice (expectedLoaded deepInput 32)]

        expectOkStack "ok/partial-slice-cursor"
          (runPldsliceDirect 12 #[.slice partialCursorSlice])
          #[.slice (expectedLoaded partialCursorSlice 12)] }
    ,
    { name := "unit/direct/cellund-insufficient-bits"
      run := do
        let insuff : Array (Nat × Nat) :=
          #[
            (1, 0),
            (8, 7),
            (64, 63),
            (255, 254),
            (256, 255)
          ]
        for (bits, avail) in insuff do
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectErr s!"cellund/bits-{bits}/avail-{avail}"
            (runPldsliceDirect bits #[.slice s]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runPldsliceDirect 8 #[.slice refsOnly]) .cellUnd

        expectErr "cellund/partial-cursor-bits5-avail4"
          (runPldsliceDirect 5 #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPldsliceDirect 8 #[]) .stkUnd
        expectErr "type/top-null" (runPldsliceDirect 8 #[.null]) .typeChk
        expectErr "type/top-int" (runPldsliceDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell" (runPldsliceDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPldsliceDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldsliceDirect 8 #[.slice (mkPldsliceInput 8 tailBits3 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldsliceDirect 8 #[.slice (mkSliceWithBitsRefs #[]), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-and-boundaries"
      run := do
        let program : Array Instr :=
          #[
            pldsliceInstr 1,
            pldsliceInstr 8,
            pldsliceInstr 255,
            pldsliceInstr 256,
            .loadSliceFixed false false 5,
            .loadSliceFixed false true 5,
            .loadSliceFixed true true 5,
            .loadSliceX true true,
            .add
          ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/pldslice-1" s0 (pldsliceInstr 1) 24
        let s2 ← expectDecodeStep "decode/pldslice-8" s1 (pldsliceInstr 8) 24
        let s3 ← expectDecodeStep "decode/pldslice-255" s2 (pldsliceInstr 255) 24
        let s4 ← expectDecodeStep "decode/pldslice-256" s3 (pldsliceInstr 256) 24
        let s5 ← expectDecodeStep "decode/ldslice-alt-5" s4 (.loadSliceFixed false false 5) 24
        let s6 ← expectDecodeStep "decode/ldsliceq-alt-5" s5 (.loadSliceFixed false true 5) 24
        let s7 ← expectDecodeStep "decode/pldsliceq-alt-5" s6 (.loadSliceFixed true true 5) 24
        let s8 ← expectDecodeStep "decode/pldslicexq-neighbor" s7 (.loadSliceX true true) 16
        let s9 ← expectDecodeStep "decode/tail-add" s8 .add 8
        if s9.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/seq-end: expected exhausted slice, got {s9.bitsRemaining} bits remaining")

        let asm8 ←
          match assembleCp0 [pldsliceInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bits8 failed: {e}")
        if asm8.bits = natToBits (pldsliceWord 8) 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bits8: expected PLDSLICE 24-bit encoding, got {asm8.bits}")
        if asm8.bits.size = 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bits8: expected 24 bits, got {asm8.bits.size}")

        match assembleCp0 [pldsliceInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits0: expected rangeChk, got success")

        match assembleCp0 [pldsliceInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits257: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let rawAltCode : Cell := Cell.mkOrdinary (natToBits (pldsliceWord 42) 24 ++ addCell.bits) #[]
        let r0 := Slice.ofCell rawAltCode
        let r1 ← expectDecodeStep "decode/raw-alt-pldslice-42" r0 (pldsliceInstr 42) 24
        let r2 ← expectDecodeStep "decode/raw-alt-tail-add" r1 .add 8
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-alt-end: expected exhausted slice, got {r2.bitsRemaining} bits remaining")

        let boundaryRawCode : Cell :=
          Cell.mkOrdinary (natToBits 0xd71b 16 ++ natToBits (pldsliceWord 5) 24 ++ addCell.bits) #[]
        let b0 := Slice.ofCell boundaryRawCode
        let b1 ← expectDecodeStep "decode/raw-boundary-0xd71b-pldslicexq" b0 (.loadSliceX true true) 16
        let b2 ← expectDecodeStep "decode/raw-boundary-pldslice-5" b1 (pldsliceInstr 5) 24
        let b3 ← expectDecodeStep "decode/raw-boundary-tail-add" b2 .add 8
        if b3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-boundary-end: expected exhausted slice, got {b3.bitsRemaining} bits remaining")

        let shortAltRawCode : Cell :=
          Cell.mkOrdinary
            (natToBits (ldsliceShortWord 8) 16 ++ natToBits (pldsliceWord 8) 24 ++ addCell.bits) #[]
        let m0 := Slice.ofCell shortAltRawCode
        let m1 ← expectDecodeStep "decode/raw-short-ldslice-8" m0 (.loadSliceFixed false false 8) 16
        let m2 ← expectDecodeStep "decode/raw-alt-pldslice-8" m1 (pldsliceInstr 8) 24
        let m3 ← expectDecodeStep "decode/raw-short-alt-tail-add" m2 .add 8
        if m3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-alt-end: expected exhausted slice, got {m3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-loadslicefixed-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runPldsliceDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-loadslicex"
          (runPldsliceDispatchFallback (.loadSliceX true false) #[intV 11])
          #[intV 11, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldsliceCase "ok/bits-1/exact" 1 #[.slice (mkPldsliceInput 1 #[] 0)],
    mkPldsliceCase "ok/bits-1/tail7" 1 #[.slice (mkPldsliceInput 1 tailBits7 1)],
    mkPldsliceCase "ok/bits-2/tail5" 2 #[.slice (mkPldsliceInput 2 tailBits5 0)],
    mkPldsliceCase "ok/bits-3/tail11" 3 #[.slice (mkPldsliceInput 3 tailBits11 1)],
    mkPldsliceCase "ok/bits-7/tail13" 7 #[.slice (mkPldsliceInput 7 tailBits13 0)],
    mkPldsliceCase "ok/bits-8/exact" 8 #[.slice (mkPldsliceInput 8 #[] 1)],
    mkPldsliceCase "ok/bits-8/tail11" 8 #[.slice (mkPldsliceInput 8 tailBits11 0)],
    mkPldsliceCase "ok/bits-15/exact" 15 #[.slice (mkPldsliceInput 15 #[] 1)],
    mkPldsliceCase "ok/bits-16/tail7" 16 #[.slice (mkPldsliceInput 16 tailBits7 0)],
    mkPldsliceCase "ok/bits-31/exact" 31 #[.slice (mkPldsliceInput 31 #[] 0)],
    mkPldsliceCase "ok/bits-63/tail5" 63 #[.slice (mkPldsliceInput 63 tailBits5 1)],
    mkPldsliceCase "ok/bits-127/exact" 127 #[.slice (mkPldsliceInput 127 #[] 1)],
    mkPldsliceCase "ok/bits-255/exact" 255 #[.slice (mkPldsliceInput 255 #[] 0)],
    mkPldsliceCase "ok/bits-255/tail1" 255 #[.slice (mkPldsliceInput 255 #[true] 1)],
    mkPldsliceCase "ok/bits-256/exact" 256 #[.slice (mkPldsliceInput 256 #[] 0)],
    mkPldsliceCase "ok/bits-256/tail3" 256 #[.slice (mkPldsliceInput 256 tailBits3 1)],
    mkPldsliceCase "ok/bits-8/refs2" 8 #[.slice (mkPldsliceInput 8 tailBits5 0 #[refLeafA, refLeafB])],
    mkPldsliceCase "ok/bits-32/refs3-tail7" 32
      #[.slice (mkPldsliceInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkPldsliceCase "ok/deep-stack-preserve" 8
      #[.null, intV 42, .slice (mkPldsliceInput 8 tailBits7 1)],
    mkPldsliceCase "ok/deep-stack-with-refs" 32
      #[.cell Cell.empty, .slice (mkPldsliceInput 32 tailBits5 0 #[refLeafA])],

    mkPldsliceCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkPldsliceCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkPldsliceCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkPldsliceCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkPldsliceCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkPldsliceCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],

    mkPldsliceCase "underflow/empty" 8 #[],
    mkPldsliceCase "type/top-null" 8 #[.null],
    mkPldsliceCase "type/top-int" 8 #[intV 0],
    mkPldsliceCase "type/top-cell" 8 #[.cell Cell.empty],
    mkPldsliceCase "type/top-builder" 8 #[.builder Builder.empty],
    mkPldsliceCase "type/deep-top-not-slice" 8 #[.slice (mkPldsliceInput 8 tailBits3 0), .null],
    mkPldsliceCase "type/order-top-not-slice-over-short-slice" 8 #[.slice (mkSliceWithBitsRefs #[]), .null],

    mkPldsliceCase "gas/exact-cost-succeeds" pldsliceGasProbeBits
      #[.slice (mkPldsliceInput pldsliceGasProbeBits tailBits11 1)]
      #[.pushInt (.num pldsliceSetGasExact), .tonEnvOp .setGasLimit, pldsliceInstr pldsliceGasProbeBits],
    mkPldsliceCase "gas/exact-minus-one-out-of-gas" pldsliceGasProbeBits
      #[.slice (mkPldsliceInput pldsliceGasProbeBits tailBits11 1)]
      #[.pushInt (.num pldsliceSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldsliceInstr pldsliceGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026021041
      count := 320
      gen := genPldsliceFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDSLICE
