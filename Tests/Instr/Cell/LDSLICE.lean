import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSLICE

/-
LDSLICE branch-mapping notes (fixed-width, non-prefetch, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadSliceFixed.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_slice_fixed`, `exec_load_slice_fixed2`, `exec_load_slice_common`).

Branch map used for this suite:
- Lean `.loadSliceFixed false false bits`: 5 branch sites / 6 terminal outcomes
  (instr guard; `popSlice` underflow/type/success; `haveBits` success/fail;
   success push order and stack preservation).
- C++ short/alt fixed-width entrypoints map to `exec_load_slice_common(..., mode=0)`:
  aligned outcomes (`pop_cellslice`; `have(bits)` split; success push order
  `subslice` then remainder; insufficient bits => `cell_und`).

Key risk areas:
- success order must be `... loaded_subslice remainder`;
- loaded subslice must contain only `bits` and zero refs (`fetch_subslice(bits, 0)`);
- insufficient bits must throw `cellUnd` (non-quiet path);
- opcode boundaries: `bits ∈ [1, 256]`;
- decoder must accept both short (`0xd6xx`) and alt (`0xd71c>>2` + args10) encodings;
- assembler currently emits the 24-bit alt form for `.loadSliceFixed`.
-/

private def ldsliceId : InstrId := { name := "LDSLICE" }

private def ldsliceInstr (bits : Nat) : Instr :=
  .loadSliceFixed false false bits

private def mkLdsliceCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[ldsliceInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldsliceId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdsliceDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadSliceFixed (ldsliceInstr bits) stack

private def runLdsliceDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadSliceFixed instr (VM.push (intV 606)) stack

private def stripeBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkLdsliceInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def expectedLoaded (s : Slice) (bits : Nat) : Slice :=
  mkSliceFromBits (s.readBits bits)

private def ldsliceShortWord (bits : Nat) : Nat :=
  0xd600 + (bits - 1)

private def ldsliceAltWord (bits : Nat) : Nat :=
  let prefix14 : Nat := (0xd71c >>> 2)
  let args10 : Nat := bits - 1
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

private def ldsliceGasProbeBits : Nat := 8

private def ldsliceSetGasExact : Int :=
  computeExactGasBudget (ldsliceInstr ldsliceGasProbeBits)

private def ldsliceSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (ldsliceInstr ldsliceGasProbeBits)

private def ldsliceBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLdsliceBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ldsliceBitsBoundaryPool.size - 1)
  (ldsliceBitsBoundaryPool[idx]!, rng')

private def pickLdsliceBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLdsliceBitsBoundary rng1
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

private def genLdsliceFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (bits, rng2) := pickLdsliceBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkLdsliceCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkLdsliceInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkLdsliceCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkLdsliceInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkLdsliceCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkLdsliceInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkLdsliceCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkLdsliceInput bits tail phase)], rng5)
  else if shape = 4 then
    let avail := bits - 1
    (mkLdsliceCase s!"fuzz/cellund/by1/bits-{bits}/avail-{avail}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits avail phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let avail := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkLdsliceCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{avail}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits avail phase) refs)], rng5)
  else if shape = 6 then
    (mkLdsliceCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkLdsliceCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkLdsliceCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng3)
  else if shape = 9 then
    (mkLdsliceCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 10 then
    (mkLdsliceCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 11 then
    (mkLdsliceCase s!"fuzz/type/top-cell/bits-{bits}" bits #[.cell Cell.empty], rng3)
  else if shape = 12 then
    (mkLdsliceCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)
  else
    (mkLdsliceCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkLdsliceInput bits tailBits3 phase), .null], rng3)

def suite : InstrSuite where
  id := ldsliceId
  unit := #[
    { name := "unit/direct/success-order-boundaries-and-refs"
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
          let input := mkLdsliceInput bits tail phase
          expectOkStack s!"ok/bits-{bits}/tail-{tail.size}"
            (runLdsliceDirect bits #[.slice input])
            #[.slice (expectedLoaded input bits), .slice (input.advanceBits bits)]

        let refsInput := mkLdsliceInput 8 tailBits5 1 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-preserved-on-remainder-and-not-loaded"
          (runLdsliceDirect 8 #[.slice refsInput])
          #[.slice (expectedLoaded refsInput 8), .slice (refsInput.advanceBits 8)]

        let deepInput := mkLdsliceInput 32 tailBits7 0
        expectOkStack "ok/deep-stack-preserved"
          (runLdsliceDirect 32 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, .slice (expectedLoaded deepInput 32), .slice (deepInput.advanceBits 32)] }
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
        for c in insuff do
          let bits := c.1
          let avail := c.2
          let s := mkSliceWithBitsRefs (stripeBits avail 0)
          expectErr s!"cellund/bits-{bits}/avail-{avail}"
            (runLdsliceDirect bits #[.slice s]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runLdsliceDirect 8 #[.slice refsOnly]) .cellUnd }
    ,
    { name := "unit/direct/underflow-and-type-check-surface"
      run := do
        expectErr "underflow/empty" (runLdsliceDirect 8 #[]) .stkUnd
        expectErr "type/top-null" (runLdsliceDirect 8 #[.null]) .typeChk
        expectErr "type/top-int" (runLdsliceDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell" (runLdsliceDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runLdsliceDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdsliceDirect 8 #[.slice (mkLdsliceInput 8 tailBits3 0), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-short-alt-and-assembler-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[ldsliceInstr 1, ldsliceInstr 8, ldsliceInstr 255, ldsliceInstr 256, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/alt-seq failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-alt-1" a0 (ldsliceInstr 1) 24
        let a2 ← expectDecodeStep "decode/asm-alt-8" a1 (ldsliceInstr 8) 24
        let a3 ← expectDecodeStep "decode/asm-alt-255" a2 (ldsliceInstr 255) 24
        let a4 ← expectDecodeStep "decode/asm-alt-256" a3 (ldsliceInstr 256) 24
        let a5 ← expectDecodeStep "decode/asm-tail-add" a4 .add 8
        if a5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-alt-end: expected exhausted slice, got {a5.bitsRemaining} bits remaining")

        let asm8 ←
          match assembleCp0 [ldsliceInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/bits8 failed: {e}")
        if asm8.bits = natToBits (ldsliceAltWord 8) 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bits8: expected alt 24-bit encoding, got {asm8.bits}")
        if asm8.bits.size = 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/bits8: expected 24 bits, got {asm8.bits.size}")

        match assembleCp0 [ldsliceInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits0: expected rangeChk, got success")

        match assembleCp0 [ldsliceInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits257: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let shortRawBits : BitString :=
          natToBits (ldsliceShortWord 1) 16
            ++ natToBits (ldsliceShortWord 8) 16
            ++ natToBits (ldsliceShortWord 255) 16
            ++ natToBits (ldsliceShortWord 256) 16
            ++ addCell.bits
        let shortRawCode : Cell := Cell.mkOrdinary shortRawBits #[]
        let s0 := Slice.ofCell shortRawCode
        let s1 ← expectDecodeStep "decode/raw-short-1" s0 (ldsliceInstr 1) 16
        let s2 ← expectDecodeStep "decode/raw-short-8" s1 (ldsliceInstr 8) 16
        let s3 ← expectDecodeStep "decode/raw-short-255" s2 (ldsliceInstr 255) 16
        let s4 ← expectDecodeStep "decode/raw-short-256" s3 (ldsliceInstr 256) 16
        let s5 ← expectDecodeStep "decode/raw-short-tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let mixedRawBits : BitString :=
          natToBits (ldsliceShortWord 8) 16
            ++ natToBits (ldsliceAltWord 8) 24
            ++ addCell.bits
        let mixedRawCode : Cell := Cell.mkOrdinary mixedRawBits #[]
        let m0 := Slice.ofCell mixedRawCode
        let m1 ← expectDecodeStep "decode/raw-mixed-short-8" m0 (ldsliceInstr 8) 16
        let m2 ← expectDecodeStep "decode/raw-mixed-alt-8" m1 (ldsliceInstr 8) 24
        let m3 ← expectDecodeStep "decode/raw-mixed-tail-add" m2 .add 8
        if m3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-mixed-end: expected exhausted slice, got {m3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-loadslicefixed-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLdsliceDispatchFallback .add #[.null])
          #[.null, intV 606]
        expectOkStack "dispatch/other-cell-op-family"
          (runLdsliceDispatchFallback (.loadSliceX false false) #[intV 11])
          #[intV 11, intV 606] }
  ]
  oracle := #[
    mkLdsliceCase "ok/bits-1/exact" 1 #[.slice (mkLdsliceInput 1 #[] 0)],
    mkLdsliceCase "ok/bits-1/tail7" 1 #[.slice (mkLdsliceInput 1 tailBits7 1)],
    mkLdsliceCase "ok/bits-2/tail5" 2 #[.slice (mkLdsliceInput 2 tailBits5 0)],
    mkLdsliceCase "ok/bits-3/tail11" 3 #[.slice (mkLdsliceInput 3 tailBits11 1)],
    mkLdsliceCase "ok/bits-7/tail13" 7 #[.slice (mkLdsliceInput 7 tailBits13 0)],
    mkLdsliceCase "ok/bits-8/exact" 8 #[.slice (mkLdsliceInput 8 #[] 1)],
    mkLdsliceCase "ok/bits-8/tail11" 8 #[.slice (mkLdsliceInput 8 tailBits11 0)],
    mkLdsliceCase "ok/bits-15/exact" 15 #[.slice (mkLdsliceInput 15 #[] 1)],
    mkLdsliceCase "ok/bits-16/tail7" 16 #[.slice (mkLdsliceInput 16 tailBits7 0)],
    mkLdsliceCase "ok/bits-31/exact" 31 #[.slice (mkLdsliceInput 31 #[] 0)],
    mkLdsliceCase "ok/bits-63/tail5" 63 #[.slice (mkLdsliceInput 63 tailBits5 1)],
    mkLdsliceCase "ok/bits-127/exact" 127 #[.slice (mkLdsliceInput 127 #[] 1)],
    mkLdsliceCase "ok/bits-255/exact" 255 #[.slice (mkLdsliceInput 255 #[] 0)],
    mkLdsliceCase "ok/bits-255/tail1" 255 #[.slice (mkLdsliceInput 255 #[true] 1)],
    mkLdsliceCase "ok/bits-256/exact" 256 #[.slice (mkLdsliceInput 256 #[] 0)],
    mkLdsliceCase "ok/bits-256/tail3" 256 #[.slice (mkLdsliceInput 256 tailBits3 1)],
    mkLdsliceCase "ok/bits-8/refs2" 8 #[.slice (mkLdsliceInput 8 tailBits5 0 #[refLeafA, refLeafB])],
    mkLdsliceCase "ok/bits-32/refs3-tail7" 32
      #[.slice (mkLdsliceInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkLdsliceCase "ok/deep-stack-preserve" 8
      #[.null, intV 42, .slice (mkLdsliceInput 8 tailBits7 1)],
    mkLdsliceCase "ok/deep-stack-with-refs" 32
      #[.cell Cell.empty, .slice (mkLdsliceInput 32 tailBits5 0 #[refLeafA])],

    mkLdsliceCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkLdsliceCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkLdsliceCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkLdsliceCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkLdsliceCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkLdsliceCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],

    mkLdsliceCase "underflow/empty" 8 #[],
    mkLdsliceCase "type/top-null" 8 #[.null],
    mkLdsliceCase "type/top-int" 8 #[intV 0],
    mkLdsliceCase "type/top-cell" 8 #[.cell Cell.empty],
    mkLdsliceCase "type/top-builder" 8 #[.builder Builder.empty],
    mkLdsliceCase "type/deep-top-not-slice" 8 #[.slice (mkLdsliceInput 8 tailBits3 0), .null],

    mkLdsliceCase "gas/exact-cost-succeeds" ldsliceGasProbeBits
      #[.slice (mkLdsliceInput ldsliceGasProbeBits tailBits11 1)]
      #[.pushInt (.num ldsliceSetGasExact), .tonEnvOp .setGasLimit, ldsliceInstr ldsliceGasProbeBits],
    mkLdsliceCase "gas/exact-minus-one-out-of-gas" ldsliceGasProbeBits
      #[.slice (mkLdsliceInput ldsliceGasProbeBits tailBits11 1)]
      #[.pushInt (.num ldsliceSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldsliceInstr ldsliceGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026021016
      count := 320
      gen := genLdsliceFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSLICE
