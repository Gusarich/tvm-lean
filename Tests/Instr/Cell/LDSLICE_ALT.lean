import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSLICE_ALT

/-
LDSLICE_ALT branch-mapping notes (fixed-width, non-prefetch, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadSliceFixed.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_slice_fixed`, `exec_load_slice_fixed2`, `exec_load_slice_common`,
     table rows `0xd6` and `0xd71c>>2`).

ALT target in this suite is `{P}LDSLICE{Q}` 24-bit family with flags=`00`
(`LDSLICE_ALT` = `.loadSliceFixed false false bits`).

Branch map used for this suite:
- Lean `.loadSliceFixed false false bits`: 5 branch sites / 6 terminal outcomes
  (instr guard; `popSlice` underflow/type/success; `haveBits` success/fail;
   success push order and stack preservation).
- C++ short/alt fixed-width entrypoints both call
  `exec_load_slice_common(..., mode=0)` for non-prefetch/non-quiet:
  aligned outcomes (`pop_cellslice`; `have(bits)` split; success push order
  `loaded` then `remainder`; insufficient bits => `cell_und`).

Key risk areas covered:
- success order must be `... loaded remainder`;
- loaded slice carries only requested bits and zero refs;
- insufficient bits throws `cellUnd` (not quiet);
- stack/type/underflow surface parity for single-slice input;
- alt decode boundaries (`bits ∈ [1, 256]`, 24-bit width);
- canonical short (`0xd6xx`) and alt (`0xd71cxxxx`) decode mapping consistency.
-/

private def ldsliceAltId : InstrId := { name := "LDSLICE_ALT" }

private def ldsliceAltInstr (bits : Nat) : Instr :=
  .loadSliceFixed false false bits

private def ldsliceAltCanonicalWord (bits : Nat) : Nat :=
  0xd600 + (bits - 1)

private def ldsliceAltWord (bits : Nat) : Nat :=
  let prefix14 : Nat := (0xd71c >>> 2)
  let args10 : Nat := bits - 1
  (prefix14 <<< 10) + args10

private def mkLdsliceAltCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[ldsliceAltInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldsliceAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdsliceAltDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadSliceFixed (ldsliceAltInstr bits) stack

private def runLdsliceAltDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadSliceFixed instr (VM.push (intV 53011)) stack

private def stripeBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkLdsliceAltInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def expectedLoaded (s : Slice) (bits : Nat) : Slice :=
  mkSliceFromBits (s.readBits bits)

private def tailBits3 : BitString := natToBits 5 3
private def tailBits5 : BitString := natToBits 21 5
private def tailBits7 : BitString := natToBits 93 7
private def tailBits11 : BitString := natToBits 1337 11
private def tailBits13 : BitString := natToBits 4242 13

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]

private def ldsliceAltGasProbeBits : Nat := 8

private def ldsliceAltSetGasExact : Int :=
  computeExactGasBudget (ldsliceAltInstr ldsliceAltGasProbeBits)

private def ldsliceAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (ldsliceAltInstr ldsliceAltGasProbeBits)

private def ldsliceAltBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLdsliceAltBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ldsliceAltBitsBoundaryPool.size - 1)
  (ldsliceAltBitsBoundaryPool[idx]!, rng')

private def pickLdsliceAltBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickLdsliceAltBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickLdsliceAltRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafA, refLeafB]
    else #[refLeafA, refLeafB, refLeafC]
  (refs, rng')

private def pickLdsliceAltNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell Cell.empty
    else .builder Builder.empty
  (v, rng')

private def genLdsliceAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (bits, rng2) := pickLdsliceAltBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkLdsliceAltCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkLdsliceAltInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkLdsliceAltCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkLdsliceAltInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickLdsliceAltRefPack rng4
    (mkLdsliceAltCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkLdsliceAltInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickLdsliceAltNoise rng4
    (mkLdsliceAltCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkLdsliceAltInput bits tail phase)], rng5)
  else if shape = 4 then
    let avail := bits - 1
    (mkLdsliceAltCase s!"fuzz/cellund/by1/bits-{bits}/avail-{avail}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits avail phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let avail := bits - delta
    let (refs, rng5) := pickLdsliceAltRefPack rng4
    (mkLdsliceAltCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{avail}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits avail phase) refs)], rng5)
  else if shape = 6 then
    (mkLdsliceAltCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickLdsliceAltRefPack rng3
    (mkLdsliceAltCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkLdsliceAltCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng3)
  else if shape = 9 then
    (mkLdsliceAltCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 10 then
    (mkLdsliceAltCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 11 then
    (mkLdsliceAltCase s!"fuzz/type/top-cell/bits-{bits}" bits #[.cell Cell.empty], rng3)
  else if shape = 12 then
    (mkLdsliceAltCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)
  else if shape = 13 then
    (mkLdsliceAltCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkLdsliceAltInput bits tailBits3 phase), .null], rng3)
  else if shape = 14 then
    let (useExact, rng4) := randBool rng3
    if useExact then
      (mkLdsliceAltCase "fuzz/gas/exact" ldsliceAltGasProbeBits
        #[.slice (mkLdsliceAltInput ldsliceAltGasProbeBits tailBits11 phase)]
        #[.pushInt (.num ldsliceAltSetGasExact), .tonEnvOp .setGasLimit, ldsliceAltInstr ldsliceAltGasProbeBits],
        rng4)
    else
      (mkLdsliceAltCase "fuzz/gas/exact-minus-one" ldsliceAltGasProbeBits
        #[.slice (mkLdsliceAltInput ldsliceAltGasProbeBits tailBits11 phase)]
        #[.pushInt (.num ldsliceAltSetGasExactMinusOne), .tonEnvOp .setGasLimit,
          ldsliceAltInstr ldsliceAltGasProbeBits],
        rng4)
  else
    let (tailLen, rng4) := randNat rng3 0 24
    let boundaryBits : Nat := if bits % 2 = 0 then 256 else 1
    let tail := stripeBits tailLen (phase + 1)
    (mkLdsliceAltCase s!"fuzz/ok/boundary/bits-{boundaryBits}/tail-{tailLen}" boundaryBits
      #[.slice (mkLdsliceAltInput boundaryBits tail phase)], rng4)

def suite : InstrSuite where
  id := ldsliceAltId
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
          let input := mkLdsliceAltInput bits tail phase
          expectOkStack s!"ok/bits-{bits}/tail-{tail.size}"
            (runLdsliceAltDirect bits #[.slice input])
            #[.slice (expectedLoaded input bits), .slice (input.advanceBits bits)]

        let refsInput := mkLdsliceAltInput 8 tailBits5 1 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-preserved-on-remainder-and-not-loaded"
          (runLdsliceAltDirect 8 #[.slice refsInput])
          #[.slice (expectedLoaded refsInput 8), .slice (refsInput.advanceBits 8)]

        let deepInput := mkLdsliceAltInput 32 tailBits7 0
        expectOkStack "ok/deep-stack-preserved"
          (runLdsliceAltDirect 32 #[.null, intV 99, .slice deepInput])
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
            (runLdsliceAltDirect bits #[.slice s]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runLdsliceAltDirect 8 #[.slice refsOnly]) .cellUnd }
    ,
    { name := "unit/direct/underflow-and-type-check-surface"
      run := do
        expectErr "underflow/empty" (runLdsliceAltDirect 8 #[]) .stkUnd
        expectErr "type/top-null" (runLdsliceAltDirect 8 #[.null]) .typeChk
        expectErr "type/top-int" (runLdsliceAltDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell" (runLdsliceAltDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runLdsliceAltDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdsliceAltDirect 8 #[.slice (mkLdsliceAltInput 8 tailBits3 0), .null]) .typeChk }
    ,
    { name := "unit/opcode/alt-decode-boundaries-and-canonical-mapping"
      run := do
        let asmProgram : Array Instr :=
          #[ldsliceAltInstr 1, ldsliceAltInstr 8, ldsliceAltInstr 255, ldsliceAltInstr 256, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/alt-seq failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-alt-1" a0 (ldsliceAltInstr 1) 24
        let a2 ← expectDecodeStep "decode/asm-alt-8" a1 (ldsliceAltInstr 8) 24
        let a3 ← expectDecodeStep "decode/asm-alt-255" a2 (ldsliceAltInstr 255) 24
        let a4 ← expectDecodeStep "decode/asm-alt-256" a3 (ldsliceAltInstr 256) 24
        let a5 ← expectDecodeStep "decode/asm-alt-tail-add" a4 .add 8
        if a5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-alt-end: expected exhausted slice, got {a5.bitsRemaining} bits remaining")

        let asm8 ←
          match assembleCp0 [ldsliceAltInstr 8] with
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

        match assembleCp0 [ldsliceAltInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits0: expected rangeChk, got success")

        match assembleCp0 [ldsliceAltInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/bits257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/bits257: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let altRawBits : BitString :=
          natToBits (ldsliceAltWord 1) 24
            ++ natToBits (ldsliceAltWord 2) 24
            ++ natToBits (ldsliceAltWord 255) 24
            ++ natToBits (ldsliceAltWord 256) 24
            ++ addCell.bits
        let altRawCode : Cell := Cell.mkOrdinary altRawBits #[]
        let alt0 := Slice.ofCell altRawCode
        let alt1 ← expectDecodeStep "decode/raw-alt-1" alt0 (ldsliceAltInstr 1) 24
        let alt2 ← expectDecodeStep "decode/raw-alt-2" alt1 (ldsliceAltInstr 2) 24
        let alt3 ← expectDecodeStep "decode/raw-alt-255" alt2 (ldsliceAltInstr 255) 24
        let alt4 ← expectDecodeStep "decode/raw-alt-256" alt3 (ldsliceAltInstr 256) 24
        let alt5 ← expectDecodeStep "decode/raw-alt-tail-add" alt4 .add 8
        if alt5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-alt-end: expected exhausted slice, got {alt5.bitsRemaining} bits remaining")

        let shortRawBits : BitString :=
          natToBits (ldsliceAltCanonicalWord 1) 16
            ++ natToBits (ldsliceAltCanonicalWord 2) 16
            ++ natToBits (ldsliceAltCanonicalWord 255) 16
            ++ natToBits (ldsliceAltCanonicalWord 256) 16
            ++ addCell.bits
        let shortRawCode : Cell := Cell.mkOrdinary shortRawBits #[]
        let s0 := Slice.ofCell shortRawCode
        let s1 ← expectDecodeStep "decode/raw-short-1" s0 (ldsliceAltInstr 1) 16
        let s2 ← expectDecodeStep "decode/raw-short-2" s1 (ldsliceAltInstr 2) 16
        let s3 ← expectDecodeStep "decode/raw-short-255" s2 (ldsliceAltInstr 255) 16
        let s4 ← expectDecodeStep "decode/raw-short-256" s3 (ldsliceAltInstr 256) 16
        let s5 ← expectDecodeStep "decode/raw-short-tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let mixedRawBits : BitString :=
          natToBits (ldsliceAltCanonicalWord 8) 16
            ++ natToBits (ldsliceAltWord 8) 24
            ++ natToBits (ldsliceAltCanonicalWord 256) 16
            ++ natToBits (ldsliceAltWord 1) 24
            ++ addCell.bits
        let mixedRawCode : Cell := Cell.mkOrdinary mixedRawBits #[]
        let m0 := Slice.ofCell mixedRawCode
        let m1 ← expectDecodeStep "decode/raw-mixed-short-8" m0 (ldsliceAltInstr 8) 16
        let m2 ← expectDecodeStep "decode/raw-mixed-alt-8" m1 (ldsliceAltInstr 8) 24
        let m3 ← expectDecodeStep "decode/raw-mixed-short-256" m2 (ldsliceAltInstr 256) 16
        let m4 ← expectDecodeStep "decode/raw-mixed-alt-1" m3 (ldsliceAltInstr 1) 24
        let m5 ← expectDecodeStep "decode/raw-mixed-tail-add" m4 .add 8
        if m5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-mixed-end: expected exhausted slice, got {m5.bitsRemaining} bits remaining")

        let mappingBits : Array Nat := #[1, 8, 255, 256]
        for bits in mappingBits do
          let altSlice := mkSliceFromBits (natToBits (ldsliceAltWord bits) 24)
          let shortSlice := mkSliceFromBits (natToBits (ldsliceAltCanonicalWord bits) 16)

          let decodedAlt ←
            match decodeCp0WithBits altSlice with
            | .ok (instr, used, _) =>
                if used = 24 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/alt/bits-{bits}: expected 24-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/alt/bits-{bits}: failed with {e}")
          let decodedShort ←
            match decodeCp0WithBits shortSlice with
            | .ok (instr, used, _) =>
                if used = 16 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/short/bits-{bits}: expected 16-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/short/bits-{bits}: failed with {e}")

          if decodedAlt == ldsliceAltInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/alt/bits-{bits}: unexpected instruction {reprStr decodedAlt}")
          if decodedShort == ldsliceAltInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/short/bits-{bits}: unexpected instruction {reprStr decodedShort}")
          if decodedAlt == decodedShort then
            pure ()
          else
            throw (IO.userError s!"decode/map/bits-{bits}: alt and short decoded to different instructions")

          let input := mkLdsliceAltInput bits tailBits7 (bits % 2) #[refLeafA]
          let expected := #[.slice (expectedLoaded input bits), .slice (input.advanceBits bits)]
          expectOkStack s!"exec/map/alt/bits-{bits}"
            (runHandlerDirect execInstrCellLoadSliceFixed decodedAlt #[.slice input])
            expected
          expectOkStack s!"exec/map/short/bits-{bits}"
            (runHandlerDirect execInstrCellLoadSliceFixed decodedShort #[.slice input])
            expected }
    ,
    { name := "unit/dispatch/non-loadslicefixed-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLdsliceAltDispatchFallback .add #[.null])
          #[.null, intV 53011]
        expectOkStack "dispatch/other-cell-op-family"
          (runLdsliceAltDispatchFallback (.loadSliceX false false) #[intV 11])
          #[intV 11, intV 53011] }
  ]
  oracle := #[
    mkLdsliceAltCase "ok/bits-1/exact" 1 #[.slice (mkLdsliceAltInput 1 #[] 0)],
    mkLdsliceAltCase "ok/bits-1/tail7" 1 #[.slice (mkLdsliceAltInput 1 tailBits7 1)],
    mkLdsliceAltCase "ok/bits-2/tail5" 2 #[.slice (mkLdsliceAltInput 2 tailBits5 0)],
    mkLdsliceAltCase "ok/bits-3/tail11" 3 #[.slice (mkLdsliceAltInput 3 tailBits11 1)],
    mkLdsliceAltCase "ok/bits-7/tail13" 7 #[.slice (mkLdsliceAltInput 7 tailBits13 0)],
    mkLdsliceAltCase "ok/bits-8/exact" 8 #[.slice (mkLdsliceAltInput 8 #[] 1)],
    mkLdsliceAltCase "ok/bits-8/tail11" 8 #[.slice (mkLdsliceAltInput 8 tailBits11 0)],
    mkLdsliceAltCase "ok/bits-15/exact" 15 #[.slice (mkLdsliceAltInput 15 #[] 1)],
    mkLdsliceAltCase "ok/bits-16/tail7" 16 #[.slice (mkLdsliceAltInput 16 tailBits7 0)],
    mkLdsliceAltCase "ok/bits-31/exact" 31 #[.slice (mkLdsliceAltInput 31 #[] 0)],
    mkLdsliceAltCase "ok/bits-63/tail5" 63 #[.slice (mkLdsliceAltInput 63 tailBits5 1)],
    mkLdsliceAltCase "ok/bits-127/exact" 127 #[.slice (mkLdsliceAltInput 127 #[] 1)],
    mkLdsliceAltCase "ok/bits-255/exact" 255 #[.slice (mkLdsliceAltInput 255 #[] 0)],
    mkLdsliceAltCase "ok/bits-255/tail1" 255 #[.slice (mkLdsliceAltInput 255 #[true] 1)],
    mkLdsliceAltCase "ok/bits-256/exact" 256 #[.slice (mkLdsliceAltInput 256 #[] 0)],
    mkLdsliceAltCase "ok/bits-256/tail3" 256 #[.slice (mkLdsliceAltInput 256 tailBits3 1)],
    mkLdsliceAltCase "ok/bits-8/refs2" 8 #[.slice (mkLdsliceAltInput 8 tailBits5 0 #[refLeafA, refLeafB])],
    mkLdsliceAltCase "ok/bits-32/refs3-tail7" 32
      #[.slice (mkLdsliceAltInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkLdsliceAltCase "ok/deep-stack-preserve" 8
      #[.null, intV 42, .slice (mkLdsliceAltInput 8 tailBits7 1)],
    mkLdsliceAltCase "ok/deep-stack-with-refs" 32
      #[.cell Cell.empty, .slice (mkLdsliceAltInput 32 tailBits5 0 #[refLeafA])],

    mkLdsliceAltCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkLdsliceAltCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkLdsliceAltCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkLdsliceAltCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkLdsliceAltCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkLdsliceAltCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],

    mkLdsliceAltCase "underflow/empty" 8 #[],
    mkLdsliceAltCase "type/top-null" 8 #[.null],
    mkLdsliceAltCase "type/top-int" 8 #[intV 0],
    mkLdsliceAltCase "type/top-cell" 8 #[.cell Cell.empty],
    mkLdsliceAltCase "type/top-builder" 8 #[.builder Builder.empty],
    mkLdsliceAltCase "type/deep-top-not-slice" 8 #[.slice (mkLdsliceAltInput 8 tailBits3 0), .null],

    mkLdsliceAltCase "gas/exact-cost-succeeds" ldsliceAltGasProbeBits
      #[.slice (mkLdsliceAltInput ldsliceAltGasProbeBits tailBits11 1)]
      #[.pushInt (.num ldsliceAltSetGasExact), .tonEnvOp .setGasLimit, ldsliceAltInstr ldsliceAltGasProbeBits],
    mkLdsliceAltCase "gas/exact-minus-one-out-of-gas" ldsliceAltGasProbeBits
      #[.slice (mkLdsliceAltInput ldsliceAltGasProbeBits tailBits11 1)]
      #[.pushInt (.num ldsliceAltSetGasExactMinusOne), .tonEnvOp .setGasLimit,
        ldsliceAltInstr ldsliceAltGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026021031
      count := 320
      gen := genLdsliceAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSLICE_ALT
