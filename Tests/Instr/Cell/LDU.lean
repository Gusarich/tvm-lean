import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDU

/-
LDU branch-mapping notes (fixed-width, non-prefetch, unsigned, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ldu.lean` (`.ldu bits`)
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean` (`.loadInt true false false bits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (short `0xd3xx` and fixed2 `0xd708>>3`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ldu` encodes; `.loadInt _ _ _ _` currently rejects)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed`, `exec_load_int_fixed2`, `exec_load_int_common`, mode=`1`).

Branch map used for this suite:
- bits==0 guard: immediate `rangeChk` before any stack read;
- stack underflow/type from `popSlice` when bits>0;
- success (`have(bits)`): push unsigned integer then remainder slice;
- failure (`!have(bits)`): throw `cellUnd` (non-quiet);
- handler dispatch fallthrough for non-`.ldu` instructions;
- opcode/decode boundaries across short LDU (`0xd3xx`) and fixed2 load-int family.

Assembler note:
- `.ldu bits` is assembleable for `bits ∈ [1, 256]`.
- `.loadInt true false false bits` (fixed2 family) decodes correctly from raw bits but is not
  directly assembleable today (`.invOpcode`), so oracle/fuzz use `.ldu` as the proxy program
  while unit tests keep direct fixed2 decode/handler coverage.
-/

private def lduId : InstrId := { name := "LDU" }

private def dispatchSentinel : Int := 967

private def lduInstr (bits : Nat) : Instr :=
  .ldu bits

private def lduFixed2Instr (bits : Nat) : Instr :=
  .loadInt true false false bits

private def loadIntFixedWord (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def lduFixed2Word (bits : Nat) : Nat :=
  loadIntFixedWord true false false bits

private def lduShortWord (bits : Nat) : Nat :=
  0xd300 + (bits - 1)

private def ldiShortWord (bits : Nat) : Nat :=
  0xd200 + (bits - 1)

private def mkLduCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[lduInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lduId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLduDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLdu (lduInstr bits) stack

private def runLduFixed2Direct (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (lduFixed2Instr bits) stack

private def runLduDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLdu instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (lduRes fixed2Res : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lduRes, fixed2Res with
    | .ok lv, .ok fv => lv == fv
    | .error le, .error fe => le == fe
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got ldu={reprStr lduRes}, fixed2={reprStr fixed2Res}")

private def mkLduInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def mkLduWordInput
    (bits word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def expectedUnsigned (slice : Slice) (bits : Nat) : Int :=
  Int.ofNat (bitsToNat (slice.readBits bits))

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 40 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 7, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 24 1) #[refLeafC]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 20, refPos := 0 }

private def lduGasProbeBits : Nat := 8

private def lduSetGasExact : Int :=
  computeExactGasBudget (lduInstr lduGasProbeBits)

private def lduSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (lduInstr lduGasProbeBits)

private def lduBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLduBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (lduBitsBoundaryPool.size - 1)
  (lduBitsBoundaryPool[idx]!, rng')

private def pickLduBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLduBitsBoundary rng1
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
  let value : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell Cell.empty
    else .builder Builder.empty
  (value, rng')

private def genLduFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (bits, rng2) := pickLduBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkLduCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkLduInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkLduCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkLduInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkLduCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkLduInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkLduCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkLduInput bits tail phase)], rng5)
  else if shape = 4 then
    let available := bits - 1
    (mkLduCase s!"fuzz/cellund/by1/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let available := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkLduCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase) refs)], rng5)
  else if shape = 6 then
    (mkLduCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkLduCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkLduCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng3)
  else if shape = 9 then
    (mkLduCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 10 then
    (mkLduCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 11 then
    (mkLduCase s!"fuzz/type/top-cell/bits-{bits}" bits #[.cell Cell.empty], rng3)
  else if shape = 12 then
    (mkLduCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)
  else if shape = 13 then
    (mkLduCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkLduInput bits tailBits3 phase), .null], rng3)
  else if shape = 14 then
    (mkLduCase "fuzz/ok/min-boundary" 1 #[.slice (mkLduWordInput 1 1 tailBits3)], rng3)
  else if shape = 15 then
    (mkLduCase "fuzz/ok/max-boundary" 256 #[.slice (mkLduInput 256 tailBits5 0)], rng3)
  else if shape = 16 then
    (mkLduCase "fuzz/cellund/max-by1" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))], rng3)
  else
    (mkLduCase s!"fuzz/type/order-top-not-slice-over-short-slice/bits-{bits}" bits
      #[.slice (mkSliceWithBitsRefs #[]), .null], rng3)

def suite : InstrSuite where
  id := lduId
  unit := #[
    { name := "unit/direct/success-pushes-unsigned-int-then-remainder"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkLduWordInput 1 0),
            (1, mkLduWordInput 1 1 tailBits7),
            (2, mkLduWordInput 2 3 tailBits3),
            (8, mkLduWordInput 8 0 tailBits5),
            (8, mkLduWordInput 8 0xff),
            (16, mkLduWordInput 16 0xface tailBits7),
            (255, mkLduInput 255 #[] 0),
            (255, mkLduInput 255 #[true] 1),
            (256, mkLduInput 256 #[] 1),
            (256, mkLduInput 256 tailBits3 0)
          ]
        for (bits, input) in checks do
          expectOkStack s!"ok/bits-{bits}/len-{input.bitsRemaining}"
            (runLduDirect bits #[.slice input])
            #[intV (expectedUnsigned input bits), .slice (input.advanceBits bits)]

        let refsInput := mkLduWordInput 8 0xa5 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-preserved-in-remainder"
          (runLduDirect 8 #[.slice refsInput])
          #[intV (expectedUnsigned refsInput 8), .slice (refsInput.advanceBits 8)]

        let deepInput := mkLduWordInput 16 0x1234 tailBits7
        expectOkStack "ok/deep-stack-preserved"
          (runLduDirect 16 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, intV (expectedUnsigned deepInput 16), .slice (deepInput.advanceBits 16)]

        expectOkStack "ok/partial-slice-cursor"
          (runLduDirect 12 #[.slice partialCursorSlice])
          #[intV (expectedUnsigned partialCursorSlice 12), .slice (partialCursorSlice.advanceBits 12)] }
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
        for (bits, available) in insuff do
          let slice := mkSliceWithBitsRefs (stripeBits available 0)
          expectErr s!"cellund/bits-{bits}/avail-{available}"
            (runLduDirect bits #[.slice slice]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runLduDirect 8 #[.slice refsOnly]) .cellUnd

        expectErr "cellund/partial-cursor-bits5-avail4"
          (runLduDirect 5 #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runLduDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runLduDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runLduDirect 0 #[.slice (mkLduInput 1 #[] 0)]) .rangeChk

        expectErr "underflow/empty"
          (runLduDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runLduDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runLduDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runLduDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runLduDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLduDirect 8 #[.slice (mkLduInput 8 tailBits3 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runLduDirect 8 #[.slice (mkSliceWithBitsRefs #[]), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-boundaries-and-assembler-constraints"
      run := do
        let asmProgram : Array Instr :=
          #[lduInstr 1, lduInstr 8, lduInstr 255, lduInstr 256, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/short-seq failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-short-1" a0 (lduInstr 1) 16
        let a2 ← expectDecodeStep "decode/asm-short-8" a1 (lduInstr 8) 16
        let a3 ← expectDecodeStep "decode/asm-short-255" a2 (lduInstr 255) 16
        let a4 ← expectDecodeStep "decode/asm-short-256" a3 (lduInstr 256) 16
        let a5 ← expectDecodeStep "decode/asm-short-tail-add" a4 .add 8
        if a5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-short-end: expected exhausted slice, got {a5.bitsRemaining} bits remaining")

        let asm8 ←
          match assembleCp0 [lduInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/ldu-8 failed: {e}")
        if asm8.bits = natToBits (lduShortWord 8) 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/ldu-8: expected short 16-bit encoding, got {asm8.bits}")
        if asm8.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/ldu-8: expected 16 bits, got {asm8.bits.size}")

        match assembleCp0 [lduInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/ldu-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldu-0: expected rangeChk, got success")

        match assembleCp0 [lduInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/ldu-257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldu-257: expected rangeChk, got success")

        match assembleCp0 [lduFixed2Instr 1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/fixed2-ldu-1: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/fixed2-ldu-1: expected invOpcode, got success")

        match assembleCp0 [lduFixed2Instr 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/fixed2-ldu-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/fixed2-ldu-256: expected invOpcode, got success")

        match assembleCp0 [lduFixed2Instr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/fixed2-ldu-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/fixed2-ldu-0: expected invOpcode, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let shortRawBits : BitString :=
          natToBits (ldiShortWord 8) 16
            ++ natToBits (lduShortWord 8) 16
            ++ natToBits 0xd4 8
            ++ addCell.bits
        let s0 := mkSliceFromBits shortRawBits
        let s1 ← expectDecodeStep "decode/raw-ldi-8-neighbor" s0 (.loadInt false false false 8) 16
        let s2 ← expectDecodeStep "decode/raw-ldu-8" s1 (lduInstr 8) 16
        let s3 ← expectDecodeStep "decode/raw-ldref-neighbor" s2 .ldref 8
        let s4 ← expectDecodeStep "decode/raw-short-tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        let fixedRawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd707 16 ++
             natToBits (lduFixed2Word 1) 24 ++
             natToBits (loadIntFixedWord false false false 8) 24 ++
             natToBits (lduFixed2Word 256) 24 ++
             natToBits 0xd710 16 ++
             addCell.bits) #[]
        let f0 := Slice.ofCell fixedRawCode
        let f1 ← expectDecodeStep "decode/raw-boundary-plduxq" f0 (.loadIntVar true true true) 16
        let f2 ← expectDecodeStep "decode/raw-fixed-ldu-1" f1 (lduFixed2Instr 1) 24
        let f3 ← expectDecodeStep "decode/raw-fixed-ldi-8-neighbor" f2 (.loadInt false false false 8) 24
        let f4 ← expectDecodeStep "decode/raw-fixed-ldu-256" f3 (lduFixed2Instr 256) 24
        let f5 ← expectDecodeStep "decode/raw-boundary-plduz-0" f4 (.cellExt (.plduz 0)) 16
        let f6 ← expectDecodeStep "decode/raw-fixed-tail-add" f5 .add 8
        if f6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-fixed-end: expected exhausted slice, got {f6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/proxy/fixed2-loadint-aligns-with-ldu"
      run := do
        let okChecks : Array (Nat × Slice) :=
          #[
            (1, mkLduWordInput 1 1 tailBits3),
            (8, mkLduWordInput 8 0xa5 tailBits5),
            (32, mkLduInput 32 tailBits7 0),
            (256, mkLduInput 256 tailBits3 1)
          ]
        for (bits, input) in okChecks do
          expectSameOutcome s!"align/ok/bits-{bits}"
            (runLduDirect bits #[.slice input])
            (runLduFixed2Direct bits #[.slice input])

        let insuff : Array (Nat × Nat) := #[(1, 0), (8, 7), (256, 255)]
        for (bits, available) in insuff do
          let slice := mkSliceWithBitsRefs (stripeBits available 0)
          expectSameOutcome s!"align/cellund/bits-{bits}/avail-{available}"
            (runLduDirect bits #[.slice slice])
            (runLduFixed2Direct bits #[.slice slice])

        expectSameOutcome "align/underflow-empty"
          (runLduDirect 8 #[])
          (runLduFixed2Direct 8 #[])
        expectSameOutcome "align/type-top-null"
          (runLduDirect 8 #[.null])
          (runLduFixed2Direct 8 #[.null])
        expectSameOutcome "align/range-bits0-before-pop"
          (runLduDirect 0 #[.slice (mkLduInput 8 #[] 0)])
          (runLduFixed2Direct 0 #[.slice (mkLduInput 8 #[] 0)]) }
    ,
    { name := "unit/dispatch/non-ldu-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLduDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/loadint-fixed2-neighbor"
          (runLduDispatchFallback (lduFixed2Instr 8) #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cell-op"
          (runLduDispatchFallback .ldref #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLduCase "ok/bits-1/exact-zero" 1 #[.slice (mkLduWordInput 1 0)],
    mkLduCase "ok/bits-1/tail7-one" 1 #[.slice (mkLduWordInput 1 1 tailBits7)],
    mkLduCase "ok/bits-2/tail5-max" 2 #[.slice (mkLduWordInput 2 3 tailBits5)],
    mkLduCase "ok/bits-3/tail11" 3 #[.slice (mkLduInput 3 tailBits11 1)],
    mkLduCase "ok/bits-7/tail13" 7 #[.slice (mkLduInput 7 tailBits13 0)],
    mkLduCase "ok/bits-8/exact-max" 8 #[.slice (mkLduWordInput 8 0xff)],
    mkLduCase "ok/bits-8/tail11-zero" 8 #[.slice (mkLduWordInput 8 0 tailBits11)],
    mkLduCase "ok/bits-15/exact" 15 #[.slice (mkLduInput 15 #[] 1)],
    mkLduCase "ok/bits-16/tail7-word" 16 #[.slice (mkLduWordInput 16 0x1234 tailBits7)],
    mkLduCase "ok/bits-31/exact" 31 #[.slice (mkLduInput 31 #[] 0)],
    mkLduCase "ok/bits-63/tail5" 63 #[.slice (mkLduInput 63 tailBits5 1)],
    mkLduCase "ok/bits-127/exact" 127 #[.slice (mkLduInput 127 #[] 1)],
    mkLduCase "ok/bits-255/exact" 255 #[.slice (mkLduInput 255 #[] 0)],
    mkLduCase "ok/bits-255/tail1" 255 #[.slice (mkLduInput 255 #[true] 1)],
    mkLduCase "ok/bits-256/exact" 256 #[.slice (mkLduInput 256 #[] 0)],
    mkLduCase "ok/bits-256/tail3" 256 #[.slice (mkLduInput 256 tailBits3 1)],
    mkLduCase "ok/bits-8/refs2" 8 #[.slice (mkLduWordInput 8 0xa5 tailBits5 #[refLeafA, refLeafB])],
    mkLduCase "ok/bits-32/refs3-tail7" 32
      #[.slice (mkLduInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkLduCase "ok/deep-stack-preserve" 8
      #[.null, intV 42, .slice (mkLduInput 8 tailBits7 1)],
    mkLduCase "ok/deep-stack-with-refs" 32
      #[.cell Cell.empty, .slice (mkLduInput 32 tailBits5 0 #[refLeafA])],

    mkLduCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkLduCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkLduCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkLduCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkLduCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkLduCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkLduCase "cellund/refs-only-no-bits" 8
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA])],

    mkLduCase "underflow/empty" 8 #[],
    mkLduCase "type/top-null" 8 #[.null],
    mkLduCase "type/top-int" 8 #[intV 0],
    mkLduCase "type/top-cell" 8 #[.cell Cell.empty],
    mkLduCase "type/top-builder" 8 #[.builder Builder.empty],
    mkLduCase "type/deep-top-not-slice" 8 #[.slice (mkLduInput 8 tailBits3 0), .null],
    mkLduCase "type/order-top-not-slice-over-short-slice" 8 #[.slice (mkSliceWithBitsRefs #[]), .null],

    mkLduCase "gas/exact-cost-succeeds" lduGasProbeBits
      #[.slice (mkLduInput lduGasProbeBits tailBits11 1)]
      #[.pushInt (.num lduSetGasExact), .tonEnvOp .setGasLimit, lduInstr lduGasProbeBits],
    mkLduCase "gas/exact-minus-one-out-of-gas" lduGasProbeBits
      #[.slice (mkLduInput lduGasProbeBits tailBits11 1)]
      #[.pushInt (.num lduSetGasExactMinusOne), .tonEnvOp .setGasLimit, lduInstr lduGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026021068
      count := 320
      gen := genLduFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDU
