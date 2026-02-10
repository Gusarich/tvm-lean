import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDI

/-
PLDI branch-mapping notes (fixed-width, prefetch, signed, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt false true false bits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd708>>3` fixed-width decode path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadInt _ _ _ _` currently rejects assembly with `.invOpcode`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed2`, `exec_load_int_common`, prefetch signed path).

Branch map used for this suite (`PLDI` = unsigned=false, prefetch=true, quiet=false):
- bits==0 guard: immediate `rangeChk` before any stack read;
- stack underflow/type from `popSlice` when bits>0;
- success (`have(bits)`): push signed integer only, no remainder/status push;
- failure (`!have(bits)`): throw `cellUnd` (non-quiet);
- handler dispatch fallthrough for non-`.loadInt` instructions;
- decode boundary around fixed-width int load family
  (`0xd707` = PLDUXQ var-form, `0xd708>>3` = fixed-width family, `0xd710` = PLDUZ family).
-/

private def pldiId : InstrId := { name := "PLDI" }

private def dispatchSentinel : Int := 953

private def pldiInstr (bits : Nat) : Instr :=
  .loadInt false true false bits

private def loadIntFixedWord (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def pldiWord (bits : Nat) : Nat :=
  loadIntFixedWord false true false bits

private def pldixInstr : Instr :=
  .loadIntVar false true false

private def pldiProgram (bits : Nat) : Array Instr :=
  -- Fixed-width PLDI opcodes decode correctly but are not directly assembleable today.
  -- Oracle/fuzz execution uses PLDIX with an explicit bit count, which maps to the
  -- same C++ `exec_load_int_common` prefetch+signed+non-quiet path.
  #[.pushInt (.num bits), pldixInstr]

private def mkPldiCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := pldiProgram bits)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldiId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldiDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (pldiInstr bits) stack

private def runPldiDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadInt instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkPldiInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def mkPldiWordInput
    (bits word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def expectedSigned (slice : Slice) (bits : Nat) : Int :=
  bitsToIntSignedTwos (slice.readBits bits)

private def tailBits3 : BitString := natToBits 5 3
private def tailBits5 : BitString := natToBits 21 5
private def tailBits7 : BitString := natToBits 93 7
private def tailBits11 : BitString := natToBits 1337 11
private def tailBits13 : BitString := natToBits 4242 13

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 40 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 7, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 24 1) #[refLeafC]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 20, refPos := 0 }

private def pldiBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickPldiBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pldiBitsBoundaryPool.size - 1)
  (pldiBitsBoundaryPool[idx]!, rng')

private def pickPldiBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickPldiBitsBoundary rng1
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

private def genPldiFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (bits, rng2) := pickPldiBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkPldiCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkPldiInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkPldiCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkPldiInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkPldiCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkPldiInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkPldiCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkPldiInput bits tail phase)], rng5)
  else if shape = 4 then
    let available := bits - 1
    (mkPldiCase s!"fuzz/cellund/by1/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let available := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkPldiCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase) refs)], rng5)
  else if shape = 6 then
    (mkPldiCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkPldiCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkPldiCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng3)
  else if shape = 9 then
    (mkPldiCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 10 then
    (mkPldiCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 11 then
    (mkPldiCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkPldiInput bits tailBits3 phase), .null], rng3)
  else if shape = 12 then
    (mkPldiCase "fuzz/signed/bits1/neg1" 1 #[.slice (mkPldiWordInput 1 1 tailBits3)], rng3)
  else if shape = 13 then
    (mkPldiCase "fuzz/signed/bits8/max-pos" 8 #[.slice (mkPldiWordInput 8 0x7f tailBits5)], rng3)
  else if shape = 14 then
    (mkPldiCase "fuzz/signed/bits8/min-neg" 8 #[.slice (mkPldiWordInput 8 0x80 tailBits7)], rng3)
  else if shape = 15 then
    (mkPldiCase "fuzz/signed/bits16/max-pos" 16 #[.slice (mkPldiWordInput 16 0x7fff tailBits3)], rng3)
  else if shape = 16 then
    (mkPldiCase "fuzz/signed/bits16/min-neg" 16 #[.slice (mkPldiWordInput 16 0x8000 tailBits5)], rng3)
  else if shape = 17 then
    (mkPldiCase "fuzz/ok/max-boundary-neg" 256 #[.slice (mkPldiInput 256 tailBits5 1)], rng3)
  else if shape = 18 then
    (mkPldiCase "fuzz/cellund/max-by1" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))], rng3)
  else
    (mkPldiCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)

def suite : InstrSuite where
  id := pldiId
  unit := #[
    { name := "unit/direct/prefetch-success-pushes-signed-int-only"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkPldiWordInput 1 0),
            (1, mkPldiWordInput 1 1),
            (2, mkPldiWordInput 2 1 tailBits3),
            (2, mkPldiWordInput 2 3),
            (8, mkPldiWordInput 8 0),
            (8, mkPldiWordInput 8 0x7f tailBits5),
            (8, mkPldiWordInput 8 0x80),
            (8, mkPldiWordInput 8 0xff tailBits7),
            (16, mkPldiWordInput 16 0x7fff tailBits3),
            (16, mkPldiWordInput 16 0x8000),
            (255, mkPldiInput 255 #[] 0),
            (255, mkPldiInput 255 #[true] 1),
            (256, mkPldiInput 256 #[] 1),
            (256, mkPldiInput 256 tailBits3 0)
          ]
        for (bits, input) in checks do
          expectOkStack s!"ok/bits-{bits}/len-{input.bitsRemaining}"
            (runPldiDirect bits #[.slice input])
            #[intV (expectedSigned input bits)]

        let refsInput := mkPldiWordInput 8 0x80 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-in-source-no-remainder-push"
          (runPldiDirect 8 #[.slice refsInput])
          #[intV (expectedSigned refsInput 8)]

        let deepInput := mkPldiWordInput 8 0xff tailBits7
        expectOkStack "ok/deep-stack-preserved"
          (runPldiDirect 8 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, intV (expectedSigned deepInput 8)]

        expectOkStack "ok/partial-slice-cursor"
          (runPldiDirect 12 #[.slice partialCursorSlice])
          #[intV (expectedSigned partialCursorSlice 12)] }
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
            (runPldiDirect bits #[.slice slice]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runPldiDirect 8 #[.slice refsOnly]) .cellUnd

        expectErr "cellund/partial-cursor-bits5-avail4"
          (runPldiDirect 5 #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runPldiDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runPldiDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runPldiDirect 0 #[.slice (mkPldiInput 1 #[] 0)]) .rangeChk

        expectErr "underflow/empty"
          (runPldiDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runPldiDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runPldiDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runPldiDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runPldiDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldiDirect 8 #[.slice (mkPldiInput 8 tailBits3 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldiDirect 8 #[.slice (mkSliceWithBitsRefs #[]), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd707 16 ++
             natToBits (pldiWord 1) 24 ++
             natToBits (loadIntFixedWord true true false 8) 24 ++
             natToBits (pldiWord 256) 24 ++
             natToBits 0xd710 16 ++
             addCell.bits) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-boundary-plduxq" s0 (.loadIntVar true true true) 16
        let s2 ← expectDecodeStep "decode/raw-pldi-1" s1 (pldiInstr 1) 24
        let s3 ← expectDecodeStep "decode/raw-neighbor-pldu-8" s2 (.loadInt true true false 8) 24
        let s4 ← expectDecodeStep "decode/raw-pldi-256" s3 (pldiInstr 256) 24
        let s5 ← expectDecodeStep "decode/raw-boundary-plduz-0" s4 (.cellExt (.plduz 0)) 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        match assembleCp0 [pldiInstr 1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/pldi-1: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldi-1: expected invOpcode, got success")

        match assembleCp0 [pldiInstr 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/pldi-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldi-256: expected invOpcode, got success")

        match assembleCp0 [pldiInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/pldi-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldi-0: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runPldiDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-fixed-loadint-var"
          (runPldiDispatchFallback (.loadIntVar false true false) #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cell-op"
          (runPldiDispatchFallback (.loadSliceFixed true false 8) #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldiCase "ok/bits-1/zero" 1 #[.slice (mkPldiWordInput 1 0)],
    mkPldiCase "ok/bits-1/neg1" 1 #[.slice (mkPldiWordInput 1 1)],
    mkPldiCase "ok/bits-2/pos1-tail3" 2 #[.slice (mkPldiWordInput 2 1 tailBits3)],
    mkPldiCase "ok/bits-2/neg1" 2 #[.slice (mkPldiWordInput 2 3)],
    mkPldiCase "ok/bits-3/neg2-tail5" 3 #[.slice (mkPldiWordInput 3 6 tailBits5)],
    mkPldiCase "ok/bits-7/tail13-neg" 7 #[.slice (mkPldiInput 7 tailBits13 1)],
    mkPldiCase "ok/bits-8/zero" 8 #[.slice (mkPldiWordInput 8 0)],
    mkPldiCase "ok/bits-8/max-pos" 8 #[.slice (mkPldiWordInput 8 0x7f tailBits5)],
    mkPldiCase "ok/bits-8/min-neg" 8 #[.slice (mkPldiWordInput 8 0x80)],
    mkPldiCase "ok/bits-8/neg1-tail11" 8 #[.slice (mkPldiWordInput 8 0xff tailBits11)],
    mkPldiCase "ok/bits-15/exact-neg" 15 #[.slice (mkPldiInput 15 #[] 1)],
    mkPldiCase "ok/bits-16/max-pos" 16 #[.slice (mkPldiWordInput 16 0x7fff tailBits3)],
    mkPldiCase "ok/bits-16/min-neg" 16 #[.slice (mkPldiWordInput 16 0x8000)],
    mkPldiCase "ok/bits-31/exact-pos" 31 #[.slice (mkPldiInput 31 #[] 0)],
    mkPldiCase "ok/bits-63/tail5-neg" 63 #[.slice (mkPldiInput 63 tailBits5 1)],
    mkPldiCase "ok/bits-127/exact-neg" 127 #[.slice (mkPldiInput 127 #[] 1)],
    mkPldiCase "ok/bits-255/exact-pos" 255 #[.slice (mkPldiInput 255 #[] 0)],
    mkPldiCase "ok/bits-255/tail1-neg" 255 #[.slice (mkPldiInput 255 #[true] 1)],
    mkPldiCase "ok/bits-256/exact-neg" 256 #[.slice (mkPldiInput 256 #[] 1)],
    mkPldiCase "ok/bits-256/tail3-pos" 256 #[.slice (mkPldiInput 256 tailBits3 0)],
    mkPldiCase "ok/bits-8/refs2-neg" 8 #[.slice (mkPldiWordInput 8 0x80 tailBits5 #[refLeafA, refLeafB])],
    mkPldiCase "ok/bits-32/refs3-tail7-neg" 32
      #[.slice (mkPldiInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkPldiCase "ok/deep-stack-preserve-neg1" 8
      #[.null, intV 42, .slice (mkPldiWordInput 8 0xff tailBits7)],
    mkPldiCase "ok/deep-stack-with-refs-pos" 32
      #[.cell Cell.empty, .slice (mkPldiInput 32 tailBits5 0 #[refLeafA])],

    mkPldiCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkPldiCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkPldiCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkPldiCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkPldiCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkPldiCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPldiCase "cellund/refs-only-no-bits" 8
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA])],

    mkPldiCase "underflow/empty" 8 #[],
    mkPldiCase "type/top-null" 8 #[.null],
    mkPldiCase "type/top-int" 8 #[intV 0],
    mkPldiCase "type/top-cell" 8 #[.cell Cell.empty],
    mkPldiCase "type/top-builder" 8 #[.builder Builder.empty],
    mkPldiCase "type/deep-top-not-slice" 8 #[.slice (mkPldiInput 8 tailBits3 0), .null],
    mkPldiCase "type/order-top-not-slice-over-short-slice" 8 #[.slice (mkSliceWithBitsRefs #[]), .null]
  ]
  fuzz := #[
    { seed := 2026021059
      count := 320
      gen := genPldiFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDI
