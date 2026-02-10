import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDU

/-
PLDU branch-mapping notes (fixed-width, prefetch, unsigned, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt true true false bits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd708>>3` fixed-width decode path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadInt _ _ _ _` currently rejects assembly with `.invOpcode`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed2`, `exec_load_int_common`, prefetch unsigned path).

Branch map used for this suite (`PLDU` = unsigned=true, prefetch=true, quiet=false):
- bits==0 guard: immediate `rangeChk` before any stack read;
- stack underflow/type from `popSlice` when bits>0;
- success (`have(bits)`): push integer only, no remainder/status push;
- failure (`!have(bits)`): throw `cellUnd` (non-quiet);
- handler dispatch fallthrough for non-`.loadInt` instructions;
- decode boundary around fixed-width int load family
  (`0xd707` = PLDUXQ var-form, `0xd708>>3` = fixed-width family, `0xd710` = PLDUZ family).
-/

private def plduId : InstrId := { name := "PLDU" }

private def dispatchSentinel : Int := 941

private def plduInstr (bits : Nat) : Instr :=
  .loadInt true true false bits

private def loadIntFixedWord (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def plduWord (bits : Nat) : Nat :=
  loadIntFixedWord true true false bits

private def plduxInstr : Instr :=
  .loadIntVar true true false

private def plduProgram (bits : Nat) : Array Instr :=
  -- Fixed-width PLDU opcodes decode correctly but are not directly assembleable today.
  -- Oracle/fuzz execution uses PLDUX with an explicit bit count, which maps to the
  -- same C++ `exec_load_int_common` prefetch+unsigned+non-quiet path.
  #[.pushInt (.num bits), plduxInstr]

private def mkPlduCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := plduProgram bits)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := plduId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPlduDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (plduInstr bits) stack

private def runPlduDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadInt instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkPlduInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def expectedUnsigned (slice : Slice) (bits : Nat) : Int :=
  Int.ofNat (bitsToNat (slice.readBits bits))

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

private def plduBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickPlduBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (plduBitsBoundaryPool.size - 1)
  (plduBitsBoundaryPool[idx]!, rng')

private def pickPlduBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickPlduBitsBoundary rng1
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

private def genPlduFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (bits, rng2) := pickPlduBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkPlduCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkPlduInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkPlduCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkPlduInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkPlduCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkPlduInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkPlduCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkPlduInput bits tail phase)], rng5)
  else if shape = 4 then
    let available := bits - 1
    (mkPlduCase s!"fuzz/cellund/by1/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let available := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkPlduCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase) refs)], rng5)
  else if shape = 6 then
    (mkPlduCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkPlduCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkPlduCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng3)
  else if shape = 9 then
    (mkPlduCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 10 then
    (mkPlduCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 11 then
    (mkPlduCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkPlduInput bits tailBits3 phase), .null], rng3)
  else if shape = 12 then
    (mkPlduCase "fuzz/ok/min-boundary" 1 #[.slice (mkPlduInput 1 tailBits3 1)], rng3)
  else if shape = 13 then
    (mkPlduCase "fuzz/ok/max-boundary" 256 #[.slice (mkPlduInput 256 tailBits5 0)], rng3)
  else if shape = 14 then
    (mkPlduCase "fuzz/cellund/max-by1" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))], rng3)
  else
    (mkPlduCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)

def suite : InstrSuite where
  id := plduId
  unit := #[
    { name := "unit/direct/prefetch-success-pushes-int-only"
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
          let input := mkPlduInput bits tail phase
          expectOkStack s!"ok/bits-{bits}/tail-{tail.size}"
            (runPlduDirect bits #[.slice input])
            #[intV (expectedUnsigned input bits)]

        let refsInput := mkPlduInput 8 tailBits5 1 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-in-source-no-remainder-push"
          (runPlduDirect 8 #[.slice refsInput])
          #[intV (expectedUnsigned refsInput 8)]

        let deepInput := mkPlduInput 32 tailBits7 0
        expectOkStack "ok/deep-stack-preserved"
          (runPlduDirect 32 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, intV (expectedUnsigned deepInput 32)]

        expectOkStack "ok/partial-slice-cursor"
          (runPlduDirect 12 #[.slice partialCursorSlice])
          #[intV (expectedUnsigned partialCursorSlice 12)] }
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
            (runPlduDirect bits #[.slice slice]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runPlduDirect 8 #[.slice refsOnly]) .cellUnd

        expectErr "cellund/partial-cursor-bits5-avail4"
          (runPlduDirect 5 #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runPlduDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runPlduDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runPlduDirect 0 #[.slice (mkPlduInput 1 #[] 0)]) .rangeChk

        expectErr "underflow/empty"
          (runPlduDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runPlduDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runPlduDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runPlduDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runPlduDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPlduDirect 8 #[.slice (mkPlduInput 8 tailBits3 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPlduDirect 8 #[.slice (mkSliceWithBitsRefs #[]), .null]) .typeChk }
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
             natToBits (plduWord 1) 24 ++
             natToBits (loadIntFixedWord false true false 8) 24 ++
             natToBits (plduWord 256) 24 ++
             natToBits 0xd710 16 ++
             addCell.bits) #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/raw-boundary-plduxq" s0 (.loadIntVar true true true) 16
        let s2 ← expectDecodeStep "decode/raw-pldu-1" s1 (plduInstr 1) 24
        let s3 ← expectDecodeStep "decode/raw-neighbor-pldi-8" s2 (.loadInt false true false 8) 24
        let s4 ← expectDecodeStep "decode/raw-pldu-256" s3 (plduInstr 256) 24
        let s5 ← expectDecodeStep "decode/raw-boundary-plduz-0" s4 (.cellExt (.plduz 0)) 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        match assembleCp0 [plduInstr 1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/pldu-1: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldu-1: expected invOpcode, got success")

        match assembleCp0 [plduInstr 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/pldu-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldu-256: expected invOpcode, got success")

        match assembleCp0 [plduInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/pldu-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/pldu-0: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runPlduDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-fixed-loadint-var"
          (runPlduDispatchFallback (.loadIntVar true true false) #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cell-op"
          (runPlduDispatchFallback (.loadSliceFixed true false 8) #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPlduCase "ok/bits-1/exact" 1 #[.slice (mkPlduInput 1 #[] 0)],
    mkPlduCase "ok/bits-1/tail7" 1 #[.slice (mkPlduInput 1 tailBits7 1)],
    mkPlduCase "ok/bits-2/tail5" 2 #[.slice (mkPlduInput 2 tailBits5 0)],
    mkPlduCase "ok/bits-3/tail11" 3 #[.slice (mkPlduInput 3 tailBits11 1)],
    mkPlduCase "ok/bits-7/tail13" 7 #[.slice (mkPlduInput 7 tailBits13 0)],
    mkPlduCase "ok/bits-8/exact" 8 #[.slice (mkPlduInput 8 #[] 1)],
    mkPlduCase "ok/bits-8/tail11" 8 #[.slice (mkPlduInput 8 tailBits11 0)],
    mkPlduCase "ok/bits-15/exact" 15 #[.slice (mkPlduInput 15 #[] 1)],
    mkPlduCase "ok/bits-16/tail7" 16 #[.slice (mkPlduInput 16 tailBits7 0)],
    mkPlduCase "ok/bits-31/exact" 31 #[.slice (mkPlduInput 31 #[] 0)],
    mkPlduCase "ok/bits-63/tail5" 63 #[.slice (mkPlduInput 63 tailBits5 1)],
    mkPlduCase "ok/bits-127/exact" 127 #[.slice (mkPlduInput 127 #[] 1)],
    mkPlduCase "ok/bits-255/exact" 255 #[.slice (mkPlduInput 255 #[] 0)],
    mkPlduCase "ok/bits-255/tail1" 255 #[.slice (mkPlduInput 255 #[true] 1)],
    mkPlduCase "ok/bits-256/exact" 256 #[.slice (mkPlduInput 256 #[] 0)],
    mkPlduCase "ok/bits-256/tail3" 256 #[.slice (mkPlduInput 256 tailBits3 1)],
    mkPlduCase "ok/bits-8/refs2" 8 #[.slice (mkPlduInput 8 tailBits5 0 #[refLeafA, refLeafB])],
    mkPlduCase "ok/bits-32/refs3-tail7" 32
      #[.slice (mkPlduInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkPlduCase "ok/deep-stack-preserve" 8
      #[.null, intV 42, .slice (mkPlduInput 8 tailBits7 1)],
    mkPlduCase "ok/deep-stack-with-refs" 32
      #[.cell Cell.empty, .slice (mkPlduInput 32 tailBits5 0 #[refLeafA])],

    mkPlduCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkPlduCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkPlduCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkPlduCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkPlduCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkPlduCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkPlduCase "cellund/refs-only-no-bits" 8
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA])],

    mkPlduCase "underflow/empty" 8 #[],
    mkPlduCase "type/top-null" 8 #[.null],
    mkPlduCase "type/top-int" 8 #[intV 0],
    mkPlduCase "type/top-cell" 8 #[.cell Cell.empty],
    mkPlduCase "type/top-builder" 8 #[.builder Builder.empty],
    mkPlduCase "type/deep-top-not-slice" 8 #[.slice (mkPlduInput 8 tailBits3 0), .null],
    mkPlduCase "type/order-top-not-slice-over-short-slice" 8 #[.slice (mkSliceWithBitsRefs #[]), .null]
  ]
  fuzz := #[
    { seed := 2026021047
      count := 320
      gen := genPlduFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDU
