import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDCNTLEAD0

/-
SDCNTLEAD0 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdCntLead0.lean` (`.sdCntLead0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode `0xc710`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (encode `0xc710`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`reg_iun_cs_cmp(..., "SDCNTLEAD0", [](auto cs) { return cs->count_leading(0); })`).

Branch map used for this suite:
- handler dispatch: `.sdCntLead0` vs fallthrough to `next`;
- stack pop branch (`VM.popSlice`): `stkUnd` / `typeChk` / valid slice;
- count loop outcomes on remaining slice bits:
  empty (`rem=0`) -> `0`,
  first bit non-zero -> `0`,
  mixed prefix zeros -> stop at first `1`,
  all remaining bits zero -> full `rem`.
-/

private def sdCntLead0Id : InstrId := { name := "SDCNTLEAD0" }

private def sdCntLead0Instr : Instr := .sdCntLead0

private def dispatchSentinel : Int := 541

private def sdCntLead0Opcode : Nat := 0xc710
private def sdCntLead1Opcode : Nat := 0xc711
private def sdCntTrail0Opcode : Nat := 0xc712
private def sdCntTrail1Opcode : Nat := 0xc713
private def sdPsfxRevOpcode : Nat := 0xc70f

private def zeros (n : Nat) : BitString :=
  Array.replicate n false

private def ones (n : Nat) : BitString :=
  Array.replicate n true

private def mkPrefixZeroSlice (prefixZeros total : Nat) (refs : Array Cell := #[]) : Slice :=
  if prefixZeros < total then
    let tailLen : Nat := total - prefixZeros - 1
    let tail := stripeBits tailLen 1
    mkSliceWithBitsRefs (zeros prefixZeros ++ #[true] ++ tail) refs
  else
    mkSliceWithBitsRefs (zeros total) refs

private def expectedLead0 (s : Slice) : Int :=
  Int.ofNat (s.countLeading false)

private def runSdCntLead0Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdCntLead0 sdCntLead0Instr stack

private def runSdCntLead0DispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdCntLead0 instr (VM.push (intV dispatchSentinel)) stack

private def mkSdCntLead0Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdCntLead0Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdCntLead0Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def sdCntLead0SetGasExact : Int :=
  computeExactGasBudget sdCntLead0Instr

private def sdCntLead0SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdCntLead0Instr

private def sdskipfirstInstr : Instr := .sdskipfirst

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    let (idx, rng2) := randNat rng1 0 (bitsBoundaryPool.size - 1)
    (((bitsBoundaryPool[idx]?).getD 0), rng2)
  else
    randNat rng1 0 1023

private def pickRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (4, rng1)
  else
    randNat rng1 0 4

private def fuzzNoisePool : Array Value :=
  #[.null, intV 0, intV 7, intV (-9), .cell Cell.empty, .builder Builder.empty, .tuple #[], .cont (.quit 0)]

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (fuzzNoisePool.size - 1)
  (((fuzzNoisePool[idx]?).getD .null), rng1)

private def genSdCntLead0FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  if shape = 0 then
    let (total, rng2) := pickBitsMixed rng1
    let (prefZeros, rng3) := randNat rng2 0 total
    let (refs, rng4) := pickRefsMixed rng3
    let s := mkPrefixZeroSlice prefZeros total (refsByCount refs)
    (mkSdCntLead0Case s!"fuzz/ok/prefix{prefZeros}/total{total}/refs{refs}" #[.slice s], rng4)
  else if shape = 1 then
    let (total, rng2) := pickBitsMixed rng1
    let (bits, rng3) := randBitString total rng2
    let (refs, rng4) := pickRefsMixed rng3
    let s := mkSliceWithBitsRefs bits (refsByCount refs)
    (mkSdCntLead0Case s!"fuzz/ok/random/len{total}/refs{refs}" #[.slice s], rng4)
  else if shape = 2 then
    let (total, rng2) := pickBitsMixed rng1
    let (prefZeros, rng3) := randNat rng2 0 total
    let (skip, rng4) := randNat rng3 0 total
    let (refs, rng5) := pickRefsMixed rng4
    let s := mkPrefixZeroSlice prefZeros total (refsByCount refs)
    let stack : Array Value := #[.slice s, intV (Int.ofNat skip)]
    let program : Array Instr := #[sdskipfirstInstr, sdCntLead0Instr]
    (mkSdCntLead0Case s!"fuzz/ok/cursor/skip{skip}" stack program, rng5)
  else if shape = 3 then
    let (total, rng2) := pickBitsMixed rng1
    let (prefZeros, rng3) := randNat rng2 0 total
    let (refs, rng4) := pickRefsMixed rng3
    let (noise, rng5) := pickNoiseValue rng4
    let s := mkPrefixZeroSlice prefZeros total (refsByCount refs)
    (mkSdCntLead0Case "fuzz/ok/deep" #[noise, .slice s], rng5)
  else if shape = 4 then
    (mkSdCntLead0Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    let (mode, rng2) := randNat rng1 0 2
    let bad : Value :=
      if mode = 0 then .null
      else if mode = 1 then intV 0
      else .cell Cell.empty
    (mkSdCntLead0Case "fuzz/type/top" #[bad], rng2)
  else
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdCntLead0Case "fuzz/type/deep-top" #[.slice (mkPrefixZeroSlice 3 8), bad], rng2)

def suite : InstrSuite where
  id := { name := "SDCNTLEAD0" }
  unit := #[
    { name := "unit/direct/success-full-slices"
      run := do
        let checks : Array (String × Slice) :=
          #[
            ("empty", mkSliceWithBitsRefs #[]),
            ("len1-zero", mkSliceWithBitsRefs #[false]),
            ("len1-one", mkSliceWithBitsRefs #[true]),
            ("len4-prefix2", mkSliceWithBitsRefs #[false, false, true, false]),
            ("len8-stripe0", mkSliceWithBitsRefs (stripeBits 8 0)),
            ("len8-stripe1", mkSliceWithBitsRefs (stripeBits 8 1)),
            ("len32-all-zero", mkSliceWithBitsRefs (zeros 32)),
            ("len64-all-one", mkSliceWithBitsRefs (ones 64))
          ]
        for (label, s) in checks do
          expectOkStack s!"ok/{label}"
            (runSdCntLead0Direct #[.slice s])
            #[intV (expectedLead0 s)] }
    ,
    { name := "unit/direct/manual-prefix-boundaries"
      run := do
        let checks : Array (Nat × Nat) :=
          #[
            (0, 1),
            (1, 2),
            (5, 16),
            (15, 16),
            (255, 256),
            (256, 256)
          ]
        for (prefixZeros, total) in checks do
          let s := mkPrefixZeroSlice prefixZeros total
          let expected : Nat := if prefixZeros < total then prefixZeros else total
          expectOkStack s!"ok/prefix-{prefixZeros}/total-{total}"
            (runSdCntLead0Direct #[.slice s])
            #[intV (Int.ofNat expected)] }
    ,
    { name := "unit/direct/partial-cursor-and-refs"
      run := do
        let baseCell : Cell :=
          Cell.mkOrdinary
            #[true, true, false, false, false, true, false, false, false, true, false, true, false, false, true, true]
            #[refLeafA, refLeafB]
        let partialA : Slice := { cell := baseCell, bitPos := 2, refPos := 1 }
        let partialB : Slice := { cell := baseCell, bitPos := 5, refPos := 0 }

        expectOkStack "ok/partial-a"
          (runSdCntLead0Direct #[.slice partialA])
          #[intV (expectedLead0 partialA)]
        expectOkStack "ok/partial-b"
          (runSdCntLead0Direct #[.slice partialB])
          #[intV (expectedLead0 partialB)]

        let tailCell : Cell := Cell.mkOrdinary (stripeBits 24 1 ++ zeros 4) #[refLeafA]
        let partialTail : Slice := { cell := tailCell, bitPos := 24, refPos := 0 }
        expectOkStack "ok/partial-tail-all-zero"
          (runSdCntLead0Direct #[.slice partialTail])
          #[intV (expectedLead0 partialTail)]

        expectOkStack "ok/deep-stack-preserved"
          (runSdCntLead0Direct #[.null, intV 77, .slice partialA])
          #[.null, intV 77, intV (expectedLead0 partialA)] }
    ,
    { name := "unit/direct/errors-underflow-type"
      run := do
        expectErr "underflow/empty"
          (runSdCntLead0Direct #[]) .stkUnd
        expectErr "type/top-null"
          (runSdCntLead0Direct #[.null]) .typeChk
        expectErr "type/top-int"
          (runSdCntLead0Direct #[intV 0]) .typeChk
        expectErr "type/top-cell"
          (runSdCntLead0Direct #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runSdCntLead0Direct #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runSdCntLead0Direct #[.slice (mkPrefixZeroSlice 2 8), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [sdCntLead0Instr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdcntlead0 failed: {e}")
        if assembled.bits = natToBits sdCntLead0Opcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcntlead0: expected 0xc710, got bits {assembled.bits}")
        if assembled.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdcntlead0: expected 16 bits, got {assembled.bits.size}")

        let dec0 := Slice.ofCell assembled
        let dec1 ← expectDecodeStep "decode/assembled-sdcntlead0" dec0 sdCntLead0Instr 16
        if dec1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/assembled-sdcntlead0: expected exhausted slice, got {dec1.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits sdPsfxRevOpcode 16 ++
          natToBits sdCntLead0Opcode 16 ++
          natToBits sdCntLead1Opcode 16 ++
          natToBits sdCntTrail0Opcode 16 ++
          natToBits sdCntTrail1Opcode 16 ++
          addCell.bits
        let s0 := mkSliceFromBits rawBits
        let s1 ← expectDecodeStep "decode/raw-neighbor-sdpsfxrev" s0 (.cellOp .sdPsfxRev) 16
        let s2 ← expectDecodeStep "decode/raw-sdcntlead0" s1 sdCntLead0Instr 16
        let s3 ← expectDecodeStep "decode/raw-neighbor-sdcntlead1" s2 (.cellOp .sdCntLead1) 16
        let s4 ← expectDecodeStep "decode/raw-neighbor-sdcnttrail0" s3 .sdCntTrail0 16
        let s5 ← expectDecodeStep "decode/raw-neighbor-sdcnttrail1" s4 (.cellOp .sdCntTrail1) 16
        let s6 ← expectDecodeStep "decode/raw-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        match decodeCp0WithBits (mkSliceFromBits (natToBits sdCntLead0Opcode 15)) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/truncated: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-sdcntlead0-falls-through"
      run := do
        let sNeighbor := mkSliceWithBitsRefs (zeros 8)
        expectOkStack "dispatch/non-cell-instr"
          (runSdCntLead0DispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdcnttrail0-neighbor"
          (runSdCntLead0DispatchFallback .sdCntTrail0 #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/sdcntlead1-neighbor"
          (runSdCntLead0DispatchFallback (.cellOp .sdCntLead1) #[.slice sNeighbor])
          #[.slice sNeighbor, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdCntLead0Case "ok/len0-empty" #[.slice (mkPrefixZeroSlice 0 0)],
    mkSdCntLead0Case "ok/len1-zero" #[.slice (mkPrefixZeroSlice 1 1)],
    mkSdCntLead0Case "ok/len1-one" #[.slice (mkPrefixZeroSlice 0 1)],
    mkSdCntLead0Case "ok/len2-all-zero" #[.slice (mkPrefixZeroSlice 2 2)],
    mkSdCntLead0Case "ok/len2-prefix1" #[.slice (mkPrefixZeroSlice 1 2)],
    mkSdCntLead0Case "ok/len8-all-zero" #[.slice (mkPrefixZeroSlice 8 8)],
    mkSdCntLead0Case "ok/len8-prefix3" #[.slice (mkPrefixZeroSlice 3 8)],
    mkSdCntLead0Case "ok/len8-prefix0" #[.slice (mkPrefixZeroSlice 0 8)],
    mkSdCntLead0Case "ok/len16-prefix7" #[.slice (mkPrefixZeroSlice 7 16)],
    mkSdCntLead0Case "ok/len32-prefix1" #[.slice (mkPrefixZeroSlice 1 32)],
    mkSdCntLead0Case "ok/len64-prefix4-refs2"
      #[.slice (mkPrefixZeroSlice 4 64 #[refLeafA, refLeafB])],
    mkSdCntLead0Case "ok/len127-all-zero" #[.slice (mkPrefixZeroSlice 127 127)],
    mkSdCntLead0Case "ok/len255-all-zero" #[.slice (mkPrefixZeroSlice 255 255)],
    mkSdCntLead0Case "ok/len256-all-zero" #[.slice (mkPrefixZeroSlice 256 256)],
    mkSdCntLead0Case "ok/len1023-all-zero" #[.slice (mkPrefixZeroSlice 1023 1023)],
    mkSdCntLead0Case "ok/deep-stack-preserve"
      #[.null, intV 42, .slice (mkPrefixZeroSlice 5 16)],

    mkSdCntLead0Case "underflow/empty" #[],
    mkSdCntLead0Case "type/top-null" #[.null],
    mkSdCntLead0Case "type/top-int" #[intV 0],
    mkSdCntLead0Case "type/top-cell" #[.cell Cell.empty],
    mkSdCntLead0Case "type/top-builder" #[.builder Builder.empty],
    mkSdCntLead0Case "type/deep-top-not-slice" #[.slice (mkPrefixZeroSlice 3 8), .null],

    mkSdCntLead0Case "gas/exact-cost-succeeds"
      #[.slice (mkPrefixZeroSlice 6 32)]
      #[.pushInt (.num sdCntLead0SetGasExact), .tonEnvOp .setGasLimit, sdCntLead0Instr],
    mkSdCntLead0Case "gas/exact-minus-one-out-of-gas"
      #[.slice (mkPrefixZeroSlice 6 32)]
      #[.pushInt (.num sdCntLead0SetGasExactMinusOne), .tonEnvOp .setGasLimit, sdCntLead0Instr]
  ]
  fuzz := #[
    { seed := 2026021116
      count := 500
      gen := genSdCntLead0FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDCNTLEAD0
