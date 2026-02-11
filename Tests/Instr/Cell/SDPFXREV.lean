import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDPFXREV

/-
SDPFXREV branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdPfxRev.lean` (`.sdPfxRev`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc709` decode to `.sdPfxRev`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdPfxRev` encodes to `0xc709`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_bin_cs_cmp`, registration `SDPFXREV` as `cs2->is_prefix_of(*cs1)`)

Branch map used for this suite:
- dispatch fallthrough for non-`.sdPfxRev` instructions;
- stack pop order: top is `pref`, next is `s` (underflow/type outcomes on each pop);
- success/failure branch: `s.haveBits(prefLen)` + bit-prefix equality;
- bit-only semantics: references are ignored by prefix comparison;
- fixed-width opcode decode/encode boundary at `0xc709` (neighbors `0xc708`, `0xc70a`, `0xc70b`).
-/

private def sdPfxRevId : InstrId := { name := "SDPFXREV" }

private def dispatchSentinel : Int := 619

private def sdPfxRevInstr : Instr := .sdPfxRev
private def sdPfxInstr : Instr := .sdPfx

private def sdPfxWord : Nat := 0xc708
private def sdPfxRevWord : Nat := 0xc709
private def sdPpfxWord : Nat := 0xc70a
private def sdPpfxRevWord : Nat := 0xc70b

private def mkSdPfxRevCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdPfxRevInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdPfxRevId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdPfxRevDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPfxRev sdPfxRevInstr stack

private def runSdPfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPfx sdPfxInstr stack

private def runSdPfxRevDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdPfxRev instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok lv, .ok rv => lv == rv
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got lhs={reprStr lhs}, rhs={reprStr rhs}")

private def mkFullSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def bitsS6 : BitString := natToBits 0x2d 6
private def bitsS6Alt : BitString := natToBits 0x2c 6
private def bitsPref3 : BitString := natToBits 0x5 3
private def bitsPref3Mismatch : BitString := natToBits 0x4 3
private def bitsS4 : BitString := natToBits 0xb 4
private def bitsS8A : BitString := natToBits 0xd6 8
private def bitsS8B : BitString := natToBits 0xaa 8
private def bitsPref6A : BitString := natToBits 0x35 6
private def bitsPref6Mismatch : BitString := natToBits 0x34 6
private def bitsPref6MidMismatch : BitString := natToBits 0x2b 6
private def bitsS8LastDiffA : BitString := natToBits 0xcc 8
private def bitsS8LastDiffB : BitString := natToBits 0xcd 8
private def bits64 : BitString := stripeBits 64 1
private def bits255 : BitString := stripeBits 255 0
private def bits256 : BitString := stripeBits 256 0
private def bitsPref128From256 : BitString := bits256.extract 0 128

private def sliceS6 : Slice := mkFullSlice bitsS6
private def sliceS6Alt : Slice := mkFullSlice bitsS6Alt
private def slicePref3 : Slice := mkFullSlice bitsPref3
private def slicePref3Mismatch : Slice := mkFullSlice bitsPref3Mismatch
private def sliceS4 : Slice := mkFullSlice bitsS4
private def slicePref6Long : Slice := mkFullSlice bitsS6
private def sliceSEmpty : Slice := mkFullSlice #[]
private def sliceS8A : Slice := mkFullSlice bitsS8A
private def sliceS8B : Slice := mkFullSlice bitsS8B
private def slicePref6A : Slice := mkFullSlice bitsPref6A
private def slicePref6Mismatch : Slice := mkFullSlice bitsPref6Mismatch
private def slicePref6MidMismatch : Slice := mkFullSlice bitsPref6MidMismatch
private def sliceS8LastDiffA : Slice := mkFullSlice bitsS8LastDiffA
private def sliceS8LastDiffB : Slice := mkFullSlice bitsS8LastDiffB
private def slice64 : Slice := mkFullSlice bits64
private def slice255 : Slice := mkFullSlice bits255
private def slice256 : Slice := mkFullSlice bits256
private def slicePref128From256 : Slice := mkFullSlice bitsPref128From256
private def sliceS256WithRef : Slice := mkFullSlice bits256 #[refLeafA]
private def slicePref128WithRefs : Slice := mkFullSlice bitsPref128From256 #[refLeafB, refLeafC]
private def sliceS8Refs : Slice := mkFullSlice bitsS8A #[refLeafA]
private def slicePref6Refs : Slice := mkFullSlice bitsPref6A #[refLeafB, refLeafC]
private def slicePref6RefsMismatch : Slice := mkFullSlice bitsPref6Mismatch #[refLeafC]

private def cursorCellS : Cell := Cell.mkOrdinary (natToBits 851 10) #[refLeafA, refLeafB]
private def cursorCellPrefMatch : Cell := Cell.mkOrdinary (natToBits 5 5) #[refLeafC]
private def cursorCellPrefMismatch : Cell := Cell.mkOrdinary (natToBits 7 5) #[refLeafC]

private def cursorSliceS : Slice := { cell := cursorCellS, bitPos := 2, refPos := 1 }
private def cursorSlicePrefMatch : Slice := { cell := cursorCellPrefMatch, bitPos := 1, refPos := 0 }
private def cursorSlicePrefMismatch : Slice := { cell := cursorCellPrefMismatch, bitPos := 1, refPos := 0 }

private def sdPfxRevSetGasExact : Int :=
  computeExactGasBudget sdPfxRevInstr

private def sdPfxRevSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdPfxRevInstr

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

private def flipHeadBit (bs : BitString) : BitString :=
  if bs.isEmpty then
    bs
  else
    let b0 := (bs[0]?).getD false
    #[!b0] ++ bs.extract 1 bs.size

private def genSdPfxRevFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (sLen, rng2) := pickBitsMixed rng1
    let (sBits, rng3) := randBitString sLen rng2
    let (prefLen, rng4) := randNat rng3 0 sLen
    let prefBits := sBits.extract 0 prefLen
    let (sRefs, rng5) := pickRefsMixed rng4
    let (prefRefs, rng6) := pickRefsMixed rng5
    let s := mkFullSlice sBits (refsByCount sRefs)
    let pref := mkFullSlice prefBits (refsByCount prefRefs)
    (mkSdPfxRevCase "fuzz/ok/prefix" #[.slice s, .slice pref], rng6)
  else if shape = 1 then
    let (sLen, rng2) := pickBitsMixed rng1
    let (sBits, rng3) := randBitString sLen rng2
    if sLen = 0 then
      (mkSdPfxRevCase "fuzz/fail/empty-s-nonempty-pref"
        #[.slice (mkFullSlice #[]), .slice (mkFullSlice #[true])], rng3)
    else
      let (prefLen, rng4) := randNat rng3 1 sLen
      let prefBits := flipHeadBit (sBits.extract 0 prefLen)
      let (sRefs, rng5) := pickRefsMixed rng4
      let (prefRefs, rng6) := pickRefsMixed rng5
      let s := mkFullSlice sBits (refsByCount sRefs)
      let pref := mkFullSlice prefBits (refsByCount prefRefs)
      (mkSdPfxRevCase "fuzz/fail/mismatch" #[.slice s, .slice pref], rng6)
  else if shape = 2 then
    let (sLen, rng2) := randNat rng1 0 128
    let (sBits, rng3) := randBitString sLen rng2
    let (extra, rng4) := randNat rng3 1 16
    let prefBits := sBits ++ #[true] ++ stripeBits (extra - 1) 1
    (mkSdPfxRevCase "fuzz/fail/pref-longer"
      #[.slice (mkFullSlice sBits), .slice (mkFullSlice prefBits)], rng4)
  else if shape = 3 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkSdPfxRevCase "fuzz/underflow/one" #[noise], rng2)
  else if shape = 4 then
    (mkSdPfxRevCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdPfxRevCase "fuzz/type/top" #[.slice sliceS6, bad], rng2)
  else if shape = 6 then
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdPfxRevCase "fuzz/type/second" #[bad, .slice slicePref3], rng2)
  else
    let (noise, rng2) := pickNoiseValue rng1
    (mkSdPfxRevCase "fuzz/ok/deep" #[noise, .slice sliceS6, .slice slicePref3], rng2)

def suite : InstrSuite where
  id := sdPfxRevId
  unit := #[
    { name := "unit/direct/success-equal-and-proper-prefix"
      run := do
        expectOkStack "ok/equal-6"
          (runSdPfxRevDirect #[.slice sliceS6, .slice sliceS6])
          #[intV (-1)]
        expectOkStack "ok/proper-prefix-3-of-6"
          (runSdPfxRevDirect #[.slice sliceS6, .slice slicePref3])
          #[intV (-1)]
        expectOkStack "ok/prefix-128-of-256"
          (runSdPfxRevDirect #[.slice sliceS256WithRef, .slice slicePref128WithRefs])
          #[intV (-1)] }
    ,
    { name := "unit/direct/success-empty-prefix-cases"
      run := do
        expectOkStack "ok/empty-prefix-nonempty-s"
          (runSdPfxRevDirect #[.slice sliceS6, .slice sliceSEmpty])
          #[intV (-1)]
        expectOkStack "ok/both-empty"
          (runSdPfxRevDirect #[.slice sliceSEmpty, .slice sliceSEmpty])
          #[intV (-1)] }
    ,
    { name := "unit/direct/failure-length-and-mismatch-cases"
      run := do
        expectOkStack "false/prefix-longer-than-s"
          (runSdPfxRevDirect #[.slice sliceS4, .slice slicePref6Long])
          #[intV 0]
        expectOkStack "false/mismatch-first-bit"
          (runSdPfxRevDirect #[.slice sliceS6, .slice slicePref3Mismatch])
          #[intV 0]
        expectOkStack "false/mismatch-mid"
          (runSdPfxRevDirect #[.slice sliceS8B, .slice slicePref6MidMismatch])
          #[intV 0]
        expectOkStack "false/same-length-different-last-bit"
          (runSdPfxRevDirect #[.slice sliceS8LastDiffA, .slice sliceS8LastDiffB])
          #[intV 0] }
    ,
    { name := "unit/direct/refs-ignored-bit-only-semantics"
      run := do
        expectOkStack "ok/refs-ignored-match"
          (runSdPfxRevDirect #[.slice sliceS8Refs, .slice slicePref6Refs])
          #[intV (-1)]
        expectOkStack "false/refs-ignored-mismatch"
          (runSdPfxRevDirect #[.slice sliceS8Refs, .slice slicePref6RefsMismatch])
          #[intV 0] }
    ,
    { name := "unit/direct/cursor-bitpos-window-used"
      run := do
        expectOkStack "ok/cursor-match"
          (runSdPfxRevDirect #[.slice cursorSliceS, .slice cursorSlicePrefMatch])
          #[intV (-1)]
        expectOkStack "false/cursor-mismatch"
          (runSdPfxRevDirect #[.slice cursorSliceS, .slice cursorSlicePrefMismatch])
          #[intV 0] }
    ,
    { name := "unit/direct/deep-stack-preserved"
      run := do
        expectOkStack "ok/deep-preserve"
          (runSdPfxRevDirect #[.null, intV 77, .slice sliceS6, .slice slicePref3])
          #[.null, intV 77, intV (-1)]
        expectOkStack "false/deep-preserve"
          (runSdPfxRevDirect #[.null, intV 77, .slice sliceS6Alt, .slice slicePref3Mismatch])
          #[.null, intV 77, intV 0] }
    ,
    { name := "unit/direct/reversed-operand-equivalence-with-sdpfx"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("align/equal-6", sliceS6, sliceS6),
            ("align/proper-prefix-3-of-6", sliceS6, slicePref3),
            ("align/mismatch-3", sliceS6, slicePref3Mismatch),
            ("align/long-128-of-256", sliceS256WithRef, slicePref128WithRefs),
            ("align/prefix-longer", sliceS4, slicePref6Long),
            ("align/empty-prefix", sliceS6, sliceSEmpty),
            ("align/both-empty", sliceSEmpty, sliceSEmpty),
            ("align/refs-match", sliceS8Refs, slicePref6Refs),
            ("align/refs-mismatch", sliceS8Refs, slicePref6RefsMismatch)
          ]
        for (label, s, pref) in checks do
          expectSameOutcome label
            (runSdPfxRevDirect #[.slice s, .slice pref])
            (runSdPfxDirect #[.slice pref, .slice s]) }
    ,
    { name := "unit/direct/underflow-and-type-ordering"
      run := do
        expectErr "underflow/empty"
          (runSdPfxRevDirect #[]) .stkUnd
        expectErr "underflow/one-item"
          (runSdPfxRevDirect #[.slice slicePref3]) .stkUnd
        expectErr "type/top-not-slice"
          (runSdPfxRevDirect #[.slice sliceS6, .null]) .typeChk
        expectErr "type/second-not-slice"
          (runSdPfxRevDirect #[.null, .slice slicePref3]) .typeChk }
    ,
    { name := "unit/opcode/decode-assemble-and-dispatch"
      run := do
        let assembled ←
          match assembleCp0 [sdPfxRevInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdpfxrev failed: {e}")
        if assembled.refs.isEmpty && assembled.bits == natToBits sdPfxRevWord 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/sdpfxrev expected bits={reprStr (natToBits sdPfxRevWord 16)} refs=0, got bits={reprStr assembled.bits} refs={assembled.refs.size}")

        let s0 := mkSliceFromBits
          (natToBits sdPfxWord 16 ++ natToBits sdPfxRevWord 16 ++
            natToBits sdPpfxWord 16 ++ natToBits sdPpfxRevWord 16)
        let s1 ← expectDecodeStep "decode/sdpfx" s0 .sdPfx 16
        let s2 ← expectDecodeStep "decode/sdpfxrev" s1 .sdPfxRev 16
        let s3 ← expectDecodeStep "decode/sdppfx" s2 .sdPpfx 16
        let s4 ← expectDecodeStep "decode/sdppfxrev" s3 .sdPpfxRev 16
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end expected exhausted slice, got {s4.bitsRemaining} bits")

        expectOkStack "dispatch/non-matching-opcode-add"
          (runSdPfxRevDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-matching-opcode-sdpfx"
          (runSdPfxRevDispatchFallback .sdPfx #[.null])
          #[.null, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdPfxRevCase "ok/equal-6"
      #[.slice sliceS6, .slice sliceS6],
    mkSdPfxRevCase "ok/proper-prefix-3-of-6"
      #[.slice sliceS6, .slice slicePref3],
    mkSdPfxRevCase "ok/empty-prefix-nonempty-s"
      #[.slice sliceS6, .slice sliceSEmpty],
    mkSdPfxRevCase "ok/both-empty"
      #[.slice sliceSEmpty, .slice sliceSEmpty],
    mkSdPfxRevCase "ok/long-128-of-256"
      #[.slice sliceS256WithRef, .slice slicePref128WithRefs],
    mkSdPfxRevCase "ok/refs-ignored-match"
      #[.slice sliceS8Refs, .slice slicePref6Refs],
    mkSdPfxRevCase "ok/deep-stack-preserved"
      #[.null, intV 42, .slice sliceS6, .slice slicePref3],
    mkSdPfxRevCase "ok/equal-64"
      #[.slice slice64, .slice slice64],

    mkSdPfxRevCase "false/prefix-longer-than-s"
      #[.slice sliceS4, .slice slicePref6Long],
    mkSdPfxRevCase "false/mismatch-first-bit"
      #[.slice sliceS6, .slice slicePref3Mismatch],
    mkSdPfxRevCase "false/mismatch-mid"
      #[.slice sliceS8B, .slice slicePref6MidMismatch],
    mkSdPfxRevCase "false/nonempty-pref-empty-s"
      #[.slice sliceSEmpty, .slice slicePref3],
    mkSdPfxRevCase "false/refs-ignored-mismatch"
      #[.slice sliceS8Refs, .slice slicePref6RefsMismatch],
    mkSdPfxRevCase "false/same-length-different-last-bit"
      #[.slice sliceS8LastDiffA, .slice sliceS8LastDiffB],
    mkSdPfxRevCase "false/prefix-256-over-255"
      #[.slice slice255, .slice slice256],

    mkSdPfxRevCase "underflow/empty" #[],
    mkSdPfxRevCase "underflow/one-item"
      #[.slice slicePref3],
    mkSdPfxRevCase "type/top-not-slice"
      #[.slice sliceS6, .null],
    mkSdPfxRevCase "type/second-not-slice"
      #[.null, .slice slicePref3],

    mkSdPfxRevCase "gas/exact-cost-succeeds"
      #[.slice sliceS6, .slice slicePref3]
      #[.pushInt (.num sdPfxRevSetGasExact), .tonEnvOp .setGasLimit, sdPfxRevInstr],
    mkSdPfxRevCase "gas/exact-minus-one-out-of-gas"
      #[.slice sliceS6, .slice slicePref3]
      #[.pushInt (.num sdPfxRevSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdPfxRevInstr]
  ]
  fuzz := #[
    { seed := 2026021121
      count := 500
      gen := genSdPfxRevFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDPFXREV
