import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDPFX

/-
SDPFX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdPfx.lean` (`.sdPfx`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc708` decode to `.sdPfx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdPfx` encode to `0xc708`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_bin_cs_cmp`, opcode registration for `SDPFX`)

Branch map used for this suite:
- dispatch guard (`.sdPfx` vs fallback-to-`next`);
- stack errors across the two `popSlice` calls (underflow/type ordering);
- core predicate: `prefBits` is a prefix of `sBits` (including equality and empty prefix);
- non-prefix outcomes (length mismatch and bit mismatch);
- opcode encode/decode boundary around neighbors `0xc705/0xc708/0xc709/0xc70a`.

Semantic intent checked here:
- stack order is `... pref s` (top is `s`);
- comparison uses remaining bits only (refs ignored);
- result is pushed as TVM bool smallint (`-1` true, `0` false).
-/

private def sdpfxId : InstrId := { name := "SDPFX" }

private def sdpfxInstr : Instr := .sdPfx

private def sdpfxWord : Nat := 0xc708

private def dispatchSentinel : Int := 708

private def mkSdpfxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdpfxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdpfxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdpfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdPfx sdpfxInstr stack

private def runSdpfxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdPfx instr (VM.push (intV dispatchSentinel)) stack

private def mkWordSlice
    (bits : Nat)
    (word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def mkStripedSlice
    (bits : Nat)
    (phase : Nat := 0)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def emptySlice : Slice := mkSliceWithBitsRefs #[]
private def pref5 : Slice := mkWordSlice 5 0x15
private def target8FromPref5 : Slice := mkWordSlice 8 0xad
private def equal8A5 : Slice := mkWordSlice 8 0xa5
private def prefix255 : Slice := mkStripedSlice 255 1
private def target256FromPrefix255 : Slice := mkStripedSlice 255 1 #[true]
private def prefix256 : Slice := mkStripedSlice 256 0
private def target255 : Slice := mkStripedSlice 255 0
private def prefix33 : Slice := mkStripedSlice 33 1
private def target32 : Slice := mkStripedSlice 32 1
private def prefix32 : Slice := mkStripedSlice 32 0
private def target64FromPrefix32 : Slice := mkStripedSlice 32 0 tailBits11

private def pref8WithRefs : Slice := mkWordSlice 8 0xa5 #[] #[refLeafA, refLeafB]
private def target8WithRefs : Slice := mkWordSlice 8 0xa5 #[] #[refLeafC]

private def cursorPrefCell : Cell := Cell.mkOrdinary (tailBits3 ++ stripeBits 11 0) #[refLeafA, refLeafB]
private def cursorTargetCell : Cell := Cell.mkOrdinary (tailBits5 ++ stripeBits 11 0 ++ tailBits7) #[refLeafC]
private def cursorMismatchTargetCell : Cell :=
  Cell.mkOrdinary (tailBits5 ++ stripeBits 11 1 ++ tailBits7) #[refLeafA, refLeafC]

private def cursorPref : Slice :=
  { cell := cursorPrefCell, bitPos := tailBits3.size, refPos := 1 }

private def cursorTarget : Slice :=
  { cell := cursorTargetCell, bitPos := tailBits5.size, refPos := 1 }

private def cursorTargetMismatch : Slice :=
  { cell := cursorMismatchTargetCell, bitPos := tailBits5.size, refPos := 1 }

private def sdpfxSetGasExact : Int :=
  computeExactGasBudget sdpfxInstr

private def sdpfxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdpfxInstr

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

private def genSdpfxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (targetLen, rng2) := pickBitsMixed rng1
    let (targetBits, rng3) := randBitString targetLen rng2
    let (prefLen, rng4) := randNat rng3 0 targetLen
    let prefBits := targetBits.extract 0 prefLen
    let (prefRefs, rng5) := pickRefsMixed rng4
    let (targetRefs, rng6) := pickRefsMixed rng5
    let pref := mkSliceWithBitsRefs prefBits (refsByCount prefRefs)
    let target := mkSliceWithBitsRefs targetBits (refsByCount targetRefs)
    (mkSdpfxCase "fuzz/ok/prefix" #[.slice pref, .slice target], rng6)
  else if shape = 1 then
    let (targetLen, rng2) := pickBitsMixed rng1
    let (targetBits, rng3) := randBitString targetLen rng2
    if targetLen = 0 then
      (mkSdpfxCase "fuzz/fail/empty-target-nonempty-pref"
        #[.slice (mkSliceWithBitsRefs #[true]), .slice (mkSliceWithBitsRefs #[])], rng3)
    else
      let (prefLen, rng4) := randNat rng3 1 targetLen
      let prefBits := flipHeadBit (targetBits.extract 0 prefLen)
      let (prefRefs, rng5) := pickRefsMixed rng4
      let (targetRefs, rng6) := pickRefsMixed rng5
      let pref := mkSliceWithBitsRefs prefBits (refsByCount prefRefs)
      let target := mkSliceWithBitsRefs targetBits (refsByCount targetRefs)
      (mkSdpfxCase "fuzz/fail/mismatch" #[.slice pref, .slice target], rng6)
  else if shape = 2 then
    let (targetLen, rng2) := randNat rng1 0 128
    let (targetBits, rng3) := randBitString targetLen rng2
    let (prefExtra, rng4) := randNat rng3 1 16
    let prefBits := targetBits ++ #[true] ++ stripeBits (prefExtra - 1) 0
    let pref := mkSliceWithBitsRefs prefBits
    let target := mkSliceWithBitsRefs targetBits
    (mkSdpfxCase "fuzz/fail/pref-longer" #[.slice pref, .slice target], rng4)
  else if shape = 3 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkSdpfxCase "fuzz/underflow/one" #[noise], rng2)
  else if shape = 4 then
    (mkSdpfxCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdpfxCase "fuzz/type/top" #[.slice equal8A5, bad], rng2)
  else if shape = 6 then
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdpfxCase "fuzz/type/second" #[bad, .slice equal8A5], rng2)
  else
    let (noise, rng2) := pickNoiseValue rng1
    let (targetBits, rng3) := randBitString 16 rng2
    let prefBits := targetBits.extract 0 5
    let pref := mkSliceWithBitsRefs prefBits
    let target := mkSliceWithBitsRefs targetBits
    (mkSdpfxCase "fuzz/ok/deep" #[noise, .slice pref, .slice target], rng3)

def suite : InstrSuite where
  id := { name := "SDPFX" }
  unit := #[
    { name := "unit/direct/prefix-truth-table"
      run := do
        let checks : Array (String × Slice × Slice × Int) :=
          #[
            ("ok/empty-vs-empty", emptySlice, emptySlice, -1),
            ("ok/empty-prefix-vs-nonempty", emptySlice, equal8A5, -1),
            ("ok/equal-8bits", equal8A5, equal8A5, -1),
            ("ok/proper-prefix-1-of-8", mkWordSlice 1 1, equal8A5, -1),
            ("ok/proper-prefix-7-of-8", mkWordSlice 7 0x52, equal8A5, -1),
            ("fail/mismatch-first-bit", mkWordSlice 8 0x80, mkWordSlice 8 0x00, 0),
            ("fail/mismatch-middle-bit", mkWordSlice 8 0xac, mkWordSlice 8 0xa4, 0),
            ("fail/mismatch-last-bit", mkWordSlice 8 0xfe, mkWordSlice 8 0xff, 0),
            ("fail/target-shorter-by-1", mkStripedSlice 9 0, mkStripedSlice 8 0, 0),
            ("ok/prefix-255-of-256", prefix255, target256FromPrefix255, -1)
          ]
        for (label, pref, s, expected) in checks do
          expectOkStack label
            (runSdpfxDirect #[.slice pref, .slice s])
            #[intV expected] }
    ,
    { name := "unit/direct/order-refs-cursor-and-deep-stack"
      run := do
        expectOkStack "ok/refs-ignored-equal-bits"
          (runSdpfxDirect #[.slice pref8WithRefs, .slice equal8A5])
          #[intV (-1)]

        expectOkStack "ok/refs-ignored-target-side"
          (runSdpfxDirect #[.slice pref5, .slice (mkWordSlice 8 0xad #[] #[refLeafA, refLeafC])])
          #[intV (-1)]

        expectOkStack "ok/cursor-prefix"
          (runSdpfxDirect #[.slice cursorPref, .slice cursorTarget])
          #[intV (-1)]

        expectOkStack "fail/cursor-prefix-mismatch"
          (runSdpfxDirect #[.slice cursorPref, .slice cursorTargetMismatch])
          #[intV 0]

        expectOkStack "ok/stack-order-pref-then-s"
          (runSdpfxDirect #[.slice pref5, .slice target8FromPref5])
          #[intV (-1)]

        expectOkStack "fail/stack-order-reversed"
          (runSdpfxDirect #[.slice target8FromPref5, .slice pref5])
          #[intV 0]

        expectOkStack "ok/deep-stack-preserved"
          (runSdpfxDirect #[.null, intV 17, .slice pref5, .slice target8FromPref5])
          #[.null, intV 17, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-ordering"
      run := do
        expectErr "underflow/empty"
          (runSdpfxDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdpfxDirect #[.slice equal8A5]) .stkUnd
        expectErr "type/one-non-slice"
          (runSdpfxDirect #[.null]) .typeChk

        expectErr "type/top-null"
          (runSdpfxDirect #[.slice equal8A5, .null]) .typeChk
        expectErr "type/top-int"
          (runSdpfxDirect #[.slice equal8A5, intV 7]) .typeChk
        expectErr "type/top-cell"
          (runSdpfxDirect #[.slice equal8A5, .cell Cell.empty]) .typeChk
        expectErr "type/second-not-slice"
          (runSdpfxDirect #[.null, .slice equal8A5]) .typeChk
        expectErr "type/second-int-not-slice"
          (runSdpfxDirect #[intV (-3), .slice equal8A5]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let singleCode ←
          match assembleCp0 [sdpfxInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdpfx failed: {e}")
        if singleCode.bits = natToBits sdpfxWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdpfx: expected 0xc708, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdpfx: expected 16 bits, got {singleCode.bits.size}")

        let asmProgram : Array Instr := #[.sdEq, sdpfxInstr, .sdPfxRev, .sdPpfx, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-sdeq" a0 .sdEq 16
        let a2 ← expectDecodeStep "decode/asm-sdpfx" a1 sdpfxInstr 16
        let a3 ← expectDecodeStep "decode/asm-sdpfxrev" a2 .sdPfxRev 16
        let a4 ← expectDecodeStep "decode/asm-sdppfx" a3 .sdPpfx 16
        let a5 ← expectDecodeStep "decode/asm-tail-add" a4 .add 8
        if a5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {a5.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xc705 16 ++
          natToBits sdpfxWord 16 ++
          natToBits 0xc709 16 ++
          natToBits 0xc70a 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdeq-neighbor" r0 .sdEq 16
        let r2 ← expectDecodeStep "decode/raw-sdpfx" r1 sdpfxInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdpfxrev-neighbor" r2 .sdPfxRev 16
        let r4 ← expectDecodeStep "decode/raw-sdppfx-neighbor" r3 .sdPpfx 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdpfx-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runSdpfxDispatchFallback .add #[.null, intV 1])
          #[.null, intV 1, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdpfxCase "ok/empty-prefix-empty-target"
      #[.slice emptySlice, .slice emptySlice],
    mkSdpfxCase "ok/empty-prefix-nonempty-target"
      #[.slice emptySlice, .slice equal8A5],
    mkSdpfxCase "ok/equal-8bits"
      #[.slice equal8A5, .slice equal8A5],
    mkSdpfxCase "ok/proper-prefix-1-of-8"
      #[.slice (mkWordSlice 1 1), .slice equal8A5],
    mkSdpfxCase "ok/proper-prefix-7-of-8"
      #[.slice (mkWordSlice 7 0x52), .slice equal8A5],
    mkSdpfxCase "ok/prefix-32-of-64"
      #[.slice prefix32, .slice target64FromPrefix32],
    mkSdpfxCase "ok/prefix-255-of-256"
      #[.slice prefix255, .slice target256FromPrefix255],
    mkSdpfxCase "ok/refs-ignored-prefix-side"
      #[.slice pref8WithRefs, .slice equal8A5],
    mkSdpfxCase "ok/refs-ignored-target-side"
      #[.slice equal8A5, .slice target8WithRefs],
    mkSdpfxCase "ok/deep-stack-preserve-null"
      #[.null, .slice pref5, .slice target8FromPref5],
    mkSdpfxCase "ok/deep-stack-preserve-null-int"
      #[.null, intV 77, .slice pref5, .slice target8FromPref5],

    mkSdpfxCase "fail/nonempty-prefix-empty-target"
      #[.slice pref5, .slice emptySlice],
    mkSdpfxCase "fail/mismatch-first-bit"
      #[.slice (mkWordSlice 8 0x80), .slice (mkWordSlice 8 0x00)],
    mkSdpfxCase "fail/mismatch-middle-bit"
      #[.slice (mkWordSlice 8 0xac), .slice (mkWordSlice 8 0xa4)],
    mkSdpfxCase "fail/mismatch-last-bit"
      #[.slice (mkWordSlice 8 0xfe), .slice (mkWordSlice 8 0xff)],
    mkSdpfxCase "fail/target-shorter-by-1"
      #[.slice prefix256, .slice target255],
    mkSdpfxCase "fail/prefix-33-vs-target-32"
      #[.slice prefix33, .slice target32],
    mkSdpfxCase "fail/reversed-order-not-prefix"
      #[.slice target8FromPref5, .slice pref5],

    mkSdpfxCase "underflow/empty"
      #[],
    mkSdpfxCase "underflow/one-slice"
      #[.slice equal8A5],
    mkSdpfxCase "type/top-null"
      #[.slice equal8A5, .null],
    mkSdpfxCase "type/top-int"
      #[.slice equal8A5, intV (-9)],
    mkSdpfxCase "type/second-not-slice"
      #[.null, .slice equal8A5],

    mkSdpfxCase "gas/exact-cost-succeeds"
      #[.slice pref5, .slice target8FromPref5]
      #[.pushInt (.num sdpfxSetGasExact), .tonEnvOp .setGasLimit, sdpfxInstr],
    mkSdpfxCase "gas/exact-minus-one-out-of-gas"
      #[.slice pref5, .slice target8FromPref5]
      #[.pushInt (.num sdpfxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdpfxInstr]
  ]
  fuzz := #[
    { seed := 2026021120
      count := 500
      gen := genSdpfxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDPFX
