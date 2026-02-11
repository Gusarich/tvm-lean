import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDBEGINSXQ

/-
SDBEGINSXQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdBeginsX.lean` (`.sdBeginsX quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xd726 = SDBEGINSX`, `0xd727 = SDBEGINSXQ`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode of `0xd726/0xd727`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_begins_with`, `exec_slice_begins_with_common`)

Branch map for this suite (`SDBEGINSXQ` = quiet=true):
- dispatch guard: only `.sdBeginsX true` executes this handler;
- stack pop order is `pref` (top) then `s` (second), so type/underflow order matters;
- core predicate uses bits only: `s` begins with `pref` over remaining cursor bits;
- quiet success pushes `[s advanced by prefLen, -1]`;
- quiet failure pushes `[original s, 0]` (no `.cellUnd`);
- opcode/decode boundary at fixed 16-bit words `0xd726` and `0xd727`.
-/

private def sdbeginsxqId : InstrId := { name := "SDBEGINSXQ" }

private def sdbeginsxInstr : Instr := .sdBeginsX false
private def sdbeginsxqInstr : Instr := .sdBeginsX true

private def sdbeginsxWord : Nat := 0xd726
private def sdbeginsxqWord : Nat := 0xd727
private def xctosWord : Nat := 0xd739

private def dispatchSentinel : Int := 727

private def mkSdbeginsxqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdbeginsxqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdbeginsxqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdbeginsxDirect (quiet : Bool) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdBeginsX (.sdBeginsX quiet) stack

private def runSdbeginsxqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runSdbeginsxDirect true stack

private def runSdbeginsxqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdBeginsX instr (VM.push (intV dispatchSentinel)) stack

private def mkFullSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def bits8A5 : BitString := natToBits 0xa5 8
private def bits8A4 : BitString := natToBits 0xa4 8
private def bits64Phase1 : BitString := stripeBits 64 1
private def bits256Phase0 : BitString := stripeBits 256 0

private def prefBits1A5 : BitString := bits8A5.extract 0 1
private def prefBits5A5 : BitString := bits8A5.extract 0 5
private def prefBits7A5 : BitString := bits8A5.extract 0 7
private def prefBits32Phase1 : BitString := bits64Phase1.extract 0 32
private def prefBits255Phase0 : BitString := bits256Phase0.extract 0 255

private def prefix1Zero : Slice := mkFullSlice (natToBits 0 1)
private def prefix5MidMismatch : Slice := mkFullSlice (natToBits 0x10 5) -- differs from 0xa5[0:5]
private def prefix33Phase0 : Slice := mkFullSlice (stripeBits 33 0)

private def sliceEmpty : Slice := mkFullSlice #[]
private def slice8A5 : Slice := mkFullSlice bits8A5
private def slice8A4 : Slice := mkFullSlice bits8A4
private def slice7A5 : Slice := mkFullSlice prefBits7A5
private def slice32Phase0 : Slice := mkFullSlice (stripeBits 32 0)
private def slice64Phase1 : Slice := mkFullSlice bits64Phase1
private def slice256Phase0 : Slice := mkFullSlice bits256Phase0

private def prefixEmpty : Slice := sliceEmpty
private def prefix1A5 : Slice := mkFullSlice prefBits1A5
private def prefix5A5 : Slice := mkFullSlice prefBits5A5
private def prefix7A5 : Slice := mkFullSlice prefBits7A5
private def prefix8A5 : Slice := slice8A5
private def prefix32Phase1 : Slice := mkFullSlice prefBits32Phase1
private def prefix255Phase0 : Slice := mkFullSlice prefBits255Phase0

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 11 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 2 2) #[]

private def slice8A5RefsA : Slice := mkFullSlice bits8A5 #[refLeafA]
private def slice8A5RefsBC : Slice := mkFullSlice bits8A5 #[refLeafB, refLeafC]
private def prefix5A5Refs : Slice := mkFullSlice prefBits5A5 #[refLeafA, refLeafB]

private def tailBits3 : BitString := natToBits 0x5 3
private def tailBits5 : BitString := natToBits 0x13 5

private def cursorTargetCell : Cell :=
  Cell.mkOrdinary (tailBits3 ++ stripeBits 10 1 ++ tailBits5) #[refLeafA, refLeafB]
private def cursorPrefixCell : Cell :=
  Cell.mkOrdinary (natToBits 0x3 2 ++ stripeBits 10 1) #[refLeafC]
private def cursorPrefixMismatchCell : Cell :=
  Cell.mkOrdinary (natToBits 0x3 2 ++ stripeBits 10 0) #[refLeafC]

private def cursorTarget : Slice :=
  { cell := cursorTargetCell, bitPos := tailBits3.size, refPos := 1 }
private def cursorPrefix : Slice :=
  { cell := cursorPrefixCell, bitPos := 2, refPos := 0 }
private def cursorPrefixMismatch : Slice :=
  { cell := cursorPrefixMismatchCell, bitPos := 2, refPos := 0 }

private def expectedQuietSuccessStack
    (below : Array Value)
    (s pref : Slice) : Array Value :=
  let prefBits := pref.readBits pref.bitsRemaining
  below ++ #[.slice (s.advanceBits prefBits.size), intV (-1)]

private def expectedQuietFailureStack
    (below : Array Value)
    (s : Slice) : Array Value :=
  below ++ #[.slice s, intV 0]

private def expectedNonQuietSuccessStack
    (below : Array Value)
    (s pref : Slice) : Array Value :=
  let prefBits := pref.readBits pref.bitsRemaining
  below ++ #[.slice (s.advanceBits prefBits.size)]

private def sdbeginsxqSetGasExact : Int :=
  computeExactGasBudget sdbeginsxqInstr

private def sdbeginsxqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdbeginsxqInstr

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

private def genSdbeginsxqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
    (mkSdbeginsxqCase "fuzz/ok/prefix" #[.slice s, .slice pref], rng6)
  else if shape = 1 then
    let (sLen0, rng2) := pickBitsMixed rng1
    let sLen : Nat := if sLen0 = 0 then 1 else sLen0
    let (sBits, rng3) := randBitString sLen rng2
    let (prefLen, rng4) := randNat rng3 1 sLen
    let prefBits := flipHeadBit (sBits.extract 0 prefLen)
    (mkSdbeginsxqCase "fuzz/fail/mismatch"
      #[.slice (mkFullSlice sBits), .slice (mkFullSlice prefBits)], rng4)
  else if shape = 2 then
    let (sLen, rng2) := randNat rng1 0 128
    let (sBits, rng3) := randBitString sLen rng2
    let prefBits := sBits ++ #[true]
    (mkSdbeginsxqCase "fuzz/fail/pref-longer"
      #[.slice (mkFullSlice sBits), .slice (mkFullSlice prefBits)], rng3)
  else if shape = 3 then
    let (noise, rng2) := pickNoiseValue rng1
    let (sLen, rng3) := pickBitsMixed rng2
    let (sBits, rng4) := randBitString sLen rng3
    let (prefLen, rng5) := randNat rng4 0 sLen
    let prefBits := sBits.extract 0 prefLen
    (mkSdbeginsxqCase "fuzz/ok/deep"
      #[noise, .slice (mkFullSlice sBits), .slice (mkFullSlice prefBits)], rng5)
  else if shape = 4 then
    (mkSdbeginsxqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkSdbeginsxqCase "fuzz/underflow/one" #[noise], rng2)
  else if shape = 6 then
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdbeginsxqCase "fuzz/type/top-pref" #[.slice slice8A5, bad], rng2)
  else
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdbeginsxqCase "fuzz/type/second-s" #[bad, .slice prefix5A5], rng2)

def suite : InstrSuite where
  id := { name := "SDBEGINSXQ" }
  unit := #[
    { name := "unit/direct/quiet-success-remainder-and-status"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("ok/empty-prefix-empty-target", sliceEmpty, prefixEmpty),
            ("ok/empty-prefix-nonempty-target", slice8A5, prefixEmpty),
            ("ok/equal-8bits", slice8A5, prefix8A5),
            ("ok/proper-prefix-1-of-8", slice8A5, prefix1A5),
            ("ok/proper-prefix-5-of-8", slice8A5, prefix5A5),
            ("ok/proper-prefix-7-of-8", slice8A5, prefix7A5),
            ("ok/prefix-255-of-256", slice256Phase0, prefix255Phase0)
          ]
        for (label, s, pref) in checks do
          expectOkStack label
            (runSdbeginsxqDirect #[.slice s, .slice pref])
            (expectedQuietSuccessStack #[] s pref)

        expectOkStack "ok/deep-stack-preserved"
          (runSdbeginsxqDirect #[.null, intV 73, .slice slice8A5, .slice prefix5A5])
          (expectedQuietSuccessStack #[.null, intV 73] slice8A5 prefix5A5) }
    ,
    { name := "unit/direct/quiet-failure-restores-original-and-status0"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("fail/mismatch-first-bit", slice8A5, prefix1Zero),
            ("fail/mismatch-middle-bit", slice8A5, prefix5MidMismatch),
            ("fail/mismatch-last-bit", slice8A5, slice8A4),
            ("fail/prefix-longer-than-target", slice7A5, prefix8A5),
            ("fail/reversed-order-stack", prefix5A5, slice8A5)
          ]
        for (label, s, pref) in checks do
          expectOkStack label
            (runSdbeginsxqDirect #[.slice s, .slice pref])
            (expectedQuietFailureStack #[] s)

        expectOkStack "fail/deep-stack-preserved"
          (runSdbeginsxqDirect #[intV 44, .slice slice8A5, .slice prefix1Zero])
          (expectedQuietFailureStack #[intV 44] slice8A5) }
    ,
    { name := "unit/direct/refs-ignored-and-cursor-window"
      run := do
        expectOkStack "ok/refs-ignored-prefix-side"
          (runSdbeginsxqDirect #[.slice slice8A5, .slice prefix5A5Refs])
          (expectedQuietSuccessStack #[] slice8A5 prefix5A5Refs)
        expectOkStack "ok/refs-ignored-target-side"
          (runSdbeginsxqDirect #[.slice slice8A5RefsA, .slice slice8A5RefsBC])
          (expectedQuietSuccessStack #[] slice8A5RefsA slice8A5RefsBC)
        expectOkStack "ok/cursor-prefix-match"
          (runSdbeginsxqDirect #[.slice cursorTarget, .slice cursorPrefix])
          (expectedQuietSuccessStack #[] cursorTarget cursorPrefix)
        expectOkStack "fail/cursor-prefix-mismatch"
          (runSdbeginsxqDirect #[.slice cursorTarget, .slice cursorPrefixMismatch])
          (expectedQuietFailureStack #[] cursorTarget) }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runSdbeginsxqDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdbeginsxqDirect #[.slice prefix5A5]) .stkUnd

        expectErr "type/top-null"
          (runSdbeginsxqDirect #[.slice slice8A5, .null]) .typeChk
        expectErr "type/top-int"
          (runSdbeginsxqDirect #[.slice slice8A5, intV 9]) .typeChk
        expectErr "type/top-cell"
          (runSdbeginsxqDirect #[.slice slice8A5, .cell refLeafA]) .typeChk

        expectErr "type/second-not-slice"
          (runSdbeginsxqDirect #[.null, .slice prefix5A5]) .typeChk
        expectErr "type/second-int-not-slice"
          (runSdbeginsxqDirect #[intV (-3), .slice prefix5A5]) .typeChk
        expectErr "order/top-type-before-second-slice"
          (runSdbeginsxqDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/direct/nonquiet-contrast-sdbeginsx"
      run := do
        expectOkStack "nonquiet/success-no-status"
          (runSdbeginsxDirect false #[.slice slice8A5, .slice prefix5A5])
          (expectedNonQuietSuccessStack #[] slice8A5 prefix5A5)
        expectOkStack "nonquiet/success-deep-stack"
          (runSdbeginsxDirect false #[intV 9, .slice slice256Phase0, .slice prefix255Phase0])
          (expectedNonQuietSuccessStack #[intV 9] slice256Phase0 prefix255Phase0)
        expectErr "nonquiet/failure-mismatch"
          (runSdbeginsxDirect false #[.slice slice8A5, .slice prefix1Zero]) .cellUnd
        expectErr "nonquiet/failure-prefix-longer"
          (runSdbeginsxDirect false #[.slice slice32Phase0, .slice prefix33Phase0]) .cellUnd }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let codeXq ←
          match assembleCp0 [sdbeginsxqInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdbeginsxq failed: {e}")
        if codeXq.bits == natToBits sdbeginsxqWord 16 && codeXq.refs.isEmpty then
          pure ()
        else
          throw (IO.userError
            s!"assemble/sdbeginsxq word mismatch: bits={reprStr codeXq.bits} refs={codeXq.refs.size}")

        let codeX ←
          match assembleCp0 [sdbeginsxInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdbeginsx failed: {e}")
        if codeX.bits == natToBits sdbeginsxWord 16 && codeX.refs.isEmpty then
          pure ()
        else
          throw (IO.userError
            s!"assemble/sdbeginsx word mismatch: bits={reprStr codeX.bits} refs={codeX.refs.size}")

        let asmProgram : Array Instr := #[sdbeginsxInstr, sdbeginsxqInstr, .xctos, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell asmCode
        let s1 ← expectDecodeStep "decode/asm-sdbeginsx" s0 sdbeginsxInstr 16
        let s2 ← expectDecodeStep "decode/asm-sdbeginsxq" s1 sdbeginsxqInstr 16
        let s3 ← expectDecodeStep "decode/asm-xctos" s2 .xctos 16
        let s4 ← expectDecodeStep "decode/asm-tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits :=
          natToBits sdbeginsxWord 16 ++
          natToBits sdbeginsxqWord 16 ++
          natToBits xctosWord 16 ++
          addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdbeginsx" r0 sdbeginsxInstr 16
        let r2 ← expectDecodeStep "decode/raw-sdbeginsxq" r1 sdbeginsxqInstr 16
        let r3 ← expectDecodeStep "decode/raw-xctos" r2 .xctos 16
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdbeginsx-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runSdbeginsxqDispatchFallback .add #[.null, intV 1])
          #[.null, intV 1, intV dispatchSentinel]
        expectOkStack "dispatch/sdpfx"
          (runSdbeginsxqDispatchFallback .sdPfx #[.slice slice8A5, .slice prefix5A5])
          #[.slice slice8A5, .slice prefix5A5, intV dispatchSentinel] }
  ]
  oracle := #[
    -- Quiet success cases
    mkSdbeginsxqCase "ok/empty-prefix-empty-target"
      #[.slice sliceEmpty, .slice prefixEmpty],
    mkSdbeginsxqCase "ok/empty-prefix-nonempty-target"
      #[.slice slice8A5, .slice prefixEmpty],
    mkSdbeginsxqCase "ok/equal-8bits"
      #[.slice slice8A5, .slice prefix8A5],
    mkSdbeginsxqCase "ok/proper-prefix-5-of-8"
      #[.slice slice8A5, .slice prefix5A5],
    mkSdbeginsxqCase "ok/proper-prefix-7-of-8"
      #[.slice slice8A5, .slice prefix7A5],
    mkSdbeginsxqCase "ok/prefix-32-of-64"
      #[.slice slice64Phase1, .slice prefix32Phase1],
    mkSdbeginsxqCase "ok/prefix-255-of-256"
      #[.slice slice256Phase0, .slice prefix255Phase0],
    mkSdbeginsxqCase "ok/refs-ignored"
      #[.slice slice8A5RefsA, .slice prefix5A5Refs],
    mkSdbeginsxqCase "ok/deep-stack-preserved"
      #[.null, intV 22, .slice slice8A5, .slice prefix5A5],

    -- Quiet failure cases
    mkSdbeginsxqCase "fail/mismatch-first-bit"
      #[.slice slice8A5, .slice prefix1Zero],
    mkSdbeginsxqCase "fail/mismatch-middle-bit"
      #[.slice slice8A5, .slice prefix5MidMismatch],
    mkSdbeginsxqCase "fail/mismatch-last-bit"
      #[.slice slice8A5, .slice slice8A4],
    mkSdbeginsxqCase "fail/prefix-longer-than-target"
      #[.slice slice32Phase0, .slice prefix33Phase0],
    mkSdbeginsxqCase "fail/reversed-order-stack"
      #[.slice prefix5A5, .slice slice8A5],
    mkSdbeginsxqCase "fail/deep-stack-preserved"
      #[intV 99, .slice slice8A5, .slice prefix1Zero],

    -- Error ordering
    mkSdbeginsxqCase "underflow/empty"
      #[],
    mkSdbeginsxqCase "underflow/one-item"
      #[.slice prefix5A5],
    mkSdbeginsxqCase "type/top-not-slice"
      #[.slice slice8A5, .null],
    mkSdbeginsxqCase "type/top-cell"
      #[.slice slice8A5, .cell refLeafA],
    mkSdbeginsxqCase "type/second-not-slice"
      #[.null, .slice prefix5A5],
    mkSdbeginsxqCase "order/top-type-before-second-slice"
      #[.null, .null],

    -- Gas edge behavior
    mkSdbeginsxqCase "gas/exact-cost-succeeds"
      #[.slice slice8A5, .slice prefix5A5]
      #[.pushInt (.num sdbeginsxqSetGasExact), .tonEnvOp .setGasLimit, sdbeginsxqInstr],
    mkSdbeginsxqCase "gas/exact-minus-one-out-of-gas"
      #[.slice slice8A5, .slice prefix5A5]
      #[.pushInt (.num sdbeginsxqSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdbeginsxqInstr]
  ]
  fuzz := #[
    { seed := 2026021127
      count := 500
      gen := genSdbeginsxqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDBEGINSXQ
