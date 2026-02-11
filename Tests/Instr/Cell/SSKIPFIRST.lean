import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SSKIPFIRST

/-
SSKIPFIRST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sskipfirst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sskipfirst` encodes to `0xd731`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd731` decodes to `.cellOp .sskipfirst`)
  - `TvmLean/Semantics/Exec/Cell/Sdskipfirst.lean` (alignment target when `refs=0`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`SSKIPFIRST` in slice-ops group)

Branch map covered:
- dispatch guard (`.cellOp .sskipfirst` handled, others fall through to `next`);
- `checkUnderflow 3`;
- pop/type/range order: `refs` (0..4) → `bits` (0..1023) → `slice`;
- data branch: success iff `haveBits bits && haveRefs refs`, else `cellUnd`;
- success result preserves backing cell and advances cursor (`bitPos`, `refPos`).

Oracle/fuzz constraint:
- oracle stack token stream accepts only full-cell slices on input (`bitPos=0`, `refPos=0`);
  cursor-offset behavior is therefore unit-tested directly.
-/

private def sskipfirstId : InstrId := { name := "SSKIPFIRST" }

private def sskipfirstInstr : Instr := .cellOp .sskipfirst
private def sdskipfirstInstr : Instr := .sdskipfirst
private def scutfirstInstr : Instr := .cellOp .scutfirst
private def scutlastInstr : Instr := .cellOp .scutlast
private def sskiplastInstr : Instr := .cellOp .sskiplast

private def sskipfirstWord : Nat := 0xd731
private def scutfirstWord : Nat := 0xd730
private def scutlastWord : Nat := 0xd732
private def sskiplastWord : Nat := 0xd733

private def dispatchSentinel : Int := 731

private def execSskipfirstOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sskipfirst => execCellOpExt .sskipfirst next
  | _ => next

private def mkSskipfirstCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sskipfirstInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sskipfirstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSskipfirstDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execSskipfirstOnly sskipfirstInstr stack

private def runSdskipfirstDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdskipfirst sdskipfirstInstr stack

private def runSskipfirstDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execSskipfirstOnly instr (VM.push (intV dispatchSentinel)) stack

private def mkSliceCursor
    (bits : BitString)
    (refs : Array Cell)
    (bitPos refPos : Nat) : Slice :=
  { cell := Cell.mkOrdinary bits refs, bitPos := bitPos, refPos := refPos }

private def advanceSlice (s : Slice) (bits refs : Nat) : Slice :=
  { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }

private def mkSskipfirstStack
    (s : Slice)
    (bits refs : Int)
    (below : Array Value := #[]) : Array Value :=
  below ++ #[.slice s, intV bits, intV refs]

private def mkSskipfirstStackNat
    (s : Slice)
    (bits refs : Nat)
    (below : Array Value := #[]) : Array Value :=
  mkSskipfirstStack s (Int.ofNat bits) (Int.ofNat refs) below

private def expectSkipResult
    (label : String)
    (s : Slice)
    (bits refs : Nat)
    (below : Array Value := #[]) : IO Unit :=
  expectOkStack label
    (runSskipfirstDirect (mkSskipfirstStackNat s bits refs below))
    (below ++ #[.slice (advanceSlice s bits refs)])

private def refA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]
private def refD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refA]
  else if n = 2 then #[refA, refB]
  else if n = 3 then #[refA, refB, refC]
  else #[refA, refB, refC, refD]

private def oracleSlice0R0 : Slice :=
  mkSliceWithBitsRefs #[]

private def oracleSlice6R2 : Slice :=
  mkSliceWithBitsRefs (natToBits 0x2d 6) #[refA, refB]

private def oracleSlice17R3 : Slice :=
  mkSliceWithBitsRefs (stripeBits 17 1) #[refA, refB, refC]

private def oracleSlice64R4 : Slice :=
  mkSliceWithBitsRefs (stripeBits 64 0) #[refA, refB, refC, refD]

private def oracleSlice255R1 : Slice :=
  mkSliceWithBitsRefs (stripeBits 255 1) #[refA]

private def oracleSlice1023R0 : Slice :=
  mkSliceWithBitsRefs (Array.replicate 1023 true)

private def oracleSlice1023R4 : Slice :=
  mkSliceWithBitsRefs (Array.replicate 1023 false) (refsByCount 4)

private def cursorBits : BitString :=
  natToBits 0x2d5 10

private def cursorRefs : Array Cell :=
  #[refA, refB, refC]

private def cursorSlice : Slice :=
  mkSliceCursor cursorBits cursorRefs 3 1

private def sskipfirstSetGasExact : Int :=
  computeExactGasBudget sskipfirstInstr

private def sskipfirstSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sskipfirstInstr

private def gasProbeSlice : Slice :=
  mkSliceWithBitsRefs (stripeBits 33 0) #[refA, refB, refC]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023]

private def pickBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (bitsBoundaryPool.size - 1)
  (bitsBoundaryPool[idx]!, rng')

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 400
    (intV (Int.ofNat n - 200), rng2)
  else if pick = 2 then
    (.cell refC, rng1)
  else if pick = 3 then
    (.slice oracleSlice6R2, rng1)
  else
    (.builder Builder.empty, rng1)

private def pickBadNatValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let bad : Value :=
    if pick = 0 then .null
    else if pick = 1 then .cell refA
    else if pick = 2 then .slice oracleSlice17R3
    else .builder Builder.empty
  (bad, rng1)

private def genSskipfirstFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (availBits, rng2) := pickBitsMixed rng1
    let (availRefs, rng3) := randNat rng2 0 4
    let (bitsReq, rng4) := randNat rng3 0 availBits
    let (refsReq, rng5) := randNat rng4 0 availRefs
    let (phase, rng6) := randNat rng5 0 1
    let s := mkSliceWithBitsRefs (stripeBits availBits phase) (refsByCount availRefs)
    (mkSskipfirstCase s!"fuzz/ok/basic/b-{bitsReq}-r-{refsReq}/avail-{availBits}-{availRefs}"
      (mkSskipfirstStackNat s bitsReq refsReq), rng6)
  else if shape = 1 then
    let (availBits, rng2) := pickBitsMixed rng1
    let (availRefs, rng3) := randNat rng2 0 4
    let (bitsReq, rng4) := randNat rng3 0 availBits
    let (refsReq, rng5) := randNat rng4 0 availRefs
    let (phase, rng6) := randNat rng5 0 1
    let (noise, rng7) := pickNoise rng6
    let s := mkSliceWithBitsRefs (stripeBits availBits phase) (refsByCount availRefs)
    (mkSskipfirstCase s!"fuzz/ok/deep/b-{bitsReq}-r-{refsReq}/avail-{availBits}-{availRefs}"
      (mkSskipfirstStackNat s bitsReq refsReq #[noise]), rng7)
  else if shape = 2 then
    (mkSskipfirstCase "fuzz/ok/max-bounds"
      (mkSskipfirstStackNat oracleSlice1023R4 1023 4), rng1)
  else if shape = 3 then
    let (availBits, rng2) := randNat rng1 0 1022
    let (availRefs, rng3) := randNat rng2 0 4
    let (phase, rng4) := randNat rng3 0 1
    let s := mkSliceWithBitsRefs (stripeBits availBits phase) (refsByCount availRefs)
    (mkSskipfirstCase s!"fuzz/cellund/bits-short/avail-{availBits}-refs-{availRefs}"
      (mkSskipfirstStackNat s (availBits + 1) 0), rng4)
  else if shape = 4 then
    let (availBits, rng2) := pickBitsMixed rng1
    let (availRefs, rng3) := randNat rng2 0 3
    let (phase, rng4) := randNat rng3 0 1
    let s := mkSliceWithBitsRefs (stripeBits availBits phase) (refsByCount availRefs)
    (mkSskipfirstCase s!"fuzz/cellund/refs-short/avail-{availBits}-refs-{availRefs}"
      (mkSskipfirstStackNat s 0 (availRefs + 1)), rng4)
  else if shape = 5 then
    let (availBits, rng2) := randNat rng1 0 1022
    let (availRefs, rng3) := randNat rng2 0 3
    let (phase, rng4) := randNat rng3 0 1
    let s := mkSliceWithBitsRefs (stripeBits availBits phase) (refsByCount availRefs)
    (mkSskipfirstCase s!"fuzz/cellund/bits-refs-short/avail-{availBits}-refs-{availRefs}"
      (mkSskipfirstStackNat s (availBits + 1) (availRefs + 1)), rng4)
  else if shape = 6 then
    (mkSskipfirstCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkSskipfirstCase "fuzz/underflow/one-item"
      #[.slice oracleSlice17R3], rng1)
  else if shape = 8 then
    (mkSskipfirstCase "fuzz/underflow/two-items"
      #[.slice oracleSlice17R3, intV 0], rng1)
  else if shape = 9 then
    let (badRef, rng2) := pickBadNatValue rng1
    (mkSskipfirstCase "fuzz/type/refs-not-int"
      #[.slice oracleSlice17R3, intV 0, badRef], rng2)
  else if shape = 10 then
    let (delta, rng2) := randNat rng1 1 128
    (mkSskipfirstCase s!"fuzz/range/refs-over4/{4 + delta}"
      #[.slice oracleSlice17R3, intV 0, intV (Int.ofNat (4 + delta))], rng2)
  else if shape = 11 then
    let (badBits, rng2) := pickBadNatValue rng1
    (mkSskipfirstCase "fuzz/type/bits-not-int"
      #[.slice oracleSlice17R3, badBits, intV 0], rng2)
  else if shape = 12 then
    let (delta, rng2) := randNat rng1 1 2048
    (mkSskipfirstCase s!"fuzz/range/bits-over1023/{1023 + delta}"
      #[.slice oracleSlice17R3, intV (Int.ofNat (1023 + delta)), intV 0], rng2)
  else if shape = 13 then
    let (badSlice, rng2) := pickBadNatValue rng1
    (mkSskipfirstCase "fuzz/type/slice-not-slice"
      #[badSlice, intV 0, intV 0], rng2)
  else if shape = 14 then
    (mkSskipfirstCase "fuzz/range/refs-nan-via-program"
      #[.slice oracleSlice17R3]
      #[.pushInt (.num 0), .pushInt .nan, sskipfirstInstr], rng1)
  else if shape = 15 then
    (mkSskipfirstCase "fuzz/range/bits-nan-via-program"
      #[.slice oracleSlice17R3]
      #[.pushInt .nan, .pushInt (.num 0), sskipfirstInstr], rng1)
  else if shape = 16 then
    (mkSskipfirstCase "fuzz/gas/exact"
      (mkSskipfirstStackNat gasProbeSlice 8 1)
      #[.pushInt (.num sskipfirstSetGasExact), .tonEnvOp .setGasLimit, sskipfirstInstr], rng1)
  else
    (mkSskipfirstCase "fuzz/gas/exact-minus-one"
      (mkSskipfirstStackNat gasProbeSlice 8 1)
      #[.pushInt (.num sskipfirstSetGasExactMinusOne), .tonEnvOp .setGasLimit, sskipfirstInstr], rng1)

def suite : InstrSuite where
  id := { name := "SSKIPFIRST" }
  unit := #[
    { name := "unit/direct/success-cursor-updates-and-deep-stack"
      run := do
        -- Branch: `haveBits && haveRefs` success path.
        expectSkipResult "ok/noop-empty" oracleSlice0R0 0 0
        expectSkipResult "ok/noop-nonempty" oracleSlice6R2 0 0
        expectSkipResult "ok/skip-bits-only" oracleSlice6R2 3 0
        expectSkipResult "ok/skip-refs-only" oracleSlice6R2 0 2
        expectSkipResult "ok/skip-bits-refs" oracleSlice17R3 5 2
        expectSkipResult "ok/exact-consume" oracleSlice17R3 17 3

        expectSkipResult "ok/cursor-window" cursorSlice 2 1
        expectSkipResult "ok/cursor-exact-remaining"
          cursorSlice cursorSlice.bitsRemaining cursorSlice.refsRemaining

        expectSkipResult "ok/deep-stack-preserved"
          oracleSlice64R4 9 3 #[.null, intV 17, .cell refA] }
    ,
    { name := "unit/direct/cellund-branches"
      run := do
        -- Branch: `!(haveBits && haveRefs)` -> `cellUnd`.
        expectErr "cellund/bits-short-by1"
          (runSskipfirstDirect (mkSskipfirstStackNat oracleSlice6R2 7 0)) .cellUnd
        expectErr "cellund/refs-short-by1"
          (runSskipfirstDirect (mkSskipfirstStackNat oracleSlice6R2 0 3)) .cellUnd
        expectErr "cellund/bits-and-refs-short"
          (runSskipfirstDirect (mkSskipfirstStackNat oracleSlice6R2 7 3)) .cellUnd
        expectErr "cellund/bits-exact-refs-short"
          (runSskipfirstDirect (mkSskipfirstStackNat oracleSlice17R3 17 4)) .cellUnd
        expectErr "cellund/empty-vs-bits1"
          (runSskipfirstDirect (mkSskipfirstStackNat oracleSlice0R0 1 0)) .cellUnd
        expectErr "cellund/high-bits-exact-refs-missing"
          (runSskipfirstDirect (mkSskipfirstStackNat oracleSlice1023R0 1023 1)) .cellUnd
        expectErr "cellund/cursor-short-refs"
          (runSskipfirstDirect (mkSskipfirstStackNat cursorSlice 0 3)) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-pop-order"
      run := do
        -- Branch: stack underflow + pop/type/range order (`refs` -> `bits` -> `slice`).
        expectErr "underflow/empty" (runSskipfirstDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runSskipfirstDirect #[.slice oracleSlice17R3]) .stkUnd
        expectErr "underflow/two-items" (runSskipfirstDirect #[.slice oracleSlice17R3, intV 0]) .stkUnd

        expectErr "type/refs-top-null"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV 0, .null]) .typeChk
        expectErr "type/refs-top-cell"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV 0, .cell refA]) .typeChk
        expectErr "range/refs-negative"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV 0, intV (-1)]) .rangeChk
        expectErr "range/refs-over4"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV 0, intV 5]) .rangeChk
        expectErr "range/refs-nan"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV 0, .int .nan]) .rangeChk

        expectErr "type/bits-null"
          (runSskipfirstDirect #[.slice oracleSlice17R3, .null, intV 0]) .typeChk
        expectErr "range/bits-negative"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV (-1), intV 0]) .rangeChk
        expectErr "range/bits-over1023"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-nan"
          (runSskipfirstDirect #[.slice oracleSlice17R3, .int .nan, intV 0]) .rangeChk

        expectErr "type/slice-not-slice-after-valid-ints"
          (runSskipfirstDirect #[.null, intV 0, intV 0]) .typeChk
        expectErr "order/refs-range-before-bits-type"
          (runSskipfirstDirect #[.null, .null, intV 5]) .rangeChk
        expectErr "order/refs-type-before-bits-range"
          (runSskipfirstDirect #[.null, intV 1024, .null]) .typeChk
        expectErr "order/bits-range-before-slice-type"
          (runSskipfirstDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "order/bits-type-before-slice-type"
          (runSskipfirstDirect #[.null, .null, intV 0]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-boundaries"
      run := do
        let canonical ←
          match assembleCp0 [sskipfirstInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sskipfirst failed: {e}")
        if canonical.bits = natToBits sskipfirstWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sskipfirst: expected 0xd731, got {canonical.bits}")
        if canonical.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sskipfirst: expected 16 bits, got {canonical.bits.size}")

        let asmProgram : Array Instr :=
          #[scutfirstInstr, sskipfirstInstr, scutlastInstr, sskiplastInstr, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/program failed: {e}")
        let s0 := Slice.ofCell asmCode
        let s1 ← expectDecodeStep "decode/asm-scutfirst-neighbor" s0 scutfirstInstr 16
        let s2 ← expectDecodeStep "decode/asm-sskipfirst" s1 sskipfirstInstr 16
        let s3 ← expectDecodeStep "decode/asm-scutlast-neighbor" s2 scutlastInstr 16
        let s4 ← expectDecodeStep "decode/asm-sskiplast-neighbor" s3 sskiplastInstr 16
        let s5 ← expectDecodeStep "decode/asm-tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let rawBits : BitString :=
          natToBits scutfirstWord 16
            ++ natToBits sskipfirstWord 16
            ++ natToBits scutlastWord 16
            ++ natToBits sskiplastWord 16
            ++ natToBits 0xa0 8
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-scutfirst-neighbor" r0 scutfirstInstr 16
        let r2 ← expectDecodeStep "decode/raw-sskipfirst" r1 sskipfirstInstr 16
        let r3 ← expectDecodeStep "decode/raw-scutlast-neighbor" r2 scutlastInstr 16
        let r4 ← expectDecodeStep "decode/raw-sskiplast-neighbor" r3 sskiplastInstr 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/alias/refs-zero-aligns-sdskipfirst"
      run := do
        -- Branch: `.sskipfirst bits 0` should align with `.sdskipfirst bits`.
        let pairs : Array (String × Slice × Nat) :=
          #[
            ("noop", oracleSlice6R2, 0),
            ("bits3", oracleSlice6R2, 3),
            ("exact6", oracleSlice6R2, 6),
            ("bits64", oracleSlice64R4, 64),
            ("cursor2", cursorSlice, 2),
            ("cursor-exact", cursorSlice, cursorSlice.bitsRemaining)
          ]
        for (label, s, bits) in pairs do
          expectSameOutcome s!"align/{label}"
            (runSskipfirstDirect (mkSskipfirstStackNat s bits 0))
            (runSdskipfirstDirect #[.slice s, intV (Int.ofNat bits)])

        expectSameOutcome "align/cellund-short"
          (runSskipfirstDirect (mkSskipfirstStackNat oracleSlice6R2 7 0))
          (runSdskipfirstDirect #[.slice oracleSlice6R2, intV 7])
        expectSameOutcome "align/range-bits-over1023"
          (runSskipfirstDirect #[.slice oracleSlice17R3, intV 1024, intV 0])
          (runSdskipfirstDirect #[.slice oracleSlice17R3, intV 1024])
        expectSameOutcome "align/type-bits-not-int"
          (runSskipfirstDirect #[.slice oracleSlice17R3, .null, intV 0])
          (runSdskipfirstDirect #[.slice oracleSlice17R3, .null])
        expectSameOutcome "align/type-slice-not-slice"
          (runSskipfirstDirect #[.null, intV 0, intV 0])
          (runSdskipfirstDirect #[.null, intV 0]) }
    ,
    { name := "unit/dispatch/non-sskipfirst-falls-through"
      run := do
        let sample := mkSskipfirstStackNat oracleSlice6R2 2 1
        expectOkStack "dispatch/non-cellop"
          (runSskipfirstDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-scutfirst"
          (runSskipfirstDispatchFallback scutfirstInstr sample)
          (sample ++ #[intV dispatchSentinel])
        expectOkStack "dispatch/neighbor-sskiplast"
          (runSskipfirstDispatchFallback sskiplastInstr sample)
          (sample ++ #[intV dispatchSentinel])
        expectOkStack "dispatch/handled-sskipfirst-no-sentinel"
          (runSskipfirstDispatchFallback sskipfirstInstr sample)
          #[.slice (advanceSlice oracleSlice6R2 2 1)] }
  ]
  oracle := #[
    -- Success matrix (`haveBits && haveRefs`).
    mkSskipfirstCase "ok/noop-empty"
      (mkSskipfirstStackNat oracleSlice0R0 0 0),
    mkSskipfirstCase "ok/noop-nonempty"
      (mkSskipfirstStackNat oracleSlice6R2 0 0),
    mkSskipfirstCase "ok/skip-bits-1"
      (mkSskipfirstStackNat oracleSlice6R2 1 0),
    mkSskipfirstCase "ok/skip-bits-exact"
      (mkSskipfirstStackNat oracleSlice6R2 6 0),
    mkSskipfirstCase "ok/skip-refs-1"
      (mkSskipfirstStackNat oracleSlice6R2 0 1),
    mkSskipfirstCase "ok/skip-refs-exact"
      (mkSskipfirstStackNat oracleSlice6R2 0 2),
    mkSskipfirstCase "ok/skip-bits-refs"
      (mkSskipfirstStackNat oracleSlice17R3 5 2),
    mkSskipfirstCase "ok/exact-bits-refs"
      (mkSskipfirstStackNat oracleSlice17R3 17 3),
    mkSskipfirstCase "ok/high-bits-255"
      (mkSskipfirstStackNat oracleSlice255R1 255 0),
    mkSskipfirstCase "ok/high-bits-1023"
      (mkSskipfirstStackNat oracleSlice1023R0 1023 0),
    mkSskipfirstCase "ok/high-refs-4"
      (mkSskipfirstStackNat oracleSlice64R4 0 4),
    mkSskipfirstCase "ok/high-bits-refs-max"
      (mkSskipfirstStackNat oracleSlice1023R4 1023 4),
    mkSskipfirstCase "ok/deep-stack-preserve"
      (mkSskipfirstStackNat oracleSlice64R4 9 3 #[.null, intV 41, .cell refB]),

    -- `cellUnd` matrix.
    mkSskipfirstCase "cellund/bits-short-by1"
      (mkSskipfirstStackNat oracleSlice6R2 7 0),
    mkSskipfirstCase "cellund/refs-short-by1"
      (mkSskipfirstStackNat oracleSlice6R2 0 3),
    mkSskipfirstCase "cellund/bits-and-refs-short"
      (mkSskipfirstStackNat oracleSlice6R2 7 3),
    mkSskipfirstCase "cellund/bits-exact-refs-short"
      (mkSskipfirstStackNat oracleSlice17R3 17 4),
    mkSskipfirstCase "cellund/empty-vs-bits1"
      (mkSskipfirstStackNat oracleSlice0R0 1 0),
    mkSskipfirstCase "cellund/high-bits-exact-refs-missing"
      (mkSskipfirstStackNat oracleSlice1023R0 1023 1),

    -- Underflow.
    mkSskipfirstCase "underflow/empty" #[],
    mkSskipfirstCase "underflow/one-item"
      #[.slice oracleSlice17R3],

    -- Type/range/order via pop order.
    mkSskipfirstCase "type/refs-top-null"
      #[.slice oracleSlice17R3, intV 0, .null],
    mkSskipfirstCase "range/refs-over4"
      #[.slice oracleSlice17R3, intV 0, intV 5],
    mkSskipfirstCase "range/refs-negative"
      #[.slice oracleSlice17R3, intV 0, intV (-1)],
    mkSskipfirstCase "range/refs-nan-via-program"
      #[.slice oracleSlice17R3]
      #[.pushInt (.num 0), .pushInt .nan, sskipfirstInstr],
    mkSskipfirstCase "type/bits-not-int"
      #[.slice oracleSlice17R3, .null, intV 0],
    mkSskipfirstCase "range/bits-over1023"
      #[.slice oracleSlice17R3, intV 1024, intV 0],
    mkSskipfirstCase "range/bits-negative"
      #[.slice oracleSlice17R3, intV (-1), intV 0],
    mkSskipfirstCase "range/bits-nan-via-program"
      #[.slice oracleSlice17R3]
      #[.pushInt .nan, .pushInt (.num 0), sskipfirstInstr],
    mkSskipfirstCase "type/slice-not-slice-after-valid-ints"
      #[.null, intV 0, intV 0],
    mkSskipfirstCase "order/refs-range-before-bits-type"
      #[.null, .null, intV 5],
    mkSskipfirstCase "order/bits-range-before-slice-type"
      #[.null, intV 1024, intV 0],

    -- Gas boundary.
    mkSskipfirstCase "gas/exact-cost-succeeds"
      (mkSskipfirstStackNat gasProbeSlice 8 1)
      #[.pushInt (.num sskipfirstSetGasExact), .tonEnvOp .setGasLimit, sskipfirstInstr],
    mkSskipfirstCase "gas/exact-minus-one-out-of-gas"
      (mkSskipfirstStackNat gasProbeSlice 8 1)
      #[.pushInt (.num sskipfirstSetGasExactMinusOne), .tonEnvOp .setGasLimit, sskipfirstInstr]
  ]
  fuzz := #[
    { seed := 2026021061
      count := 320
      gen := genSskipfirstFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SSKIPFIRST
