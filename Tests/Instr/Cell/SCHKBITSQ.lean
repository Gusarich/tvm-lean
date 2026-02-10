import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCHKBITSQ

/-
SCHKBITSQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/SchkBits.lean` (`.schkBits quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SCHKBITS=0xd741`, `SCHKBITSQ=0xd745`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode of `0xd741` / `0xd745`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_chk_slice_bits`, quiet/non-quiet variants).

Branch map for `SCHKBITSQ`:
- dispatch guard: only `.cellOp (.schkBits true)` executes here; others must call `next`;
- stack gate: `checkUnderflow 2` before any typed pops;
- pop order: top `bits` via `popNatUpTo 1023`, then `slice` via `popSlice`;
- quiet behavior: push `-1` on `haveBits(bits)`, push `0` otherwise (never `cellUnd` for shortage);
- non-quiet contrast (`SCHKBITS`): same pop/check logic, but shortage throws `.cellUnd`;
- opcode/decode boundaries: canonical quiet opcode `0xd745`, with adjacent SCHK family words.
-/

private def schkbitsqId : InstrId := { name := "SCHKBITSQ" }

private def schkBitsInstr (quiet : Bool) : Instr :=
  .cellOp (.schkBits quiet)

private def schkbitsInstr : Instr :=
  schkBitsInstr false

private def schkbitsqInstr : Instr :=
  schkBitsInstr true

private def schkBitsWord : Nat := 0xd741
private def schkRefsWord : Nat := 0xd742
private def schkBitRefsWord : Nat := 0xd743
private def schkBitsQWord : Nat := 0xd745
private def schkRefsQWord : Nat := 0xd746
private def schkBitRefsQWord : Nat := 0xd747

private def dispatchSentinel : Int := 745

private def natV (n : Nat) : Value :=
  intV (Int.ofNat n)

private def mkSchkbitsqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[schkbitsqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkbitsqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSchkbitsqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkSchkbitsqCase name stack program gasLimits fuel

private def execCellOpSchkBitsInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpSchkBits op next
  | _ => next

private def runSchkbitsDirect (quiet : Bool) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpSchkBitsInstr (schkBitsInstr quiet) stack

private def runSchkbitsqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runSchkbitsDirect true stack

private def runSchkbitsqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpSchkBitsInstr instr (VM.push (intV dispatchSentinel)) stack

private def schkbitsqSetGasExact : Int :=
  computeExactGasBudget schkbitsqInstr

private def schkbitsqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne schkbitsqInstr

private def patternedBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 0) || ((i.1 + phase) % 5 = 1)

private def refLeafA : Cell :=
  Cell.mkOrdinary (patternedBits 3 0) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (patternedBits 5 1) #[Cell.empty]

private def refLeafC : Cell :=
  Cell.mkOrdinary (patternedBits 7 2) #[refLeafA]

private def mkPatternSlice (bits : Nat) (phase : Nat := 0) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternedBits bits phase) refs)

private def s0 : Slice := mkPatternSlice 0
private def s1 : Slice := mkPatternSlice 1
private def s7 : Slice := mkPatternSlice 7
private def s63 : Slice := mkPatternSlice 63 1
private def s255 : Slice := mkPatternSlice 255 2
private def s1023 : Slice := mkPatternSlice 1023 3
private def s12Refs2 : Slice := mkPatternSlice 12 1 #[refLeafA, refLeafB]

private def partialCell : Cell :=
  Cell.mkOrdinary (patternedBits 21 2) #[refLeafA, refLeafC]

private def sPartial : Slice :=
  { cell := partialCell, bitPos := 11, refPos := 1 }

private def expectedQuietStack (below : Array Value) (s : Slice) (bits : Nat) : Array Value :=
  below ++ #[intV (if s.haveBits bits then -1 else 0)]

private def needBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def pickNeedBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (needBitsBoundaryPool.size - 1)
  (needBitsBoundaryPool[idx]!, rng')

private def pickNeedBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickNeedBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickAvailAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickAvailBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickRefPack (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  if pick = 0 then
    (#[], rng1)
  else if pick = 1 then
    (#[refLeafA], rng1)
  else if pick = 2 then
    (#[refLeafA, refLeafB], rng1)
  else
    (#[refLeafA, refLeafB, refLeafC], rng1)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    (intV 19, rng1)
  else if pick = 2 then
    (.cell refLeafA, rng1)
  else
    (.slice (mkPatternSlice 9 2 #[refLeafB]), rng1)

private def genSchkbitsqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (need0, rng2) := pickNeedBitsMixed rng1
  if shape = 0 then
    let (avail, rng3) := pickAvailAtLeast need0 rng2
    (mkSchkbitsqCase s!"fuzz/ok/exact-or-extra/b-{need0}-a-{avail}"
      #[.slice (mkPatternSlice avail), natV need0], rng3)
  else if shape = 1 then
    let need := if need0 = 0 then 1 else need0
    let (avail, rng3) := pickAvailBelow need rng2
    (mkSchkbitsqCase s!"fuzz/fail/short/b-{need}-a-{avail}"
      #[.slice (mkPatternSlice avail), natV need], rng3)
  else if shape = 2 then
    let (avail, rng3) := pickAvailAtLeast need0 rng2
    let (noise, rng4) := pickNoiseValue rng3
    (mkSchkbitsqCase s!"fuzz/ok/deep/b-{need0}-a-{avail}"
      #[noise, .slice (mkPatternSlice avail), natV need0], rng4)
  else if shape = 3 then
    let need := if need0 = 0 then 1 else need0
    let (avail, rng3) := pickAvailBelow need rng2
    let (noise, rng4) := pickNoiseValue rng3
    (mkSchkbitsqCase s!"fuzz/fail/deep/b-{need}-a-{avail}"
      #[noise, .slice (mkPatternSlice avail), natV need], rng4)
  else if shape = 4 then
    let (avail, rng3) := pickAvailAtLeast need0 rng2
    let (refs, rng4) := pickRefPack rng3
    (mkSchkbitsqCase s!"fuzz/ok/refs-ignored/b-{need0}-a-{avail}-r-{refs.size}"
      #[.slice (mkPatternSlice avail 1 refs), natV need0], rng4)
  else if shape = 5 then
    let need := if need0 = 0 then 1 else need0
    let (avail, rng3) := pickAvailBelow need rng2
    let (refs, rng4) := pickRefPack rng3
    (mkSchkbitsqCase s!"fuzz/fail/refs-ignored/b-{need}-a-{avail}-r-{refs.size}"
      #[.slice (mkPatternSlice avail 2 refs), natV need], rng4)
  else if shape = 6 then
    (mkSchkbitsqCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 7 then
    (mkSchkbitsqCase "fuzz/type/top-bits-not-int" #[.slice s7, .null], rng2)
  else if shape = 8 then
    (mkSchkbitsqCase "fuzz/range/bits-negative" #[.slice s7, intV (-1)], rng2)
  else if shape = 9 then
    (mkSchkbitsqCase "fuzz/range/bits-gt1023" #[.slice s7, natV 1024], rng2)
  else if shape = 10 then
    (mkSchkbitsqCase "fuzz/type/top-bits-cell" #[.slice s7, .cell refLeafA], rng2)
  else if shape = 11 then
    (mkSchkbitsqCase "fuzz/type/slice-not-slice-after-valid-bits" #[.null, natV 3], rng2)
  else if shape = 12 then
    (mkSchkbitsqCase "fuzz/order/range-before-slice-type" #[.null, natV 1024], rng2)
  else if shape = 13 then
    (mkSchkbitsqProgramCase "fuzz/gas/exact"
      #[.slice s63, natV 8]
      #[.pushInt (.num schkbitsqSetGasExact), .tonEnvOp .setGasLimit, schkbitsqInstr], rng2)
  else
    (mkSchkbitsqProgramCase "fuzz/gas/exact-minus-one"
      #[.slice s63, natV 8]
      #[.pushInt (.num schkbitsqSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkbitsqInstr], rng2)

def suite : InstrSuite where
  id := { name := "SCHKBITSQ" }
  unit := #[
    { name := "unit/direct/quiet-status-and-stack-effect"
      run := do
        let checks : Array (String × Slice × Nat) :=
          #[
            ("ok/empty-b0", s0, 0),
            ("ok/s1-b1", s1, 1),
            ("ok/s7-b7", s7, 7),
            ("ok/s63-b63", s63, 63),
            ("ok/s255-b200", s255, 200),
            ("ok/s1023-b1023", s1023, 1023),
            ("fail/empty-b1", s0, 1),
            ("fail/s7-b8", s7, 8),
            ("fail/s63-b64", s63, 64),
            ("fail/s255-b256", s255, 256)
          ]
        for c in checks do
          let label := c.1
          let s := c.2.1
          let bits := c.2.2
          expectOkStack label
            (runSchkbitsqDirect #[.slice s, natV bits])
            (expectedQuietStack #[] s bits)

        expectOkStack "ok/deep-preserve-two-below"
          (runSchkbitsqDirect #[.null, intV 91, .slice s63, natV 8])
          (expectedQuietStack #[.null, intV 91] s63 8)
        expectOkStack "fail/deep-preserve-two-below"
          (runSchkbitsqDirect #[.cell refLeafA, intV (-9), .slice s7, natV 8])
          (expectedQuietStack #[.cell refLeafA, intV (-9)] s7 8) }
    ,
    { name := "unit/direct/bits-check-uses-bitsremaining-only"
      run := do
        expectOkStack "ok/refs-ignored-exact"
          (runSchkbitsqDirect #[.slice s12Refs2, natV 12])
          (expectedQuietStack #[] s12Refs2 12)
        expectOkStack "fail/refs-ignored-shortage"
          (runSchkbitsqDirect #[.slice s12Refs2, natV 13])
          (expectedQuietStack #[] s12Refs2 13)

        let avail := sPartial.bitsRemaining
        expectOkStack "ok/partial-cursor-exact"
          (runSchkbitsqDirect #[.slice sPartial, natV avail])
          (expectedQuietStack #[] sPartial avail)
        expectOkStack "fail/partial-cursor-short"
          (runSchkbitsqDirect #[.slice sPartial, natV (avail + 1)])
          (expectedQuietStack #[] sPartial (avail + 1)) }
    ,
    { name := "unit/direct/underflow-type-range-and-pop-order"
      run := do
        expectErr "underflow/empty" (runSchkbitsqDirect #[]) .stkUnd
        expectErr "underflow/one-item-int" (runSchkbitsqDirect #[natV 0]) .stkUnd
        expectErr "underflow/one-item-slice" (runSchkbitsqDirect #[.slice s7]) .stkUnd

        expectErr "type/top-bits-null"
          (runSchkbitsqDirect #[.slice s7, .null]) .typeChk
        expectErr "type/top-bits-cell"
          (runSchkbitsqDirect #[.slice s7, .cell refLeafA]) .typeChk
        expectErr "range/top-bits-negative"
          (runSchkbitsqDirect #[.slice s7, intV (-1)]) .rangeChk
        expectErr "range/top-bits-gt1023"
          (runSchkbitsqDirect #[.slice s7, natV 1024]) .rangeChk
        expectErr "range/top-bits-nan"
          (runSchkbitsqDirect #[.slice s7, .int .nan]) .rangeChk

        expectErr "type/slice-not-slice-after-valid-bits"
          (runSchkbitsqDirect #[.null, natV 3]) .typeChk
        expectErr "order/range-before-slice-type"
          (runSchkbitsqDirect #[.null, natV 1024]) .rangeChk
        expectErr "order/type-on-bits-before-slice-type"
          (runSchkbitsqDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/direct/contrast-with-nonquiet-schkbits"
      run := do
        expectOkStack "quiet/success-pushes-minus1"
          (runSchkbitsDirect true #[.slice s63, natV 63])
          #[intV (-1)]
        expectOkStack "nonquiet/success-pushes-nothing"
          (runSchkbitsDirect false #[.slice s63, natV 63])
          #[]
        expectOkStack "quiet/failure-pushes-zero"
          (runSchkbitsDirect true #[.slice s7, natV 8])
          #[intV 0]
        expectErr "nonquiet/failure-throws-cellund"
          (runSchkbitsDirect false #[.slice s7, natV 8]) .cellUnd

        expectOkStack "quiet/deep-preserve-below"
          (runSchkbitsDirect true #[intV 33, .slice s63, natV 8])
          (expectedQuietStack #[intV 33] s63 8)
        expectOkStack "nonquiet/deep-preserve-below"
          (runSchkbitsDirect false #[intV 33, .slice s63, natV 8])
          #[intV 33] }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[
            schkbitsInstr,
            .cellOp (.schkRefs false),
            .cellOp (.schkBitRefs false),
            schkbitsqInstr,
            .cellOp (.schkRefs true),
            .cellOp (.schkBitRefs true),
            .add
          ]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/schkbits" s0 schkbitsInstr 16
        let s2 ← expectDecodeStep "decode/schkrefs" s1 (.cellOp (.schkRefs false)) 16
        let s3 ← expectDecodeStep "decode/schkbitrefs" s2 (.cellOp (.schkBitRefs false)) 16
        let s4 ← expectDecodeStep "decode/schkbitsq" s3 schkbitsqInstr 16
        let s5 ← expectDecodeStep "decode/schkrefsq" s4 (.cellOp (.schkRefs true)) 16
        let s6 ← expectDecodeStep "decode/schkbitrefsq" s5 (.cellOp (.schkBitRefs true)) 16
        let s7 ← expectDecodeStep "decode/tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let qCode ←
          match assembleCp0 [schkbitsqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/schkbitsq failed: {e}")
        if qCode.bits == natToBits schkBitsQWord 16 && qCode.refs.isEmpty then
          pure ()
        else
          throw (IO.userError
            s!"assemble/schkbitsq mismatch: bits={reprStr qCode.bits}, refs={qCode.refs.size}")

        let raw : BitString :=
          natToBits schkBitsWord 16 ++
            natToBits schkRefsWord 16 ++
            natToBits schkBitRefsWord 16 ++
            natToBits schkBitsQWord 16 ++
            natToBits schkRefsQWord 16 ++
            natToBits schkBitRefsQWord 16 ++
            natToBits 0xa0 8
        let r0 := mkSliceFromBits raw
        let r1 ← expectDecodeStep "decode/raw-schkbits" r0 schkbitsInstr 16
        let r2 ← expectDecodeStep "decode/raw-schkrefs" r1 (.cellOp (.schkRefs false)) 16
        let r3 ← expectDecodeStep "decode/raw-schkbitrefs" r2 (.cellOp (.schkBitRefs false)) 16
        let r4 ← expectDecodeStep "decode/raw-schkbitsq" r3 schkbitsqInstr 16
        let r5 ← expectDecodeStep "decode/raw-schkrefsq" r4 (.cellOp (.schkRefs true)) 16
        let r6 ← expectDecodeStep "decode/raw-schkbitrefsq" r5 (.cellOp (.schkBitRefs true)) 16
        let r7 ← expectDecodeStep "decode/raw-tail-add" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-schkbits-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-op"
          (runSchkbitsqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/schkrefsq-neighbor"
          (runSchkbitsqDispatchFallback (.cellOp (.schkRefs true)) #[intV 4])
          #[intV 4, intV dispatchSentinel]
        expectOkStack "dispatch/schkbitrefs-neighbor"
          (runSchkbitsqDispatchFallback (.cellOp (.schkBitRefs false)) #[.cell refLeafA])
          #[.cell refLeafA, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSchkbitsqCase "ok/empty/bits-0"
      #[.slice s0, natV 0],
    mkSchkbitsqCase "ok/nonempty/bits-0"
      #[.slice s63, natV 0],
    mkSchkbitsqCase "ok/a1/b1"
      #[.slice s1, natV 1],
    mkSchkbitsqCase "ok/a7/b7"
      #[.slice s7, natV 7],
    mkSchkbitsqCase "ok/a63/b63"
      #[.slice s63, natV 63],
    mkSchkbitsqCase "ok/a255/b200"
      #[.slice s255, natV 200],
    mkSchkbitsqCase "ok/a1023/b1023"
      #[.slice s1023, natV 1023],
    mkSchkbitsqCase "ok/refs-ignored/a12-r2-b12"
      #[.slice s12Refs2, natV 12],
    mkSchkbitsqCase "ok/deep-stack-preserve-one-below"
      #[intV 5, .slice s12Refs2, natV 12],
    mkSchkbitsqCase "ok/deep-stack-preserve-two-below"
      #[.null, intV (-3), .slice s63, natV 8],

    mkSchkbitsqCase "fail/empty/b1"
      #[.slice s0, natV 1],
    mkSchkbitsqCase "fail/a7/b8"
      #[.slice s7, natV 8],
    mkSchkbitsqCase "fail/a63/b64"
      #[.slice s63, natV 64],
    mkSchkbitsqCase "fail/refs-ignored/a12-r2-b13"
      #[.slice s12Refs2, natV 13],
    mkSchkbitsqCase "fail/deep-stack-preserve-below"
      #[.cell refLeafA, .slice s7, natV 8],

    mkSchkbitsqCase "underflow/empty"
      #[],
    mkSchkbitsqCase "type/top-bits-null"
      #[.slice s7, .null],
    mkSchkbitsqCase "range/top-bits-negative"
      #[.slice s7, intV (-1)],
    mkSchkbitsqCase "range/top-bits-gt1023"
      #[.slice s7, natV 1024],
    mkSchkbitsqCase "type/slice-not-slice-after-valid-bits"
      #[.null, natV 3],
    mkSchkbitsqCase "order/range-before-slice-type"
      #[.null, natV 1024],

    mkSchkbitsqProgramCase "gas/exact-cost-succeeds"
      #[.slice s63, natV 8]
      #[.pushInt (.num schkbitsqSetGasExact), .tonEnvOp .setGasLimit, schkbitsqInstr],
    mkSchkbitsqProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice s63, natV 8]
      #[.pushInt (.num schkbitsqSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkbitsqInstr]
  ]
  fuzz := #[
    { seed := 2026021027
      count := 240
      gen := genSchkbitsqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCHKBITSQ
