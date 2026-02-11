import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SBITS

/-
SBITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sbits.lean` (`.sbits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd749` decode to `.sbits`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sbits` encode as `0xd749`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`OpcodeInstr::mksimple(0xd749, 16, "SBITS", ... exec_slice_bits_refs(..., 1))`).

Branch map covered by this suite:
- dispatch guard (`.sbits` arm vs `next`);
- stack pop (`popSlice`) underflow/type/success paths;
- success contract: push `Int.ofNat s.bitsRemaining` (refs intentionally ignored);
- decode/assembler boundary around opcode family neighbors (`0xd748..0xd74b`).
-/

private def sbitsId : InstrId := { name := "SBITS" }

private def sbitsInstr : Instr := .sbits

private def sbitsWord : Nat := 0xd749

private def dispatchSentinel : Int := 1749

private def mkSbitsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sbitsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sbitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSbitsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSbits sbitsInstr stack

private def runSbitsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSbits instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1) || ((idx.1 + phase) % 5 = 0)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 6 3) #[]

private def refLeafD : Cell :=
  Cell.mkOrdinary (natToBits 0x2d 6) #[refLeafA]

private def refPool : Array Cell :=
  #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkSliceWithSize (bits refs : Nat) (phase : Nat := 0) : Slice :=
  let pickedRefs : Array Cell :=
    Array.ofFn (n := refs) fun i => refPool[i.1 % refPool.size]!
  mkSliceWithBitsRefs (stripeBits bits phase) pickedRefs

private def sbitsSetGasExact : Int :=
  computeExactGasBudget sbitsInstr

private def sbitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sbitsInstr

private def sbitsLenPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023]

private def pickSbitsBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (sbitsLenPool.size - 1)
    (sbitsLenPool[idx]!, rng2)
  else if mode ≤ 6 then
    randNat rng1 0 96
  else
    randNat rng1 97 1023

private def pickSbitsRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (4, rng1)
  else
    randNat rng1 0 4

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    (intV 17, rng1)
  else
    (.cell refLeafA, rng1)

private def pickBadTopValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    (intV 0, "int", rng1)
  else if pick = 2 then
    (.cell refLeafB, "cell", rng1)
  else if pick = 3 then
    (.builder Builder.empty, "builder", rng1)
  else if pick = 4 then
    (.tuple #[], "tuple", rng1)
  else
    (.cont (.quit 0), "cont", rng1)

private def sskipfirstInstr : Instr := .cellOp .sskipfirst

private def genSbitsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (bits, rng2) := pickSbitsBitsMixed rng1
    let (refs, rng3) := pickSbitsRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    (mkSbitsCase s!"fuzz/ok/full/bits-{bits}/refs-{refs}"
      #[.slice (mkSliceWithSize bits refs phase)], rng4)
  else if shape = 1 then
    let (bits, rng2) := pickSbitsBitsMixed rng1
    let (refs, rng3) := pickSbitsRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    let (noise, rng5) := pickNoiseValue rng4
    (mkSbitsCase s!"fuzz/ok/deep/bits-{bits}/refs-{refs}"
      #[noise, .slice (mkSliceWithSize bits refs phase)], rng5)
  else if shape = 2 then
    let (bits, rng2) := pickSbitsBitsMixed rng1
    let (refs, rng3) := pickSbitsRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    let (skipBits, rng5) := randNat rng4 0 bits
    let (skipRefs, rng6) := randNat rng5 0 refs
    (mkSbitsCase s!"fuzz/ok/cursor/skipb-{skipBits}/skipr-{skipRefs}/bits-{bits}/refs-{refs}"
      #[.slice (mkSliceWithSize bits refs phase), intV (Int.ofNat skipBits), intV (Int.ofNat skipRefs)]
      #[sskipfirstInstr, sbitsInstr], rng6)
  else if shape = 3 then
    let (refs, rng2) := pickSbitsRefsMixed rng1
    let (phase, rng3) := randNat rng2 0 3
    (mkSbitsCase s!"fuzz/ok/refs-only/refs-{refs}"
      #[.slice (mkSliceWithSize 0 refs phase)], rng3)
  else if shape = 4 then
    let (bits, rng2) := pickSbitsBitsMixed rng1
    let (phase, rng3) := randNat rng2 0 3
    (mkSbitsCase s!"fuzz/ok/bits-only/bits-{bits}"
      #[.slice (mkSliceWithSize bits 0 phase)], rng3)
  else if shape = 5 then
    (mkSbitsCase "fuzz/underflow/empty" #[], rng1)
  else
    let (bad, tag, rng2) := pickBadTopValue rng1
    let (bits, rng3) := pickSbitsBitsMixed rng2
    let (refs, rng4) := pickSbitsRefsMixed rng3
    let (phase, rng5) := randNat rng4 0 3
    if shape = 6 then
      (mkSbitsCase s!"fuzz/type/top-{tag}" #[bad], rng5)
    else
      (mkSbitsCase s!"fuzz/type/deep-top-{tag}" #[.slice (mkSliceWithSize bits refs phase), bad], rng5)

def suite : InstrSuite where
  id := { name := "SBITS" }
  unit := #[
    { name := "unit/direct/returns-bitsremaining-on-full-slices"
      run := do
        let checks : Array (Nat × Nat × Nat) :=
          #[
            (0, 0, 0),
            (0, 4, 1),
            (1, 0, 0),
            (1, 4, 1),
            (7, 0, 0),
            (8, 2, 1),
            (31, 1, 0),
            (32, 3, 1),
            (255, 0, 0),
            (256, 1, 1),
            (511, 3, 0),
            (1023, 0, 1),
            (1023, 4, 0)
          ]
        for c in checks do
          let bits := c.1
          let refs := c.2.1
          let phase := c.2.2
          expectOkStack s!"bits-{bits}/refs-{refs}/phase-{phase}"
            (runSbitsDirect #[.slice (mkSliceWithSize bits refs phase)])
            #[intV (Int.ofNat bits)] }
    ,
    { name := "unit/direct/partial-slices-use-current-bitpos"
      run := do
        let cellA : Cell := Cell.mkOrdinary (stripeBits 19 0) #[refLeafA, refLeafB]
        let cellB : Cell := Cell.mkOrdinary (stripeBits 1023 1) #[refLeafA, refLeafB, refLeafC, refLeafD]
        let checks : Array (String × Slice × Int) :=
          #[
            ("partial/bits19/bitpos0/refpos1", { cell := cellA, bitPos := 0, refPos := 1 }, 19),
            ("partial/bits19/bitpos5/refpos0", { cell := cellA, bitPos := 5, refPos := 0 }, 14),
            ("partial/bits19/bitpos19/refpos2", { cell := cellA, bitPos := 19, refPos := 2 }, 0),
            ("partial/bits1023/bitpos1022/refpos4", { cell := cellB, bitPos := 1022, refPos := 4 }, 1),
            ("partial/bits1023/bitpos1023/refpos0", { cell := cellB, bitPos := 1023, refPos := 0 }, 0)
          ]
        for c in checks do
          let label := c.1
          let s := c.2.1
          let expected := c.2.2
          expectOkStack label
            (runSbitsDirect #[.slice s])
            #[intV expected] }
    ,
    { name := "unit/direct/deep-stack-preserved"
      run := do
        let below : Array Value := #[.null, intV 9, .cell refLeafC]
        expectOkStack "preserve/below-with-zero"
          (runSbitsDirect (below ++ #[.slice (mkSliceWithSize 0 2)]))
          (below ++ #[intV 0])
        expectOkStack "preserve/below-with-nonzero"
          (runSbitsDirect (below ++ #[.slice (mkSliceWithSize 32 1)]))
          (below ++ #[intV 32]) }
    ,
    { name := "unit/direct/pop-order-top-slice-controls-result"
      run := do
        let low := mkSliceWithSize 9 1
        let high := mkSliceWithSize 37 2
        expectOkStack "order/two-slices-pop-top"
          (runSbitsDirect #[.slice low, .slice high])
          #[.slice low, intV 37]

        let below : Array Value := #[.cell refLeafA, .slice (mkSliceWithSize 8 0)]
        let top := mkSliceWithSize 255 0
        expectOkStack "order/deep-stack-only-top-slice-popped"
          (runSbitsDirect (below ++ #[.slice top]))
          (below ++ #[intV 255]) }
    ,
    { name := "unit/direct/underflow-and-type-errors"
      run := do
        expectErr "underflow/empty" (runSbitsDirect #[]) .stkUnd

        let bads : Array (String × Value) :=
          #[
            ("null", .null),
            ("int", intV 0),
            ("cell", .cell Cell.empty),
            ("builder", .builder Builder.empty),
            ("tuple", .tuple #[]),
            ("cont", .cont (.quit 0))
          ]
        for bad in bads do
          expectErr s!"type/{bad.1}" (runSbitsDirect #[bad.2]) .typeChk

        expectErr "error-order/top-first-over-valid-slice"
          (runSbitsDirect #[.slice (mkSliceWithSize 13 1), .null]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable-for-sbits"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success-zero", runSbitsDirect #[.slice (mkSliceWithSize 0 0)]),
            ("success-nonzero", runSbitsDirect #[.slice (mkSliceWithSize 255 4)]),
            ("underflow", runSbitsDirect #[]),
            ("type", runSbitsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for SBITS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-assemble-neighbors-and-boundary"
      run := do
        let canonical ←
          match assembleCp0 [sbitsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assembleCp0 SBITS failed: {e}")
        if canonical.bits = natToBits sbitsWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/sbits: expected 0xd749 encoding, got bits {canonical.bits}")
        if canonical.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/sbits: expected 16-bit encoding, got {canonical.bits.size}")

        let program : Array Instr := #[
          .cellOp (.schkBitRefs true),
          .cellOp .pldRefVar,
          sbitsInstr,
          .srefs,
          .sbitrefs,
          .pldRefIdx 0,
          .pldRefIdx 3,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble family failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/schkbitrefsq" s0 (.cellOp (.schkBitRefs true)) 16
        let s2 ← expectDecodeStep "decode/pldrefvar" s1 (.cellOp .pldRefVar) 16
        let s3 ← expectDecodeStep "decode/sbits" s2 sbitsInstr 16
        let s4 ← expectDecodeStep "decode/srefs" s3 .srefs 16
        let s5 ← expectDecodeStep "decode/sbitrefs" s4 .sbitrefs 16
        let s6 ← expectDecodeStep "decode/pldrefidx0" s5 (.pldRefIdx 0) 16
        let s7 ← expectDecodeStep "decode/pldrefidx3" s6 (.pldRefIdx 3) 16
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/family-end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd748 16 ++ natToBits sbitsWord 16 ++ natToBits 0xd74a 16 ++ natToBits 0xd74b 16 ++ addCell.bits
        let raw := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-0xd748-pldrefvar" raw (.cellOp .pldRefVar) 16
        let r2 ← expectDecodeStep "decode/raw-0xd749-sbits" r1 sbitsInstr 16
        let r3 ← expectDecodeStep "decode/raw-0xd74a-srefs" r2 .srefs 16
        let r4 ← expectDecodeStep "decode/raw-0xd74b-sbitrefs" r3 .sbitrefs 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining")

        let payload := mkSliceFromBits (natToBits sbitsWord 16 ++ natToBits 0xa5 8)
        let rest ← expectDecodeStep "decode/raw-sbits-with-payload" payload sbitsInstr 16
        if rest.readBits 8 = natToBits 0xa5 8 then
          pure ()
        else
          throw (IO.userError "decode/raw-sbits-with-payload: trailing payload mismatch") }
    ,
    { name := "unit/dispatch/non-sbits-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runSbitsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-srefs"
          (runSbitsDispatchFallback .srefs #[.slice (mkSliceWithSize 8 0)])
          #[.slice (mkSliceWithSize 8 0), intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cellop-pldrefvar"
          (runSbitsDispatchFallback (.cellOp .pldRefVar) #[intV 3, .slice (mkSliceWithSize 5 1)])
          #[intV 3, .slice (mkSliceWithSize 5 1), intV dispatchSentinel] }
  ]
  oracle := #[
    mkSbitsCase "ok/bits0-refs0" #[.slice (mkSliceWithSize 0 0)],
    mkSbitsCase "ok/bits0-refs4" #[.slice (mkSliceWithSize 0 4)],
    mkSbitsCase "ok/bits1-refs0" #[.slice (mkSliceWithSize 1 0)],
    mkSbitsCase "ok/bits1-refs4" #[.slice (mkSliceWithSize 1 4)],
    mkSbitsCase "ok/bits7-refs0" #[.slice (mkSliceWithSize 7 0)],
    mkSbitsCase "ok/bits8-refs2" #[.slice (mkSliceWithSize 8 2)],
    mkSbitsCase "ok/bits31-refs1" #[.slice (mkSliceWithSize 31 1)],
    mkSbitsCase "ok/bits32-refs3" #[.slice (mkSliceWithSize 32 3)],
    mkSbitsCase "ok/bits255-refs0" #[.slice (mkSliceWithSize 255 0)],
    mkSbitsCase "ok/bits256-refs1" #[.slice (mkSliceWithSize 256 1)],
    mkSbitsCase "ok/bits511-refs3" #[.slice (mkSliceWithSize 511 3)],
    mkSbitsCase "ok/bits1023-refs0" #[.slice (mkSliceWithSize 1023 0)],
    mkSbitsCase "ok/deep-below-null" #[.null, .slice (mkSliceWithSize 16 1)],
    mkSbitsCase "ok/deep-below-int" #[intV (-7), .slice (mkSliceWithSize 1023 4)],

    mkSbitsCase "underflow/empty-stack" #[],
    mkSbitsCase "type/top-null" #[.null],
    mkSbitsCase "type/top-int" #[intV 0],
    mkSbitsCase "type/top-cell" #[.cell Cell.empty],
    mkSbitsCase "type/top-builder" #[.builder Builder.empty],
    mkSbitsCase "type/top-tuple-empty" #[.tuple #[]],
    mkSbitsCase "error-order/top-nonslice-over-valid-slice"
      #[.slice (mkSliceWithSize 9 1), .null],

    mkSbitsCase "gas/exact-succeeds"
      #[.slice (mkSliceWithSize 1 0)]
      #[.pushInt (.num sbitsSetGasExact), .tonEnvOp .setGasLimit, sbitsInstr],
    mkSbitsCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSliceWithSize 1 0)]
      #[.pushInt (.num sbitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, sbitsInstr]
  ]
  fuzz := #[
    { seed := 2026021109
      count := 500
      gen := genSbitsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SBITS
