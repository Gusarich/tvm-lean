import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDEPTH

/-
SDEPTH branch-mapping notes:
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Sdepth.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain position)
  - `TvmLean/Semantics/VM/Ops/Cells.lean` (`popSlice` error behavior)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SDEPTH` encode: `0xd764`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd764` decode)

Branch map covered by this suite:
- dispatch guard: only `.cellOp .sdepth` is handled; others must hit `next`;
- stack checks: `popSlice` enforces underflow (`stkUnd`) and strict top type (`typeChk`);
- success path: pushes exactly one int `s.cell.depth` and preserves values below top;
- cursor invariance: result depends on `s.cell.depth`, not `bitPos`/`refPos`;
- opcode/decode boundary: canonical opcode is `0xd764`; nearby hole `0xd763` stays invalid;
  right neighbor `0xd765` decodes to `.cdepth` (distinct instruction family).
-/

private def sdepthId : InstrId := { name := "SDEPTH" }

private def sdepthInstr : Instr := .cellOp .sdepth
private def ldsameInstr : Instr := .cellOp .ldSame
private def cdepthInstr : Instr := .cdepth
private def clevelInstr : Instr := .cellOp .clevel

private def sdepthWord : Nat := 0xd764
private def ldsameWord : Nat := 0xd762
private def cdepthWord : Nat := 0xd765
private def clevelWord : Nat := 0xd766

private def dispatchSentinel : Int := 76491

private def execInstrCellOpSdepthOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpSdepth op next
  | _ => next

private def mkSdepthCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdepthInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdepthId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdepthDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSdepthOnly sdepthInstr stack

private def runSdepthDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSdepthOnly instr (VM.push (intV dispatchSentinel)) stack

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def mkPatternBits (bitCount : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := bitCount) fun i =>
    ((i.1 + phase) % 2 = 0) || ((i.1 + phase) % 5 = 1)

private def mkCellWith
    (bitCount : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary (mkPatternBits bitCount phase) refs

private def mkFullSlice
    (bitCount : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (mkCellWith bitCount phase refs)

private def mkDepthChain : Nat → Cell
  | 0 => Cell.empty
  | n + 1 =>
      Cell.mkOrdinary (natToBits (n + 1) 6) #[mkDepthChain n]

private def cellDepth0 : Cell := mkDepthChain 0
private def cellDepth1 : Cell := mkDepthChain 1
private def cellDepth2 : Cell := mkDepthChain 2
private def cellDepth3 : Cell := mkDepthChain 3
private def cellDepth4 : Cell := mkDepthChain 4
private def cellDepth5 : Cell := mkDepthChain 5

private def cellDepth4Wide : Cell :=
  Cell.mkOrdinary (natToBits 45 6) #[cellDepth1, cellDepth3]

private def cellDepth5Wide : Cell :=
  Cell.mkOrdinary (natToBits 21 6) #[cellDepth4Wide, cellDepth2]

private def sliceDepth0Empty : Slice := Slice.ofCell cellDepth0
private def sliceDepth0Bits1 : Slice := mkFullSlice 1 0
private def sliceDepth0Bits1023 : Slice := mkFullSlice 1023 1
private def sliceDepth1SingleRef : Slice := mkFullSlice 9 2 #[cellDepth0]
private def sliceDepth2Chain : Slice := mkFullSlice 11 3 #[cellDepth1]
private def sliceDepth3Mixed : Slice := mkFullSlice 17 4 #[cellDepth0, cellDepth2]
private def sliceDepth4Mixed : Slice := mkFullSlice 27 5 #[cellDepth1, cellDepth3, cellDepth2]
private def sliceDepth5Wide : Slice := Slice.ofCell cellDepth5Wide
private def sliceDepth5Chain : Slice := Slice.ofCell cellDepth5

private def windowCellDepth4 : Cell :=
  mkCellWith 23 7 #[cellDepth0, cellDepth3, cellDepth2]

private def sliceWindowHead : Slice :=
  { cell := windowCellDepth4
    bitPos := 0
    refPos := 0 }

private def sliceWindowMid : Slice :=
  { cell := windowCellDepth4
    bitPos := 7
    refPos := 1 }

private def sliceWindowConsumed : Slice :=
  { cell := windowCellDepth4
    bitPos := 23
    refPos := 3 }

private def sdepthExpectedOut (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[intV (Int.ofNat s.cell.depth)]

private def sdepthSetGasExact : Int :=
  computeExactGasBudget sdepthInstr

private def sdepthSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdepthInstr

private def refPool : Array Cell :=
  #[cellDepth0, cellDepth1, cellDepth2, cellDepth4Wide]

private def takeRefCells (n : Nat) : Array Cell :=
  refPool.extract 0 (Nat.min n refPool.size)

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 768, 1023]

private def pickFromPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickFromPool rng1 bitsBoundaryPool
  else
    randNat rng1 0 1023

private def pickRefCountMixed (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 4

private def pickNoiseValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 200
    (intV (Int.ofNat n - 100), "int", rng2)
  else if pick = 2 then
    (.cell cellDepth2, "cell", rng1)
  else if pick = 3 then
    (.builder Builder.empty, "builder", rng1)
  else if pick = 4 then
    (.tuple #[], "tuple", rng1)
  else
    (.cont (.quit 0), "cont", rng1)

private def pickBadTopValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 255
    (intV (Int.ofNat n - 128), "int", rng2)
  else if pick = 2 then
    (.cell cellDepth1, "cell", rng1)
  else if pick = 3 then
    (.builder Builder.empty, "builder", rng1)
  else if pick = 4 then
    (.tuple #[], "tuple", rng1)
  else
    (.cont (.quit 0), "cont", rng1)

private def genSdepthFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      (mkSdepthCase "fuzz/ok/full-empty-cell" #[.slice sliceDepth0Empty], rng1)
    else if shape = 1 then
      let (bits, rng2) := pickBitsMixed rng1
      (mkSdepthCase s!"fuzz/ok/bits-only-{bits}" #[.slice (mkFullSlice bits 0)], rng2)
    else if shape = 2 then
      let (refs, rng2) := pickRefCountMixed rng1
      (mkSdepthCase s!"fuzz/ok/refs-only-{refs}" #[.slice (mkFullSlice 0 1 (takeRefCells refs))], rng2)
    else if shape = 3 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefCountMixed rng2
      (mkSdepthCase s!"fuzz/ok/mixed-bits-{bits}-refs-{refs}"
        #[.slice (mkFullSlice bits 2 (takeRefCells refs))], rng3)
    else if shape = 4 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefCountMixed rng2
      let (noise, tag, rng4) := pickNoiseValue rng3
      (mkSdepthCase s!"fuzz/ok/deep-{tag}/bits-{bits}/refs-{refs}"
        #[noise, .slice (mkFullSlice bits 3 (takeRefCells refs))], rng4)
    else if shape = 5 then
      (mkSdepthCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 6 then
      (mkSdepthCase "fuzz/type/top-null" #[.null], rng1)
    else if shape = 7 then
      let (n, rng2) := randNat rng1 0 255
      (mkSdepthCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
    else if shape = 8 then
      (mkSdepthCase "fuzz/type/top-cell" #[.cell cellDepth3], rng1)
    else if shape = 9 then
      (mkSdepthCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
    else if shape = 10 then
      (mkSdepthCase "fuzz/type/top-tuple" #[.tuple #[]], rng1)
    else if shape = 11 then
      (mkSdepthCase "fuzz/type/top-cont" #[.cont (.quit 0)], rng1)
    else if shape = 12 then
      let (bad, badTag, rng2) := pickBadTopValue rng1
      (mkSdepthCase s!"fuzz/type/order-top-{badTag}" #[.slice sliceDepth4Mixed, bad], rng2)
    else if shape = 13 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefCountMixed rng2
      (mkSdepthCase "fuzz/gas/exact"
        #[.slice (mkFullSlice bits 4 (takeRefCells refs))]
        #[.pushInt (.num sdepthSetGasExact), .tonEnvOp .setGasLimit, sdepthInstr], rng3)
    else if shape = 14 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefCountMixed rng2
      (mkSdepthCase "fuzz/gas/exact-minus-one"
        #[.slice (mkFullSlice bits 5 (takeRefCells refs))]
        #[.pushInt (.num sdepthSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdepthInstr], rng3)
    else
      (mkSdepthCase "fuzz/stress/max-bits-refs"
        #[.slice (mkFullSlice 1023 6 (takeRefCells 4))], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkSdepthCase "ok/full/depth0-empty-cell"
      #[.slice sliceDepth0Empty],
    mkSdepthCase "ok/full/depth0-bits1"
      #[.slice sliceDepth0Bits1],
    mkSdepthCase "ok/full/depth0-bits1023"
      #[.slice sliceDepth0Bits1023],
    mkSdepthCase "ok/full/depth1-single-ref"
      #[.slice sliceDepth1SingleRef],
    mkSdepthCase "ok/full/depth2-chain"
      #[.slice sliceDepth2Chain],
    mkSdepthCase "ok/full/depth3-mixed"
      #[.slice sliceDepth3Mixed],
    mkSdepthCase "ok/full/depth4-mixed"
      #[.slice sliceDepth4Mixed],
    mkSdepthCase "ok/full/depth5-wide"
      #[.slice sliceDepth5Wide],
    mkSdepthCase "ok/full/depth5-chain"
      #[.slice sliceDepth5Chain],

    mkSdepthCase "ok/deep/null-preserved"
      #[.null, .slice sliceDepth4Mixed],
    mkSdepthCase "ok/deep/int-preserved"
      #[intV (-17), .slice sliceDepth3Mixed],
    mkSdepthCase "ok/deep/cell-preserved"
      #[.cell cellDepth2, .slice sliceDepth5Wide],
    mkSdepthCase "ok/deep/cont-builder-tuple-preserved"
      #[.cont (.quit 0), .builder Builder.empty, .tuple #[], .slice sliceDepth1SingleRef]
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkSdepthCase "underflow/empty"
      #[],
    mkSdepthCase "type/top-null"
      #[.null],
    mkSdepthCase "type/top-int"
      #[intV 5],
    mkSdepthCase "type/top-cell"
      #[.cell cellDepth1],
    mkSdepthCase "type/top-builder"
      #[.builder Builder.empty],
    mkSdepthCase "type/top-tuple-empty"
      #[.tuple #[]],
    mkSdepthCase "type/top-cont-quit0"
      #[.cont (.quit 0)],
    mkSdepthCase "type/order-top-null-over-slice"
      #[.slice sliceDepth2Chain, .null]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkSdepthCase "gas/exact-cost-succeeds"
      #[.slice sliceDepth3Mixed]
      #[.pushInt (.num sdepthSetGasExact), .tonEnvOp .setGasLimit, sdepthInstr],
    mkSdepthCase "gas/exact-minus-one-out-of-gas"
      #[.slice sliceDepth3Mixed]
      #[.pushInt (.num sdepthSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdepthInstr]
  ]

def suite : InstrSuite where
  id := { name := "SDEPTH" }
  unit := #[
    -- Branch: success pushes `s.cell.depth` and preserves below-stack values.
    { name := "unit/direct/success-depth-and-stack-contract"
      run := do
        let checks : Array Slice :=
          #[
            sliceDepth0Empty,
            sliceDepth0Bits1,
            sliceDepth0Bits1023,
            sliceDepth1SingleRef,
            sliceDepth2Chain,
            sliceDepth3Mixed,
            sliceDepth4Mixed,
            sliceDepth5Wide,
            sliceDepth5Chain
          ]
        for s in checks do
          expectOkStack s!"ok/full/depth-{s.cell.depth}/bits-{s.bitsRemaining}/refs-{s.refsRemaining}"
            (runSdepthDirect #[.slice s])
            (sdepthExpectedOut #[] s)

        let below : Array Value := #[.null, intV 77, .cell cellDepth1]
        expectOkStack "ok/deep-stack-preserved"
          (runSdepthDirect (below ++ #[.slice sliceDepth5Wide]))
          (sdepthExpectedOut below sliceDepth5Wide) }
    ,
    -- Branch: `SDEPTH` reads depth from the backing cell, not from slice cursor positions.
    { name := "unit/direct/cursor-invariance-window-slices"
      run := do
        let windows : Array Slice := #[sliceWindowHead, sliceWindowMid, sliceWindowConsumed]
        for s in windows do
          expectOkStack s!"window/bitPos-{s.bitPos}/refPos-{s.refPos}"
            (runSdepthDirect #[.slice s])
            (sdepthExpectedOut #[] s) }
    ,
    -- Branch: all direct failures come from `popSlice`.
    { name := "unit/direct/underflow-and-type-checks"
      run := do
        expectErr "underflow/empty"
          (runSdepthDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runSdepthDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runSdepthDirect #[intV (-1)]) .typeChk
        expectErr "type/top-cell"
          (runSdepthDirect #[.cell cellDepth0]) .typeChk
        expectErr "type/top-builder"
          (runSdepthDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty"
          (runSdepthDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont-quit0"
          (runSdepthDirect #[.cont (.quit 0)]) .typeChk

        expectErr "type/order-top-null-over-slice"
          (runSdepthDirect #[.slice sliceDepth2Chain, .null]) .typeChk }
    ,
    -- Branch invariant: no integer-immediate path exists for SDEPTH, so `rangeChk` is unreachable.
    { name := "unit/direct/rangechk-unreachable-for-sdepth"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runSdepthDirect #[.slice sliceDepth4Mixed]),
            ("underflow", runSdepthDirect #[]),
            ("type", runSdepthDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for SDEPTH")
          | _ => pure () }
    ,
    -- Branch: opcode/decode contract around the `0xd764` slot.
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let single ←
          match assembleCp0 [sdepthInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sdepth failed: {e}")
        if single.bits = natToBits sdepthWord 16 then
          pure ()
        else
          throw (IO.userError s!"sdepth canonical encode mismatch: got bits {single.bits}")

        let program : Array Instr :=
          #[ldsameInstr, sdepthInstr, cdepthInstr, clevelInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldsame-left-neighbor" s0 ldsameInstr 16
        let s2 ← expectDecodeStep "decode/sdepth" s1 sdepthInstr 16
        let s3 ← expectDecodeStep "decode/cdepth-right-neighbor" s2 cdepthInstr 16
        let s4 ← expectDecodeStep "decode/clevel-right-neighbor" s3 clevelInstr 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-0xd763-invalid-hole"
          (mkSliceFromBits (natToBits 0xd763 16 ++ natToBits sdepthWord 16)) .invOpcode

        let raw := mkSliceFromBits
          (natToBits ldsameWord 16 ++
            natToBits sdepthWord 16 ++
            natToBits cdepthWord 16 ++
            natToBits clevelWord 16)
        let r1 ← expectDecodeStep "decode/raw-ldsame" raw ldsameInstr 16
        let r2 ← expectDecodeStep "decode/raw-sdepth" r1 sdepthInstr 16
        let r3 ← expectDecodeStep "decode/raw-cdepth" r2 cdepthInstr 16
        let r4 ← expectDecodeStep "decode/raw-clevel" r3 clevelInstr 16
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r4.bitsRemaining} bits remaining") }
    ,
    -- Branch: explicit pass-through to `next` for non-target ops/instrs.
    { name := "unit/dispatch/fallback-and-handled"
      run := do
        expectOkStack "dispatch/handled-sdepth"
          (runSdepthDispatchFallback sdepthInstr #[.slice sliceDepth1SingleRef])
          (sdepthExpectedOut #[] sliceDepth1SingleRef)

        expectOkStack "dispatch/non-cellop-add"
          (runSdepthDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-cdepth"
          (runSdepthDispatchFallback .cdepth #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-ldsame"
          (runSdepthDispatchFallback ldsameInstr #[.slice sliceDepth0Empty, intV 0])
          #[.slice sliceDepth0Empty, intV 0, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-clevel"
          (runSdepthDispatchFallback clevelInstr #[.cell cellDepth1])
          #[.cell cellDepth1, intV dispatchSentinel] }
  ]
  oracle := oracleSuccessCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021007
      count := 320
      gen := genSdepthFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDEPTH
