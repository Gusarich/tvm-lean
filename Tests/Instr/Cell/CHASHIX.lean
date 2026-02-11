import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CHASHIX

/-
CHASHIX branch mapping:
- dispatch: only `.cellOp .chashIX` is handled; all other instructions fall through;
- pop order: index is popped first (`popNatUpTo 3`), then cell (`popCell`);
- index failures (`stkUnd`/`typeChk`/`rangeChk`) happen before any cell checks;
- cell metadata failures from `computeLevelInfo?` map to `cellUnd`;
- success: pushes hash at requested level (`getHash i`), with level clamping by cell effective level;
- opcode/decode boundary: canonical word `0xd770`, adjacent to `0xd76f` (`CDEPTHI 3`) and
  `0xd771` (`CDEPTHIX`).
-/

private def chashIXId : InstrId := { name := "CHASHIX" }

private def chashIXInstr : Instr :=
  .cellOp .chashIX

private def chashIXWord : Nat := 0xd770
private def cdepthI3Word : Nat := 0xd76f
private def cdepthIXWord : Nat := 0xd771

private def dispatchSentinel : Int := 9770

private def execInstrCellOpChashIXOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpChashIX op next
  | _ => next

private def execInstrCellOpChashIOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpChashI op next
  | _ => next

private def mkChashIXCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[chashIXInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := chashIXId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runChashIXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpChashIXOnly chashIXInstr stack

private def runChashIDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpChashIOnly (.cellOp (.chashI idx)) stack

private def runChashIXDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpChashIXOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def expectSameOutcome
    (label : String)
    (a b : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match a, b with
    | .ok sa, .ok sb => sa == sb
    | .error ea, .error eb => ea == eb
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected same outcome, got lhs={reprStr a}, rhs={reprStr b}")

private def mkPatternBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 3 = 1) || ((i.1 + phase) % 5 = 0)

private def mkFullSlice (bitCount : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkPatternBits bitCount phase) #[])

private def mkDepthChain : Nat → Cell
  | 0 => Cell.empty
  | n + 1 => Cell.mkOrdinary (natToBits (n + 1) 6) #[mkDepthChain n]

private def cellDepth1 : Cell := mkDepthChain 1
private def cellDepth2 : Cell := mkDepthChain 2
private def cellDepth4 : Cell := mkDepthChain 4

private def specialLibraryCell : Cell :=
  -- Type byte `2` + 256-bit hash payload.
  { bits := natToBits 2 8 ++ natToBits 0x5a 256
    refs := #[]
    special := true
    levelMask := 0 }

private def bytesToBitsBE (bs : Array UInt8) : BitString := Id.run do
  let mut out : BitString := #[]
  for b in bs do
    out := out ++ natToBits b.toNat 8
  return out

private def mkHashPattern (offset : Nat) : Array UInt8 :=
  Array.ofFn (n := 32) fun i => UInt8.ofNat ((offset + i.1 * 29) % 256)

private def prunedHash0 : Array UInt8 := mkHashPattern 7
private def prunedHash1 : Array UInt8 := mkHashPattern 91
private def prunedHash2 : Array UInt8 := mkHashPattern 173

private def specialPrunedL7 : Cell :=
  -- Pruned branch with level mask `0b111` (effective level 3).
  { bits :=
      natToBits 1 8 ++
      natToBits 7 8 ++
      bytesToBitsBE prunedHash0 ++
      bytesToBitsBE prunedHash1 ++
      bytesToBitsBE prunedHash2 ++
      natToBits 3 16 ++
      natToBits 9 16 ++
      natToBits 27 16
    refs := #[]
    special := true
    levelMask := 7 }

private def specialPrunedL1 : Cell :=
  -- Pruned branch with level mask `0b001` (effective level 1): indexes 1..3 clamp together.
  { bits :=
      natToBits 1 8 ++
      natToBits 1 8 ++
      bytesToBitsBE (mkHashPattern 33) ++
      natToBits 19 16
    refs := #[]
    special := true
    levelMask := 1 }

private def malformedOrdinaryLevelMask : Cell :=
  { Cell.empty with levelMask := 1 }

private def malformedSpecialShort7 : Cell :=
  { bits := natToBits 0b1010110 7
    refs := #[]
    special := true
    levelMask := 0 }

private def malformedSpecialTag255 : Cell :=
  { bits := natToBits 255 8
    refs := #[]
    special := true
    levelMask := 0 }

private def malformedLibraryWithRef : Cell :=
  { bits := natToBits 2 8 ++ natToBits 0 256
    refs := #[Cell.empty]
    special := true
    levelMask := 0 }

private def hashIntAt (c : Cell) (idx : Nat) : Except String Int := do
  let info ← c.computeLevelInfo?
  pure (Int.ofNat (bytesToNatBE (info.getHash idx)))

private def hashIntAtIO (label : String) (c : Cell) (idx : Nat) : IO Int := do
  match hashIntAt c idx with
  | .ok n => pure n
  | .error e => throw (IO.userError s!"{label}: failed to compute expected hash[{idx}] ({e})")

private def expectComputeFails (label : String) (c : Cell) : IO Unit := do
  match c.computeLevelInfo? with
  | .ok info =>
      throw (IO.userError s!"{label}: expected computeLevelInfo? failure, got {reprStr info}")
  | .error _ =>
      pure ()

private def chashIXSetGasExact : Int :=
  computeExactGasBudget chashIXInstr

private def chashIXSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne chashIXInstr

private def okCellPool : Array Cell :=
  #[
    Cell.empty,
    cellDepth1,
    cellDepth2,
    cellDepth4,
    specialLibraryCell,
    specialPrunedL7,
    specialPrunedL1
  ]

private def noisePool : Array Value :=
  #[
    .null,
    intV 0,
    intV 7,
    .cell Cell.empty,
    .slice (mkFullSlice 9 0),
    .builder Builder.empty,
    .tuple #[]
  ]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genChashIXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    (mkChashIXCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 1 then
    (mkChashIXCase "fuzz/underflow/index-only" #[intV 0], rng1)
  else if shape = 2 then
    (mkChashIXCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 3 then
    (mkChashIXCase "fuzz/type/top-cell" #[.cell Cell.empty], rng1)
  else if shape = 4 then
    (mkChashIXCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkChashIXCase "fuzz/type/top-slice" #[.slice (mkFullSlice 7 1)], rng1)
  else if shape = 6 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    (mkChashIXCase "fuzz/ok/top-only" #[.cell c, intV (Int.ofNat idx)], rng3)
  else if shape = 7 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    let (noise, rng4) := pickFromPool noisePool rng3
    (mkChashIXCase "fuzz/ok/deep-noise" #[noise, .cell c, intV (Int.ofNat idx)], rng4)
  else if shape = 8 then
    let (idxBad, rng2) := pickFromPool (#[-1, 4, 9] : Array Int) rng1
    (mkChashIXCase "fuzz/range/order-before-cell-type" #[.null, intV idxBad], rng2)
  else if shape = 9 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idxBad, rng3) := pickFromPool (#[-1, 4, 9] : Array Int) rng2
    (mkChashIXCase "fuzz/range/index-oob" #[.cell c, intV idxBad], rng3)
  else if shape = 10 then
    let (c, rng2) := pickFromPool okCellPool rng1
    (mkChashIXCase "fuzz/range/index-nan-program" #[.cell c] #[.pushInt .nan, chashIXInstr], rng2)
  else if shape = 11 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    let stack : Array Value := #[.null, intV 77, .slice (mkFullSlice 9 1), .cell c, intV (Int.ofNat idx)]
    (mkChashIXCase "fuzz/ok/deep-fixed" stack, rng3)
  else if shape = 12 then
    let badCellPos : Array Value := #[.null, intV 77, .builder Builder.empty, .tuple #[]]
    let (idx, rng2) := randNat rng1 0 3
    (mkChashIXCase "fuzz/type/cell-position" (badCellPos ++ #[intV (Int.ofNat idx)]), rng2)
  else
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    let code : Array Instr := #[chashIXInstr, chashIXInstr]
    (mkChashIXCase "fuzz/ok/repeat-twice" #[.cell c, intV (Int.ofNat idx)] code, rng3)

def suite : InstrSuite where
  id := { name := "CHASHIX" }
  unit := #[
    -- Branch: success path + stack contract (pop cell+index, push hash, preserve below).
    { name := "unit/direct/success-index-boundaries-and-stack-contract"
      run := do
        let checks : Array (String × Array Value × Cell × Nat) :=
          #[("ok/empty/i0", #[], Cell.empty, 0),
            ("ok/empty/i3", #[], Cell.empty, 3),
            ("ok/depth4/i2", #[], cellDepth4, 2),
            ("ok/library/i1", #[], specialLibraryCell, 1),
            ("ok/deep-preserve", #[.null, intV 77, .slice (mkFullSlice 9 1)], specialLibraryCell, 0)]
        for p in checks do
          let label := p.1
          let below := p.2.1
          let c := p.2.2.1
          let idx := p.2.2.2
          let h ← hashIntAtIO label c idx
          expectOkStack label
            (runChashIXDirect (below ++ #[.cell c, intV (Int.ofNat idx)]))
            (below ++ #[intV h]) }
    ,
    -- Branch: level-index behavior on pruned branches (`effectiveLevel=3` vs `effectiveLevel=1` clamp).
    { name := "unit/direct/pruned-level-index-behavior"
      run := do
        let infoL7 ←
          match specialPrunedL7.computeLevelInfo? with
          | .ok info => pure info
          | .error e => throw (IO.userError s!"pruned-l7 invalid: {e}")
        if infoL7.effectiveLevel = 3 then
          pure ()
        else
          throw (IO.userError s!"pruned-l7: expected effectiveLevel=3, got {infoL7.effectiveLevel}")

        for idx in ([0, 1, 2, 3] : List Nat) do
          let h ← hashIntAtIO s!"pruned-l7/i{idx}" specialPrunedL7 idx
          expectOkStack s!"pruned-l7/i{idx}"
            (runChashIXDirect #[.cell specialPrunedL7, intV (Int.ofNat idx)])
            #[intV h]

        let h1 ← hashIntAtIO "pruned-l1/i1" specialPrunedL1 1
        let h3 ← hashIntAtIO "pruned-l1/i3" specialPrunedL1 3
        if h1 = h3 then
          pure ()
        else
          throw (IO.userError s!"pruned-l1: expected hash[1] == hash[3], got {h1} vs {h3}")

        expectOkStack "pruned-l1/i1"
          (runChashIXDirect #[.cell specialPrunedL1, intV 1])
          #[intV h1]
        expectOkStack "pruned-l1/i3"
          (runChashIXDirect #[.cell specialPrunedL1, intV 3])
          #[intV h3] }
    ,
    -- Branch: index errors are emitted before cell pop/type checks.
    { name := "unit/direct/errors-underflow-type-range-and-order"
      run := do
        expectErr "underflow/empty" (runChashIXDirect #[]) .stkUnd
        expectErr "underflow/index-only" (runChashIXDirect #[intV 0]) .stkUnd

        expectErr "type/top-null" (runChashIXDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runChashIXDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-slice" (runChashIXDirect #[.slice (mkFullSlice 7 0)]) .typeChk
        expectErr "type/second-not-cell-null" (runChashIXDirect #[.null, intV 0]) .typeChk

        expectErr "range/top-negative" (runChashIXDirect #[.cell cellDepth2, intV (-1)]) .rangeChk
        expectErr "range/top-too-large" (runChashIXDirect #[.cell cellDepth2, intV 4]) .rangeChk
        expectErr "range/top-nan" (runChashIXDirect #[.cell cellDepth2, .int .nan]) .rangeChk

        expectErr "order/range-before-cell-type"
          (runChashIXDirect #[.null, intV 4]) .rangeChk
        expectErr "order/range-before-underflow"
          (runChashIXDirect #[intV 4]) .rangeChk }
    ,
    -- Branch: invalid cell metadata always maps to `cellUnd`.
    { name := "unit/direct/cellund-for-malformed-cells"
      run := do
        let malformed : Array (String × Cell) :=
          #[("ordinary-level-mask", malformedOrdinaryLevelMask),
            ("special-short7", malformedSpecialShort7),
            ("special-tag255", malformedSpecialTag255),
            ("library-with-ref", malformedLibraryWithRef)]
        for p in malformed do
          expectComputeFails p.1 p.2
          expectErr s!"cellund/{p.1}/i0"
            (runChashIXDirect #[.cell p.2, intV 0]) .cellUnd
          expectErr s!"cellund/{p.1}/i3"
            (runChashIXDirect #[.cell p.2, intV 3]) .cellUnd }
    ,
    -- Branch alignment: CHASHIX(index-on-stack) must match CHASHI(immediate-index).
    { name := "unit/equivalence/chashix-vs-chashi"
      run := do
        let okCells : Array (String × Cell) :=
          #[("empty", Cell.empty),
            ("depth4", cellDepth4),
            ("library", specialLibraryCell),
            ("pruned-l7", specialPrunedL7),
            ("pruned-l1", specialPrunedL1)]
        for p in okCells do
          for idx in ([0, 1, 2, 3] : List Nat) do
            expectSameOutcome s!"ok/{p.1}/i{idx}"
              (runChashIXDirect #[.cell p.2, intV (Int.ofNat idx)])
              (runChashIDirect idx #[.cell p.2])

        let badCells : Array (String × Cell) :=
          #[("special-short7", malformedSpecialShort7),
            ("library-with-ref", malformedLibraryWithRef)]
        for p in badCells do
          for idx in ([0, 2, 3] : List Nat) do
            expectSameOutcome s!"err/{p.1}/i{idx}"
              (runChashIXDirect #[.cell p.2, intV (Int.ofNat idx)])
              (runChashIDirect idx #[.cell p.2]) }
    ,
    -- Branch: opcode/decode boundaries around CHASHIX (`0xd770`).
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let single ←
          match assembleCp0 [chashIXInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/chashix failed: {e}")
        if single.bits = natToBits chashIXWord 16 then
          pure ()
        else
          throw (IO.userError s!"chashix encode mismatch: got bits {single.bits}")

        if single.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"chashix encode mismatch: expected 16 bits, got {single.bits.size}")

        match assembleCp0 [.cellOp (.chashI 4)] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/chashi-4: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/chashi-4: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let seq : BitString :=
          natToBits cdepthI3Word 16 ++
          natToBits chashIXWord 16 ++
          natToBits cdepthIXWord 16 ++
          addCell.bits
        let s0 := mkSliceFromBits seq
        let s1 ← expectDecodeStep "decode/cdepthi3-neighbor" s0 (.cellOp (.cdepthI 3)) 16
        let s2 ← expectDecodeStep "decode/chashix" s1 chashIXInstr 16
        let s3 ← expectDecodeStep "decode/cdepthix-neighbor" s2 (.cellOp .cdepthIX) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits")

        let raw := mkSliceFromBits (natToBits chashIXWord 16 ++ natToBits chashIXWord 16)
        let r1 ← expectDecodeStep "decode/raw-first-chashix" raw chashIXInstr 16
        let r2 ← expectDecodeStep "decode/raw-second-chashix" r1 chashIXInstr 16
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits")

        expectDecodeErr "decode/raw-0xd763-invalid"
          (mkSliceFromBits (natToBits 0xd763 16 ++ natToBits chashIXWord 16)) .invOpcode }
    ,
    -- Branch: explicit pass-through behavior when opcode is not CHASHIX.
    { name := "unit/dispatch/fallback-and-handled"
      run := do
        let hHandled ← hashIntAtIO "dispatch/handled" specialPrunedL7 2
        expectOkStack "dispatch/handled-chashix"
          (runChashIXDispatchFallback chashIXInstr #[.cell specialPrunedL7, intV 2])
          #[intV hHandled]

        expectOkStack "dispatch/non-cellop-add"
          (runChashIXDispatchFallback .add #[intV 11])
          #[intV 11, intV dispatchSentinel]

        expectOkStack "dispatch/neighbor-cdepthix"
          (runChashIXDispatchFallback (.cellOp .cdepthIX) #[.cell Cell.empty, intV 0])
          #[.cell Cell.empty, intV 0, intV dispatchSentinel]

        expectOkStack "dispatch/neighbor-chashi"
          (runChashIXDispatchFallback (.cellOp (.chashI 1)) #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
    ,
    -- Branch invariant: CHASHIX should only produce its expected exception set.
    { name := "unit/direct/no-unexpected-exceptions"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[("ok", runChashIXDirect #[.cell cellDepth1, intV 0]),
            ("underflow", runChashIXDirect #[]),
            ("type", runChashIXDirect #[.null]),
            ("range", runChashIXDirect #[.cell cellDepth1, intV 9]),
            ("cellund", runChashIXDirect #[.cell malformedSpecialShort7, intV 0])]
        for p in probes do
          match p.2 with
          | .error .intOv =>
              throw (IO.userError s!"{p.1}: unexpected intOv")
          | .error .cellOv =>
              throw (IO.userError s!"{p.1}: unexpected cellOv")
          | .error .outOfGas =>
              throw (IO.userError s!"{p.1}: unexpected outOfGas in direct handler run")
          | _ =>
              pure () }
  ]
  oracle := #[
    mkChashIXCase "ok/top-empty/index0" #[.cell Cell.empty, intV 0],
    mkChashIXCase "ok/top-empty/index3" #[.cell Cell.empty, intV 3],
    mkChashIXCase "ok/top-depth4/index2" #[.cell cellDepth4, intV 2],
    mkChashIXCase "ok/top-library/index1" #[.cell specialLibraryCell, intV 1],
    mkChashIXCase "ok/top-pruned-l7/index0" #[.cell specialPrunedL7, intV 0],
    mkChashIXCase "ok/top-pruned-l7/index1" #[.cell specialPrunedL7, intV 1],
    mkChashIXCase "ok/top-pruned-l7/index2" #[.cell specialPrunedL7, intV 2],
    mkChashIXCase "ok/deep-below-null/pruned-l7-index3"
      #[.null, .cell specialPrunedL7, intV 3],

    mkChashIXCase "underflow/empty" #[],
    mkChashIXCase "underflow/index-only" #[intV 0],

    mkChashIXCase "type/top-null" #[.null],
    mkChashIXCase "type/top-cell" #[.cell Cell.empty],
    mkChashIXCase "type/top-slice" #[.slice (mkFullSlice 7 1)],
    mkChashIXCase "type/second-not-cell-null" #[.null, intV 0],

    mkChashIXCase "range/index-negative" #[.cell cellDepth2, intV (-1)],
    mkChashIXCase "range/index-too-large" #[.cell cellDepth2, intV 4],
    mkChashIXCase "range/index-nan-program"
      #[.cell cellDepth2]
      #[.pushInt .nan, chashIXInstr],

    mkChashIXCase "ok/top-pruned-l7/index3" #[.cell specialPrunedL7, intV 3],
    mkChashIXCase "type/top-builder" #[.builder Builder.empty],
    mkChashIXCase "range/order-range-before-cell-type" #[.null, intV 4],

    mkChashIXCase "gas/exact-cost-succeeds"
      #[.cell cellDepth1, intV 0]
      #[.pushInt (.num chashIXSetGasExact), .tonEnvOp .setGasLimit, chashIXInstr],
    mkChashIXCase "gas/exact-minus-one-out-of-gas"
      #[.cell cellDepth1, intV 0]
      #[.pushInt (.num chashIXSetGasExactMinusOne), .tonEnvOp .setGasLimit, chashIXInstr]
  ]
  fuzz := #[
    { seed := 2026021103
      count := 500
      gen := genChashIXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.CHASHIX
