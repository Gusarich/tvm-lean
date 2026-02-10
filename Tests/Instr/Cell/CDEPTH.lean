import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CDEPTH

/-
CDEPTH branch mapping:
- dispatch: only `.cdepth` is handled; all other instructions must fall through to `next`;
- stack checks: `popMaybeCell` enforces underflow (`stkUnd`) and strict top-type (`typeChk`),
  while allowing `null` and `cell`;
- success: `null -> 0`, `cell -> cell.depth`, preserving values below top;
- malformed cell metadata: `Cell.depth` falls back to `0` when `computeLevelInfo?` fails;
- opcode/decode: canonical encoding is `0xd765`; nearby `0xd764/.sdepth` and `0xd766/.clevel`
  decode distinctly; hole `0xd763` stays invalid.
-/

private def cdepthId : InstrId := { name := "CDEPTH" }

private def cdepthInstr : Instr := .cdepth

private def cdepthWord : Nat := 0xd765
private def sdepthWord : Nat := 0xd764
private def clevelWord : Nat := 0xd766

private def dispatchSentinel : Int := 4765

private def mkCdepthCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[cdepthInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := cdepthId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runCdepthDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellCdepth cdepthInstr stack

private def runCdepthDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellCdepth instr (VM.push (intV dispatchSentinel)) stack

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

private def mkPatternBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 3 = 1) || ((i.1 + phase) % 5 = 0)

private def mkFullSlice
    (bitCount : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkPatternBits bitCount phase) refs)

private def mkDepthChain : Nat → Cell
  | 0 => Cell.empty
  | n + 1 => Cell.mkOrdinary (natToBits (n + 1) 6) #[mkDepthChain n]

private def cellDepth0 : Cell := mkDepthChain 0
private def cellDepth1 : Cell := mkDepthChain 1
private def cellDepth2 : Cell := mkDepthChain 2
private def cellDepth3 : Cell := mkDepthChain 3
private def cellDepth4 : Cell := mkDepthChain 4
private def cellDepth5 : Cell := mkDepthChain 5

private def cellWideDepth5 : Cell :=
  Cell.mkOrdinary (natToBits 0x2d 6) #[cellDepth1, cellDepth4, cellDepth2]

private def specialLibraryCell : Cell :=
  -- Type byte `2` + 256-bit hash payload.
  { bits := natToBits 2 8 ++ natToBits 0 256
    refs := #[]
    special := true
    levelMask := 0 }

private def malformedSpecialShort7 : Cell :=
  { bits := natToBits 0b1010101 7
    refs := #[]
    special := true
    levelMask := 0 }

private def malformedSpecialTag255 : Cell :=
  { bits := natToBits 255 8
    refs := #[]
    special := true
    levelMask := 0 }

private def cdepthOf (c? : Option Cell) : Int :=
  Int.ofNat <| match c? with
    | none => 0
    | some c => c.depth

private def expectedCdepthOut (below : Array Value) (c? : Option Cell) : Array Value :=
  below ++ #[intV (cdepthOf c?)]

private def cdepthSetGasExact : Int :=
  computeExactGasBudget cdepthInstr

private def cdepthSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne cdepthInstr

private def depthSamplePool : Array Cell :=
  #[cellDepth0, cellDepth1, cellDepth2, cellDepth3, cellDepth4, cellDepth5, cellWideDepth5, specialLibraryCell]

private def pickDepthSample (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (depthSamplePool.size - 1)
  (depthSamplePool[idx]!, rng')

private def pickNoiseValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 6
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 255
    (intV (Int.ofNat n - 128), "int", rng2)
  else if pick = 2 then
    (.slice (mkFullSlice 9 1), "slice", rng1)
  else if pick = 3 then
    (.builder Builder.empty, "builder", rng1)
  else if pick = 4 then
    (.tuple #[], "tuple0", rng1)
  else if pick = 5 then
    (.cont (.quit 0), "quit0", rng1)
  else
    let (c, rng2) := pickDepthSample rng1
    (.cell c, "cell", rng2)

private def genCdepthFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng2) :=
    if shape = 0 then
      (mkCdepthCase "fuzz/ok/top-null" #[.null], rng1)
    else if shape = 1 then
      let (c, rng2) := pickDepthSample rng1
      (mkCdepthCase s!"fuzz/ok/top-cell-depth-{c.depth}" #[.cell c], rng2)
    else if shape = 2 then
      let (noise, tag, rng2) := pickNoiseValue rng1
      let (c, rng3) := pickDepthSample rng2
      (mkCdepthCase s!"fuzz/ok/deep-{tag}/cell-depth-{c.depth}" #[noise, .cell c], rng3)
    else if shape = 3 then
      let (noise, tag, rng2) := pickNoiseValue rng1
      (mkCdepthCase s!"fuzz/ok/deep-{tag}/null" #[noise, .null], rng2)
    else if shape = 4 then
      (mkCdepthCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 5 then
      let (n, rng2) := randNat rng1 0 1023
      (mkCdepthCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 512)], rng2)
    else if shape = 6 then
      (mkCdepthCase "fuzz/type/top-slice" #[.slice (mkFullSlice 7 2)], rng1)
    else if shape = 7 then
      (mkCdepthCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
    else if shape = 8 then
      let (c, rng2) := pickDepthSample rng1
      (mkCdepthCase s!"fuzz/type/order-top-int-over-cell-depth-{c.depth}" #[.cell c, intV 3], rng2)
    else if shape = 9 then
      let (c, rng2) := pickDepthSample rng1
      (mkCdepthCase "fuzz/gas/exact"
        #[.cell c]
        #[.pushInt (.num cdepthSetGasExact), .tonEnvOp .setGasLimit, cdepthInstr], rng2)
    else if shape = 10 then
      let (c, rng2) := pickDepthSample rng1
      (mkCdepthCase "fuzz/gas/exact-minus-one"
        #[.cell c]
        #[.pushInt (.num cdepthSetGasExactMinusOne), .tonEnvOp .setGasLimit, cdepthInstr], rng2)
    else
      (mkCdepthCase "fuzz/type/top-empty-tuple" #[.tuple #[]], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := cdepthId
  unit := #[
    -- Branch: success contract on `null` and cells with different depth shapes.
    { name := "unit/direct/success-null-and-depth-samples"
      run := do
        let samples : Array (String × Option Cell) :=
          #[
            ("null", none),
            ("cell-depth0-empty", some cellDepth0),
            ("cell-depth1", some cellDepth1),
            ("cell-depth3", some cellDepth3),
            ("cell-depth5-chain", some cellDepth5),
            ("cell-depth5-wide", some cellWideDepth5),
            ("cell-library-special", some specialLibraryCell)
          ]
        for sample in samples do
          let st :=
            match sample.2 with
            | none => #[.null]
            | some c => #[.cell c]
          expectOkStack sample.1
            (runCdepthDirect st)
            (expectedCdepthOut #[] sample.2) }
    ,
    -- Branch: pop/replace affects only the top argument; below-stack values are preserved.
    { name := "unit/direct/deep-stack-preserved"
      run := do
        let belowA : Array Value := #[.null, intV 77, .slice (mkFullSlice 5 1)]
        expectOkStack "deep/cell"
          (runCdepthDirect (belowA ++ #[.cell cellDepth4]))
          (expectedCdepthOut belowA (some cellDepth4))

        let belowB : Array Value := #[.tuple #[], .cont (.quit 0), .cell cellDepth1]
        expectOkStack "deep/null"
          (runCdepthDirect (belowB ++ #[.null]))
          (expectedCdepthOut belowB none) }
    ,
    -- Branch: malformed exotic cell metadata does not throw; `Cell.depth` falls back to `0`.
    { name := "unit/direct/malformed-special-depth-fallback"
      run := do
        let malformed : Array (String × Cell) :=
          #[("short7", malformedSpecialShort7), ("tag255", malformedSpecialTag255)]
        for p in malformed do
          match p.2.computeLevelInfo? with
          | .ok _ =>
              throw (IO.userError s!"{p.1}: expected malformed special cell metadata")
          | .error _ =>
              expectOkStack s!"fallback/{p.1}"
                (runCdepthDirect #[.cell p.2])
                #[intV 0] }
    ,
    -- Branch: all failures come from `popMaybeCell` (`stkUnd` or `typeChk`).
    { name := "unit/direct/errors-underflow-and-type"
      run := do
        expectErr "underflow/empty" (runCdepthDirect #[]) .stkUnd
        expectErr "type/top-int" (runCdepthDirect #[intV (-1)]) .typeChk
        expectErr "type/top-slice" (runCdepthDirect #[.slice (mkFullSlice 6 0)]) .typeChk
        expectErr "type/top-builder" (runCdepthDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-empty-tuple" (runCdepthDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-quit0-cont" (runCdepthDirect #[.cont (.quit 0)]) .typeChk }
    ,
    -- Branch: top-of-stack type is checked first even when a valid cell is below it.
    { name := "unit/direct/error-order-top-first"
      run := do
        expectErr "top-int-over-cell"
          (runCdepthDirect #[.cell cellDepth3, intV 9]) .typeChk
        expectErr "top-builder-over-cell"
          (runCdepthDirect #[.cell cellDepth2, .builder Builder.empty]) .typeChk }
    ,
    -- Branch invariant: CDEPTH should not produce unrelated exceptions.
    { name := "unit/direct/no-unexpected-exceptions"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok-null", runCdepthDirect #[.null]),
            ("ok-cell", runCdepthDirect #[.cell cellDepth2]),
            ("underflow", runCdepthDirect #[]),
            ("type", runCdepthDirect #[.builder Builder.empty])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for CDEPTH")
          | .error .cellUnd =>
              throw (IO.userError s!"{p.1}: unexpected cellUnd for CDEPTH")
          | .error .intOv =>
              throw (IO.userError s!"{p.1}: unexpected intOv for CDEPTH")
          | _ => pure () }
    ,
    -- Branch: opcode/decode boundary around `0xd765` and nearby `0xd76x` opcodes.
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let single ←
          match assembleCp0 [cdepthInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble cdepth failed: {e}")
        if single.bits = natToBits cdepthWord 16 then
          pure ()
        else
          throw (IO.userError s!"cdepth canonical encode mismatch: got bits {single.bits}")

        let seq : BitString :=
          natToBits sdepthWord 16 ++
          natToBits cdepthWord 16 ++
          natToBits clevelWord 16 ++
          natToBits 0xb0 8
        let s0 := mkSliceFromBits seq
        let s1 ← expectDecodeStep "decode/sdepth-neighbor" s0 (.cellOp .sdepth) 16
        let s2 ← expectDecodeStep "decode/cdepth" s1 cdepthInstr 16
        let s3 ← expectDecodeStep "decode/clevel-neighbor" s2 (.cellOp .clevel) 16
        let s4 ← expectDecodeStep "decode/tail-and" s3 .and_ 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits")

        expectDecodeErr "decode/raw-0xd763-invalid"
          (mkSliceFromBits (natToBits 0xd763 16 ++ natToBits cdepthWord 16)) .invOpcode

        let raw := mkSliceFromBits (natToBits cdepthWord 16 ++ natToBits cdepthWord 16)
        let r1 ← expectDecodeStep "decode/raw-first-cdepth" raw cdepthInstr 16
        let r2 ← expectDecodeStep "decode/raw-second-cdepth" r1 cdepthInstr 16
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits") }
    ,
    -- Branch: explicit pass-through for non-target instructions.
    { name := "unit/dispatch/fallback-and-handled"
      run := do
        expectOkStack "dispatch/handled-cdepth"
          (runCdepthDispatchFallback cdepthInstr #[.cell cellDepth2])
          #[intV 2]

        expectOkStack "dispatch/non-cellop-add"
          (runCdepthDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-sdepth"
          (runCdepthDispatchFallback (.cellOp .sdepth) #[intV 8])
          #[intV 8, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-clevel"
          (runCdepthDispatchFallback (.cellOp .clevel) #[.cell cellDepth1])
          #[.cell cellDepth1, intV dispatchSentinel] }
  ]
  oracle := #[
    mkCdepthCase "ok/top-null" #[.null],
    mkCdepthCase "ok/top-cell-empty-depth0" #[.cell cellDepth0],
    mkCdepthCase "ok/top-cell-depth1" #[.cell cellDepth1],
    mkCdepthCase "ok/top-cell-depth2" #[.cell cellDepth2],
    mkCdepthCase "ok/top-cell-depth5-chain" #[.cell cellDepth5],
    mkCdepthCase "ok/top-cell-depth5-wide" #[.cell cellWideDepth5],
    mkCdepthCase "ok/top-library-special-depth0" #[.cell specialLibraryCell],

    mkCdepthCase "ok/deep-below-null-cell-depth3" #[.null, .cell cellDepth3],
    mkCdepthCase "ok/deep-below-int-cell-depth4" #[intV (-7), .cell cellDepth4],
    mkCdepthCase "ok/deep-below-cell-null-top" #[.cell cellDepth2, .null],
    mkCdepthCase "ok/deep-below-slice-cell-depth1" #[.slice (mkFullSlice 6 2), .cell cellDepth1],
    mkCdepthCase "ok/deep-below-empty-tuple-cell-depth2" #[.tuple #[], .cell cellDepth2],
    mkCdepthCase "ok/deep-below-quit0-null-top" #[.cont (.quit 0), .null],

    mkCdepthCase "underflow/empty" #[],

    mkCdepthCase "type/top-int" #[intV 42],
    mkCdepthCase "type/top-slice" #[.slice (mkFullSlice 4 0)],
    mkCdepthCase "type/top-builder" #[.builder Builder.empty],
    mkCdepthCase "type/top-empty-tuple" #[.tuple #[]],
    mkCdepthCase "type/top-quit0-cont" #[.cont (.quit 0)],
    mkCdepthCase "type/order-top-int-over-cell" #[.cell cellDepth3, intV 9],

    mkCdepthCase "gas/exact-cost-succeeds"
      #[.cell cellDepth1]
      #[.pushInt (.num cdepthSetGasExact), .tonEnvOp .setGasLimit, cdepthInstr],
    mkCdepthCase "gas/exact-minus-one-out-of-gas"
      #[.cell cellDepth1]
      #[.pushInt (.num cdepthSetGasExactMinusOne), .tonEnvOp .setGasLimit, cdepthInstr]
  ]
  fuzz := #[
    { seed := 2026021093
      count := 192
      gen := genCdepthFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.CDEPTH
