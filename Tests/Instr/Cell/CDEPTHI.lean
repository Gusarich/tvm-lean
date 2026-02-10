import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CDEPTHI

/-
CDEPTHI branch mapping:
- dispatch: only `.cellOp (.cdepthI i)` is handled; all other instructions must fall through to `next`;
- stack checks: `popCell` enforces underflow (`stkUnd`) and strict top type (`typeChk`);
- success: computes `c.computeLevelInfo?`, then pushes `getDepth i` (with level clamping in `getDepth`);
- malformed metadata: any `computeLevelInfo?` failure maps to `cellUnd`;
- immediate/opcode boundaries: assembler accepts only `i ≤ 3` (`0xd76c..0xd76f`);
  nearby words decode as `0xd76b -> CHASHI 3`, `0xd770 -> CHASHIX`, `0xd771 -> CDEPTHIX`.
-/

private def cdepthiId : InstrId := { name := "CDEPTHI" }

private def cdepthiInstr (i : Nat) : Instr := .cellOp (.cdepthI i)

private def chashi3Instr : Instr := .cellOp (.chashI 3)
private def chashixInstr : Instr := .cellOp .chashIX
private def cdepthixInstr : Instr := .cellOp .cdepthIX

private def cdepthiOpcodeBase : Nat := 0xd76c

private def dispatchSentinel : Int := 7681

private def execInstrCellOpCdepthIOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpCdepthI op next
  | _ => next

private def mkCdepthiCase
    (name : String)
    (i : Nat)
    (stack : Array Value)
    (program : Array Instr := #[cdepthiInstr i])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := cdepthiId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runCdepthiDirect (i : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpCdepthIOnly (cdepthiInstr i) stack

private def runCdepthiDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpCdepthIOnly instr (VM.push (intV dispatchSentinel)) stack

private def bitsFromBytes (bytes : Array UInt8) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

private def mkPatternBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i =>
    ((i.1 + phase) % 2 = 0) || ((i.1 + phase) % 5 = 1)

private def mkFullSlice (bitCount : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkPatternBits bitCount phase) #[])

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

private def mkLibraryCell (hashSeed : Nat := 0) : Cell :=
  { bits := natToBits 2 8 ++ natToBits hashSeed 256
    refs := #[]
    special := true
    levelMask := 0 }

private def mkPrunedCell (mask : Nat) (seed : Nat := 0) : Cell :=
  let hashCount : Nat := LevelMask.getHashI mask
  let hashBytes : Array UInt8 :=
    Array.ofFn (n := hashCount * 32) fun i =>
      UInt8.ofNat ((seed + i.1 * 37 + mask * 11) % 256)
  let depthBytes : Array UInt8 :=
    Array.ofFn (n := hashCount * 2) fun i =>
      if i.1 % 2 = 0 then
        UInt8.ofNat ((seed + mask * 17 + i.1) % 4)
      else
        UInt8.ofNat ((seed + mask * 5 + i.1 * 29) % 251)
  let payload : Array UInt8 := #[UInt8.ofNat 1, UInt8.ofNat mask] ++ hashBytes ++ depthBytes
  { bits := bitsFromBytes payload
    refs := #[]
    special := true
    levelMask := mask }

private def cLibrary : Cell := mkLibraryCell 0x9A
private def cPruned1 : Cell := mkPrunedCell 1 17
private def cPruned2 : Cell := mkPrunedCell 2 29
private def cPruned7 : Cell := mkPrunedCell 7 83

private def malformedSpecialShort7 : Cell :=
  { bits := natToBits 0b1011011 7
    refs := #[]
    special := true
    levelMask := 0 }

private def malformedSpecialTag255 : Cell :=
  { bits := natToBits 255 8
    refs := #[]
    special := true
    levelMask := 0 }

private def malformedPrunedMask0 : Cell :=
  -- `type=pruned_branch`, but level mask `0` is invalid for pruned cells.
  { bits := bitsFromBytes #[UInt8.ofNat 1, UInt8.ofNat 0]
    refs := #[]
    special := true
    levelMask := 0 }

private def malformedOrdTooManyRefs : Cell :=
  Cell.mkOrdinary #[] #[cellDepth0, cellDepth1, cellDepth2, cellDepth3, cellDepth4]

private def cdepthiDepth (c : Cell) (i : Nat) : Except Excno Int := do
  let info ←
    match c.computeLevelInfo? with
    | .ok v => pure v
    | .error _ => throw .cellUnd
  pure (Int.ofNat (info.getDepth i))

private def expectedCdepthiOut (below : Array Value) (c : Cell) (i : Nat) :
    Except Excno (Array Value) := do
  let d ← cdepthiDepth c i
  pure (below ++ #[intV d])

private def expectedOutOrThrow (label : String) (below : Array Value) (c : Cell) (i : Nat) :
    IO (Array Value) := do
  match expectedCdepthiOut below c i with
  | .ok out => pure out
  | .error e => throw (IO.userError s!"{label}: failed to build expected output ({e})")

private def expectDirectOk (label : String) (i : Nat) (below : Array Value) (c : Cell) :
    IO Unit := do
  let expected ← expectedOutOrThrow label below c i
  expectOkStack label (runCdepthiDirect i (below ++ #[.cell c])) expected

private def cdepthiGasInstr : Instr := cdepthiInstr 2

private def cdepthiSetGasExact : Int :=
  computeExactGasBudget cdepthiGasInstr

private def cdepthiSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne cdepthiGasInstr

private def cdepthiSuccessPool : Array Cell :=
  #[cellDepth0, cellDepth5, cellWideDepth5, cLibrary, cPruned1, cPruned2, cPruned7]

private def pickSuccessCell (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (cdepthiSuccessPool.size - 1)
  (cdepthiSuccessPool[idx]!, rng')

private def pickNoiseValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
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
  else
    (.cont (.quit 0), "quit0", rng1)

private def genCdepthiFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (i, rng2) := randNat rng1 0 3
      let (c, rng3) := pickSuccessCell rng2
      (mkCdepthiCase s!"fuzz/ok/top/i-{i}" i #[.cell c], rng3)
    else if shape = 1 then
      let (i, rng2) := randNat rng1 0 3
      let (c, rng3) := pickSuccessCell rng2
      let (noise, tag, rng4) := pickNoiseValue rng3
      (mkCdepthiCase s!"fuzz/ok/deep-{tag}/i-{i}" i #[noise, .cell c], rng4)
    else if shape = 2 then
      (mkCdepthiCase "fuzz/ok/pruned7/i3" 3 #[.cell cPruned7], rng1)
    else if shape = 3 then
      (mkCdepthiCase "fuzz/ok/library/i1" 1 #[.cell cLibrary], rng1)
    else if shape = 4 then
      let (i, rng2) := randNat rng1 0 3
      (mkCdepthiCase s!"fuzz/ok/pruned1/i-{i}" i #[.cell cPruned1], rng2)
    else if shape = 5 then
      (mkCdepthiCase "fuzz/underflow/empty" 2 #[], rng1)
    else if shape = 6 then
      (mkCdepthiCase "fuzz/type/top-null" 1 #[.null], rng1)
    else if shape = 7 then
      let (n, rng2) := randNat rng1 0 1023
      (mkCdepthiCase s!"fuzz/type/top-int-{n}" 3 #[intV (Int.ofNat n - 512)], rng2)
    else if shape = 8 then
      (mkCdepthiCase "fuzz/type/top-slice" 0 #[.slice (mkFullSlice 7 2)], rng1)
    else if shape = 9 then
      (mkCdepthiCase "fuzz/type/top-builder" 2 #[.builder Builder.empty], rng1)
    else if shape = 10 then
      let (c, rng2) := pickSuccessCell rng1
      (mkCdepthiCase "fuzz/type/order-top-int-over-cell" 1 #[.cell c, intV 9], rng2)
    else if shape = 11 then
      let (c, rng2) := pickSuccessCell rng1
      (mkCdepthiCase "fuzz/gas/exact"
        2
        #[.cell c]
        #[.pushInt (.num cdepthiSetGasExact), .tonEnvOp .setGasLimit, cdepthiGasInstr], rng2)
    else if shape = 12 then
      let (c, rng2) := pickSuccessCell rng1
      (mkCdepthiCase "fuzz/gas/exact-minus-one"
        2
        #[.cell c]
        #[.pushInt (.num cdepthiSetGasExactMinusOne), .tonEnvOp .setGasLimit, cdepthiGasInstr], rng2)
    else if shape = 13 then
      let (i, rng2) := randNat rng1 0 3
      (mkCdepthiCase s!"fuzz/ok/pruned2/i-{i}" i #[.cell cPruned2], rng2)
    else if shape = 14 then
      (mkCdepthiCase "fuzz/type/top-cont" 0 #[.cont (.quit 0)], rng1)
    else
      (mkCdepthiCase "fuzz/type/top-empty-tuple" 0 #[.tuple #[]], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := { name := "CDEPTHI" }
  unit := #[
    -- Branch: success over valid cells and immediates, plus direct high-`i` clamp behavior.
    { name := "unit/direct/success-index-coverage-and-clamp"
      run := do
        let checks : Array (String × Nat × Cell) :=
          #[
            ("ordinary-empty/i0", 0, cellDepth0),
            ("ordinary-empty/i3", 3, cellDepth0),
            ("chain-depth5/i1", 1, cellDepth5),
            ("wide-depth5/i2", 2, cellWideDepth5),
            ("library/i0", 0, cLibrary),
            ("library/i3", 3, cLibrary),
            ("pruned1/i0", 0, cPruned1),
            ("pruned1/i3", 3, cPruned1),
            ("pruned2/i0", 0, cPruned2),
            ("pruned2/i2", 2, cPruned2),
            ("pruned7/i0", 0, cPruned7),
            ("pruned7/i1", 1, cPruned7),
            ("pruned7/i2", 2, cPruned7),
            ("pruned7/i3", 3, cPruned7)
          ]
        for check in checks do
          let label := check.1
          let idx := check.2.1
          let c := check.2.2
          expectDirectOk s!"ok/{label}" idx #[] c

        let expected3 ← expectedOutOrThrow "ok/pruned7/high-immediate-clamp" #[] cPruned7 3
        expectOkStack "ok/pruned7/high-immediate-clamp"
          (runCdepthiDirect 9 #[.cell cPruned7])
          expected3 }
    ,
    -- Branch: stack contract pops top cell and preserves everything below.
    { name := "unit/direct/deep-stack-preserved"
      run := do
        let belowA : Array Value := #[.null, intV 41, .slice (mkFullSlice 8 1)]
        expectDirectOk "deep/pruned7/i2" 2 belowA cPruned7

        let belowB : Array Value := #[.tuple #[], .cont (.quit 0), intV (-7)]
        expectDirectOk "deep/ordinary/i0" 0 belowB cellDepth5 }
    ,
    -- Branch: any metadata decoding failure in `computeLevelInfo?` must map to `cellUnd`.
    { name := "unit/direct/cellund-on-malformed-metadata"
      run := do
        let malformed : Array (String × Cell) :=
          #[
            ("special-short7", malformedSpecialShort7),
            ("special-tag255", malformedSpecialTag255),
            ("pruned-mask0", malformedPrunedMask0),
            ("ordinary-too-many-refs", malformedOrdTooManyRefs)
          ]
        for pair in malformed do
          let label := pair.1
          let c := pair.2
          match c.computeLevelInfo? with
          | .ok _ =>
              throw (IO.userError s!"{label}: expected malformed cell metadata")
          | .error _ =>
              expectErr s!"cellund/{label}/i0"
                (runCdepthiDirect 0 #[.cell c]) .cellUnd
              expectErr s!"cellund/{label}/i3"
                (runCdepthiDirect 3 #[.cell c]) .cellUnd }
    ,
    -- Branch: `popCell` provides all stack/type failures; direct handler should not raise range/int overflow.
    { name := "unit/direct/underflow-type-order-and-error-surface"
      run := do
        expectErr "underflow/empty"
          (runCdepthiDirect 1 #[]) .stkUnd

        expectErr "type/top-null"
          (runCdepthiDirect 0 #[.null]) .typeChk
        expectErr "type/top-int"
          (runCdepthiDirect 2 #[intV (-3)]) .typeChk
        expectErr "type/top-slice"
          (runCdepthiDirect 3 #[.slice (mkFullSlice 6 0)]) .typeChk
        expectErr "type/top-builder"
          (runCdepthiDirect 1 #[.builder Builder.empty]) .typeChk
        expectErr "type/top-empty-tuple"
          (runCdepthiDirect 0 #[.tuple #[]]) .typeChk
        expectErr "type/top-cont"
          (runCdepthiDirect 2 #[.cont (.quit 0)]) .typeChk

        expectErr "type/order-top-int-over-cell"
          (runCdepthiDirect 3 #[.cell cPruned7, intV 9]) .typeChk

        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok", runCdepthiDirect 0 #[.cell cellDepth0]),
            ("underflow", runCdepthiDirect 1 #[]),
            ("type", runCdepthiDirect 2 #[.null]),
            ("cellund", runCdepthiDirect 3 #[.cell malformedSpecialTag255])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for CDEPTHI")
          | .error .intOv =>
              throw (IO.userError s!"{p.1}: unexpected intOv for CDEPTHI")
          | _ => pure () }
    ,
    -- Branch: fixed-index opcode family decode and assembler immediate boundaries.
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        for idx in [0:4] do
          let assembled ←
            match assembleCp0 [cdepthiInstr idx] with
            | .ok cell => pure cell
            | .error e => throw (IO.userError s!"assemble/cdepthi-{idx} failed: {e}")
          let expectedBits := natToBits (cdepthiOpcodeBase + idx) 16
          if assembled.bits = expectedBits then
            pure ()
          else
            throw (IO.userError s!"assemble/cdepthi-{idx}: expected opcode bits {expectedBits}, got {assembled.bits}")

        match assembleCp0 [cdepthiInstr 4] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/cdepthi-4: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/cdepthi-4: expected rangeChk, got success")

        let seq : Array Instr :=
          #[chashi3Instr, cdepthiInstr 0, cdepthiInstr 1, cdepthiInstr 2, cdepthiInstr 3, chashixInstr, cdepthixInstr, .add]
        let code ←
          match assembleCp0 seq.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/chashi3-neighbor" s0 chashi3Instr 16
        let s2 ← expectDecodeStep "decode/cdepthi-0" s1 (cdepthiInstr 0) 16
        let s3 ← expectDecodeStep "decode/cdepthi-1" s2 (cdepthiInstr 1) 16
        let s4 ← expectDecodeStep "decode/cdepthi-2" s3 (cdepthiInstr 2) 16
        let s5 ← expectDecodeStep "decode/cdepthi-3" s4 (cdepthiInstr 3) 16
        let s6 ← expectDecodeStep "decode/chashix-neighbor" s5 chashixInstr 16
        let s7 ← expectDecodeStep "decode/cdepthix-neighbor" s6 cdepthixInstr 16
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s8.bitsRemaining} bits")

        let t0 := mkSliceFromBits (natToBits cdepthiOpcodeBase 14)
        let t1 ← expectDecodeStep "decode/truncated-prefix-14bits-falls-back-to-twoover" t0 .twoOver 8
        if t1.bitsRemaining = 6 then
          pure ()
        else
          throw (IO.userError s!"decode/truncated14-end: expected 6 bits remaining, got {t1.bitsRemaining}") }
    ,
    -- Branch: explicit pass-through when instruction is not `CDEPTHI`.
    { name := "unit/dispatch/fallback-and-target-match"
      run := do
        let expectedHandled ← expectedOutOrThrow "dispatch/handled-cdepthi2" #[] cPruned7 2
        expectOkStack "dispatch/handled-cdepthi2"
          (runCdepthiDispatchFallback (cdepthiInstr 2) #[.cell cPruned7])
          expectedHandled

        expectOkStack "dispatch/non-cellop-add"
          (runCdepthiDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-chashix"
          (runCdepthiDispatchFallback chashixInstr #[.cell cellDepth0])
          #[.cell cellDepth0, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-cdepth"
          (runCdepthiDispatchFallback .cdepth #[.cell cellDepth1])
          #[.cell cellDepth1, intV dispatchSentinel] }
  ]
  oracle := #[
    mkCdepthiCase "ok/ordinary-empty/i0" 0 #[.cell cellDepth0],
    mkCdepthiCase "ok/ordinary-empty/i3" 3 #[.cell cellDepth0],
    mkCdepthiCase "ok/chain-depth5/i1" 1 #[.cell cellDepth5],
    mkCdepthiCase "ok/wide-depth5/i2" 2 #[.cell cellWideDepth5],
    mkCdepthiCase "ok/library/i0" 0 #[.cell cLibrary],
    mkCdepthiCase "ok/library/i3" 3 #[.cell cLibrary],
    mkCdepthiCase "ok/pruned1/i0" 0 #[.cell cPruned1],
    mkCdepthiCase "ok/pruned1/i3" 3 #[.cell cPruned1],
    mkCdepthiCase "ok/pruned2/i0" 0 #[.cell cPruned2],
    mkCdepthiCase "ok/pruned2/i2" 2 #[.cell cPruned2],
    mkCdepthiCase "ok/pruned7/i0" 0 #[.cell cPruned7],
    mkCdepthiCase "ok/pruned7/i1" 1 #[.cell cPruned7],
    mkCdepthiCase "ok/pruned7/i3" 3 #[.cell cPruned7],
    mkCdepthiCase "ok/deep-stack-preserved/pruned7/i2" 2 #[.null, intV (-9), .cell cPruned7],

    mkCdepthiCase "underflow/empty" 1 #[],
    mkCdepthiCase "type/top-null" 0 #[.null],
    mkCdepthiCase "type/top-int" 2 #[intV 42],
    mkCdepthiCase "type/top-slice" 3 #[.slice (mkFullSlice 5 0)],
    mkCdepthiCase "type/top-builder" 1 #[.builder Builder.empty],
    mkCdepthiCase "type/top-empty-tuple" 0 #[.tuple #[]],
    mkCdepthiCase "type/order-top-int-over-cell" 0 #[.cell cPruned7, intV 7],

    mkCdepthiCase "gas/exact-cost-succeeds"
      2
      #[.cell cPruned7]
      #[.pushInt (.num cdepthiSetGasExact), .tonEnvOp .setGasLimit, cdepthiGasInstr],
    mkCdepthiCase "gas/exact-minus-one-out-of-gas"
      2
      #[.cell cPruned7]
      #[.pushInt (.num cdepthiSetGasExactMinusOne), .tonEnvOp .setGasLimit, cdepthiGasInstr]
  ]
  fuzz := #[
    { seed := 2026021031
      count := 192
      gen := genCdepthiFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.CDEPTHI
