import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CDEPTHIX

/-
CDEPTHIX branch mapping:
- dispatch: only `.cellOp .cdepthIX` is handled; non-target instructions/opcodes fall through to `next`;
- stack checks: `popNatUpTo 3` consumes top index first (`stkUnd`/`typeChk`/`rangeChk`), then `popCell` checks the next value;
- semantic failure: any `computeLevelInfo?` failure is mapped to `cellUnd`;
- success: pushes exactly one small int `getDepth i` for `i ∈ [0, 3]`, preserving deeper stack values;
- opcode/decode: canonical encoding is `0xd771`; `0xd770` decodes as `CHASHIX` and `0xd772` remains invalid.
-/

private def cdepthIxId : InstrId := { name := "CDEPTHIX" }

private def cdepthIxInstr : Instr := .cellOp .cdepthIX

private def cdepthIxWord : Nat := 0xd771

private def dispatchSentinel : Int := 9157

private def execInstrCellOpCdepthIXOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpCdepthIX op next
  | _ => next

private def mkCdepthIxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[cdepthIxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := cdepthIxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runCdepthIxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpCdepthIXOnly cdepthIxInstr stack

private def runCdepthIxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpCdepthIXOnly instr (VM.push (intV dispatchSentinel)) stack

private def mkDepthChain : Nat → Cell
  | 0 => Cell.empty
  | n + 1 => Cell.mkOrdinary (natToBits (n + 1) 8) #[mkDepthChain n]

private def cellDepth0 : Cell := mkDepthChain 0
private def cellDepth1 : Cell := mkDepthChain 1
private def cellDepth2 : Cell := mkDepthChain 2
private def cellDepth3 : Cell := mkDepthChain 3
private def cellDepth4 : Cell := mkDepthChain 4
private def cellDepth5 : Cell := mkDepthChain 5
private def cellDepth7 : Cell := mkDepthChain 7

private def cellBranchDepth4 : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 8) #[cellDepth1, cellDepth3, cellDepth2]

private def cellBranchDepth6 : Cell :=
  Cell.mkOrdinary (natToBits 0x15 8) #[cellDepth5, cellDepth2]

private def bytesToBits (bs : Array UInt8) : BitString :=
  bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

private def depthToBytes2 (d : Nat) : Array UInt8 :=
  #[UInt8.ofNat ((d >>> 8) &&& 0xff), UInt8.ofNat (d &&& 0xff)]

private def mkPrunedMask1 (d0 : Nat) : Cell :=
  let bytes : Array UInt8 :=
    #[UInt8.ofNat 1, UInt8.ofNat 1]
      ++ Array.replicate 32 (UInt8.ofNat 0)
      ++ depthToBytes2 d0
  { bits := bytesToBits bytes, refs := #[], special := true, levelMask := 1 }

private def mkPrunedMask7 (d0 d1 d2 : Nat) : Cell :=
  let bytes : Array UInt8 :=
    #[UInt8.ofNat 1, UInt8.ofNat 7]
      ++ Array.replicate 96 (UInt8.ofNat 0)
      ++ depthToBytes2 d0
      ++ depthToBytes2 d1
      ++ depthToBytes2 d2
  { bits := bytesToBits bytes, refs := #[], special := true, levelMask := 7 }

private def prunedMask1Depth9 : Cell := mkPrunedMask1 9

private def prunedMask7Depths : Cell := mkPrunedMask7 5 7 11

private def malformedRefs5 : Cell :=
  { bits := #[], refs := Array.replicate 5 Cell.empty, special := false, levelMask := 0 }

private def malformedBits1024 : Cell :=
  { bits := Array.replicate 1024 false, refs := #[], special := false, levelMask := 0 }

private def malformedMaskOrdinary : Cell :=
  { bits := natToBits 0x13 8, refs := #[], special := false, levelMask := 1 }

private def cdepthIxDepth (c : Cell) (idx : Nat) : Except Excno Nat :=
  match c.computeLevelInfo? with
  | .ok info => .ok (info.getDepth idx)
  | .error _ => .error .cellUnd

private def expectedCdepthIxOut (below : Array Value) (c : Cell) (idx : Nat) :
    Except Excno (Array Value) := do
  let d ← cdepthIxDepth c idx
  pure (below ++ #[intV (Int.ofNat d)])

private def expectDepthOk (label : String) (below : Array Value) (c : Cell) (idx : Nat) : IO Unit := do
  let expected ←
    match expectedCdepthIxOut below c idx with
    | .ok st => pure st
    | .error e => throw (IO.userError s!"{label}: expected value derivation failed with {e}")
  let stack := below ++ #[.cell c, intV (Int.ofNat idx)]
  expectOkStack label (runCdepthIxDirect stack) expected

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
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def cdepthIxSetGasExact : Int :=
  computeExactGasBudget cdepthIxInstr

private def cdepthIxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne cdepthIxInstr

private def mkSuccessCase
    (name : String)
    (c : Cell)
    (idx : Nat)
    (below : Array Value := #[]) : OracleCase :=
  mkCdepthIxCase name (below ++ #[.cell c, intV (Int.ofNat idx)])

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkSuccessCase "ok/empty/i0" cellDepth0 0,
    mkSuccessCase "ok/empty/i3" cellDepth0 3,
    mkSuccessCase "ok/depth1/i0" cellDepth1 0,
    mkSuccessCase "ok/depth1/i3" cellDepth1 3,
    mkSuccessCase "ok/depth2/i1" cellDepth2 1,
    mkSuccessCase "ok/depth4/i2" cellDepth4 2,
    mkSuccessCase "ok/depth5/i0" cellDepth5 0,
    mkSuccessCase "ok/depth5/i3" cellDepth5 3,
    mkSuccessCase "ok/depth7/i3" cellDepth7 3,
    mkSuccessCase "ok/branch-depth4/i0" cellBranchDepth4 0,
    mkSuccessCase "ok/branch-depth4/i3" cellBranchDepth4 3,
    mkSuccessCase "ok/branch-depth6/i3" cellBranchDepth6 3,
    mkSuccessCase "ok/branch-depth6/i2" cellBranchDepth6 2,
    mkSuccessCase "ok/pruned-mask1/i0" prunedMask1Depth9 0,
    mkSuccessCase "ok/pruned-mask1/i3" prunedMask1Depth9 3,
    mkSuccessCase "ok/pruned-mask7/i0" prunedMask7Depths 0,
    mkSuccessCase "ok/pruned-mask7/i1" prunedMask7Depths 1,
    mkSuccessCase "ok/pruned-mask7/i2" prunedMask7Depths 2,
    mkSuccessCase "ok/pruned-mask7/i3" prunedMask7Depths 3,
    mkSuccessCase "ok/deep-stack/null-int-depth3/i1"
      cellDepth3 1 #[.null, intV 42],
    mkSuccessCase "ok/deep-stack/cell-null-depth6/i0"
      cellBranchDepth6 0 #[.cell cellDepth1, .null],
    mkSuccessCase "ok/deep-stack/slice-builder-pruned7/i1"
      prunedMask7Depths 1 #[.slice (Slice.ofCell cellDepth2), .builder Builder.empty]
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkCdepthIxCase "underflow/empty"
      #[],
    mkCdepthIxCase "type/top-null"
      #[.null],
    mkCdepthIxCase "type/top-cell"
      #[.cell cellDepth2],
    mkCdepthIxCase "type/top-empty-builder"
      #[.builder Builder.empty],
    mkCdepthIxCase "type/top-full-slice"
      #[.slice (Slice.ofCell cellDepth2)],
    mkCdepthIxCase "type/top-empty-tuple"
      #[.tuple #[]],
    mkCdepthIxCase "range/top-negative"
      #[.cell cellDepth2, intV (-1)],
    mkCdepthIxCase "range/top-too-large"
      #[.cell cellDepth2, intV 4],
    mkCdepthIxCase "range/top-nan-program"
      #[.cell cellDepth2]
      #[.pushInt .nan, cdepthIxInstr],
    mkCdepthIxCase "range/order-before-cell-type"
      #[.null, intV 4],
    mkCdepthIxCase "underflow/missing-cell-after-index"
      #[intV 0],
    mkCdepthIxCase "type/cell-position-null"
      #[.null, intV 2],
    mkCdepthIxCase "type/cell-position-int"
      #[intV 9, intV 1],
    mkCdepthIxCase "type/cell-position-slice"
      #[.slice (Slice.ofCell cellDepth1), intV 2],
    mkCdepthIxCase "type/cell-position-builder"
      #[.builder Builder.empty, intV 3],
    -- Malformed cell layouts (e.g. >4 refs, levelMask mismatch) are rejected by the C++ oracle at BOC
    -- deserialization time, so they are covered by unit tests only.
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkCdepthIxCase "gas/exact-cost-succeeds"
      #[.cell cellDepth3, intV 2]
      #[.pushInt (.num cdepthIxSetGasExact), .tonEnvOp .setGasLimit, cdepthIxInstr],
    mkCdepthIxCase "gas/exact-minus-one-out-of-gas"
      #[.cell cellDepth3, intV 2]
      #[.pushInt (.num cdepthIxSetGasExactMinusOne), .tonEnvOp .setGasLimit, cdepthIxInstr]
  ]

private def okCellPool : Array Cell :=
  #[
    cellDepth0,
    cellDepth1,
    cellDepth2,
    cellDepth3,
    cellDepth4,
    cellDepth5,
    cellDepth7,
    cellBranchDepth4,
    cellBranchDepth6,
    prunedMask1Depth9,
    prunedMask7Depths
  ]

private def noisePool : Array Value :=
  #[
    .null,
    intV 0,
    intV 7,
    .cell cellDepth1,
    .slice (Slice.ofCell cellDepth2),
    .builder Builder.empty,
    .tuple #[]
  ]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genCdepthIxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    (mkCdepthIxCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 1 then
    (mkCdepthIxCase "fuzz/underflow/index-only" #[intV 0], rng1)
  else if shape = 2 then
    (mkCdepthIxCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 3 then
    (mkCdepthIxCase "fuzz/type/top-cell" #[.cell cellDepth2], rng1)
  else if shape = 4 then
    (mkCdepthIxCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkCdepthIxCase "fuzz/type/top-slice" #[.slice (Slice.ofCell cellDepth1)], rng1)
  else if shape = 6 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    (mkCdepthIxCase "fuzz/ok/top-only" #[.cell c, intV (Int.ofNat idx)], rng3)
  else if shape = 7 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    let (noise, rng4) := pickFromPool noisePool rng3
    (mkCdepthIxCase "fuzz/ok/deep-noise" #[noise, .cell c, intV (Int.ofNat idx)], rng4)
  else if shape = 8 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let badCellPos : Array Value := #[.null, intV 77, .builder Builder.empty, .tuple #[]]
    let (idx, rng3) := randNat rng2 0 3
    (mkCdepthIxCase "fuzz/type/cell-position" (badCellPos ++ #[intV (Int.ofNat idx)]), rng3)
  else if shape = 9 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idxBad, rng3) := pickFromPool (#[-1, 4, 9] : Array Int) rng2
    (mkCdepthIxCase "fuzz/range/index-oob" #[.cell c, intV idxBad], rng3)
  else if shape = 10 then
    let (idxBad, rng2) := pickFromPool (#[-1, 4, 9] : Array Int) rng1
    (mkCdepthIxCase "fuzz/range/order-before-cell-type" #[.null, intV idxBad], rng2)
  else if shape = 11 then
    let (c, rng2) := pickFromPool okCellPool rng1
    (mkCdepthIxCase "fuzz/range/index-nan-program" #[.cell c] #[.pushInt .nan, cdepthIxInstr], rng2)
  else if shape = 12 then
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    let code : Array Instr := #[cdepthIxInstr, cdepthIxInstr]
    (mkCdepthIxCase "fuzz/ok/reload-same-cell-twice" #[.cell c, intV (Int.ofNat idx)] code, rng3)
  else
    let (c, rng2) := pickFromPool okCellPool rng1
    let (idx, rng3) := randNat rng2 0 3
    let stack : Array Value := #[.cell cellDepth1, .null, .cell c, intV (Int.ofNat idx)]
    (mkCdepthIxCase "fuzz/ok/deep-fixed" stack, rng3)

def suite : InstrSuite where
  id := cdepthIxId
  unit := #[
    -- Branch: success returns `getDepth i` and keeps all values below `(cell, i)` untouched.
    { name := "unit/direct/success-depth-by-index-and-stack-contract"
      run := do
        expectDepthOk "ok/ordinary-depth0-i0" #[] cellDepth0 0
        expectDepthOk "ok/ordinary-depth4-i3" #[] cellDepth4 3
        expectDepthOk "ok/ordinary-branch-depth6-i2" #[] cellBranchDepth6 2
        expectDepthOk "ok/pruned-mask1-i0" #[] prunedMask1Depth9 0
        expectDepthOk "ok/pruned-mask1-i1" #[] prunedMask1Depth9 1
        expectDepthOk "ok/pruned-mask7-i0" #[] prunedMask7Depths 0
        expectDepthOk "ok/pruned-mask7-i1" #[] prunedMask7Depths 1
        expectDepthOk "ok/pruned-mask7-i2" #[] prunedMask7Depths 2
        expectDepthOk "ok/pruned-mask7-i3" #[] prunedMask7Depths 3
        let below : Array Value := #[.null, intV 77, .cell cellDepth1]
        expectDepthOk "ok/deep-stack-preserved" below cellDepth5 1 }
    ,
    -- Branch: first pop (`popNatUpTo 3`) provides underflow/type/range failures.
    { name := "unit/direct/first-pop-underflow-type-range"
      run := do
        expectErr "underflow/empty"
          (runCdepthIxDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runCdepthIxDirect #[.null]) .typeChk
        expectErr "type/top-cell"
          (runCdepthIxDirect #[.cell cellDepth1]) .typeChk
        expectErr "type/top-builder"
          (runCdepthIxDirect #[.builder Builder.empty]) .typeChk

        expectErr "range/top-nan"
          (runCdepthIxDirect #[.int .nan]) .rangeChk
        expectErr "range/top-negative"
          (runCdepthIxDirect #[intV (-1)]) .rangeChk
        expectErr "range/top-too-large"
          (runCdepthIxDirect #[intV 4]) .rangeChk }
    ,
    -- Branch: second pop (`popCell`) checks underflow and strict cell typing.
    { name := "unit/direct/second-pop-underflow-and-type"
      run := do
        expectErr "underflow/missing-cell"
          (runCdepthIxDirect #[intV 0]) .stkUnd

        expectErr "type/cell-position-null"
          (runCdepthIxDirect #[.null, intV 0]) .typeChk
        expectErr "type/cell-position-int"
          (runCdepthIxDirect #[intV 5, intV 1]) .typeChk
        expectErr "type/cell-position-slice"
          (runCdepthIxDirect #[.slice (Slice.ofCell cellDepth1), intV 2]) .typeChk
        expectErr "type/cell-position-builder"
          (runCdepthIxDirect #[.builder Builder.empty, intV 3]) .typeChk }
    ,
    -- Branch: any level-info computation failure is translated to `cellUnd`.
    { name := "unit/direct/cellund-from-malformed-cells"
      run := do
        expectErr "cellund/refs-overflow"
          (runCdepthIxDirect #[.cell malformedRefs5, intV 0]) .cellUnd
        expectErr "cellund/bits-overflow"
          (runCdepthIxDirect #[.cell malformedBits1024, intV 0]) .cellUnd
        expectErr "cellund/level-mask-mismatch"
          (runCdepthIxDirect #[.cell malformedMaskOrdinary, intV 0]) .cellUnd }
    ,
    -- Branch: opcode contract around the `0xd771` decode/encode boundary.
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let single ←
          match assembleCp0 [cdepthIxInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble cdepthix failed: {e}")
        if single.bits = natToBits cdepthIxWord 16 then
          pure ()
        else
          throw (IO.userError s!"cdepthix canonical encode mismatch: got bits {single.bits}")

        let program : Array Instr :=
          #[.cellOp .chashIX, cdepthIxInstr, .cellOp (.cdepthI 3), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/chashix" s0 (.cellOp .chashIX) 16
        let s2 ← expectDecodeStep "decode/cdepthix" s1 cdepthIxInstr 16
        let s3 ← expectDecodeStep "decode/cdepthi3" s2 (.cellOp (.cdepthI 3)) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-0xd772-invalid"
          (mkSliceFromBits (natToBits 0xd772 16 ++ natToBits cdepthIxWord 16)) .invOpcode
        expectDecodeErr "decode/raw-0xd773-invalid"
          (mkSliceFromBits (natToBits 0xd773 16 ++ natToBits cdepthIxWord 16)) .invOpcode

        let raw := mkSliceFromBits (natToBits 0xd770 16 ++ natToBits cdepthIxWord 16)
        let r1 ← expectDecodeStep "decode/raw-chashix" raw (.cellOp .chashIX) 16
        let r2 ← expectDecodeStep "decode/raw-cdepthix" r1 cdepthIxInstr 16
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits remaining") }
    ,
    -- Branch: dispatcher passes through when the op/instruction is not `.cellOp .cdepthIX`.
    { name := "unit/dispatch/fallback-and-handled"
      run := do
        let expectedHandled ←
          match expectedCdepthIxOut #[] cellDepth4 2 with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"dispatch/handled expected derivation failed with {e}")
        expectOkStack "dispatch/handled-cdepthix"
          (runCdepthIxDispatchFallback cdepthIxInstr #[.cell cellDepth4, intV 2])
          expectedHandled

        expectOkStack "dispatch/non-cellop-add"
          (runCdepthIxDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-cdepth"
          (runCdepthIxDispatchFallback .cdepth #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-chashix"
          (runCdepthIxDispatchFallback (.cellOp .chashIX) #[.cell cellDepth1, intV 0])
          #[.cell cellDepth1, intV 0, intV dispatchSentinel] }
  ]
  oracle := oracleSuccessCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021102
      count := 500
      gen := genCdepthIxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.CDEPTHIX
