import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BDEPTH

/-
BDEPTH branch mapping:
- dispatch: only `.cellOp .bdepth` is handled; non-target ops/instrs must fall through to `next`;
- stack checks: `popBuilder` enforces underflow (`stkUnd`) and strict top-type (`typeChk`);
- success: pushes exactly one integer `max (ref.depth + 1)` (or `0` for no refs), bits ignored;
- opcode/decode: canonical encoding is `0xcf30`; nearby holes `0xcf2f` and `0xcf34` stay invalid.
-/

private def bdepthId : InstrId := { name := "BDEPTH" }

private def bdepthInstr : Instr := .cellOp .bdepth

private def bdepthWord : Nat := 0xcf30

private def dispatchSentinel : Int := 3042

private def execInstrCellOpBdepthOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBdepth op next
  | _ => next

private def mkBdepthCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bdepthInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bdepthId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPatternBits (bitCount : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := bitCount) fun i =>
    ((i.1 + phase) % 2 = 0) || ((i.1 + phase) % 5 = 1)

private def mkBuilderWith
    (bitCount : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Builder :=
  { bits := mkPatternBits bitCount phase, refs := refs }

private def mkFullSlice
    (bitCount : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkPatternBits bitCount phase) refs)

private def mkDepthChain : Nat → Cell
  | 0 => Cell.empty
  | n + 1 =>
      Cell.mkOrdinary (natToBits (n + 1) 6) #[mkDepthChain n]

private def cellDepth0 : Cell := mkDepthChain 0
private def cellDepth1 : Cell := mkDepthChain 1
private def cellDepth2 : Cell := mkDepthChain 2
private def cellDepth3 : Cell := mkDepthChain 3
private def cellDepth4 : Cell := mkDepthChain 4
private def cellDepth4Alt : Cell := Cell.mkOrdinary (natToBits 45 6) #[cellDepth1, cellDepth3]

private def refPool : Array Cell :=
  #[cellDepth0, cellDepth1, cellDepth2, cellDepth4Alt]

private def takeRefCells (n : Nat) : Array Cell :=
  refPool.extract 0 (Nat.min n refPool.size)

private def cellsToStack (cells : Array Cell) : Array Value :=
  cells.map (fun c => .cell c)

private def bdepthNatOfRefs (refs : Array Cell) : Nat :=
  refs.foldl (fun acc r => Nat.max acc (r.depth + 1)) 0

private def expectedBdepthOutRefs (below : Array Value) (refs : Array Cell) : Array Value :=
  below ++ #[intV (Int.ofNat (bdepthNatOfRefs refs))]

private def expectedBdepthOutBuilder (below : Array Value) (b : Builder) : Array Value :=
  expectedBdepthOutRefs below b.refs

private def stuChunks (bitCount : Nat) : Array Nat :=
  let fullChunks := Array.replicate (bitCount / 256) 256
  let rem := bitCount % 256
  if rem = 0 then fullChunks else fullChunks.push rem

private def buildBuilderProgram (bitCount : Nat) (refCount : Nat := 0) : Array Instr := Id.run do
  let mut program : Array Instr := #[.newc]
  for chunk in stuChunks bitCount do
    program := program ++ #[.pushInt (.num 0), .xchg0 1, .stu chunk]
  for _ in [0:refCount] do
    program := program.push .stref
  program := program.push bdepthInstr
  return program

private def mkBdepthBuildCase
    (name : String)
    (bitCount : Nat)
    (refs : Array Cell)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let stack := below ++ cellsToStack refs
  mkBdepthCase name stack (buildBuilderProgram bitCount refs.size) gasLimits fuel

private def runBdepthDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBdepthOnly bdepthInstr stack

private def runBdepthDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBdepthOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def bdepthSetGasExact : Int :=
  computeExactGasBudget bdepthInstr

private def bdepthSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bdepthInstr

private def builderEmpty : Builder :=
  Builder.empty

private def builderBitsOnly1023 : Builder :=
  mkBuilderWith 1023 1

private def builderLeafDepth1 : Builder :=
  mkBuilderWith 9 2 #[cellDepth0]

private def builderMixedDepth4 : Builder :=
  mkBuilderWith 33 3 #[cellDepth1, cellDepth3, cellDepth2]

private def builderDeepDepth5 : Builder :=
  mkBuilderWith 511 4 #[cellDepth0, cellDepth4Alt, cellDepth2, cellDepth3]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 511, 768, 1023]

private def pickBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (bitsBoundaryPool.size - 1)
  (bitsBoundaryPool[idx]!, rng')

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then pickBitsBoundary rng1 else randNat rng1 0 1023

private def pickNoiseValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), "int", rng2)
  else if pick = 2 then
    (.cell cellDepth2, "cell", rng1)
  else if pick = 3 then
    (.slice (mkFullSlice 9 1 #[cellDepth0]), "slice", rng1)
  else
    (.builder Builder.empty, "builder", rng1)

private def pickBadTopValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 255
    (intV (Int.ofNat n - 128), "int", rng2)
  else if pick = 2 then
    (.cell cellDepth1, "cell", rng1)
  else
    (.slice (mkFullSlice 7 2), "slice", rng1)

private def genBdepthFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      (mkBdepthCase "fuzz/ok/direct-empty-builder" #[.builder Builder.empty], rng1)
    else if shape = 1 then
      let (noise, tag, rng2) := pickNoiseValue rng1
      (mkBdepthCase s!"fuzz/ok/direct-deep-{tag}" #[noise, .builder Builder.empty], rng2)
    else if shape = 2 then
      let (bits, rng2) := pickBitsBoundary rng1
      (mkBdepthBuildCase s!"fuzz/ok/program/boundary-bits-{bits}-refs0" bits #[], rng2)
    else if shape = 3 then
      let (bits, rng2) := pickBitsBoundary rng1
      let (refCount, rng3) := randNat rng2 1 4
      (mkBdepthBuildCase s!"fuzz/ok/program/boundary-bits-{bits}-refs-{refCount}"
        bits (takeRefCells refCount), rng3)
    else if shape = 4 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refCount, rng3) := randNat rng2 0 4
      (mkBdepthBuildCase s!"fuzz/ok/program/mixed-bits-{bits}-refs-{refCount}"
        bits (takeRefCells refCount), rng3)
    else if shape = 5 then
      let (refCount, rng2) := randNat rng1 1 4
      (mkBdepthBuildCase s!"fuzz/ok/program/refs-only-{refCount}" 0 (takeRefCells refCount), rng2)
    else if shape = 6 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refCount, rng3) := randNat rng2 0 4
      let (noise, tag, rng4) := pickNoiseValue rng3
      (mkBdepthBuildCase s!"fuzz/ok/program/deep-{tag}/bits-{bits}/refs-{refCount}"
        bits (takeRefCells refCount) #[noise], rng4)
    else if shape = 7 then
      (mkBdepthCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 8 then
      (mkBdepthCase "fuzz/type/top-null" #[.null], rng1)
    else if shape = 9 then
      let (n, rng2) := randNat rng1 0 255
      (mkBdepthCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
    else if shape = 10 then
      (mkBdepthCase "fuzz/type/top-cell" #[.cell cellDepth3], rng1)
    else if shape = 11 then
      (mkBdepthCase "fuzz/type/top-slice" #[.slice (mkFullSlice 6 0)], rng1)
    else if shape = 12 then
      let (bad, badTag, rng2) := pickBadTopValue rng1
      (mkBdepthCase s!"fuzz/type/order-top-{badTag}" #[.builder Builder.empty, bad], rng2)
    else if shape = 13 then
      (mkBdepthCase "fuzz/gas/exact"
        #[.builder Builder.empty]
        #[.pushInt (.num bdepthSetGasExact), .tonEnvOp .setGasLimit, bdepthInstr], rng1)
    else if shape = 14 then
      (mkBdepthCase "fuzz/gas/exact-minus-one"
        #[.builder Builder.empty]
        #[.pushInt (.num bdepthSetGasExactMinusOne), .tonEnvOp .setGasLimit, bdepthInstr], rng1)
    else
      let (noise, tag, rng2) := pickNoiseValue rng1
      (mkBdepthBuildCase s!"fuzz/stress/max/deep-{tag}" 1023 (takeRefCells 4) #[noise], rng2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkBdepthCase "ok/direct-empty-builder"
      #[.builder Builder.empty],
    mkBdepthCase "ok/direct-deep-empty-builder"
      #[intV 11, .null, .builder Builder.empty],

    mkBdepthBuildCase "ok/program/bits-0-refs0"
      0 #[],
    mkBdepthBuildCase "ok/program/bits-1-refs0"
      1 #[],
    mkBdepthBuildCase "ok/program/bits-8-refs0"
      8 #[],
    mkBdepthBuildCase "ok/program/bits-255-refs0"
      255 #[],
    mkBdepthBuildCase "ok/program/bits-256-refs0"
      256 #[],
    mkBdepthBuildCase "ok/program/bits-1023-refs0"
      1023 #[],

    mkBdepthBuildCase "ok/program/refs-only-1"
      0 (takeRefCells 1),
    mkBdepthBuildCase "ok/program/refs-only-2"
      0 (takeRefCells 2),
    mkBdepthBuildCase "ok/program/refs-only-3"
      0 (takeRefCells 3),
    mkBdepthBuildCase "ok/program/refs-only-4"
      0 (takeRefCells 4),

    mkBdepthBuildCase "ok/program/bits-32-refs2"
      32 (takeRefCells 2),
    mkBdepthBuildCase "ok/program/bits-511-refs4"
      511 (takeRefCells 4),
    mkBdepthBuildCase "ok/program/deep-int/bits-7-refs1"
      7 #[cellDepth2] #[intV (-9)],
    mkBdepthBuildCase "ok/program/deep-slice-cell/bits-19-refs3"
      19 #[cellDepth0, cellDepth3, cellDepth1]
      #[.slice (mkFullSlice 5 1 #[cellDepth0]), .cell cellDepth2],

    mkBdepthBuildCase "ok/program/deepest-ref-first"
      12 #[cellDepth4Alt, cellDepth1, cellDepth2],
    mkBdepthBuildCase "ok/program/deepest-ref-last"
      12 #[cellDepth1, cellDepth2, cellDepth4Alt]
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkBdepthCase "underflow/empty"
      #[],
    mkBdepthCase "type/top-null"
      #[.null],
    mkBdepthCase "type/top-int"
      #[intV 5],
    mkBdepthCase "type/top-cell"
      #[.cell cellDepth1],
    mkBdepthCase "type/top-full-slice"
      #[.slice (mkFullSlice 6 2 #[cellDepth0])],
    mkBdepthCase "type/order-top-null-over-builder"
      #[.builder Builder.empty, .null]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkBdepthCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty]
      #[.pushInt (.num bdepthSetGasExact), .tonEnvOp .setGasLimit, bdepthInstr],
    mkBdepthCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty]
      #[.pushInt (.num bdepthSetGasExactMinusOne), .tonEnvOp .setGasLimit, bdepthInstr]
  ]

def suite : InstrSuite where
  id := bdepthId
  unit := #[
    -- Branch: success path computes max(ref.depth + 1), preserving values below the builder.
    { name := "unit/direct/success-depth-and-stack-contract"
      run := do
        expectOkStack "ok/empty-builder"
          (runBdepthDirect #[.builder builderEmpty])
          (expectedBdepthOutBuilder #[] builderEmpty)
        expectOkStack "ok/bits-only-1023"
          (runBdepthDirect #[.builder builderBitsOnly1023])
          (expectedBdepthOutBuilder #[] builderBitsOnly1023)
        expectOkStack "ok/single-ref-depth1"
          (runBdepthDirect #[.builder builderLeafDepth1])
          (expectedBdepthOutBuilder #[] builderLeafDepth1)
        expectOkStack "ok/mixed-depth4"
          (runBdepthDirect #[.builder builderMixedDepth4])
          (expectedBdepthOutBuilder #[] builderMixedDepth4)
        expectOkStack "ok/mixed-depth5"
          (runBdepthDirect #[.builder builderDeepDepth5])
          (expectedBdepthOutBuilder #[] builderDeepDepth5)

        let below : Array Value := #[.null, intV 77, .slice (mkFullSlice 4 1)]
        expectOkStack "ok/deep-stack-preserved"
          (runBdepthDirect (below ++ #[.builder builderDeepDepth5]))
          (expectedBdepthOutBuilder below builderDeepDepth5) }
    ,
    -- Branch: all stack-shape failures come from `popBuilder`.
    { name := "unit/direct/underflow-and-type-checks"
      run := do
        expectErr "underflow/empty"
          (runBdepthDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runBdepthDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runBdepthDirect #[intV (-1)]) .typeChk
        expectErr "type/top-cell"
          (runBdepthDirect #[.cell cellDepth0]) .typeChk
        expectErr "type/top-slice"
          (runBdepthDirect #[.slice (mkFullSlice 3 0)]) .typeChk
        expectErr "type/top-tuple"
          (runBdepthDirect #[.tuple #[]]) .typeChk

        expectErr "type/order-top-null-over-builder"
          (runBdepthDirect #[.builder Builder.empty, .null]) .typeChk }
    ,
    -- Branch invariant: BDEPTH has no range-checked immediate arguments.
    { name := "unit/direct/rangechk-unreachable-for-bdepth"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runBdepthDirect #[.builder builderMixedDepth4]),
            ("underflow", runBdepthDirect #[]),
            ("type", runBdepthDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for BDEPTH")
          | _ => pure () }
    ,
    -- Branch: formula-level property across hand-picked cell-depth patterns.
    { name := "unit/direct/depth-formula-samples"
      run := do
        let samples : Array (String × Array Cell) :=
          #[
            ("none", #[]),
            ("depth0", #[cellDepth0]),
            ("depth2", #[cellDepth2]),
            ("mixed", #[cellDepth1, cellDepth4Alt, cellDepth3]),
            ("same-max", #[cellDepth4, cellDepth4Alt, cellDepth1])
          ]
        for sample in samples do
          let b := mkBuilderWith 17 4 sample.2
          expectOkStack s!"formula/{sample.1}"
            (runBdepthDirect #[.builder b])
            (expectedBdepthOutBuilder #[] b) }
    ,
    -- Branch: opcode contract at assembler/decode boundaries around the 0xcf3x family.
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let single ←
          match assembleCp0 [bdepthInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble bdepth failed: {e}")
        if single.bits = natToBits bdepthWord 16 then
          pure ()
        else
          throw (IO.userError s!"bdepth canonical encode mismatch: got bits {single.bits}")

        let program : Array Instr :=
          #[bdepthInstr, .bbits, .cellOp .brefs, .cellOp .brembits, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/bdepth" s0 bdepthInstr 16
        let s2 ← expectDecodeStep "decode/bbits" s1 .bbits 16
        let s3 ← expectDecodeStep "decode/brefs" s2 (.cellOp .brefs) 16
        let s4 ← expectDecodeStep "decode/brembits" s3 (.cellOp .brembits) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-0xcf2f-invalid"
          (mkSliceFromBits (natToBits 0xcf2f 16 ++ natToBits bdepthWord 16)) .invOpcode
        expectDecodeErr "decode/raw-0xcf34-invalid"
          (mkSliceFromBits (natToBits 0xcf34 16 ++ natToBits bdepthWord 16)) .invOpcode

        let raw := mkSliceFromBits (natToBits bdepthWord 16 ++ natToBits 0xcf31 16)
        let r1 ← expectDecodeStep "decode/raw-bdepth" raw bdepthInstr 16
        let r2 ← expectDecodeStep "decode/raw-bbits" r1 .bbits 16
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits remaining") }
    ,
    -- Branch: next-handler pass-through when op/instr does not match `.cellOp .bdepth`.
    { name := "unit/dispatch/fallback-and-handled"
      run := do
        expectOkStack "dispatch/handled-bdepth"
          (runBdepthDispatchFallback bdepthInstr #[.builder builderLeafDepth1])
          (expectedBdepthOutBuilder #[] builderLeafDepth1)

        expectOkStack "dispatch/non-cellop-add"
          (runBdepthDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-bbits"
          (runBdepthDispatchFallback .bbits #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-brefs"
          (runBdepthDispatchFallback (.cellOp .brefs) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-bchk"
          (runBdepthDispatchFallback (.cellOp (.bchk true false false)) #[.slice (mkFullSlice 2 1)])
          #[.slice (mkFullSlice 2 1), intV dispatchSentinel] }
  ]
  oracle := oracleSuccessCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021091
      count := 500
      gen := genBdepthFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BDEPTH
