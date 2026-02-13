import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.DEPTH

/-
INSTRUCTION: DEPTH

BRANCH ANALYSIS (derived from Lean + C++ source):
1. [Dispatch] `execInstrStackDepth` handles only `.depth`:
   - match branch executes handler body when `i = .depth`;
   - all other opcodes pass to `next`.
2. [Runtime semantics] Success path computes `Int.ofNat st.stack.size` and appends it:
   - stack always preserves all pre-existing values and grows by one.
   - works for empty and non-empty stacks, and mixed-value topologies.
3. [Runtime error] No explicit underflow/type/range checks are present on `DEPTH`:
   - unlike many stack ops, this instruction cannot fail in C++ via stack checks;
   - underflow/type/range branches are therefore absent here.
4. [Assembler encoding] `.depth` is fixed-width and parameter-free:
   - canonical encoding in `Asm/Cp0` is exact `0x68 8`;
   - there are no parameter-boundary failures inside the assembler for this opcode.
5. [Decoder boundaries] decode of `0x68` is `.depth`;
   - `0x67` must remain `.xchgX`, `0x69` must remain `.chkDepth`, `0x6a` remains `.onlyTopX`;
   - nearby non-assigned values such as `0x6c/0x6f` must fail (`invOpcode`).
6. [Gas accounting] `DEPTH` is a fixed-cost instruction with no conditional gas branches:
   - gas exactness should succeed at exact budget;
   - exact minus one should fail with out-of-gas.

TOTAL BRANCHES: 6
-/

private def depthId : InstrId := { name := "DEPTH" }

private def depthInstr : Instr := .depth
private def xchgXInstr : Instr := .xchgX
private def chkDepthInstr : Instr := .chkDepth
private def onlyTopXInstr : Instr := .onlyTopX
private def invalidWord : Nat := 0x6c
private def depthWord : Nat := 0x68
private def xchgXWord : Nat := 0x67
private def chkDepthWord : Nat := 0x69
private def onlyTopXWord : Nat := 0x6a

private def dispatchSentinel : Int := 27103

private def depthCellA : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
private def depthSliceA : Slice := Slice.ofCell depthCellA

private def depthCellB : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[depthCellA]
private def depthSliceB : Slice := Slice.ofCell depthCellB

private def depthNoisePrefix : Array Value :=
  #[.null, intV 0, intV (-1), .cell depthCellA, .slice depthSliceA, .builder Builder.empty, .tuple #[], .cont (.quit 0), .cell depthCellB]

private def depthBoundaries : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 511, 768, 1023, 1024]

private def mkDepthCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[depthInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := depthId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDepthDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackDepth depthInstr stack

private def runDepthDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackDepth instr (VM.push (intV dispatchSentinel)) stack

private def depthExpectedOut (stack : Array Value) : Array Value :=
  stack ++ #[intV (Int.ofNat stack.size)]

private def mkBoundaryStack (n : Nat) : Array Value :=
  (Array.range n).map fun i =>
    let r := i % 8
    if r = 0 then
      intV (Int.ofNat (i + 1))
    else if r = 1 then
      .null
    else if r = 2 then
      .cell depthCellA
    else if r = 3 then
      .slice depthSliceA
    else if r = 4 then
      .builder Builder.empty
    else if r = 5 then
      .tuple #[]
    else if r = 6 then
      .cont (.quit 0)
    else
      intV (Int.ofNat i - 1024)

private def depthSetGasExact : Int :=
  computeExactGasBudget depthInstr

private def depthSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne depthInstr

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
      throw (IO.userError s!"{label}: expected decode error {expected}, got {instr} ({bits} bits)")

private def pickBoundarySize (rng0 : StdGen) : Nat × StdGen :=
  let (idx, rng1) := randNat rng0 0 (depthBoundaries.size - 1)
  (depthBoundaries[idx]!, rng1)

private def pickNoisePrefix (rng0 : StdGen) : Array Value × StdGen :=
  let (n, rng1) := randNat rng0 0 (depthNoisePrefix.size - 1)
  (depthNoisePrefix.extract 0 (Nat.min (n + 1) depthNoisePrefix.size), rng1)

private def genDepthFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (case0, rng2) :=
    if shape = 0 then
      (mkDepthCase "fuzz/ok/empty" #[], rng1)
    else if shape = 1 then
      (mkDepthCase "fuzz/ok/one-null" #[.null], rng1)
    else if shape = 2 then
      let (n, rng2) := pickBoundarySize rng1
      (mkDepthCase s!"fuzz/ok/boundary-{n}" (mkBoundaryStack n), rng2)
    else if shape = 3 then
      let (n, rng2) := pickBoundarySize rng1
      let (noise, rng3) := pickNoisePrefix rng2
      (mkDepthCase s!"fuzz/ok/boundary-{n}-noise" (noise ++ mkBoundaryStack n), rng3)
    else if shape = 4 then
      let (n0, rng2) := pickBoundarySize rng1
      let (n1, rng3) := pickBoundarySize rng2
      (mkDepthCase "fuzz/ok/compound" (mkBoundaryStack n0 ++ mkBoundaryStack n1), rng3)
    else if shape = 5 then
      let (n, rng2) := pickBoundarySize rng1
      let (x, rng3) := pickSigned257ish rng2
      let (noise, rng4) := pickNoisePrefix rng3
      (mkDepthCase s!"fuzz/ok/large-mixed-{n}" (mkBoundaryStack n ++ noise ++ (mkBoundaryStack 8 ++ #[intV x])), rng4)
    else if shape = 6 then
      let program := #[.pushInt (.num depthSetGasExact), .tonEnvOp .setGasLimit, depthInstr]
      (mkDepthCase "fuzz/gas/exact" #[intV 42] program, rng1)
    else if shape = 7 then
      let program := #[.pushInt (.num depthSetGasExactMinusOne), .tonEnvOp .setGasLimit, depthInstr]
      (mkDepthCase "fuzz/gas/exact-minus-one" #[intV 42] program, rng1)
    else if shape = 8 then
      (mkDepthCase "fuzz/ok/slice-top" (#[(.slice depthSliceA), intV 7, .cont (.quit 0)] ++ mkBoundaryStack 16), rng1)
    else
      let (noise, rng2) := pickNoisePrefix rng1
      (mkDepthCase "fuzz/ok/repeated-snapshot" (mkBoundaryStack 256 ++ noise ++ mkBoundaryStack 1), rng2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleCases : Array OracleCase := #[
  -- [B1,B3] Empty stack: baseline success.
  mkDepthCase "ok/empty" #[],
  -- [B1,B3,B4] Small singletons.
  mkDepthCase "ok/one-int-zero" #[intV 0],
  mkDepthCase "ok/one-int-positive" #[intV 7],
  mkDepthCase "ok/one-int-negative" #[intV (-7)],
  mkDepthCase "ok/one-null" #[.null],
  mkDepthCase "ok/one-cell" #[.cell depthCellA],
  mkDepthCase "ok/one-slice" #[.slice depthSliceA],
  mkDepthCase "ok/one-builder-empty" #[.builder Builder.empty],
  mkDepthCase "ok/one-tuple-empty" #[.tuple #[]],
  mkDepthCase "ok/one-cont-quit0" #[.cont (.quit 0)],
  -- [B1,B4] Mixed-order preservation.
  mkDepthCase "ok/mixed-small" #[.null, intV 1, .cell depthCellA, .slice depthSliceA],
  mkDepthCase "ok/mixed-preserve-1" #[.cont (.quit 0), intV 12, .tuple #[], .builder Builder.empty, .null, .cell depthCellB, .slice depthSliceB],
  mkDepthCase "ok/mixed-preserve-2" #[intV 1, .slice depthSliceB, .tuple #[], .cont (.quit 0), .cell depthCellA, intV (-3), .null, .builder Builder.empty],
  -- [B1,B4,B5] Boundary-sized stack families.
  mkDepthCase "ok/size-7" (mkBoundaryStack 7),
  mkDepthCase "ok/size-8" (mkBoundaryStack 8),
  mkDepthCase "ok/size-15" (mkBoundaryStack 15),
  mkDepthCase "ok/size-16" (mkBoundaryStack 16),
  mkDepthCase "ok/size-31" (mkBoundaryStack 31),
  mkDepthCase "ok/size-32" (mkBoundaryStack 32),
  mkDepthCase "ok/size-63" (mkBoundaryStack 63),
  mkDepthCase "ok/size-64" (mkBoundaryStack 64),
  mkDepthCase "ok/size-127" (mkBoundaryStack 127),
  mkDepthCase "ok/size-128" (mkBoundaryStack 128),
  mkDepthCase "ok/size-255" (mkBoundaryStack 255),
  mkDepthCase "ok/size-256" (mkBoundaryStack 256),
  mkDepthCase "ok/size-257" (mkBoundaryStack 257),
  mkDepthCase "ok/size-511" (mkBoundaryStack 511),
  mkDepthCase "ok/size-512" (mkBoundaryStack 512),
  mkDepthCase "ok/size-768" (mkBoundaryStack 768),
  mkDepthCase "ok/size-1023" (mkBoundaryStack 1023),
  mkDepthCase "ok/size-1024" (mkBoundaryStack 1024),
  mkDepthCase "ok/size-2048" (mkBoundaryStack 2048),
  -- [B4] Additional crafted large stack shapes.
  mkDepthCase "ok/large-mixed-1024-plus" (mkBoundaryStack 1024 ++ mkBoundaryStack 7),
  mkDepthCase "ok/large-noise-255-plus" (mkBoundaryStack 255 ++ #[.cell depthCellA, .slice depthSliceB, .null, .cont (.quit 0), .tuple #[]]),
  mkDepthCase "ok/large-noise-257-plus" (mkBoundaryStack 257 ++ depthNoisePrefix),
  -- [B6] exact gas succeeds.
  mkDepthCase "gas/exact-success"
    #[intV 5]
    #[.pushInt (.num depthSetGasExact), .tonEnvOp .setGasLimit, depthInstr],
  -- [B7] exact-gas-minus-one must fail with out-of-gas.
  mkDepthCase "gas/exact-minus-one-fails"
    #[intV 5]
    #[.pushInt (.num depthSetGasExactMinusOne), .tonEnvOp .setGasLimit, depthInstr]
]

def suite : InstrSuite where
  id := depthId
  unit := #[
    { name := "unit/direct/size-and-preserve"
      run := do
        let checks : Array (String × Array Value) :=
          #[
            ("empty", #[]),
            ("one-int", #[intV 0]),
            ("one-int-negative", #[intV (-3)]),
            ("one-null", #[.null]),
            ("short-mixed", #[.null, intV 11, .cell depthCellA]),
            ("size-7", mkBoundaryStack 7),
            ("size-16", mkBoundaryStack 16),
            ("size-257", mkBoundaryStack 257),
            ("size-1024", mkBoundaryStack 1024)
          ]
        for c in checks do
          expectOkStack s!"direct/{c.1}" (runDepthDirect c.2) (depthExpectedOut c.2) },
    { name := "unit/direct/dispatch"
      run := do
        expectOkStack "dispatch/handled-depth" (runDepthDispatchFallback depthInstr #[intV 7, .cell depthCellA])
          (depthExpectedOut #[intV 7, .cell depthCellA])
        expectOkStack "dispatch/fallback-nop"
          (runDepthDispatchFallback .nop #[intV 7, .cell depthCellA])
          (#[
            intV 7,
            .cell depthCellA,
            intV dispatchSentinel
          ]) },
    { name := "unit/decode-boundary"
      run := do
        match assembleCp0 [depthInstr] with
        | .error e =>
            throw (IO.userError s!"assemble DEPTH failed: {e}")
        | .ok cell =>
            if cell.bits != natToBits depthWord 8 then
              throw (IO.userError s!"unexpected DEPTH bits: expected {natToBits depthWord 8}, got {cell.bits}")
            else
              pure ()
        let code := mkSliceFromBits (natToBits xchgXWord 8 ++ natToBits depthWord 8 ++ natToBits chkDepthWord 8 ++ natToBits onlyTopXWord 8)
        let s1 ← expectDecodeStep "decode/xchgX" code xchgXInstr 8
        let s2 ← expectDecodeStep "decode/depth" s1 depthInstr 8
        let s3 ← expectDecodeStep "decode/chkDepth" s2 chkDepthInstr 8
        let s4 ← expectDecodeStep "decode/onlyTopX" s3 .onlyTopX 8
        if s4.bitsRemaining ≠ 0 then
          throw (IO.userError s!"expected decode tail exhaustion, got {s4.bitsRemaining} bits")
        expectDecodeErr "decode/invalid-0x6c" (mkSliceFromBits (natToBits invalidWord 8)) .invOpcode
        expectDecodeErr "decode/invalid-0x6f" (mkSliceFromBits (natToBits 0x6f 8)) .invOpcode },
    { name := "unit/self-check/oracle-count"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small, expected >=30, got {oracleCases.size}")
    }
  ]
  oracle := oracleCases ++ #[
    -- [B8] Explicitly cover decode boundaries with oracle-side raw opcode cases.
    { name := "decode/ok/xchg-depth-chk"
      instr := depthId
      codeCell? := some (Cell.mkOrdinary (natToBits xchgXWord 8 ++ natToBits depthWord 8 ++ natToBits chkDepthWord 8))
      initStack := #[] },
    -- [B8] Nearest right-neighbor decode boundary.
    { name := "decode/ok/depth-onlytopx-neighbor"
      instr := depthId
      codeCell? := some (Cell.mkOrdinary (natToBits depthWord 8 ++ natToBits onlyTopXWord 8))
      initStack := #[intV 1] },
    -- [B8] Invalid opcode is rejected at decode boundary.
    { name := "decode/err/invalid-6c"
      instr := depthId
      codeCell? := some (Cell.mkOrdinary (natToBits invalidWord 8))
      initStack := #[],
      gasLimits := { gasLimit := 1_000_000, gasMax := 1_000_000, gasCredit := 0 } }
  ]
  fuzz := #[
    { seed := 2026021407
      count := 500
      gen := genDepthFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.DEPTH
