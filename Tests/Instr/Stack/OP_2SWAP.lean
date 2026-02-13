/-
INSTRUCTION: 2SWAP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Normal path] — stack has at least 4 elements; handler swaps (1,3) then (0,2), effectively
   `[a, b, c, d, ...] -> [c, d, a, b, ...]`, and returns `.ok`.
2. [Error path] — stack underflow when `size < 4`; throws `.stkUnd`.
3. [Assembler encoding] — `.twoSwap` maps to a fixed 8-bit opcode `0x5a`; there are no immediate args and no range checks for this opcode, so no rejection branches from `Asm/Cp0` beyond generic opcode handling.
4. [Decoder behavior] — 8-bit `0x5a` decodes to `.twoSwap` with 8 bits consumed.
5. [Decoder non-match + adjacency] — neighboring encodings decode to distinct instructions (`0x59`/`0x5b` etc.), so `0x5a` has no aliasing in decode.
6. [Gas edge case] — gas branch for exact budget (`computeExactGasBudget .twoSwap`) succeeds.
7. [Gas edge case] — budget minus one (`computeExactGasBudgetMinusOne .twoSwap`) should fail with out-of-gas.

TOTAL BRANCHES: 7
Each oracle test below is tagged with the branch(es) it covers.
-/

import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.OP_2SWAP

private def twoSwapId : InstrId := { name := "2SWAP" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.twoSwap])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := twoSwapId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def run2SwapDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackTwoSwap .twoSwap stack

private def twoSwapExactGas : Int :=
  computeExactGasBudget .twoSwap

private def twoSwapExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne .twoSwap

private def sampleRandomValue (rng0 : StdGen) : Value × StdGen :=
  let (mode, rng1) := randNat rng0 0 8
  if mode = 0 then
    let (n, rng2) := pickInt257Boundary rng1
    (intV n, rng2)
  else if mode = 1 then
    let (n, rng2) := pickSigned257ish rng1
    (intV n, rng2)
  else if mode = 2 then
    (.null, rng1)
  else if mode = 3 then
    (.cell Cell.empty, rng1)
  else if mode = 4 then
    (.tuple #[], rng1)
  else if mode = 5 then
    (.builder Builder.empty, rng1)
  else if mode = 6 then
    (.cont (.quit 0), rng1)
  else
    (.null, rng1)

private def sampleRandomStack (len : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut rng := rng0
  let mut out : Array Value := #[]
  let mut i : Nat := 0
  while i < len do
    let (v, rng') := sampleRandomValue rng
    out := out.push v
    rng := rng'
    i := i + 1
  pure (out, rng)

private def sampleBoundary4 (rng0 : StdGen) : Array Value × StdGen :=
  let (a, rng1) := pickInt257Boundary rng0
  let (b, rng2) := pickInt257Boundary rng1
  let (c, rng3) := pickInt257Boundary rng2
  let (d, rng4) := pickInt257Boundary rng3
  (#[intV a, intV b, intV c, intV d], rng4)

private def sampleFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  if shape = 0 then
    let (stack, rng2) := sampleBoundary4 rng1
    (mkCase "fuzz/boundary4" stack, rng2)
  else if shape = 1 then
    let (stack, rng2) := sampleRandomStack 4 rng1
    (mkCase "fuzz/random4" stack, rng2)
  else if shape = 2 then
    let (top4, rng2) := sampleBoundary4 rng1
    let (tail, rng3) := sampleRandomStack 2 rng2
    (mkCase "fuzz/long6" (top4 ++ tail), rng3)
  else if shape = 3 then
    let (stack, rng2) := sampleRandomStack 8 rng1
    (mkCase "fuzz/long8" stack, rng2)
  else if shape = 4 then
    (mkCase "fuzz/underflow_0" #[], rng1)
  else if shape = 5 then
    let (a, rng2) := pickSigned257ish rng1
    (mkCase "fuzz/underflow_1-int" #[intV a], rng2)
  else if shape = 6 then
    (mkCase "fuzz/underflow_2" #[intV 11, .null], rng1)
  else if shape = 7 then
    (mkCase "fuzz/underflow_3" #[.cell Cell.empty, .null, intV 9], rng1)
  else
    (mkCase "fuzz/underflow_1-null" #[.null], rng1)

private def assertDecode8 (label : String) (opcode : Nat) (expected : Instr) : IO Unit := do
  let code : Cell := Cell.mkOrdinary (natToBits opcode 8) #[]
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e => throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, _) =>
      if bits != 8 then
        throw (IO.userError s!"{label}: expected 8 bits, got {bits}")
      else if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")

def suite : InstrSuite where
  id := twoSwapId
  unit := #[
    { name := "unit/direct/swap-ints"
      run := do
        expectOkStack "unit/direct/1" (run2SwapDirect #[intV 1, intV 2, intV 3, intV 4]) #[intV 3, intV 4, intV 1, intV 2]
        expectOkStack "unit/direct/2" (run2SwapDirect #[intV 10, intV 20, intV 30, intV 40]) #[intV 30, intV 40, intV 10, intV 20]
        expectOkStack "unit/direct/3" (run2SwapDirect #[intV (-1), intV 7, intV 0, intV 5]) #[intV 0, intV 5, intV (-1), intV 7]
        expectOkStack "unit/direct/long" (run2SwapDirect #[intV 1, intV 2, intV 3, intV 4, .null, .cell Cell.empty]) #[intV 1, intV 2, .null, .cell Cell.empty, intV 3, intV 4]
        expectOkStack "unit/direct/types"
          (run2SwapDirect #[.null, .cell Cell.empty, .cont (.quit 0), intV 99])
          #[.cont (.quit 0), intV 99, .null, .cell Cell.empty] }
    ,
    { name := "unit/direct/underflow"
      run := do
        expectErr "unit/direct/underflow-0" (run2SwapDirect #[]) .stkUnd
        expectErr "unit/direct/underflow-1" (run2SwapDirect #[intV 11]) .stkUnd
        expectErr "unit/direct/underflow-2" (run2SwapDirect #[intV 1, intV 2]) .stkUnd
        expectErr "unit/direct/underflow-3" (run2SwapDirect #[.null, .cell Cell.empty, intV 7]) .stkUnd }
    ,
    { name := "unit/asm/roundtrip"
      run := do
        let code ←
          match assembleCp0 [.twoSwap] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/asm/roundtrip: assemble failed: {e}")
        if code.bits != natToBits 0x5a 8 then
          throw (IO.userError "unit/asm/roundtrip: wrong raw bits")
        match decodeCp0WithBits (Slice.ofCell code) with
        | .ok (instr, bits, _) =>
            if instr != .twoSwap then
              throw (IO.userError s!"unit/asm/roundtrip: expected twoSwap, got {reprStr instr}")
            if bits != 8 then
              throw (IO.userError s!"unit/asm/roundtrip: expected 8 bits, got {bits}")
        | .error e =>
            throw (IO.userError s!"unit/asm/roundtrip: decode failed with {e}")
        assertDecode8 "unit/asm/adjacent-rot" 0x59 .rotRev
        assertDecode8 "unit/asm/adjacent-drop2" 0x5b .drop2
        assertDecode8 "unit/asm/adjacent-two-over" 0x5d .twoOver
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits 0x5a 4) #[])) with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"unit/asm/truncated: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"unit/asm/truncated: expected error, got {reprStr instr} with {bits} bits") }
  ]
  oracle := #[
    -- [B1]
    mkCase "ok/bounds/ascending" #[intV 1, intV 2, intV 3, intV 4],
    -- [B1]
    mkCase "ok/bounds/descending" #[intV 4, intV 3, intV 2, intV 1],
    -- [B1]
    mkCase "ok/negative-mix" #[intV (-1), intV 7, intV (-5), intV 9],
    -- [B1]
    mkCase "ok/zeros" #[intV 0, intV 0, intV 0, intV 0],
    -- [B1]
    mkCase "ok/mixed-sign" #[intV 17, intV (-17), intV 2, intV (-2)],
    -- [B1]
    mkCase "ok/big-boundary" #[intV (maxInt257), intV (maxInt257 - 1), intV (minInt257), intV (minInt257 + 1)],
    -- [B1]
    mkCase "ok/duplicate-pair" #[intV 9, intV 9, intV 11, intV 11],
    -- [B1]
    mkCase "ok/all-top-null" #[.null, .null, .null, .null],
    -- [B1]
    mkCase "ok/all-top-cells" #[.cell Cell.empty, .cell Cell.empty, .cell Cell.empty, .cell Cell.empty],
    -- [B1]
    mkCase "ok/all-top-tuples" #[.tuple #[], .tuple #[], .tuple #[], .tuple #[]],
    -- [B1]
    mkCase "ok/all-top-builders" #[.builder Builder.empty, .builder Builder.empty, .builder Builder.empty, .builder Builder.empty],
    -- [B1]
    mkCase "ok/all-top-conts" #[.cont (.quit 0), .cont (.quit 0), .cont (.quit 0), .cont (.quit 0)],
    -- [B1]
    mkCase "ok/mixed-top" #[.null, .cell Cell.empty, .cont (.quit 0), intV 42],
    -- [B1]
    mkCase "ok/type-heavy" #[.builder Builder.empty, intV (-7), .tuple #[], .cell Cell.empty],
    -- [B1]
    mkCase "ok/with-tail-1" #[intV 1, intV 2, intV 3, intV 4, .null],
    -- [B1]
    mkCase "ok/with-tail-2" #[intV 10, intV 20, intV 30, intV 40, .cell Cell.empty, .cont (.quit 0)],
    -- [B1]
    mkCase "ok/with-tail-3" #[.null, .cell Cell.empty, intV 5, intV 6, .builder Builder.empty, .tuple #[], intV 99],
    -- [B1]
    mkCase "ok/with-tail-4" #[intV 7, intV 8, intV 9, intV 10, .null, intV 0, .cell Cell.empty],
    -- [B1]
    mkCase "ok/all-variant-top" #[.cont (.quit 0), .builder Builder.empty, .tuple #[], .cell Cell.empty],
    -- [B2]
    mkCase "err/underflow-empty" #[],
    -- [B2]
    mkCase "err/underflow-1-int" #[intV 1],
    -- [B2]
    mkCase "err/underflow-1-null" #[.null],
    -- [B2]
    mkCase "err/underflow-2-int-int" #[intV 1, intV 2],
    -- [B2]
    mkCase "err/underflow-2-mixed" #[.null, intV 3],
    -- [B2]
    mkCase "err/underflow-2-mixed-rev" #[intV 3, .cell Cell.empty],
    -- [B2]
    mkCase "err/underflow-3-mixed" #[intV 1, .null, .cell Cell.empty],
    -- [B2]
    mkCase "err/underflow-3-cont" #[.cont (.quit 0), intV 0, .builder Builder.empty],
    -- [B2]
    mkCase "err/underflow-3-builder" #[.builder Builder.empty, .tuple #[], .cont (.quit 0)],
    -- [B6]
    { name := "gas/exact-success"
      instr := twoSwapId
      program := #[.pushInt (.num twoSwapExactGas), .tonEnvOp .setGasLimit, .twoSwap]
      initStack := #[intV 1, intV 2, intV 3, intV 4]
      gasLimits := { gasLimit := twoSwapExactGas, gasMax := twoSwapExactGas, gasCredit := 0 } },
    -- [B7]
    { name := "gas/exact-minus-one-out-of-gas"
      instr := twoSwapId
      program := #[.pushInt (.num twoSwapExactGasMinusOne), .tonEnvOp .setGasLimit, .twoSwap]
      initStack := #[intV 1, intV 2, intV 3, intV 4]
      gasLimits := { gasLimit := twoSwapExactGasMinusOne, gasMax := twoSwapExactGasMinusOne, gasCredit := 0 }}
  ]
  fuzz := #[
    { seed := 2026021301
      count := 500
      gen := sampleFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.OP_2SWAP
