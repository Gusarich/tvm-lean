import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.OP_2DROP

/-
INSTRUCTION: 2DROP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success — when `stack.size ≥ 2`, `execInstrFlowDrop2` takes the top two
   elements and removes exactly two values from the front of the stack, preserving all deeper
   elements unchanged.
2. [B2] Runtime error — when `stack.size < 2`, both Lean (`check_underflow 2`) and C++
   (`stack.check_underflow(2)`) throw `.stkUnd`.
3. [B3] Value-kind behavior — there are no type checks in success flow; `null`, `cell`, `tuple`,
   `builder`, `cont`, and integer values are all accepted and preserved identically.
4. [B4] Assembler encoding — `.drop2` is a fixed 8-bit opcode `0x5b`; there are no
   constructor parameters and no range check branches in `encode`.
5. [B5] Decoder behavior — decoding `0x5b` yields `.drop2` with fixed `8`-bit consumption; neighboring
   opcodes decode to distinct instructions (`0x5a`/`0x5c`).
6. [B6] Gas edge — fixed base gas only (`gasPerInstr + 8`). Exact-gas execution should succeed, while
   exact-minus-one should fail on out-of-gas. No variable penalty branches are present.

TOTAL BRANCHES: 6

Each oracle test below is tagged [Bn] to the branch(es) it covers.
-/

private def drop2Id : InstrId := { name := "2DROP" }

private def drop2Instr : Instr := .drop2

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[drop2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := drop2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkDrop2CodeCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := drop2Id
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDrop2Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowDrop2 drop2Instr stack

private def drop2SetGasExact : Int :=
  computeExactGasBudget drop2Instr

private def drop2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne drop2Instr

private def drop2Raw8 : Cell :=
  Cell.mkOrdinary (natToBits 0x5b 8) #[]

private def drop2TwoSwap : Cell :=
  Cell.mkOrdinary (natToBits 0x5a 8 ++ natToBits 0x5b 8) #[]

private def drop2TwoDrop : Cell :=
  Cell.mkOrdinary (natToBits 0x5b 8 ++ natToBits 0x5b 8) #[]

private def q0 : Value := .cont (.quit 0)

private def drop2SampleNoise : Array Value :=
  #[
    .null,
    .cell Cell.empty,
    .slice (mkSliceFromBits (natToBits 0xa5 8)),
    .tuple #[],
    .builder Builder.empty,
    q0,
    intV 0,
    intV (-1),
    intV 7,
    intV maxInt257,
    intV (maxInt257 - 1),
    intV minInt257,
    intV (minInt257 + 1)
  ]

private def pickDrop2Noise (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (drop2SampleNoise.size - 1)
  (drop2SampleNoise[idx]!, rng1)

private def pickDrop2RandomStack (len : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut rng := rng0
  let mut out : Array Value := #[]
  for _ in [0:len] do
    let (x, rng') :=
      if len % 2 = 0 then
        let (n, rng2) := pickSigned257ish rng
        (intV n, rng2)
      else
        let shape : Nat := len % 4
        if shape = 0 then
          let (n, rng2) := pickInt257Boundary rng
          (intV n, rng2)
        else if shape = 1 then
          pickDrop2Noise rng
        else
          let (n, rng2) := pickSigned257ish rng
          if len % 3 = 0 then
            (intV n, rng2)
          else
            pickDrop2Noise rng2
    out := out.push x
    rng := rng'
  return (out, rng)

private def genDrop2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case, rng2) :=
    if shape = 0 then
      let (a, r2) := pickInt257Boundary rng1
      let (b, r3) := pickInt257Boundary r2
      (mkCase (s!"fuzz/boundary2/{a}/{b}") #[intV a, intV b], r3)
    else if shape = 1 then
      let (a, r2) := pickSigned257ish rng1
      let (b, r3) := pickSigned257ish r2
      (mkCase (s!"fuzz/random2/{a}/{b}") #[intV a, intV b], r3)
    else if shape = 2 then
      let (a, r2) := pickSigned257ish rng1
      let (b, r3) := pickSigned257ish r2
      let (c, r4) := pickDrop2Noise r3
      (mkCase (s!"fuzz/deep3/{a}/{b}/{reprStr c}") #[intV a, intV b, c], r4)
    else if shape = 3 then
      let (a, r2) := pickSigned257ish rng1
      let (b, r3) := pickSigned257ish r2
      let (c, r4) := pickSigned257ish r3
      let (d, r5) := pickSigned257ish r4
      (mkCase (s!"fuzz/exact4/{a}/{b}/{c}/{d}") #[intV a, intV b, intV c, intV d], r5)
    else if shape = 4 then
      let (stack, r2) := pickDrop2RandomStack 5 rng1
      (mkCase "fuzz/deep-noise-5" stack, r2)
    else if shape = 5 then
      let (stack, r2) := pickDrop2RandomStack 8 rng1
      (mkCase "fuzz/deep-noise-8" stack, r2)
    else if shape = 6 then
      (mkCase "fuzz/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (n, r2) := pickInt257Boundary rng1
      (mkCase (s!"fuzz/underflow-one/{n}") #[intV n], r2)
    else if shape = 8 then
      let (shape2, r2) := randNat rng1 0 3
      if shape2 = 0 then
        (mkCase "fuzz/underflow-one-null" #[.null], r2)
      else if shape2 = 1 then
        (mkCase "fuzz/underflow-one-cell" #[.cell Cell.empty], r2)
      else if shape2 = 2 then
        (mkCase "fuzz/underflow-one-tuple" #[.tuple #[]], r2)
      else
        (mkCase "fuzz/underflow-one-builder" #[.builder Builder.empty], r2)
    else if shape = 9 then
      let (a, r2) := pickSigned257ish rng1
      let (b, r3) := pickSigned257ish r2
      (mkCase "fuzz/gas-exact-success"
         #[intV a, intV b]
         #[.pushInt (.num drop2SetGasExact), .tonEnvOp .setGasLimit, .drop2], r3)
    else
      let (a, r2) := pickSigned257ish rng1
      let (b, r3) := pickSigned257ish r2
      (mkCase "fuzz/gas-exact-minus-one-out-of-gas"
         #[intV a, intV b]
         #[.pushInt (.num drop2SetGasExactMinusOne), .tonEnvOp .setGasLimit, .drop2], r3)
  (case, rng2)

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
  id := drop2Id
  unit := #[
    { name := "unit/direct/drop2-basic"
      run := do
        expectOkStack "unit/direct/two" (runDrop2Direct #[intV 11, intV 22]) #[]
        expectOkStack "unit/direct/three" (runDrop2Direct #[intV 1, intV 2, intV 3]) #[intV 1]
        expectOkStack "unit/direct/four"
          (runDrop2Direct #[intV 7, intV 8, intV 9, intV 10]) #[intV 7, intV 8]
        expectOkStack "unit/direct/five-tail"
          (runDrop2Direct #[intV 9, intV 10, .null, .cell Cell.empty, intV 99])
          #[intV 9, intV 10, .null]
        expectOkStack "unit/direct/non-int-tail"
          (runDrop2Direct #[.null, .cell Cell.empty, intV 1, intV 2, .tuple #[]])
          #[.null, .cell Cell.empty, intV 1] }
    ,
    { name := "unit/direct/underflow"
      run := do
        expectErr "unit/direct/underflow-empty" (runDrop2Direct #[]) .stkUnd
        expectErr "unit/direct/underflow-one" (runDrop2Direct #[intV 1]) .stkUnd
        expectErr "unit/direct/underflow-nonint" (runDrop2Direct #[q0]) .stkUnd }
    ,
    { name := "unit/asm-and-decoding"
      run := do
        let code ←
          match assembleCp0 [drop2Instr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/asm-and-decoding: assemble failed: {e}")
        if code.bits != natToBits 0x5b 8 then
          throw (IO.userError "unit/asm-and-decoding: wrong opcode bits")
        match decodeCp0WithBits (Slice.ofCell code) with
        | .ok (instr, bits, _) =>
            if instr != .drop2 then
              throw (IO.userError s!"unit/asm-and-decoding: expected drop2, got {reprStr instr}")
            if bits != 8 then
              throw (IO.userError s!"unit/asm-and-decoding: expected 8 bits, got {bits}")
        | .error e => throw (IO.userError s!"unit/asm-and-decoding: decode failed with {e}")
        assertDecode8 "unit/asm-and-decoding/adj-2swap" 0x5a .twoSwap
        assertDecode8 "unit/asm-and-decoding/adj-2dup" 0x5c .twoDup
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits 0x5b 4) #[])) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"unit/asm-and-decoding/truncated: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"unit/asm-and-decoding/truncated: expected error, got {reprStr instr} with {bits} bits") }
  ]
  oracle := #[
    -- [B1]
    mkCase "ok/int-ascending" #[intV 1, intV 2],
    -- [B1]
    mkCase "ok/int-descending" #[intV 3, intV 1],
    -- [B1]
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    -- [B1]
    mkCase "ok/mixed-sign" #[intV 17, intV (-9)],
    -- [B1]
    mkCase "ok/repeated" #[intV 7, intV 7],
    -- [B1]
    mkCase "ok/boundary-max-minus1" #[intV maxInt257, intV (maxInt257 - 1)],
    -- [B1]
    mkCase "ok/boundary-min-plus1" #[intV minInt257, intV (minInt257 + 1)],
    -- [B1]
    mkCase "ok/boundary-edges" #[intV maxInt257, intV minInt257],
    -- [B1]
    mkCase "ok/three-items" #[intV 1, intV 2, intV 3],
    -- [B1]
    mkCase "ok/four-items" #[intV 1, intV 2, intV 3, intV 4],
    -- [B1,B3]
    mkCase "ok/type-tail-nulls" #[intV 1, intV 2, .null, .null],
    -- [B1,B3]
    mkCase "ok/type-tail-cells" #[intV 4, intV 5, .cell Cell.empty, .cell Cell.empty],
    -- [B1,B3]
    mkCase "ok/type-tail-tuples" #[intV 9, intV 10, .tuple #[], .tuple #[]],
    -- [B1,B3]
    mkCase "ok/type-tail-builders" #[intV 11, intV 12, .builder Builder.empty, .builder Builder.empty],
    -- [B1,B3]
    mkCase "ok/type-tail-strings" #[intV 21, intV 22, .slice (mkSliceFromBits (natToBits 0xa5 8)), q0],
    -- [B1,B3]
    mkCase "ok/type-tail-continuations" #[intV 31, intV 32, q0, q0],
    -- [B1,B3]
    mkCase "ok/with-long-tail" #[intV 1, intV 2, intV 3, intV 4, intV 5, .tuple #[], .builder Builder.empty],
    -- [B1,B3]
    mkCase "ok/with-mixed-tail" #[intV 99, intV 100, .null, .cell Cell.empty, intV 7, intV 8],
    -- [B1,B3]
    mkCase "ok/three-plus-noise" #[.cell Cell.empty, intV 3, intV 4, .slice (mkSliceFromBits (natToBits 0x5b 8))],
    -- [B1]
    mkCase "ok/exact4/max-min-rev" #[intV (minInt257 + 1), intV maxInt257, intV (-1), intV 0],
    -- [B1]
    mkCase "ok/exact4/neg-mix" #[intV (-1), intV 0, intV 1, intV (-2)],
    -- [B2]
    mkCase "err/underflow-empty" #[],
    -- [B2]
    mkCase "err/underflow-single-int" #[intV 1],
    -- [B2]
    mkCase "err/underflow-single-null" #[.null],
    -- [B2]
    mkCase "err/underflow-single-cell" #[.cell Cell.empty],
    -- [B2]
    mkCase "err/underflow-single-tuple" #[.tuple #[]],
    -- [B2]
    mkCase "err/underflow-single-builder" #[.builder Builder.empty],
    -- [B2]
    mkCase "err/underflow-single-cont" #[q0],
    -- [B4,B5]
    mkDrop2CodeCase "asm/raw-5b" #[intV 10, intV 20] drop2Raw8,
    -- [B4,B5]
    mkDrop2CodeCase "asm/raw-5a-5b" #[intV 1, intV 2, intV 3, intV 4] drop2TwoSwap
      {},
    -- [B4,B5]
    mkDrop2CodeCase "asm/raw-5b-5b" #[intV 1, intV 2, intV 3, intV 4] drop2TwoDrop
      {},
    -- [B6]
    { name := "gas/exact-success"
      instr := drop2Id
      program := #[.pushInt (.num drop2SetGasExact), .tonEnvOp .setGasLimit, .drop2]
      initStack := #[intV 7, intV 13]
      gasLimits := { gasLimit := drop2SetGasExact, gasMax := drop2SetGasExact, gasCredit := 0 } },
    -- [B6]
    { name := "gas/exact-minus-one-out-of-gas"
      instr := drop2Id
      program := #[.pushInt (.num drop2SetGasExactMinusOne), .tonEnvOp .setGasLimit, .drop2]
      initStack := #[intV 7, intV 13]
      gasLimits := { gasLimit := drop2SetGasExactMinusOne, gasMax := drop2SetGasExactMinusOne, gasCredit := 0 } }
  ]
  fuzz := #[
    { seed := 2026030201
      count := 500
      gen := genDrop2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.OP_2DROP
