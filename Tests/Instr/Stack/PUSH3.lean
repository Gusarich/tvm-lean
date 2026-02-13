import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.PUSH3

/-
INSTRUCTION: PUSH3

BRANCH ANALYSIS (derived from reading Lean + C++ source):
1. [B1] Runtime normal-path success in `execInstrStackPush3`:
   - Underflow check is `need < st.stack.size`, where `need := max x y z`.
   - Execution order is `fetch x`, `push(fetch x)`, `fetch (y+1)`, `push(fetch y+1)`, `fetch (z+2)`, `push(fetch z+2)`.
2. [B2] Type of selected operands is unconstrained: any `Value` forms are copied unchanged and preserved on the top of the stack.
3. [B3] Runtime underflow error path:
   - If `max x y z` is not strictly less than input stack depth.
4. [B4] Boundary/adjacency stack-depth behavior:
   - Edge stack sizes at `0`, `1`, `2`, `need`, and `need+1` produce distinct outcomes.
5. [B5] Runtime dispatch branch: `.push3` executes this branch, any other instruction follows `next` (fallback).
6. [B6] Assembler validity:
   - `.push3 x y z` is accepted for `x,y,z ∈ [0,15]` and encodes as fixed-width 24-bit opcode `0x547`.
7. [B7] Assembler out-of-range error path:
   - Any argument `> 15` must raise `.rangeChk`.
8. [B8] Decoder success path:
   - 24-bit decode where `w24 >>> 12 = 0x547` maps to `.push3 x y z`, with `x=(args >>>8)&15`, `y=(args>>>4)&15`, `z=args&15`.
9. [B9] Decoder adjacency/aliasing:
   - Neighboring opcode families decode differently (`0x546` -> `.pu2xc`, and boundary aliases should not be treated as `.push3`).
10. [B10] Decoder invalid/truncated payload path:
    - Incomplete/truncated bitstream or non-matching opcode must fail with `.invOpcode`.
11. [B11] Gas base-cost success:
    - `PUSH3` uses generic `instrGas` (`gasPerInstr + totBits`) with fixed width 24.
12. [B12] Exact vs exact-minus-one gas behavior:
    - Exact budget should succeed; budget-1 should fail consistently in oracle comparison.
13. [B13] Variable gas penalties: none for argument values (`push3 0 0 0` and `push3 15 15 15` must share same nominal budget).

TOTAL BRANCHES: 13

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered via the fuzzer.
-/

private def push3Id : InstrId :=
  { name := "PUSH3" }

private def push3Opcode : Nat := 0x547

private def rawOp24 (bits : Nat) : Cell :=
  Cell.mkOrdinary (natToBits bits 24) #[]

private def push3Raw (x y z : Nat) : Cell :=
  rawOp24 ((push3Opcode <<< 12) + ((x <<< 8) + (y <<< 4) + z))

private def sentinel : Int := 271_828

private def push3SetGasExact : Int :=
  computeExactGasBudget (.push3 0 0 0)

private def push3SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.push3 0 0 0)

private def push3SetGasExactLimits : OracleGasLimits :=
  oracleGasLimitsExact push3SetGasExact

private def push3SetGasExactMinusOneLimits : OracleGasLimits :=
  oracleGasLimitsExact push3SetGasExactMinusOne

private def runPush3Direct (x y z : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPush3 (.push3 x y z) stack

private def runPush3Fallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPush3 instr (VM.push (intV sentinel)) stack

private def baseStack : Array Value :=
  #[
    intV 0,
    .null,
    intV (-1),
    .cell (Cell.mkOrdinary (natToBits 0xa5 8) #[]),
    intV 11,
    .builder Builder.empty,
    intV (-22),
    .cell (Cell.mkOrdinary (natToBits 0x5a 8) #[]),
    intV 33,
    .null,
    intV 99,
    .builder Builder.empty,
    intV 7,
    .cell (Cell.mkOrdinary (natToBits 0x13 8) #[]),
    intV (-9),
    intV 4,
    intV 42
  ]

private def stackDepth16 : Array Value := baseStack
private def stackDepth15 : Array Value := baseStack.extract 0 15
private def stackDepth9 : Array Value := baseStack.extract 0 9
private def stackDepth8 : Array Value := baseStack.extract 0 8
private def stackDepth5 : Array Value := baseStack.extract 0 5
private def stackDepth3 : Array Value := baseStack.extract 0 3
private def stackDepth2 : Array Value := baseStack.extract 0 2
private def stackDepth1 : Array Value := baseStack.extract 0 1
private def stackDepth0 : Array Value := #[]

private def expectedPush3 (stack : Array Value) (x y z : Nat) : Array Value :=
  let depth := stack.size
  let vX : Value := stack[depth - 1 - x]!
  let vY : Value := stack[depth - 1 - (y + 1)]!
  let vZ : Value := stack[depth - 1 - (z + 2)]!
  stack.push vX |>.push vY |>.push vZ

private def mkPush3Case
    (name : String)
    (x y z : Nat)
    (stack : Array Value)
    (program : Array Instr := #[(.push3 x y z)])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  {
    name := name
    instr := push3Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel
  }

private def mkPush3GasCase
    (name : String)
    (x y z : Nat)
    (stack : Array Value)
    (setGasLimit : Int)
    (fuel : Nat := 1_000_000) : OracleCase :=
  {
    name := name
    instr := push3Id
    program := #[
      .pushInt (.num setGasLimit),
      .tonEnvOp .setGasLimit,
      .push3 x y z
    ]
    initStack := stack
    gasLimits := oracleGasLimitsExact setGasLimit
    fuel := fuel
  }

private def mkPush3RawCase
    (name : String)
    (raw : Cell)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  {
    name := name
    instr := push3Id
    codeCell? := some raw
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel
  }

private def expectDecodeStepPush3
    (label : String)
    (raw : Cell)
    (expected : Instr)
    (expectedBits : Nat := 24) : IO Unit := do
  let s0 : Slice := Slice.ofCell raw
  let s1 ← expectDecodeStep label s0 expected expectedBits
  if s1.bitsRemaining + s1.refsRemaining != 0 then
    throw (IO.userError
      s!"{label}: expected empty tail after decode, got bits={s1.bitsRemaining} refs={s1.refsRemaining}")

private def expectDecodeErr
    (label : String)
    (raw : Cell)
    (expected : Excno := .invOpcode) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell raw) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, rest) =>
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instr={reprStr instr} bits={bits} tail={reprStr rest}")

private def mkFallbackCase (name : String) (x y z : Nat) (stack : Array Value) : OracleCase :=
  {
    name := name
    instr := push3Id
    program := #[.pushInt (.num (1_234 : Int)), .tonEnvOp .setGasLimit, .push3 x y z]
    initStack := stack
    gasLimits := {}
  }

private def genPush3FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    let (z, rng4) := randNat rng3 0 15
    (mkPush3Case (s!"fuzz/ok/any-{x}-{y}-{z}") x y z stackDepth16, rng4)
  else if shape = 1 then
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    let (z, rng4) := randNat rng3 0 15
    (mkPush3Case (s!"fuzz/ok/boundary-{x}-{y}-{z}") x y z stackDepth16, rng4)
  else if shape = 2 then
    (mkPush3Case "fuzz/ok/max-offsets" 15 15 15 stackDepth16, rng1)
  else if shape = 3 then
    (mkPush3Case "fuzz/err/underflow-empty" 0 0 0 stackDepth0, rng1)
  else if shape = 4 then
    (mkPush3Case "fuzz/err/underflow-small" 2 0 0 stackDepth2, rng1)
  else if shape = 5 then
    (mkPush3GasCase "fuzz/gas/exact" 0 1 2 stackDepth16 push3SetGasExact, rng1)
  else if shape = 6 then
    (mkPush3GasCase "fuzz/gas/exact-minus-one" 0 1 2 stackDepth16 push3SetGasExactMinusOne, rng1)
  else
    (mkPush3RawCase "fuzz/decoder/truncated" (Cell.mkOrdinary (natToBits 0x5470 16) #[]) stackDepth8, rng1)

def suite : InstrSuite where
  id := push3Id
  unit := #[
    { name := "unit/direct/stack-ordering-and-boundaries"
      run := do
        let checks : Array (Nat × Nat × Nat × Array Value) :=
          #[
            (0, 0, 0, stackDepth3),
            (2, 1, 0, stackDepth3),
            (0, 1, 2, stackDepth5),
            (15, 14, 13, stackDepth16),
            (15, 0, 14, stackDepth16),
            (0, 15, 14, stackDepth16),
            (15, 15, 15, stackDepth16),
            (4, 4, 4, stackDepth5),
            (7, 11, 2, stackDepth16),
            (14, 14, 14, stackDepth16)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let st := c.2.2.2
          expectOkStack
            s!"ok/{x}-{y}-{z}"
            (runPush3Direct x y z st)
            (expectedPush3 st x y z)
    }
    ,
    { name := "unit/direct/type-mix-and-deep-stack-preserved"
      run := do
        let st : Array Value :=
          #[intV 7, .null, .cell (Cell.mkOrdinary (natToBits 0x99 8) #[]), .builder Builder.empty, intV (-3), intV 42]
        expectOkStack
          "ok/non-numeric-values"
          (runPush3Direct 5 3 0 st)
          (expectedPush3 st 5 3 0)
    }
    ,
    { name := "unit/direct/underflow-variants"
      run := do
        expectErr "err/empty" (runPush3Direct 0 0 0 stackDepth0) .stkUnd
        expectErr "err/one" (runPush3Direct 0 0 0 stackDepth1) .stkUnd
        expectErr "err/two" (runPush3Direct 2 0 0 stackDepth2) .stkUnd
        expectErr "err/three" (runPush3Direct 3 0 0 stackDepth3) .stkUnd
        expectErr "err/size9" (runPush3Direct 9 8 7 stackDepth9) .stkUnd
        expectErr "err/size15" (runPush3Direct 15 14 13 stackDepth15) .stkUnd
    }
    ,
    { name := "unit/direct/dispatch-fallback"
      run := do
        expectOkStack
          "fallback-non-matching-instruction"
          (runPush3Fallback (.pushInt (.num 321)) stackDepth3)
          (stackDepth3.push (intV sentinel))
    }
    ,
    { name := "unit/asm/assemble-success-boundaries"
      run := do
        match assembleCp0 [(.push3 0 0 0)] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble 0,0,0 failed: {e}")
        match assembleCp0 [(.push3 15 15 15)] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble 15,15,15 failed: {e}")
    }
    ,
    { name := "unit/asm/assemble-out-of-range-rejections"
      run := do
        match assembleCp0 [(.push3 16 0 0)] with
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"assemble 16,0,0 expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble 16,0,0 unexpectedly succeeded")
        match assembleCp0 [(.push3 0 16 0)] with
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"assemble 0,16,0 expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble 0,16,0 unexpectedly succeeded")
        match assembleCp0 [(.push3 0 0 16)] with
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"assemble 0,0,16 expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble 0,0,16 unexpectedly succeeded")
    }
    ,
    { name := "unit/decode/roundtrip-and-neighbors"
      run := do
        expectDecodeStepPush3 "decode/roundtrip-0-0-0" (push3Raw 0 0 0) (.push3 0 0 0)
        expectDecodeStepPush3 "decode/roundtrip-15-15-15" (push3Raw 15 15 15) (.push3 15 15 15)
        expectDecodeStepPush3 "decode/neighbor-0x546" (rawOp24 (0x546 <<< 12)) (.pu2xc 0 0 0)
        expectDecodeErr "decode/neighbor-0x548" (rawOp24 (0x548 <<< 12))
        expectDecodeErr "decode/truncated-16" (Cell.mkOrdinary (natToBits 0x5470 16) #[])
    }
    ,
    { name := "unit/gas/no-variable-penalty-across-args"
      run := do
        if push3SetGasExact != computeExactGasBudget (.push3 15 15 15) then
          throw (IO.userError
            s!"expected fixed gas across offsets, got {push3SetGasExact} and {computeExactGasBudget (.push3 15 15 15)}")
    }
  ]
  oracle := #[
    -- [B1] runtime success with boundary duplicates and offsets
    mkPush3Case "ok/stack3-basic" 0 0 0 stackDepth3,
    -- [B1] runtime success with mixed offsets
    mkPush3Case "ok/stack3-mix" 2 1 0 stackDepth3,
    -- [B1] runtime success from 5-entry stack
    mkPush3Case "ok/stack5-mix" 0 1 2 stackDepth5,
    -- [B1] runtime success using high offsets
    mkPush3Case "ok/stack16-high-15-14-13" 15 14 13 stackDepth16,
    -- [B1] runtime success all arguments at max
    mkPush3Case "ok/stack16-all-max" 15 15 15 stackDepth16,
    -- [B1] runtime success with mixed types
    mkPush3Case "ok/stack16-mixed" 4 3 2 stackDepth16,
    -- [B1] runtime success repeated offsets
    mkPush3Case "ok/stack16-repeated" 7 7 7 stackDepth16,
    -- [B1] runtime success with adjacent near-top target
    mkPush3Case "ok/stack16-near-top" 0 15 14 stackDepth16,
    -- [B1] runtime success with descending offsets
    mkPush3Case "ok/stack16-descending" 14 13 12 stackDepth16,
    -- [B1] runtime success custom payload stack
    mkPush3Case "ok/stack16-null-cell" 12 11 10
      (#[.null, intV 100, .cell (Cell.mkOrdinary (natToBits 0xfe 8) #[]), intV 9, intV 1]),
    -- [B1] runtime success with top-of-stack alternation
    mkPush3Case "ok/stack16-noise" 10 5 1
      (#[(.builder Builder.empty), .null, intV (-1), .cell (Cell.mkOrdinary (natToBits 0x22 8) #[]), intV 4, intV 12, intV (-3), intV 40, intV 2, intV 9, intV 8, intV 7]),

    -- [B3] runtime underflow empty stack
    mkPush3Case "err/underflow-empty" 0 0 0 stackDepth0,
    -- [B3] runtime underflow single element
    mkPush3Case "err/underflow-one" 0 0 0 stackDepth1,
    -- [B3] runtime underflow edge at two
    mkPush3Case "err/underflow-two" 2 0 0 stackDepth2,
    -- [B3] runtime underflow with small stack and large offsets
    mkPush3Case "err/underflow-three" 3 0 0 stackDepth3,
    -- [B3] runtime underflow around size-9 boundary
    mkPush3Case "err/underflow-size9" 9 8 7 stackDepth9,
    -- [B3] runtime underflow around size-15 boundary
    mkPush3Case "err/underflow-size15" 15 14 13 stackDepth15,

    -- [B8] decode raw canonical max-form
    mkPush3RawCase "ok/raw/push3-0-0-0" (push3Raw 0 0 0) stackDepth8,
    -- [B8] decode raw canonical with mixed args
    mkPush3RawCase "ok/raw/push3-3-9-12" (push3Raw 3 9 12) stackDepth8,
    -- [B8] decode raw canonical all-15 offsets
    mkPush3RawCase "ok/raw/push3-15-15-15" (push3Raw 15 15 15) stackDepth8,
    -- [B9] decode neighbor opcode 0x546 resolves to pu2xc
    mkPush3RawCase "ok/raw/neighbor-0x546" (rawOp24 (0x546 <<< 12)) stackDepth8,
    -- [B9] decode neighbor opcode 0x548 rejects as invalid
    mkPush3RawCase "ok/raw/neighbor-0x548" (rawOp24 (0x548 <<< 12)) stackDepth8,
    -- [B10] decode truncated 16-bit payload should remain invOpcode
    mkPush3RawCase "err/raw/truncated-16" (Cell.mkOrdinary (natToBits 0x5470 16) #[]) stackDepth8,

    -- [B11,B12,B13] exact gas succeeds for fixed bitwidth
    mkPush3GasCase "gas/exact-success" 0 1 2 stackDepth16 push3SetGasExact,
    -- [B11,B12] exact gas for boundary max-offset success
    mkPush3GasCase "gas/exact-success-boundary" 15 15 15 stackDepth16 push3SetGasExact,
    -- [B12] exact-minus-one budget failure path
    mkPush3GasCase "gas/exact-minus-one-fails" 0 1 2 stackDepth16 push3SetGasExactMinusOne,
    -- [B12] exact-minus-one also on boundary offsets
    mkPush3GasCase "gas/exact-minus-one-fails-boundary" 15 15 15 stackDepth16 push3SetGasExactMinusOne
  ]
  fuzz := #[
    {
      seed := 2026021801
      count := 500
      gen := genPush3FuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PUSH3
