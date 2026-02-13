import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.PUSH2

/-
INSTRUCTION: PUSH2

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success:
   - `execInstrStackPush2` checks `need := max x y`.
   - If `need < stack.size`, it fetches `x` and `y + 1`, then pushes both values in order.
2. [B2] Runtime guard underflow:
   - If `need ≥ stack.size` (`need = max x y`), execution fails immediately with `.stkUnd`.
   - `PUSH2 s(x),s(y)` requires `max x y < stack.size` for the guard to pass.
3. [B3] Runtime post-guard underflow:
   - `need < stack.size` can still hold while `fetch (y + 1)` fails (`y + 1 = stack.size`).
4. [B4] Dispatch branch:
   - Handler only matches `.push2`; other instructions pass through `next`.
5. [B5] Assembler valid branch:
   - `.push2 x y` is legal iff `x ≤ 15` and `y ≤ 15`, encoded as fixed opcode `0x53` + args byte.
6. [B6] Assembler range error branch:
   - Any `x > 15` or `y > 15` fails with `.rangeChk`.
7. [B7] Decoder success branch:
   - Prefix `0x53` consumes 16 bits and decodes to `.push2 x y`.
8. [B8] Decoder malformed/truncated branch:
   - `0x53` without second byte, or with <16 total bits, must fail with `.invOpcode`.
9. [B9] Decoder adjacency branch:
   - Neighboring opcodes (`0x52`, `0x55`, `0x56`) decode to `.puxc`, `.blkSwap`, `.push` respectively.
10. [B10] Gas edge branch:
    - `instrGas (.push2 x y) = Nat.max x y + 1` (from oracle gas table), so exact gas succeeds and exact-1 fails.

TOTAL BRANCHES: 10
-/

private def push2Id : InstrId := { name := "PUSH2" }

private def raw8 (bits : Nat) : Cell :=
  Cell.mkOrdinary (natToBits bits 8) #[]

private def raw16 (bits : Nat) : Cell :=
  Cell.mkOrdinary (natToBits bits 16) #[]

private def push2Raw (x y : Nat) : Cell :=
  raw16 ((0x53 <<< 8) + ((x <<< 4) + y))

private def rawPuxc : Cell := raw16 (0x52 <<< 8)

private def rawBlkSwap : Cell := raw16 (0x55 <<< 8)

private def rawPush : Cell := raw16 (0x56 <<< 8)

private def rawPush2Trunc8 : Cell := raw8 0x53

private def rawPush2Trunc15 : Cell :=
  Cell.mkOrdinary (natToBits 0x5300 15) #[]

private def mkCase
    (name : String)
    (x y : Nat)
    (stack : Array Value)
    (program : Array Instr := #[.push2 x y])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := push2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := push2Id
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPush2Direct (x y : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPush2 (.push2 x y) stack

private def runPush2Fallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPush2 (.add) (VM.push (intV 77)) stack

private def expectDecodeStep
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected failure, got {reprStr instr} using {bits} bits")

private def expectAssembleRangeErr (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected range error, got success")

private def expectAssembleRoundTrip (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok code =>
      let expectedBits : Nat := 16
      expectDecodeStep label code instr expectedBits
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")

private def expectedPush2 (stack : Array Value) (x y : Nat) : Array Value :=
  let depth : Nat := stack.size
  let first : Value := stack[depth - 1 - x]!
  let second : Value := stack[depth - 1 - (y + 1)]!
  stack.push first |>.push second

private def runPush2ProgramGas (gasLimit : Int) (x y : Nat) : Array Instr :=
  #[.pushInt (.num gasLimit), .tonEnvOp .setGasLimit, .push2 x y]

private def push2ExactGas : Int :=
  computeExactGasBudget (.push2 15 15)

private def push2ExactMinusOneGas : Int :=
  computeExactGasBudgetMinusOne (.push2 15 15)

private def push2ExactGasLimits : OracleGasLimits :=
  oracleGasLimitsExact push2ExactGas

private def push2ExactMinusOneGasLimits : OracleGasLimits :=
  oracleGasLimitsExact push2ExactMinusOneGas

private def mkDepthStack (n : Nat) : Array Value :=
  Array.range n |>.map (fun i => intV (Int.ofNat (i + 1)))

private def stack0 : Array Value := #[]

private def stack1 : Array Value := mkDepthStack 1

private def stack2 : Array Value := mkDepthStack 2

private def stack3 : Array Value := mkDepthStack 3

private def stack4 : Array Value := mkDepthStack 4

private def stack5 : Array Value := mkDepthStack 5

private def stack6 : Array Value := mkDepthStack 6

private def stack7 : Array Value := mkDepthStack 7

private def stack8 : Array Value := mkDepthStack 8

private def stack10 : Array Value := mkDepthStack 10

private def stack15 : Array Value := mkDepthStack 15

private def stack16 : Array Value := mkDepthStack 16

private def stack17 : Array Value := mkDepthStack 17

private def minStackSizeForPush2 (x y : Nat) : Nat :=
  Nat.max x (y + 1) + 1

private def stackMixed : Array Value :=
  #[
    .null,
    .cell Cell.empty,
    .tuple #[],
    .builder Builder.empty,
    intV 42,
    intV (-7),
    .cont (.quit 0),
    intV maxInt257,
    intV minInt257,
    .tuple (#[])
  ]

private def pickPush2Arg (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then (1, rng1)
  else if mode = 2 then (2, rng1)
  else if mode = 3 then (3, rng1)
  else if mode = 4 then (7, rng1)
  else if mode = 5 then (8, rng1)
  else if mode = 6 then (14, rng1)
  else if mode = 7 then (15, rng1)
  else randNat rng1 0 15

private def pickPush2Value (rng0 : StdGen) : Value × StdGen :=
  let (mode, rng1) := randNat rng0 0 10
  if mode = 0 then
    (intV 0, rng1)
  else if mode = 1 then
    (intV 1, rng1)
  else if mode = 2 then
    (intV (-1), rng1)
  else if mode = 3 then
    (intV maxInt257, rng1)
  else if mode = 4 then
    (intV minInt257, rng1)
  else if mode = 5 then
    (intV 42, rng1)
  else if mode = 6 then
    (intV (-42), rng1)
  else if mode = 7 then
    (.null, rng1)
  else if mode = 8 then
    (.cell Cell.empty, rng1)
  else if mode = 9 then
    (.tuple #[], rng1)
  else
    let (n, rng2) := pickSigned257ish rng1
    (intV n, rng2)

private def randomStack (size : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in Finset.range size do
      let (v, rng') := pickPush2Value rng
      out := out.push v
      rng := rng'
    return (out, rng)

private def genPush2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (tag, rng2) := randNat rng1 0 999_999
  let (rawCase, rng3) : OracleCase × StdGen :=
    match shape with
    | 0 =>
        let (x, rng4) := pickPush2Arg rng2
        let (y, rng5) := pickPush2Arg rng4
        let needed := minStackSizeForPush2 x y
        let (bonus, rng6) := randNat rng5 0 4
        let (stack, rng7) := randomStack (needed + bonus) rng6
        (mkCase "fuzz/ok/safe" x y stack, rng7)
    | 1 =>
        let (x, rng4) := pickPush2Arg rng2
        let (y, rng5) := pickPush2Arg rng4
        let needed := minStackSizeForPush2 x y
        let (stack, rng6) := randomStack (needed + 1) rng5
        (mkCase "fuzz/ok/safe-noise" x y stack, rng6)
    | 2 =>
        let (x, rng4) := pickPush2Arg rng2
        let (y, rng5) := pickPush2Arg rng4
        (mkCase "fuzz/ok/boundary-max" x y stack17, rng5)
    | 3 =>
        let (x, rng4) := pickPush2Arg rng2
        let (y, rng5) := pickPush2Arg rng4
        (mkCase "fuzz/err/guard-empty" x y stack0, rng5)
    | 4 =>
        let (x, rng4) := pickPush2Arg rng2
        let (y, rng5) := pickPush2Arg rng4
        let size := Nat.max x y
        let (stack, rng6) := randomStack size rng5
        (mkCase "fuzz/err/guard-tiny" x y stack, rng6)
    | 5 =>
        let (y, rng4) := randNat rng2 0 14
        let x := y
        let (stack, rng5) := randomStack (y + 1) rng4
        (mkCase "fuzz/err/fetch-boundary" x y stack, rng5)
    | 6 =>
        let (y, rng4) := randNat rng2 0 14
        let x := if y = 0 then 0 else y - 1
        let (stack, rng5) := randomStack (y + 1) rng4
        (mkCase "fuzz/err/fetch-boundary-alt" x y stack, rng5)
    | 7 =>
        let (x, rng4) := pickPush2Arg rng2
        let (y, rng5) := pickPush2Arg rng4
        (mkRawCase (s!"fuzz/decode/raw/{x}/{y}") stack3 (push2Raw x y), rng5)
    | 8 =>
        (mkRawCase "fuzz/decode/truncated8" stack1 rawPush2Trunc8, rng2)
    | 9 =>
        (mkRawCase "fuzz/decode/truncated15" stack1 rawPush2Trunc15, rng2)
    | 10 =>
        let (codeIdx, rng4) := randNat rng2 0 2
        let code : Cell :=
          if codeIdx = 0 then rawPuxc
          else if codeIdx = 1 then rawBlkSwap
          else rawPush
        (mkRawCase "fuzz/decode/neighbor" stack2 code, rng4)
    | 11 =>
        (mkCase "fuzz/gas/exact" 15 15
          stack17
          (runPush2ProgramGas push2ExactGas 15 15)
          push2ExactGasLimits, rng2)
    | _ =>
        (mkCase "fuzz/gas/minus-one" 15 15
          stack17
          (runPush2ProgramGas push2ExactMinusOneGas 15 15)
          push2ExactMinusOneGasLimits, rng2)
  ({ rawCase with name := s!"{rawCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := push2Id
  unit := #[
    { name := "unit/runtime/success/order-preserving"
      run := do
        let input : Array Value := stackMixed
        expectOkStack
          "unit/runtime/success/order-preserving"
          (runPush2Direct 2 3 input)
          (expectedPush2 input 2 3)
    },
    { name := "unit/runtime/guard-fails-on-empty"
      run := do
        expectErr "unit/runtime/guard-fails-on-empty" (runPush2Direct 0 0 stack0) .stkUnd
    },
    { name := "unit/runtime/fetch-boundary-fails-underflow"
      run := do
        let input : Array Value := stack1
        expectErr "unit/runtime/fetch-boundary-fails-underflow" (runPush2Direct 0 0 input) .stkUnd
    },
    { name := "unit/runtime/guard-small-stack-fails"
      run := do
        let input : Array Value := stack2
        expectErr "unit/runtime/guard-small-stack-fails" (runPush2Direct 2 0 input) .stkUnd
    },
    { name := "unit/runtime/dispatch-fallback"
      run := do
        expectOkStack
          "unit/runtime/dispatch-fallback"
          (runPush2Fallback #[])
          (#[(intV 77)])
    },
    { name := "unit/asm/roundtrip-low"
      run := do
        expectAssembleRoundTrip "unit/asm/roundtrip-low" (.push2 0 0)
    },
    { name := "unit/asm/roundtrip-high"
      run := do
        expectAssembleRoundTrip "unit/asm/roundtrip-high" (.push2 15 15)
    },
    { name := "unit/asm/range-error-x"
      run := do
        expectAssembleRangeErr "unit/asm/range-error-x" (.push2 16 0)
    },
    { name := "unit/asm/range-error-y"
      run := do
        expectAssembleRangeErr "unit/asm/range-error-y" (.push2 0 16)
    },
    { name := "unit/decode/success-and-neighbors"
      run := do
        expectDecodeStep "unit/decode/push2-00" (push2Raw 0 0) (.push2 0 0) 16
        expectDecodeStep "unit/decode/push2-ff" (push2Raw 15 15) (.push2 15 15) 16
        expectDecodeStep "unit/decode/neighbor-puxc" rawPuxc (.puxc 0 0) 16
        expectDecodeStep "unit/decode/neighbor-blkswap" rawBlkSwap (.blkSwap 1 1) 16
        expectDecodeStep "unit/decode/neighbor-push" rawPush (.push 0) 16
    },
    { name := "unit/decode/truncated"
      run := do
        expectDecodeErr "unit/decode/truncated8" rawPush2Trunc8 .invOpcode
        expectDecodeErr "unit/decode/truncated15" rawPush2Trunc15 .invOpcode
    },
    { name := "unit/gas/exact-vs-minus-one"
      run := do
        if push2ExactGasLimits.gasLimit != push2ExactGas then
          throw (IO.userError
            s!"unit/gas/exact-vs-minus-one: exact gas mismatch {push2ExactGasLimits.gasLimit} vs {push2ExactGas}")
        if push2ExactMinusOneGasLimits.gasLimit != push2ExactMinusOneGas then
          throw (IO.userError
            s!"unit/gas/exact-vs-minus-one: exact-1 gas mismatch {push2ExactMinusOneGasLimits.gasLimit} vs {push2ExactMinusOneGas}")
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/ok/min-depth-x0-y0" 0 0 stack2,
    -- [B1]
    mkCase "oracle/ok/min-depth-x1-y0" 1 0 stack2,
    -- [B1]
    mkCase "oracle/ok/min-depth-x0-y1" 0 1 stack2,
    -- [B1]
    mkCase "oracle/ok/min-depth-x2-y0" 2 0 stack3,
    -- [B1]
    mkCase "oracle/ok/min-depth-x0-y2" 0 2 stack3,
    -- [B1]
    mkCase "oracle/ok/min-depth-x1-y2" 1 2 stack3,
    -- [B1]
    mkCase "oracle/ok/boundary-x2-y3" 2 3 stack4,
    -- [B1]
    mkCase "oracle/ok/boundary-x8-y7" 8 7 stack10,
    -- [B1]
    mkCase "oracle/ok/boundary-x14-y15" 14 15 stack16,
    -- [B1]
    mkCase "oracle/ok/boundary-x15-y15" 15 15 stack17,
    -- [B1]
    mkCase "oracle/ok/boundary-x7-y3-mixed"
      7 3
      (#[
        .null,
        .cell Cell.empty,
        intV (-1),
        intV 7,
        intV 8,
        intV 9,
        .cont (.quit 0),
        .tuple #[],
        intV maxInt257,
        intV minInt257,
        intV 99
      ]),
    -- [B1]
    mkCase "oracle/ok/preserve-underlying"
      4 2
      (#[
        .builder Builder.empty,
        .cell Cell.empty,
        intV 10,
        intV 20,
        intV 30,
        intV 40,
        intV 50,
        intV 60,
        intV 70
      ]),

    -- [B2]
    mkCase "oracle/err/guard-empty" 0 0 stack0,
    -- [B2]
    mkCase "oracle/err/guard-single" 1 1 stack1,
    -- [B2]
    mkCase "oracle/err/guard-size2-x2-y1" 2 1 stack2,
    -- [B2]
    mkCase "oracle/err/guard-size3-x3-y3" 3 3 stack3,
    -- [B2]
    mkCase "oracle/err/guard-size5-x5-y5" 5 5 stack5,
    -- [B2]
    mkCase "oracle/err/guard-size7-x7-y1" 7 1 stack7,

    -- [B3]
    mkCase "oracle/err/fetch-size1-x0-y0" 0 0 stack1,
    -- [B3]
    mkCase "oracle/err/fetch-size2-x1-y0" 1 0 stack2,
    -- [B3]
    mkCase "oracle/err/fetch-size2-x2-y1" 2 1 stack2,
    -- [B3]
    mkCase "oracle/err/fetch-size4-x3-y3" 3 3 stack4,
    -- [B3]
    mkCase "oracle/err/fetch-size6-x10-y14" 10 14 stack15,
    -- [B3]
    mkCase "oracle/err/fetch-size16-x14-y15" 14 15 stack16,

    -- [B5]
    mkCase "oracle/asm/low" 0 0 stack2,
    -- [B5]
    mkCase "oracle/asm/high" 15 15 stack17,
    -- [B5]
    mkCase "oracle/asm/boundary" 0 15 stack16,

    -- [B6]
    { name := "oracle/asm/err/x-overflow", instr := push2Id, program := #[.push2 16 0], initStack := stack2 },
    -- [B6]
    { name := "oracle/asm/err/y-overflow", instr := push2Id, program := #[.push2 0 16], initStack := stack2 },
    -- [B6]
    { name := "oracle/asm/err/both-overflow", instr := push2Id, program := #[.push2 16 16], initStack := stack2 },

    -- [B7]
    mkRawCase "oracle/decode/ok/push2-00" stack1 (push2Raw 0 0),
    -- [B7]
    mkRawCase "oracle/decode/ok/push2-ff" stack1 (push2Raw 15 15),
    -- [B7]
    mkRawCase "oracle/decode/ok/push2-7f" stack1 (push2Raw 7 15),

    -- [B8]
    mkRawCase "oracle/decode/err/truncated8" stack1 rawPush2Trunc8,
    -- [B8]
    mkRawCase "oracle/decode/err/truncated15" stack1 rawPush2Trunc15,

    -- [B9]
    mkRawCase "oracle/decode/neighbor/puxc" stack2 rawPuxc,
    -- [B9]
    mkRawCase "oracle/decode/neighbor/blkswap" stack2 rawBlkSwap,
    -- [B9]
    mkRawCase "oracle/decode/neighbor/push" stack2 rawPush,

    -- [B10]
    mkCase "oracle/gas/exact" 15 15
      stack17
      (runPush2ProgramGas push2ExactGas 15 15)
      push2ExactGasLimits,
    -- [B10]
    mkCase "oracle/gas/exact-minus-one" 15 15
      stack17
      (runPush2ProgramGas push2ExactMinusOneGas 15 15)
      push2ExactMinusOneGasLimits
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr push2Id
      count := 500
      gen := genPush2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PUSH2
