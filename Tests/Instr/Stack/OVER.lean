import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.OVER

/-
INSTRUCTION: OVER

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success (stack depth ≥ 2): `OVER` is `PUSH 1`, so duplicate stack[1].
   This covers `[a, b] => [a, b, a]` and deeper stacks preserve all items except duplicated index.
2. [B2] Runtime underflow for empty stack: no fetch is possible, `.stkUnd`.
3. [B3] Runtime underflow for singleton stack: `< 2` values also yields `.stkUnd`.
4. [B4] Runtime depth/shape preservation: items below top-two entries must remain untouched.
5. [B5] Dispatch behavior in `execInstrStackPush`: non-`PUSH` instruction must call `next`, not mutate.
6. [B6] Assembler canonical mapping: `.push 1` encodes to opcode `0x21`.
7. [B7] Assembler boundary behavior: only the `0 <= idx <= 255` range is supported by PUSH;
   this is exercised via direct `.push` branch checks for the OVER alias and immediate reject cases.
8. [B8] Decoder canonical mapping: raw opcode `0x21` decodes to `.push 1`.
9. [B9] Decoder adjacency/aliasing: neighbors (`0x20`, `0x22`) remain distinct `.push 0` / `.push 2`.
10. [B10] Decoder malformed/truncated stream must return `invOpcode`.
11. [B11] Gas success path: exact budget computed by Lean (`computeExactGasBudget`) should execute.
12. [B12] Gas edge: exact-1 budget must fail from gas accounting before mutation.

Gas note: no data-dependent gas penalty branch exists for this instruction family, only base
`gasPerInstr + bits`.

TOTAL BRANCHES: 12
-/

private def overId : InstrId :=
  { name := "OVER" }

private def overInstr : Instr :=
  .push 1

private def overGasExact : Int :=
  computeExactGasBudget overInstr

private def overGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne overInstr

private def overGasExactLimits : OracleGasLimits :=
  oracleGasLimitsExact overGasExact

private def overGasExactMinusOneLimits : OracleGasLimits :=
  oracleGasLimitsExactMinusOne overGasExact

private def dispatchSentinel : Int :=
  42424

private def mkOverCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[overInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := overId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkOverRawCase
    (name : String)
    (code : Cell)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := overId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCell8 (byte : Nat) : Cell :=
  Cell.mkOrdinary (natToBits byte 8) #[]

private def mkCell16 (first second : Nat) : Cell :=
  Cell.mkOrdinary (natToBits first 8 ++ natToBits second 8) #[]

private def mkCell (bits : Nat) (len : Nat) : Cell :=
  Cell.mkOrdinary (natToBits bits len) #[]

private def mkEmptyCell : Cell :=
  Cell.mkOrdinary #[] #[]

private def mkOverDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPush instr (VM.push (intV dispatchSentinel)) stack

private def runOverDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPush overInstr stack

private def expectAssembleOver : IO Unit := do
  let code ←
    match assembleCp0 [overInstr] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assemble/over: expected success, got {e}")
  if code.bits = natToBits 0x21 8 then
    if code.refs.size = 0 then
      pure ()
    else
      throw (IO.userError s!"assemble/over: expected no refs, got {code.refs.size}")
  else
    throw (IO.userError s!"assemble/over: expected bits 0x21, got {reprStr code.bits}")

private def expectAssembleOverOutOfRange (label : String) (idx : Nat) : IO Unit := do
  match assembleCp0 [ .push idx ] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected rangeChk for idx={idx}, got success")
  | .error e =>
      if e != .rangeChk then
        throw (IO.userError s!"{label}: expected rangeChk, got {e}")

private def expectDecodeOver : IO Unit := do
  let s0 : Slice := Slice.ofCell (mkCell8 0x21)
  let _s1 ← expectDecodeStep "decode/over-raw-21" s0 overInstr 8
  pure ()

private def expectDecodeOverAdjacent : IO Unit := do
  let s0 : Slice := Slice.ofCell (mkCell8 0x20)
  let _ ← expectDecodeStep "decode/over-adjacent-lower" s0 (.push 0) 8
  let s1 : Slice := Slice.ofCell (mkCell8 0x22)
  let _ ← expectDecodeStep "decode/over-adjacent-upper" s1 (.push 2) 8
  pure ()

private def expectDecodeErr (label : String) (code : Cell) : IO Unit := do
  let s := Slice.ofCell code
  match decodeCp0WithBits s with
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, used, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {instr} using {used} bits")

private def overValuePool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 255,
    intV (-255),
    intV maxInt257,
    intV (maxInt257 - 1),
    intV minInt257,
    intV (minInt257 + 1),
    .null,
    .cell Cell.empty,
    .builder Builder.empty,
    .tuple #[],
    .cont (.quit 0)
  ]

private def pickOverValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (overValuePool.size - 1)
  (overValuePool[idx]!, rng1)

private def genOverStack (size : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in [0:size] do
      let (v, rng') := pickOverValue rng
      out := out.push v
      rng := rng'
    return (out, rng)

private def genOverFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (case, rng2) :=
    if shape = 0 then
      (mkOverCase "fuzz/ok/depth2/basic" #[intV 10, intV 20], rng1)
    else if shape = 1 then
      (mkOverCase "fuzz/ok/depth2/mixed" #[.null, intV 22], rng1)
    else if shape = 2 then
      let (stack, rng2) := genOverStack 4 rng1
      (mkOverCase "fuzz/ok/depth4-preserve" stack, rng2)
    else if shape = 3 then
      let (stack, rng2) := genOverStack 7 rng1
      (mkOverCase "fuzz/ok/depth7-preserve" stack, rng2)
    else if shape = 4 then
      let (stack, rng2) := genOverStack 12 rng1
      (mkOverCase "fuzz/ok/depth12-preserve" stack, rng2)
    else if shape = 5 then
      (mkOverCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 6 then
      (mkOverCase "fuzz/err/underflow-single" #[intV 7], rng1)
    else if shape = 7 then
      let gasProgram : Array Instr :=
        #[.pushInt (.num overGasExact), .tonEnvOp .setGasLimit, overInstr]
      (mkOverCase "fuzz/gas/exact" #[intV 11, intV 12] gasProgram overGasExactLimits, rng1)
    else if shape = 8 then
      let gasProgram : Array Instr :=
        #[.pushInt (.num overGasExactMinusOne), .tonEnvOp .setGasLimit, overInstr]
      (mkOverCase "fuzz/gas/exact-minus-one" #[intV 11, intV 12] gasProgram overGasExactMinusOneLimits, rng1)
    else if shape = 9 then
      (mkOverRawCase "fuzz/decode/neighbor-lower" (mkCell8 0x20) #[intV 1, intV 2], rng1)
    else if shape = 10 then
      (mkOverRawCase "fuzz/decode/neighbor-upper" (mkCell8 0x22) #[intV 1, intV 2], rng1)
    else if shape = 11 then
      (mkOverRawCase "fuzz/decode/over-tail" (mkCell16 0x21 0x58) #[intV 3, intV 4], rng1)
    else if shape = 12 then
      (mkOverRawCase "fuzz/decode/truncated-4" (mkCell 0x2 4) #[], rng1)
    else if shape = 13 then
      (mkOverCase "fuzz/dispatch-fallback-add" #[intV 1, intV 2] (program := #[.add]), rng1)
    else if shape = 14 then
      (mkOverCase "fuzz/dispatch-fallback-swap" #[intV 8, intV 9, intV 10] (program := #[.xchg0 1]), rng1)
    else
      let (stack, rng2) := genOverStack 6 rng1
      (mkOverCase "fuzz/ok/depth6-noncanonical" stack, rng2)
  (case, rng2)

def suite : InstrSuite where
  id := overId
  unit := #[
    { name := "unit/direct/success"
      run := do
        expectOkStack "unit/direct/success"
          (runOverDirect #[intV 10, intV 20])
          #[intV 10, intV 20, intV 10]
    },
    { name := "unit/direct/underflow-empty"
      run := do
        expectErr "unit/direct/underflow-empty" (runOverDirect #[]) .stkUnd
    },
    { name := "unit/direct/underflow-single"
      run := do
        expectErr "unit/direct/underflow-single" (runOverDirect #[intV 7]) .stkUnd
    },
    { name := "unit/direct/dispatch-fallback"
      run := do
        let ok := mkOverDispatchFallback .add #[intV 1, intV 2]
        expectOkStack "unit/direct/dispatch-fallback" ok #[intV 1, intV 2, intV dispatchSentinel]
    },
    { name := "unit/asm/encode-over"
      run := expectAssembleOver
    },
    { name := "unit/asm/over-range-reject-256"
      run := expectAssembleOverOutOfRange "unit/asm/over-range-reject-256" 256
    },
    { name := "unit/asm/over-range-reject-300"
      run := expectAssembleOverOutOfRange "unit/asm/over-range-reject-300" 300
    },
    { name := "unit/codec/decode-over"
      run := expectDecodeOver
    },
    { name := "unit/codec/decode-neighbors"
      run := expectDecodeOverAdjacent
    },
    { name := "unit/codec/decode-truncated-4"
      run := expectDecodeErr "unit/codec/decode-truncated-4" (mkCell 0x5 4)
    },
    { name := "unit/codec/decode-truncated-empty"
      run := expectDecodeErr "unit/codec/decode-truncated-empty" mkEmptyCell
    },
    { name := "unit/gas/branch"
      run := do
        if overGasExact <= 0 then
          throw (IO.userError s!"unit/gas/branch: computed gas is non-positive: {overGasExact}")
        if overGasExactMinusOne ≥ overGasExact then
          throw (IO.userError s!"unit/gas/branch: exact-1 is not strictly smaller ({overGasExactMinusOne} >= {overGasExact})")
        else
          pure ()
    }
  ]
  oracle := #[
    -- [B1]
    mkOverCase "runtime/ok/depth2-basic" #[intV 10, intV 20],
    -- [B1]
    mkOverCase "runtime/ok/depth2-negative" #[intV (-7), intV (-2)],
    -- [B1]
    mkOverCase "runtime/ok/depth2-nan" #[intV 3, .int .nan],
    -- [B1]
    mkOverCase "runtime/ok/depth2-null" #[.null, intV 7],
    -- [B1]
    mkOverCase "runtime/ok/depth2-cell" #[.cell Cell.empty, intV 9],
    -- [B1]
    mkOverCase "runtime/ok/depth2-builder" #[.builder Builder.empty, intV 11],
    -- [B1]
    mkOverCase "runtime/ok/depth2-tuple" #[.tuple #[], intV 13],
    -- [B1]
    mkOverCase "runtime/ok/depth2-cont" #[.cont (.quit 0), intV 17],
    -- [B1]
    mkOverCase "runtime/ok/depth3" #[intV 1, intV 2, intV 3],
    -- [B1]
    mkOverCase "runtime/ok/depth4-basic" #[intV 1, intV 2, intV 3, intV 4],
    -- [B1]
    mkOverCase "runtime/ok/depth4-non-int-tail" #[.null, .cell Cell.empty, intV 9, intV 11],
    -- [B2]
    mkOverCase "runtime/err/underflow-empty" #[],
    -- [B3]
    mkOverCase "runtime/err/underflow-single" #[intV 99],
    -- [B4]
    mkOverCase "runtime/ok/depth8-preserve-prefix" (genOverStack 8 (mkStdGen 1)).1,
    -- [B4]
    mkOverCase "runtime/ok/depth10-preserve-prefix" (genOverStack 10 (mkStdGen 2)).1,
    -- [B4]
    mkOverCase "runtime/ok/depth16-preserve-prefix" (genOverStack 16 (mkStdGen 3)).1,
    -- [B5]
    mkOverCase "dispatch/other-instr-falls-through-add" #[intV 4, intV 5] (program := #[.add]),
    -- [B5]
    mkOverCase "dispatch/other-instr-falls-through-swap" #[intV 9, intV 11, intV 13] (program := #[.xchg0 1]),
    -- [B8]
    mkOverRawCase "decode/raw-21" (mkCell8 0x21) #[intV 11, intV 12],
    -- [B8]
    mkOverRawCase "decode/raw-21-with-tail" (mkCell16 0x21 0x58) #[intV 22, intV 33],
    -- [B9]
    mkOverRawCase "decode/raw-20" (mkCell8 0x20) #[intV 44, intV 55],
    -- [B9]
    mkOverRawCase "decode/raw-22" (mkCell8 0x22) #[intV 66, intV 77],
    -- [B10]
    mkOverRawCase "decode/truncated-7" (mkCell 0x5 7) #[],
    -- [B10]
    mkOverRawCase "decode/truncated-3" (mkCell 0x0 3) #[],
    -- [B11]
    mkOverCase "gas/exact"
      #[intV 10, intV 20]
      #[.pushInt (.num overGasExact), .tonEnvOp .setGasLimit, overInstr]
      overGasExactLimits,
    -- [B11]
    mkOverCase "gas/exact-with-noise"
      #[.null, .builder Builder.empty, intV 9, intV 10]
      #[.pushInt (.num overGasExact), .tonEnvOp .setGasLimit, overInstr]
      overGasExactLimits,
    -- [B12]
    mkOverCase "gas/exact-minus-one"
      #[intV 10, intV 20]
      #[.pushInt (.num overGasExactMinusOne), .tonEnvOp .setGasLimit, overInstr]
      overGasExactMinusOneLimits,
    -- [B12]
    mkOverCase "gas/exact-minus-one-with-noise"
      #[.cell Cell.empty, intV 2, intV 3]
      #[.pushInt (.num overGasExactMinusOne), .tonEnvOp .setGasLimit, overInstr]
      overGasExactMinusOneLimits,
    -- [B6]
    mkOverCase "asm/over-encoded-form" #[intV 7, intV 8],
    -- [B7]
    mkOverCase "dispatch/other-instr-falls-through-swap-short" #[intV 1, intV 2] (program := #[.xchg0 1])
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr overId
      count := 500
      gen := genOverFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.OVER
