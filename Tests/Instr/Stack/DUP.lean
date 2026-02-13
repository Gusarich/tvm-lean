import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.DUP

/- 
INSTRUCTION: DUP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Normal path] [B1] — `DUP` is `.push 0`; with non-empty stack, `runHandlerDirect execInstrStackPush` executes `VM.fetch 0` then `VM.push`, duplicating top value and appending it once.
2. [Edge case] [B2] — runtime underflow when stack is empty (`VM.fetch 0` throws `.stkUnd` in Lean, `check_underflow(1)` in C++).
3. [Runtime property] [B3] — no type checks: any `Value` variant may be duplicated (int, null, cell, tuple, nan, etc.), and values below top are unchanged.
4. [Dispatch behavior] [B4] — `.push` path is handled by `execInstrStackPush`; non-`.push` instructions in stack execution must fall through to `next`.
5. [Assembler encoding] [B5] — fixed-form assembly for index 0: `.push 0` → `0x20` (8 bits), no immediate args.
6. [Assembler validation] [B6] — assembler rejects `.push idx` when `idx > 255` with `.rangeChk`.
7. [Decoder behavior] [B7] — fixed decoder branch maps byte `0x20` to `.push 0`.
8. [Decoder behavior] [B8] — opcode boundary/alignment: `0x1f` belongs to `.xchg1` family, `0x21` belongs to `.push 1`; both must stay separate from `0x20`.
9. [Decoder behavior] [B9] — decode fails with `.invOpcode` on truncated or malformed bitstreams (e.g. fewer than 8 bits).
10. [Gas accounting] [B10] — fixed gas bill: `instrGas = gasPerInstr + 8` for this fixed form.
11. [Gas edge case] [B11] — exact gas succeeds, exact-1 fails before mutation.

Category note: no variable gas component exists for `.push` in this form; gas differences are only in total bit width.

TOTAL BRANCHES: 11

Each branch is tagged [B#] in the oracle list or covered by unit tests as required.
-/

private def dupId : InstrId :=
  { name := "DUP" }

private def dupInstr : Instr :=
  .push 0

private def dupSetGasExact : Int :=
  computeExactGasBudget dupInstr

private def dupSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne dupInstr

private def dupExactGasLimits : OracleGasLimits :=
  { gasLimit := dupSetGasExact, gasMax := dupSetGasExact }

private def dupMinusOneGasLimits : OracleGasLimits :=
  { gasLimit := dupSetGasExactMinusOne, gasMax := dupSetGasExactMinusOne }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dupInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dupId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (bits : Nat)
    (len : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dupId
    codeCell? := some (Cell.mkOrdinary (natToBits bits len) #[])
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCell (bits : Nat) (len : Nat) : Cell :=
  Cell.mkOrdinary (natToBits bits len) #[]

private def gasProgram (limit : Int) : Array Instr :=
  #[.pushInt (.num limit), .tonEnvOp .setGasLimit, dupInstr]

private def runDupDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPush dupInstr stack

private def runDupDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPush .add (VM.push (intV 999)) stack

private def expectDecodeErr (label : String) (bits : Nat) (len : Nat) : IO Unit := do
  match decodeCp0WithBits (mkCodeCell bits len |> Slice.ofCell) with
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, decodedBits, _) =>
      throw (IO.userError s!"{label}: expected failure, got {reprStr instr} with decodedBits={decodedBits}")

private def genDupFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (case, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/shape-0/error/underflow-empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/shape-1/ok/depth1-int-pos" #[intV 7], rng1)
    else if shape = 2 then
      (mkCase "fuzz/shape-2/ok/depth1-int-neg" #[intV (-17)], rng1)
    else if shape = 3 then
      (mkCase "fuzz/shape-3/ok/depth2-mixed"
        #[.null, .cell Cell.empty], rng1)
    else if shape = 4 then
      (mkCase "fuzz/shape-4/ok/depth5-mixed"
        #[intV 1, intV 2, .cell Cell.empty, .null, intV 9], rng1)
    else if shape = 5 then
      (mkCase "fuzz/shape-5/ok/depth10-tails"
        #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10], rng1)
    else if shape = 6 then
      (mkCase "fuzz/shape-6/ok/boundary-max"
        #[intV maxInt257], rng1)
    else if shape = 7 then
      (mkCase "fuzz/shape-7/gas/exact"
        #[intV 42]
        (gasProgram dupSetGasExact)
        dupExactGasLimits, rng1)
    else if shape = 8 then
      (mkCase "fuzz/shape-8/gas/exact-minus-one"
        #[intV 42]
        (gasProgram dupSetGasExactMinusOne)
        dupMinusOneGasLimits, rng1)
    else if shape = 9 then
      (mkRawCase "fuzz/shape-9/raw/opcode-0x20/with-stack"
        0x20 8 #[intV 123], rng1)
    else
      (mkRawCase "fuzz/shape-10/raw/opcode-0x21-push1"
        0x21 8 #[intV 123], rng1)
  (case, rng2)

def suite : InstrSuite where
  id := { name := "DUP" }
  unit := #[
    { name := "unit/ok/depth1-int"
      run := do
        expectOkStack "unit/ok/depth1-int"
          (runDupDirect #[intV 10])
          #[intV 10, intV 10]
    }
    ,
    { name := "unit/ok/depth1-null"
      run := do
        expectOkStack "unit/ok/depth1-null"
          (runDupDirect #[.null])
          #[.null, .null]
    }
    ,
    { name := "unit/ok/depth4-tail-preserved"
      run := do
        expectOkStack "unit/ok/depth4-tail-preserved"
          (runDupDirect #[intV 1, intV 2, .cell Cell.empty, intV 9])
          #[intV 1, intV 2, .cell Cell.empty, intV 9, intV 9]
    }
    ,
    { name := "unit/error/underflow-empty"
      run := do
        expectErr "unit/error/underflow-empty" (runDupDirect #[]) .stkUnd
    }
    ,
    { name := "unit/dispatch/fallthrough"
      run := do
        expectOkStack "unit/dispatch/fallthrough"
          (runDupDispatchFallback #[])
          #[intV 999]
    }
    ,
    { name := "unit/asm/encode-0x20"
      run := do
        match assembleCp0 [dupInstr] with
        | .error e => throw (IO.userError s!"unit/asm/encode-0x20 failed: {reprStr e}")
        | .ok code =>
            if code.bits != natToBits 0x20 8 ∨ code.refs.size != 0 then
              throw (IO.userError s!"unit/asm/encode-0x20 expected bits={natToBits 0x20 8}, refs=0, got bits={code.bits}, refs={code.refs.size}")
    }
    ,
    { name := "unit/asm/reject-push-256"
      run := do
        match assembleCp0 [.push 256] with
        | .ok _ => throw (IO.userError "unit/asm/reject-push-256: expected rangeChk")
        | .error e =>
            if e != .rangeChk then
              throw (IO.userError s!"unit/asm/reject-push-256: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/asm/alias-raw-neighbors"
      run := do
        let slice20 : Slice := Slice.ofCell (mkCodeCell 0x20 8)
        let slice21 : Slice := Slice.ofCell (mkCodeCell 0x21 8)
        let slice1f : Slice := Slice.ofCell (mkCodeCell 0x1f 8)
        match decodeCp0WithBits slice20 with
        | .ok (i, bits, rest) =>
            if i != .push 0 ∨ bits != 8 ∨ rest.bitsRemaining != 0 then
              throw (IO.userError "unit/asm/alias-raw-neighbors expected 0x20 -> .push 0")
        | .error e =>
            throw (IO.userError s!"unit/asm/alias-raw-neighbors decode 0x20 failed: {e}")
        match decodeCp0WithBits slice21 with
        | .ok (i, bits, rest) =>
            if i != .push 1 ∨ bits != 8 ∨ rest.bitsRemaining != 0 then
              throw (IO.userError "unit/asm/alias-raw-neighbors expected 0x21 -> .push 1")
        | .error e =>
            throw (IO.userError s!"unit/asm/alias-raw-neighbors decode 0x21 failed: {e}")
        match decodeCp0WithBits slice1f with
        | .ok (i, _, _) =>
            if i != .xchg1 15 then
              throw (IO.userError "unit/asm/alias-raw-neighbors expected 0x1f -> .xchg1 15")
        | .error e =>
            throw (IO.userError s!"unit/asm/alias-raw-neighbors decode 0x1f failed: {e}")
    }
    ,
    { name := "unit/codec/truncated-4bits"
      run := do
        expectDecodeErr "unit/codec/truncated-4bits" 0x2 4
        expectDecodeErr "unit/codec/truncated-empty" 0x0 0
    }
    ,
    { name := "unit/gas/exact-cost"
      run := do
        if dupSetGasExact <= 0 then
          throw (IO.userError s!"unexpected non-positive gas for DUP: {dupSetGasExact}")
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/ok/depth1-int-pos" #[intV 11],
    -- [B1]
    mkCase "oracle/ok/depth1-int-neg" #[intV (-11)],
    -- [B1, B3]
    mkCase "oracle/ok/depth1-zero" #[intV 0],
    -- [B1, B3]
    mkCase "oracle/ok/depth1-null" #[.null],
    -- [B1, B3]
    mkCase "oracle/ok/depth1-cell" #[.cell Cell.empty],
    -- [B1, B3]
    mkCase "oracle/ok/depth1-builder" #[.builder Builder.empty],
    -- [B1, B3]
    mkCase "oracle/ok/depth1-tuple" #[.tuple #[]],
    -- [B1, B3]
    mkCase "oracle/ok/depth1-cont" #[.cont (.quit 0)],
    -- [B1, B3]
    mkCase "oracle/ok/depth2-top-null" #[intV 100, .null],
    -- [B1, B3]
    mkCase "oracle/ok/depth2-top-cell" #[.cell Cell.empty, intV 10],
    -- [B1, B3]
    mkCase "oracle/ok/depth3-mixed" #[intV 1, intV 2, .null],
    -- [B1, B3, B4]
    mkCase "oracle/ok/depth4-mixed-tail" #[intV 1, .null, .cell Cell.empty, intV 9],
    -- [B1, B3]
    mkCase "oracle/ok/depth5-mixed-types" #[intV 1, intV 2, .null, .cell Cell.empty, intV 3],
    -- [B1, B3]
    mkCase "oracle/ok/depth6-mixed" #[intV 1, .null, .cell Cell.empty, intV 4, .tuple #[], intV 6],
    -- [B1, B3]
    mkCase "oracle/ok/depth10-long-tail" #[intV 1, intV 2, intV 3, intV 4, intV 5, .null, .cell Cell.empty, intV 7, intV 8, intV 9],
    -- [B1, B3]
    mkCase "oracle/ok/near-max" #[intV (maxInt257)],
    -- [B1]
    mkCase "oracle/ok/near-min" #[intV (minInt257)],
    -- [B1]
    mkCase "oracle/ok/max-1" #[intV (maxInt257 - 1)],
    -- [B1]
    mkCase "oracle/ok/min-1" #[intV (minInt257 + 1)],
    -- [B1]
    mkCase "oracle/ok/pattern-repeat" #[intV 7, intV 7, intV 7],
    -- [B1]
    mkCase "oracle/ok/sign-flip" #[intV 1, intV (-1), intV 0],
    -- [B1]
    mkCase "oracle/ok/redundant-top" #[intV 42, .null, intV 42],
    -- [B2]
    mkCase "oracle/error/underflow-empty" #[],
    -- [B5]
    mkCase "oracle/asm/encode-dup-idx0" #[intV 9],
    -- [B7]
    mkRawCase "oracle/codec/decode-0x20" 0x20 8 #[intV 11],
    -- [B8]
    mkRawCase "oracle/codec/decode-0x1f" 0x1f 8 #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16],
    -- [B8]
    mkRawCase "oracle/codec/decode-0x21" 0x21 8 #[intV 11, intV 22],
    -- [B9]
    mkRawCase "oracle/codec/truncated-4bits" 0x2 4 #[intV 11],
    -- [B9]
    mkRawCase "oracle/codec/truncated-empty" 0x0 0 #[],
    -- [B10, B11]
    mkCase "oracle/gas/exact" #[intV 11] (gasProgram dupSetGasExact) dupExactGasLimits,
    -- [B10, B11]
    mkCase "oracle/gas/exact-minus-one" #[intV 11] (gasProgram dupSetGasExactMinusOne) dupMinusOneGasLimits,
    -- [B3]
    mkCase "oracle/ok/depth15-deep" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, .null, .cell Cell.empty, intV 10, intV 11, intV 12, intV 13],
    -- [B3]
    mkCase "oracle/ok/depth16-all-varied" #[intV 1, .null, .cell Cell.empty, intV 4, .tuple #[], .builder Builder.empty, .cont (.quit 0), intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, .null, .cell Cell.empty, intV 15, intV 16],
    -- [B3]
    mkCase "oracle/ok/depth17-random-shape" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16, intV 17],
    -- [B10]
    mkCase "oracle/ok/gas-large-stack" #[intV 99] (gasProgram dupSetGasExact) dupExactGasLimits,
    -- [B11]
    mkCase "oracle/gas/out-of-gas-large-stack" #[intV 99] (gasProgram dupSetGasExactMinusOne) dupMinusOneGasLimits
  ]
  fuzz := #[
    { seed := 2026010101
      count := 500
      gen := genDupFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.DUP
