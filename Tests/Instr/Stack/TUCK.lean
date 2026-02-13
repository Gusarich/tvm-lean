import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.TUCK

/-
INSTRUCTION: TUCK

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch:
   - `.tuck` handler is matched only when decode selects TUCK.
   - Any non-matching opcode (e.g. `.add`) must fall through to `next`.

2. [B2] Runtime underflow branch:
   - `VM.swap 0 1` requires at least two stack items.
   - If `size < 2`, execution fails with `.stkUnd` without mutating state.

3. [B3] Normal two-item semantics:
   - For two values `[x, y]` (top is right), TUCK transforms to `[y, x, y]`.

4. [B4] Runtime prefix-preservation branch:
   - For stacks deeper than 2, elements below top two are preserved in order.
   - TUCK performs local top-two reshuffle and appends one copied value.

5. [B5] Value-path branch (no type restrictions):
   - TUCK has no `popInt`/`typeChk`/`rangeChk` path because it never pops by type.
   - Any `Value` shape can occupy the top-two positions.

6. [B6] Assembler/decoder boundary branches:
   - Assembly is fixed-width 8 bits (`0x66`) with no argument validation branches.
   - Neighbouring opcodes `0x65` and `0x67` must decode to different instructions.
   - Truncated 4-bit prefixes must fail decode (`.invOpcode`).

7. [B7] Gas accounting:
   - TUCK itself has base-cost semantics only (no variable gas penalty).
   - Exact-gas-success and exact-gas-minus-one-failure are boundary checks.

TOTAL BRANCHES: 7
Each oracle test below is tagged with branch coverage markers.
-/

private def tuckId : InstrId := { name := "TUCK" }

private def tuckInstr : Instr := .tuck

private def dispatchSentinel : Int := 42424

private def sampleCell : Cell := Cell.mkOrdinary (natToBits 0x66 8) #[]

private def sampleSlice : Slice := Slice.ofCell sampleCell

private def sampleBuilder : Builder := Builder.empty

private def tuckCode : Cell := Cell.mkOrdinary (natToBits 0x66 8) #[]

private def dropXCode : Cell := Cell.mkOrdinary (natToBits 0x65 8) #[]

private def xchgXCode : Cell := Cell.mkOrdinary (natToBits 0x67 8) #[]

private def truncated4Code : Cell := Cell.mkOrdinary (natToBits 0x6 4) #[]

private def runTuckDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackTuck tuckInstr stack

private def runTuckDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackTuck instr (VM.push (intV dispatchSentinel)) stack

private def runTuckRaw
    (stack : Array Value)
    (instr : Instr := tuckInstr) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrStackTuck instr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (res, st) := out
  match res with
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected {expected}, got success")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectDecodeTuck
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 8)
    (expectEmptyTail : Bool := true) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .tuck then
        throw (IO.userError s!"{label}: expected .tuck, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if expectEmptyTail && rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def expectDecodeDropX
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 8)
    (expectEmptyTail : Bool := true) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .dropX then
        throw (IO.userError s!"{label}: expected .dropX, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if expectEmptyTail && rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def expectDecodeXchgX
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 8)
    (expectEmptyTail : Bool := true) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .xchgX then
        throw (IO.userError s!"{label}: expected .xchgX, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if expectEmptyTail && rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[tuckInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := tuckId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := tuckId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def tuckGasExact : Int :=
  computeExactGasBudget tuckInstr

private def tuckGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne tuckInstr

private def typedValuePool : Array Value :=
  #[
    .null,
    .cell sampleCell,
    .slice sampleSlice,
    .builder sampleBuilder,
    .tuple #[],
    .cont (.quit 0)
  ]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genTuckFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng12) :=
    if shape = 0 then
      let (x, rng2) := pickSigned257ish rng1
      let (y, rng3) := pickSigned257ish rng2
      (mkCase "fuzz/ok/two-random-ints" #[intV x, intV y], rng3)
    else if shape = 1 then
      let (x, rng2) := pickSigned257ish rng1
      let (y, rng3) := pickSigned257ish rng2
      let (z, rng4) := pickSigned257ish rng3
      (mkCase "fuzz/ok/three-random-ints" #[intV x, intV y, intV z], rng4)
    else if shape = 2 then
      let (x, rng2) := pickSigned257ish rng1
      let (y, rng3) := pickSigned257ish rng2
      let (v1, rng4) := pickFromPool typedValuePool rng3
      let (v2, rng5) := pickFromPool typedValuePool rng4
      (mkCase "fuzz/ok/mixed-values-on-top" #[v1, intV x, intV y, v2], rng5)
    else if shape = 3 then
      let (x, rng2) := pickSigned257ish rng1
      let (v1, rng3) := pickFromPool typedValuePool rng2
      (mkCase "fuzz/ok/two-int-top-with-typed-bottom" #[v1, intV x, intV (x + 1)], rng3)
    else if shape = 4 then
      (mkCase "fuzz/ok/boundary-max-minus-one" #[intV (maxInt257 - 1), intV 1], rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/boundary-min-plus-one" #[intV (minInt257 + 1), intV (-1)], rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/all-typed" #[.null, .cell sampleCell, .slice sampleSlice], rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/underflow-one-int" #[intV 13], rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/underflow-one-non-int" #[.builder sampleBuilder], rng1)
    else if shape = 10 then
      (mkCase "fuzz/dispatch/fallback-add" #[intV 7, intV 9] #[.add], rng1)
    else
      (mkCaseCode "fuzz/err/truncated-4bit-prefix" #[] truncated4Code, rng1)
  let (tag, rng13) := randNat rng12 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng13)


def suite : InstrSuite where
  id := tuckId
  unit := #[
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add" (runTuckDispatchFallback .add #[intV 10, intV 32]) #[intV 10, intV 32, intV dispatchSentinel]
    },
    { name := "unit/dispatch/matched-tuck"
      run := do
        expectOkStack "tuck/matched-two-values" (runTuckDirect #[intV 7, intV 11]) #[intV 11, intV 7, intV 11]
    },
    { name := "unit/error/underflow-on-empty-and-singleton"
      run := do
        let _ ← expectRawErr "underflow/empty" (runTuckRaw #[]) .stkUnd
        let _ ← expectRawErr "underflow/one-int" (runTuckRaw #[intV 5]) .stkUnd
        let _ ← expectRawErr "underflow/one-non-int" (runTuckRaw #[.null]) .stkUnd
    },
    { name := "unit/ok/stack-shape-preserved"
      run := do
        expectOkStack "deep-stack/preserve-prefix-3" (runTuckDirect #[.null, intV 1, intV 2]) #[.null, intV 2, intV 1, intV 2]
        expectOkStack "deep-stack/preserve-prefix-4"
          (runTuckDirect #[intV (-3), .cell sampleCell, .slice sampleSlice, intV 99])
          #[intV (-3), .cell sampleCell, intV 99, .slice sampleSlice, intV 99]
    },
    { name := "unit/ok/type-agnostic-values"
      run := do
        expectOkStack "typed-null-x" (runTuckDirect #[.null, intV 17]) #[intV 17, .null, intV 17]
        expectOkStack "typed-cell-x" (runTuckDirect #[intV (-4), .cell sampleCell]) #[.cell sampleCell, intV (-4), .cell sampleCell]
        expectOkStack "typed-slice-x" (runTuckDirect #[.slice sampleSlice, .cell sampleCell])
          #[.cell sampleCell, .slice sampleSlice, .cell sampleCell]
        expectOkStack "typed-builder" (runTuckDirect #[intV 5, .builder sampleBuilder])
          #[.builder sampleBuilder, intV 5, .builder sampleBuilder]
    },
    { name := "unit/opcode/assemble-decode-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [tuckInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/tuck failed: {reprStr e}")
        if assembled.bits != natToBits 0x66 8 then
          throw (IO.userError s!"assemble/tuck expected 0x66, got {reprStr assembled.bits}")
        expectDecodeTuck "decode/tuck-ok-8bit" tuckCode
        expectDecodeErr "decode/truncated-4bit" truncated4Code .invOpcode
        expectDecodeTuck "decode/tuck-with-trailing" (Cell.mkOrdinary (natToBits 0x667f 16) #[]) 8 false
        expectDecodeDropX "decode/dropx" dropXCode 8 false
        expectDecodeXchgX "decode/xchgx" xchgXCode 8 false
    }
  ]
  oracle := #[
    -- [B1]
    -- [B6]
    -- [B6]
    -- [B1]
    mkCase "dispatch/fallback/add" #[intV 7, intV 9] #[.add],
    -- [B2]
    mkCase "underflow/empty" #[],
    -- [B2]
    mkCase "underflow/one-item/int" #[intV 1],
    -- [B2]
    mkCase "underflow/one-item/null" #[.null],
    -- [B3]
    mkCase "ok/two-ints/zero-zero" #[intV 0, intV 0],
    -- [B3]
    mkCase "ok/two-ints/positive" #[intV 4, intV 9],
    -- [B3]
    mkCase "ok/two-ints/negative" #[intV (-4), intV 13],
    -- [B3]
    mkCase "ok/two-ints/mixed-sign" #[intV (-9), intV (-12)],
    -- [B3]
    mkCase "ok/two-ints/one-max" #[intV maxInt257, intV 1],
    -- [B3]
    mkCase "ok/two-ints/one-min" #[intV minInt257, intV (-1)],
    -- [B3]
    mkCase "ok/two-ints/duplicate" #[intV 77, intV 77],
    -- [B3, B5]
    mkCase "ok/typed/mixed-null-int" #[.null, intV 22],
    -- [B3, B5]
    mkCase "ok/typed/mixed-int-null" #[intV 22, .null],
    -- [B3, B5]
    mkCase "ok/typed/mixed-cell-int" #[.cell sampleCell, intV 3],
    -- [B3, B5]
    mkCase "ok/typed/mixed-slice-int" #[.slice sampleSlice, intV 3],
    -- [B3, B5]
    mkCase "ok/typed/mixed-builder-int" #[.builder sampleBuilder, intV 3],
    -- [B3, B5]
    mkCase "ok/typed/mixed-tuple-int" #[.tuple #[], intV 4],
    -- [B3, B5]
    mkCase "ok/typed/mixed-cont-int" #[.cont (.quit 0), intV 19],
    -- [B4]
    mkCase "ok/deep/preserve-prefix-3" #[intV 1, intV 2, intV 3],
    -- [B4]
    mkCase "ok/deep/preserve-prefix-4" #[.null, intV 10, .cell sampleCell, intV 7],
    -- [B4]
    mkCase "ok/deep/preserve-prefix-5" #[intV 1, .slice sampleSlice, .builder sampleBuilder, .tuple #[], intV 99],
    -- [B4]
    mkCase "ok/deep/all-typed" #[.null, .cell sampleCell, .slice sampleSlice, intV 5],
    -- [B4]
    mkCase "ok/deep/long" #[intV 1, intV 2, intV 3, intV 4, intV 5],
    -- [B5]
    mkCase "ok/typed/top-two-null" #[.null, .null],
    -- [B5]
    mkCase "ok/typed/top-two-cell" #[.cell sampleCell, .cell sampleCell],
    -- [B5]
    mkCase "ok/typed/top-two-slice" #[.slice sampleSlice, .slice sampleSlice],
    -- [B5]
    mkCase "ok/typed/top-two-builder" #[.builder sampleBuilder, .builder sampleBuilder],
    -- [B6]
    mkCaseCode "decode/roundtrip/tuck" #[intV 11, intV 22] tuckCode,
    -- [B6]
    mkCaseCode "decode/roundtrip/dropx-mismatch" #[intV 11, intV 22] dropXCode,
    -- [B6]
    mkCaseCode "decode/roundtrip/xchgx-mismatch" #[intV 11, intV 22] xchgXCode,
    -- [B6]
    mkCaseCode "decode/truncated-4bit-prefix" #[] truncated4Code,
    -- [B6]
    mkCaseCode "decode/truncated-4bit-prefix-with-noise" #[intV 1] truncated4Code,
    -- [B7]
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num tuckGasExact), .tonEnvOp .setGasLimit, tuckInstr],
    -- [B7]
    mkCase "gas/exact-cost-minus-one-fails" #[intV 7, intV 5]
      #[.pushInt (.num tuckGasExactMinusOne), .tonEnvOp .setGasLimit, tuckInstr],
    -- [B1, B6]
    mkCase "dispatch/fallback/add-same-stack" #[intV 8, intV 16] #[.add],
    -- [B6]
    mkCaseCode "decode/empty-tail-16bit" #[intV 1, intV 2] (Cell.mkOrdinary (natToBits 0x6600 16) #[]),
    -- [B4, B5]
    mkCase "ok/typed/deep-negative" #[.null, intV (-3), .cell sampleCell, intV (-9)],
    -- [B4]
    mkCase "ok/deep/boundary-and-type" #[intV (maxInt257 - 1), intV (-1), .null, .slice sampleSlice],
    -- [B4]
    mkCase "ok/deep/boundary-and-type-2" #[intV (minInt257 + 1), intV 1, .builder sampleBuilder, .cont (.quit 0)],
    -- [B1]
    mkCase "dispatch/fallback/add-with-noise" #[] #[.pushInt (.num 10), .pushInt (.num 20), .add]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr tuckId
      count := 500
      gen := genTuckFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.TUCK
