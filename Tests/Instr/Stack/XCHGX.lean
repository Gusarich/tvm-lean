import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHGX

/- 
INSTRUCTION: XCHGX

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch:
   - Runtime handler executes only on `.xchgX`.
   - Any different opcode must execute `next` unchanged.

2. [B2] Runtime pre-parse underflow branch:
   - `VM.popNatUpTo` in `execInstrStackXchgX` requires a non-empty stack through implicit `checkUnderflow 1`.
   - Empty stack triggers `.stkUnd`.

3. [B3] Runtime type branch:
   - If stack top is not Int, `popInt` inside `popNatUpTo` raises `.typeChk`.

4. [B4] Runtime range branch (`x < 0`):
   - Valid Int but negative values fail `VM.popNatUpTo` with `.rangeChk`.

5. [B5] Runtime range branch (`x > max`):
   - Lean allows `x ≤ 2^30-1` (`popNatUpTo ((1 <<< 30) - 1)`).
   - `x = 2^30` and larger (or `.nan`) also trigger `.rangeChk`.
   - C++ uses the same bound in version >= 4; branch behavior matches in the current Lean model.

6. [B6] Runtime underflow-after-pop branch:
   - After successful parse/validation, if `x ≥ st.stack.size`, `VM.swap 0 x` fails with `.stkUnd`.
   - This path is independent of value types below `x`.

7. [B7] Runtime success branch:
   - With `x` in bounds and `x < st.stack.size`, top value is swapped with stack position `x`.
   - Prefix elements below swapped indices are preserved.
   - No type constraints on those values.

8. [B8] Assembler/decoder branches:
   - `.xchgX` assembles to fixed `0x67` (8 bits) with no argument parsing.
   - Round-trip decoding must preserve `0x67` → `.xchgX`.
   - Adjacent opcodes must remain distinct: `0x66` is `.tuck`, `0x68` is `.depth`.
   - Truncated 4-bit `0x6` input must decode as `.invOpcode`.

9. [B9] Gas accounting:
   - `XCHGX` has fixed instruction gas cost with no variable penalty in Lean/C++.
   - Exact budget should succeed and exact-minus-one should fail.

TOTAL BRANCHES: 9

Each oracle test below is tagged with which branches it exercises.
-/

private def xchgXId : InstrId := { name := "XCHGX" }

private def xchgXInstr : Instr := .xchgX

private def dispatchSentinel : Int := 50067

private def sampleCell : Cell := Cell.mkOrdinary (natToBits 0xaa 8) #[]
private def sampleSlice : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[])
private def sampleBuilder : Builder := Builder.empty

private def xchgXCode : Cell := Cell.mkOrdinary (natToBits 0x67 8) #[]
private def tuckCode : Cell := Cell.mkOrdinary (natToBits 0x66 8) #[]
private def depthCode : Cell := Cell.mkOrdinary (natToBits 0x68 8) #[]
private def truncated4Code : Cell := Cell.mkOrdinary (natToBits 0x6 4) #[]

private def runXchgXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXchgX xchgXInstr stack

private def runXchgXDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackXchgX instr (VM.push (intV dispatchSentinel)) stack

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
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[xchgXInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchgXId
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
    instr := xchgXId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def xchgXGasExact : Int :=
  computeExactGasBudget .xchgX

private def xchgXGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .xchgX

private def valuePool : Array Value :=
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

private def genStackWithTop (below : Nat) (top : Value) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut st : Array Value := #[]
    let mut rng := rng0
    let mut i : Nat := 0
    while i < below do
      let (v, rng') := pickFromPool valuePool rng
      st := st.push v
      rng := rng'
      i := i + 1
    pure (st.push top, rng)

private def genXchgXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case, rng2) :=
    if shape = 0 then
      -- [B7] success at x = 0 on minimal depth.
      (mkCase "fuzz/ok/min-depth-x0" #[intV 11, intV 0], rng1)
    else if shape = 1 then
      -- [B7] success at x = 1 on minimal depth.
      (mkCase "fuzz/ok/min-depth-x1" #[intV 9, intV 1], rng1)
    else if shape = 2 then
      -- [B7] x = 2 with mixed values below.
      (mkCase "fuzz/ok/depth4-x2-mixed"
        #[intV 10, .null, .cell sampleCell, intV 2], rng1)
    else if shape = 3 then
      let (stack, rng3) := genStackWithTop 6 (intV 3) rng1
      -- [B7] preserve prefix with non-int values under the swapped slots.
      ((mkCase "fuzz/ok/depth7-x3-mix" stack), rng3)
    else if shape = 4 then
      let (stack, rng3) := genStackWithTop 7 (intV 7) rng1
      -- [B7] max practical success index for small stress stack.
      ((mkCase "fuzz/ok/depth8-x7" stack), rng3)
    else if shape = 5 then
      -- [B2] no stack before pop => stkUnd.
      ((mkCase "fuzz/err/underflow/empty" #[]), rng1)
    else if shape = 6 then
      -- [B2] singleton cannot satisfy pre-check.
      ((mkCase "fuzz/err/underflow/one-item" #[intV 1]), rng1)
    else if shape = 7 then
      -- [B6] parsed x is valid but out of bounds.
      ((mkCase "fuzz/err/underflow/x2-on-size2" #[intV 9, intV 2]), rng1)
    else if shape = 8 then
      -- [B6] deep out-of-bounds by top-index.
      ((mkCase "fuzz/err/underflow/x7-on-size7" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7]), rng1)
    else if shape = 9 then
      -- [B3] non-int top.
      ((mkCase "fuzz/err/type/top-null" #[.null, intV 2, .cell sampleCell]), rng1)
    else if shape = 10 then
      -- [B3] non-int top.
      ((mkCase "fuzz/err/type/top-slice" #[.slice sampleSlice, intV 3]), rng1)
    else if shape = 11 then
      -- [B3] non-int top.
      ((mkCase "fuzz/err/type/top-builder" #[.builder sampleBuilder, intV 4]), rng1)
    else if shape = 12 then
      -- [B4] negative top after pop.
      ((mkCase "fuzz/err/range/negative" #[intV (-1), intV 17]), rng1)
    else if shape = 13 then
      -- [B5] too-large top index.
      ((mkCase "fuzz/err/range/too-large" #[intV (Int.ofNat (1 <<< 30)), intV 18]), rng1)
    else if shape = 14 then
      -- [B5] runtime path should still reject non-finite index.
      ((mkCase "fuzz/err/range/nan" #[.int .nan, intV 19]), rng1)
    else
      -- [B1] dispatch fallback path (raw code provided separately from runtime).
      ((mkCase "fuzz/dispatch/neighbor-op" #[intV 11, intV 22] #[.add]), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case with name := s!"{case.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := xchgXId
  unit := #[
    { name := "unit/dispatch/fallback-or-match"
      run := do
        expectOkStack "fallback/add"
          (runXchgXDispatchFallback .add #[intV 11, intV 22]) #[intV 22, intV dispatchSentinel]
        expectOkStack "matched-xchgx"
          (runXchgXDirect #[intV 5, intV 6]) #[intV 6, intV 5] },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "underflow/empty" (runXchgXDirect #[]) .stkUnd
        expectErr "underflow/one-item-x1" (runXchgXDirect #[intV 1]) .stkUnd },
    { name := "unit/runtime/error-branches"
      run := do
        expectErr "type/top-null" (runXchgXDirect #[.null, intV 0]) .typeChk
        expectErr "range/top-negative" (runXchgXDirect #[intV (-2), intV 7]) .rangeChk
        expectErr "range/top-too-large" (runXchgXDirect #[intV (Int.ofNat (1 <<< 30)), intV 7]) .rangeChk
        expectErr "range/top-nan" (runXchgXDirect #[.int .nan, intV 7]) .rangeChk
        expectErr "underflow/parsed-x-on-boundary"
          (runXchgXDirect #[intV 1, intV 2, intV 3]) .stkUnd },
    { name := "unit/asm-decode-boundaries"
      run := do
        let code ←
          match assembleCp0 [xchgXInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/xchgx failed: {e}")
        if code.bits = natToBits 0x67 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/xchgx expected 0x67, got bits {code.bits}")
        if code.bits.size = 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/xchgx expected 8 bits, got {code.bits.size}")
        expectDecodeXchgX "decode/xchgx" code
        expectDecodeXchgX "decode/xchgx-with-tail" (Cell.mkOrdinary (natToBits 0x6700 16) #[]) 8 false
        expectDecodeErr "decode/truncated-4bit" truncated4Code .invOpcode
        expectDecodeXchgX "decode/xchgx-neighbor-before" tuckCode 8 false
        expectDecodeXchgX "decode/xchgx-neighbor-after" depthCode 8 false }
  ]
  oracle := #[
    -- [B1]
    mkCase "dispatch/fallback/add" #[intV 7, intV 9] #[.add],
    -- [B1]
    mkCase "dispatch/fallback/add-with-noise" #[.cell sampleCell, intV 17] #[.pushInt (.num 1), .add],
    -- [B2]
    mkCase "err/underflow/empty" #[],
    -- [B2]
    mkCase "err/underflow/one-item" #[intV 1],
    -- [B2]
    mkCase "err/underflow/one-item-non-int" #[.builder sampleBuilder],
    -- [B3]
    mkCase "err/type/top-null" #[.null, intV 1],
    -- [B3]
    mkCase "err/type/top-cell" #[.cell sampleCell, intV 1],
    -- [B3]
    mkCase "err/type/top-slice" #[.slice sampleSlice, intV 1],
    -- [B3]
    mkCase "err/type/top-builder" #[.builder sampleBuilder, intV 1],
    -- [B3]
    mkCase "err/type/top-cont" #[.cont (.quit 7), intV 1],
    -- [B4]
    mkCase "err/range/negative-1" #[intV (-1), intV 0],
    -- [B4]
    mkCase "err/range/negative-7" #[intV (-7), intV 99],
    -- [B5]
    mkCase "err/range/too-large-boundary-plus-1" #[intV (Int.ofNat ((1 <<< 30))), intV 0],
    -- [B5]
    mkCase "err/range/too-large-257ish" #[intV (Int.ofNat ((1 <<< 31))), intV 1],
    -- [B5]
    mkCase "err/range/nan-top" #[.int .nan, intV 2],
    -- [B6]
    mkCase "err/underflow/size1-x1" #[intV 1],
    -- [B6]
    mkCase "err/underflow/size2-x2" #[intV 2, intV 4],
    -- [B6]
    mkCase "err/underflow/size3-x3" #[intV 1, intV 1, intV 3],
    -- [B6]
    mkCase "err/underflow/size7-x7" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7],
    -- [B6]
    mkCase "err/underflow/size7-mix"
      #[.null, .cell sampleCell, .slice sampleSlice, .builder sampleBuilder, intV 5, intV 6, intV 7],
    -- [B7]
    mkCase "ok/x0/swap-identity" #[intV 7, intV 0],
    -- [B7]
    mkCase "ok/x0/negative-top" #[intV (-1), intV 0, intV 0],
    -- [B7]
    mkCase "ok/x1/min-depth" #[intV 10, intV 1],
    -- [B7]
    mkCase "ok/x1/typed-mixed" #[.cell sampleCell, intV 11, intV 1],
    -- [B7]
    mkCase "ok/x2/min-depth-with-below" #[intV 9, intV 8, intV 7, intV 2],
    -- [B7]
    mkCase "ok/x2/with-builder" #[intV 5, .builder sampleBuilder, intV 3, intV 2],
    -- [B7]
    mkCase "ok/x3/depth4-mixed-type" #[intV 13, .null, .tuple #[], intV 3, intV 4, intV 3],
    -- [B7]
    mkCase "ok/x3/deep-preserve" #[intV 1, .slice sampleSlice, .cell sampleCell, intV 99, intV 1],
    -- [B7]
    mkCase "ok/x7/depth8" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, .null, intV 7],
    -- [B7]
    mkCase "ok/x7/with-nonint-target" #[intV 11, .cell sampleCell, .builder sampleBuilder, .cont (.quit 1), intV 4, .slice sampleSlice, intV 9, intV 7],
    -- [B8]
    mkCaseCode "decode/roundtrip/xchgx" #[intV 8, intV 2] xchgXCode,
    -- [B8]
    mkCaseCode "decode/xchgx-vs-tuck" #[intV 1, intV 2] tuckCode,
    -- [B8]
    mkCaseCode "decode/xchgx-vs-depth" #[intV 1, intV 2] depthCode,
    -- [B8]
    mkCaseCode "decode/truncated-4bit-prefix" #[intV 3] truncated4Code,
    -- [B9]
    mkCase "gas/exact-success"
      #[intV 99, intV 0]
      #[.pushInt (.num xchgXGasExact), .tonEnvOp .setGasLimit, xchgXInstr]
      (oracleGasLimitsExact xchgXGasExact),
    -- [B9]
    mkCase "gas/exact-minus-one-fails"
      #[intV 99, intV 0]
      #[.pushInt (.num xchgXGasExactMinusOne), .tonEnvOp .setGasLimit, xchgXInstr]
      (oracleGasLimitsExact xchgXGasExactMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xchgXId
      count := 500
      gen := genXchgXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHGX
