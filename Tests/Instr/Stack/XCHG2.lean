import Std
import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHG2

/-
INSTRUCTION: XCHG2

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success path:
   - Lean computes `need := max (max x y) 1`.
   - C++ computes `more_than(x, y, 1)`.
   - If `need < stack.size`, run:
       `swap(1, x)` then `swap(0, y)` (always succeeds when gate passes).
2. [B2] Runtime underflow path:
   - If any required index is out of range (`need >= stack.size`) both Lean and C++ throw `stkUnd`.
   - This is the only explicit runtime error branch.
3. [B3] Runtime overlap/value-shape edge cases (same `need` gate):
   - `x = y`, `x = 0`, `y = 0`, and `x/y = 1` all take the same gate but produce
     distinct data-shape outcomes due to swap interactions.
4. [B4] Assembler encoding branch:
   - Valid forms: `x, y ≤ 15`, encoded as `0x50` + `(x << 4) + y`.
   - No additional C++-style adjacency checks for `x`/`y`; only assembler range filtering applies.
5. [B5] Assembler range failure:
   - Any `x > 15` or `y > 15` must fail in assembler validation with `rangeChk`.
6. [B6] Decoder branch:
   - Byte `0x50` is a fixed 8-bit opcode (`0x50` then one args byte).
   - Decoder always emits `x := args >>> 4`, `y := args &&& 0xf` and consumes 16 bits.
7. [B7] Decoder adjacency branch:
   - `0x50` must decode as XCHG2, and must not alias adjacent fixed opcodes (`0x51` XCPU).
   - Truncated `0x50` (no args byte) must fail `invOpcode`.
8. [B8] Gas accounting:
   - `instrGas (xchg2 x y) = Nat.max x y + 1` (from `Validation/Oracle/Runner.lean`).
   - Need exact-budget success and exact-budget-minus-one failure coverage.

TOTAL BRANCHES: 8
-/

private def xchg2Id : InstrId := { name := "XCHG2" }

private def mkCase
    (name : String)
    (x y : Nat)
    (stack : Array Value)
    (program : Array Instr := #[.xchg2 x y])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchg2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runXchg2Direct (x y : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXchg2 (.xchg2 x y) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def expectAssembleRangeErr (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected range check failure, got successful assembly")
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {e}")

private def sampleStack16 : Array Value :=
  #[
    intV 0, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7,
    intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15
  ]

private def xchg2ExactGas : Int :=
  computeExactGasBudget (.xchg2 15 0)

private def xchg2ExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xchg2 15 0)

private def minStackSizeFor (x y : Nat) : Nat :=
  Nat.max (Nat.max x y) 1 + 1

private def pickFuzzStackValue (rng0 : StdGen) : Value × StdGen :=
  let (mode, rng1) := randNat rng0 0 8
  if mode = 0 then
    (intV 0, rng1)
  else if mode = 1 then
    (intV 1, rng1)
  else if mode = 2 then
    (intV (-1), rng1)
  else if mode = 3 then
    (intV 42, rng1)
  else if mode = 4 then
    (intV (-42), rng1)
  else if mode = 5 then
    (.null, rng1)
  else if mode = 6 then
    (.cell Cell.empty, rng1)
  else if mode = 7 then
    (.tuple #[], rng1)
  else
    match pickSigned257ish rng1 with
    | (n, rng2) => (intV n, rng2)

private def genFuzzStack (size : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  let mut i : Nat := 0
  while i < size do
    let (v, rng') := pickFuzzStackValue rng
    out := out.push v
    rng := rng'
    i := i + 1
  pure (out, rng)

private def pickXchg2Args (rng0 : StdGen) : (Nat × Nat × StdGen) :=
  let (mode, rng1) := randNat rng0 0 11
  if mode = 0 then
    (0, 0, rng1)
  else if mode = 1 then
    (1, 1, rng1)
  else if mode = 2 then
    (0, 1, rng1)
  else if mode = 3 then
    (1, 0, rng1)
  else if mode = 4 then
    (15, 0, rng1)
  else if mode = 5 then
    (0, 15, rng1)
  else if mode = 6 then
    (15, 15, rng1)
  else if mode = 7 then
    (8, 3, rng1)
  else if mode = 8 then
    (3, 8, rng1)
  else
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := randNat rng2 0 15
    (x, y, rng3)

private def genXchg2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (x, y, rng2) := pickXchg2Args rng1
  let minSize : Nat := minStackSizeFor x y
  let (size, rng3) :=
    if shape ≤ 7 then
      let (bonus, rng4) := randNat rng2 0 4
      (minSize + bonus, rng4)
    else if shape = 8 then
      (minSize - 1, rng2)
    else if shape = 9 then
      (0, rng2)
    else
      let maxUnder : Nat := minSize - 1
      let (u, rng4) := randNat rng2 0 maxUnder
      (u, rng4)
  let (stack, rng4) := genFuzzStack size rng3
  let (tag, rng5) := randNat rng4 0 999_999
  ({ name := s!"fuzz/shape-{shape}/x-{x}/y-{y}/size-{size}/{tag}"
     , instr := xchg2Id
     , program := #[.xchg2 x y]
     , initStack := stack }, rng5)

def suite : InstrSuite where
  id := xchg2Id
  unit := #[
    { name := "unit/encoding/roundtrip-boundary"
      run := do
        let code ←
          match assembleCp0 [(.xchg2 15 15)] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble xchg2 15 15 failed: {e}")
        let s1 ← expectDecodeStep "decode/xchg2/max-boundary" (Slice.ofCell code) (.xchg2 15 15) 16
        if s1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/xchg2/max-boundary: expected end-of-stream, got {s1.bitsRemaining} bits") }
    ,
    { name := "unit/encoding/invalid-out-of-range"
      run := do
        expectAssembleRangeErr "encode/xchg2-x-overflow" (.xchg2 16 0)
        expectAssembleRangeErr "encode/xchg2-y-overflow" (.xchg2 0 16) }
    ,
    { name := "unit/decode/adjacent-opcodes"
      run := do
        let code ←
          match assembleCp0 [(.xchg2 2 3), (.xcpu 4 5)] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble opcode pair failed: {e}")
        let s1 ← expectDecodeStep "decode/first-op/xchg2" (Slice.ofCell code) (.xchg2 2 3) 16
        let _ ← expectDecodeStep "decode/second-op/xcpu" s1 (.xcpu 4 5) 16
        pure () }
    ,
    { name := "unit/decode/truncated-xchg2-fails"
      run := do
        let shortCode : Cell := Cell.mkOrdinary (natToBits 0x50 8)
        match decodeCp0WithBits (Slice.ofCell shortCode) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/xchg2/truncated: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/xchg2/truncated: expected failure, got {reprStr instr}, bits={bits}") }
    ,
    { name := "unit/runtime/underflow-empty-stack"
      run := do
        expectErr "runtime/underflow-empty" (runXchg2Direct 0 0 #[]) .stkUnd
        expectErr "runtime/underflow-one-item"
          (runXchg2Direct 1 1 #[intV 7]) .stkUnd }
    ,
    { name := "unit/runtime/ok-identity-overlap"
      run := do
        let input : Array Value := #[intV 10, intV 20]
        expectOkStack "runtime/top-identity-overlap" (runXchg2Direct 0 0 input) #[intV 20, intV 10]
        let input2 : Array Value := #[.null, .cell Cell.empty, intV 5, intV 6]
        expectOkStack "runtime/overlap-x0-y2"
          (runXchg2Direct 0 2 input2) #[.null, intV 5, intV 6, .cell Cell.empty] }
  ]
  oracle := #[
    -- [B1] runtime success: minimal depth with top-2 swap.
    mkCase "ok/success/min-depth-x0-y0" 0 0 #[intV 1, intV 2]
    -- [B1] runtime success: minimal depth with x=1,y=0.
    , mkCase "ok/success/min-depth-x1-y0" 1 0 #[intV 10, intV 20]
    -- [B1] runtime success: minimal depth with x=0,y=1.
    , mkCase "ok/success/min-depth-x0-y1" 0 1 #[intV 30, intV 40]
    -- [B2] runtime overlap edge: x=y=1, no-op style via aliasing.
    , mkCase "ok/overlap/x1-y1-min-depth" 1 1 #[intV 100, intV 200]
    -- [B1] runtime success: x=2,y=0 at minimum depth.
    , mkCase "ok/success/x2-y0-size4" 2 0 #[intV 1, intV 2, intV 3, intV 4]
    -- [B1] runtime success: x=0,y=2 at minimum depth.
    , mkCase "ok/success/x0-y2-size4" 0 2 #[intV 11, intV 22, intV 33, intV 44]
    -- [B1] runtime success: x=2,y=1 at minimum depth.
    , mkCase "ok/success/x2-y1-size3" 2 1 #[intV 1, intV 2, intV 3]
    -- [B1] runtime success: x=1,y=2 at minimum depth.
    , mkCase "ok/success/x1-y2-size3" 1 2 #[intV 9, intV 10, intV 11]
    -- [B1] runtime success: x=3,y=1 near-small-depth case.
    , mkCase "ok/success/x3-y1-size4" 3 1 #[intV 1, intV 2, intV 3, intV 4]
    -- [B2] runtime overlap edge: x=0, y=0 with mixed values.
    , mkCase "ok/success/overlap-x0-y0-mix"
      0 0 #[intV 5, .null, .cell Cell.empty, intV 10]
    -- [B1] runtime success: max-arg decode/exec boundary x=15,y=0.
    , mkCase "ok/success/x15-y0-size16" 15 0 sampleStack16
    -- [B1] runtime success: max-arg decode/exec boundary x=15,y=15.
    , mkCase "ok/success/x15-y15-size16" 15 15 sampleStack16
    -- [B1] runtime success: mixed stack with x=2,y=7 and non-int values.
    , mkCase "ok/success/type-mix/x2-y7"
      2 7 #[.null, .cell Cell.empty, intV 12, intV 13, intV 14, intV 15, intV 16]
    -- [B1] runtime success: mixed stack with x=7,y=2.
    , mkCase "ok/success/type-mix/x7-y2"
      7 2 #[intV 90, .tuple #[], .cell Cell.empty, intV 1, intV 2, intV 3, intV 4, intV 5]
    -- [B1] runtime success: overlap-prone values x=4,y=4.
    , mkCase "ok/success/x4-y4-size6"
      4 4 #[intV 111, .cell Cell.empty, intV 222, .tuple #[], intV 333, intV 444]
    -- [B1] runtime success: mixed boundary args x=8,y=15.
    , mkCase "ok/success/x8-y15-size16"
      8 15 sampleStack16
    -- [B1] runtime success: mixed boundary args x=14,y=0.
    , mkCase "ok/success/x14-y0-size15"
      14 0 #[
        intV 0, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9,
        intV 10, intV 11, intV 12, intV 13, intV 14
      ]
    -- [B1] runtime success: same-index high x with cont value.
    , mkCase "ok/success/x9-y9-size10"
      9 9 #[
        intV 10, .cont (.quit 0), intV 20, .tuple #[], intV 30, .null,
        intV 40, .cell Cell.empty, intV 50, intV 60
      ]
    -- [B1] runtime success: x=0,y=14 near-boundary.
    , mkCase "ok/success/x0-y14-size15"
      0 14 #[
        intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10,
        intV 11, intV 12, intV 13, intV 14, intV 15
      ]
    -- [B3] runtime underflow: empty stack.
    , mkCase "err/underflow/empty-x0-y0" 0 0 #[]
    -- [B3] runtime underflow: one item when two required.
    , mkCase "err/underflow/one-item-x0-y0" 0 0 #[intV 7]
    -- [B3] runtime underflow: one item for high x.
    , mkCase "err/underflow/one-item-x1-y1" 1 1 #[intV 8]
    -- [B3] runtime underflow: two items insufficient for x=2.
    , mkCase "err/underflow/two-items-x2-y0" 2 0 #[intV 1, intV 2]
    -- [B3] runtime underflow: two items insufficient for y=2.
    , mkCase "err/underflow/two-items-x1-y2" 1 2 #[intV 1, intV 2]
    -- [B3] runtime underflow: three items insufficient for x=4,y=4.
    , mkCase "err/underflow/three-items-x4-y4" 4 4 #[intV 1, intV 2, intV 3]
    -- [B3] runtime underflow: size12 insufficient for x=12,y=8.
    , mkCase "err/underflow/size12-x12-y8" 12 8
      #[
        intV 0, intV 1, intV 2, intV 3, intV 4, intV 5,
        intV 6, intV 7, intV 8, intV 9, intV 10, intV 11
      ]
    -- [B3] runtime underflow: size15 insufficient for x=15.
    , mkCase "err/underflow/size15-x15-y0"
      15 0 #[
        intV 0, intV 1, intV 2, intV 3, intV 4,
        intV 5, intV 6, intV 7, intV 8, intV 9,
        intV 10, intV 11, intV 12, intV 13, intV 14
      ]
    -- [B3] runtime underflow: size13 insufficient for x=0,y=12.
    , mkCase "err/underflow/size13-x0-y12"
      0 12 #[
        intV 1, intV 2, intV 3, intV 4, intV 5, intV 6,
        intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13
      ]
    -- [B3] runtime underflow: all stack values are non-int to confirm stack-only path is value-agnostic.
    , mkCase "err/underflow/non-int-stack-small"
      3 3 #[.null, .cell Cell.empty, .tuple #[]]
    -- [B3] runtime underflow: boundary size for x=5,y=5.
    , mkCase "err/underflow/size5-x5-y5"
      5 5 #[
        intV 1, intV 2, intV 3, intV 4, intV 5
      ]
    -- [B3] runtime underflow: boundary size for x=5,y=7.
    , mkCase "err/underflow/size7-x5-y7"
      5 7 #[
        intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7
      ]
    -- [B3] runtime underflow: boundary size for x=14,y=15.
    , mkCase "err/underflow/size15-x14-y15"
      14 15 #[
        intV 0, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9,
        intV 10, intV 11, intV 12, intV 13, intV 14
      ]
    -- [B8] gas exact path: exact budget must execute.
    , mkCase "gas/exact-cost-succeeds"
      15 0 sampleStack16
      (#[.pushInt (.num xchg2ExactGas), .tonEnvOp .setGasLimit, .xchg2 15 0])
      (oracleGasLimitsExact xchg2ExactGas)
    -- [B8] gas exact-minus-one path: exact-1 must fail from oracle runner as out-of-gas.
    , mkCase "gas/exact-minus-one-fails"
      15 0 sampleStack16
      (#[.pushInt (.num xchg2ExactGasMinusOne), .tonEnvOp .setGasLimit, .xchg2 15 0])
      (oracleGasLimitsExact xchg2ExactGasMinusOne)
  ]
  fuzz := #[
    { seed := 2026021401
      count := 500
      gen := genXchg2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHG2
