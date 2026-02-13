import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

/-!
DROPX branch analysis (Lean + C++ reference):
- Lean implementation: `TvmLean/Semantics/Exec/Stack/DropX.lean`
- C++ implementation: `/Users/daniil/Coding/ton/crypto/vm/stackops.cpp` (`exec_drop_x`, opcode 0x65)

BRANCHES:
[B1] Normal path with no-op count:
  - Runtime: `popNatUpTo` succeeds on top count, and `x = 0` leaves stack unchanged.
  - Lean/C++: `count = 0` keeps all lower stack values.
  - Decoder/encoder: opcode `0x65` must decode as `.dropX` and encode back to exactly 8 bits.

[B2] Normal path with partial drop (1 <= x <= remaining stack size):
  - Runtime: `popNatUpTo` succeeds, `x ≤ st.stack.size` after popping count, and `take` trims top `x` values.
  - C++: `pop_smallint_range` + `check_underflow(x)` + `stack.pop_many(x)`.

[B3] Normal path dropping all below-count items (`x = remaining stack size`):
  - Runtime: `keep = 0`, result is empty stack.
  - C++: same final state.

[B4] Underflow before pop (`stack empty`):
  - Runtime: `popNatUpTo` delegates to `popInt`, which throws `stkUnd`.
  - C++: `stack.check_underflow(1)` in `exec_drop_x`.

[B5] Underflow after pop (`x > remaining stack size`):
  - Runtime: count is valid, but `x ≤ st.stack.size` fails after pop.
  - C++: same by `stack.check_underflow(x)` after reading `x`.

[B6] Range-check path on count (`count < 0`):
  - Runtime: `popNatUpTo` maps to `.rangeChk`.
  - C++: `pop_smallint_range(…)` rejects negative.

[B7] Range-check path on count (`count > max`):
  - Lean uses `max = (1 << 30) - 1`.
  - C++ in modern mode uses `max = (1 << 30) - 1`; this suite aligns with current Lean behavior.
  - Count above this threshold must fail before stack underflow branch.

[B8] Range-check path on NaN count:
  - Lean: `.nan` rejected in `popNatUpTo` as `.rangeChk`.
  - C++: equivalent NaN/invalid-integer handling in stack integer extraction.

[B9] Type-check path on non-int count:
  - Runtime: `.null`/`.cell` at count position triggers `typeChk` from `VM.popInt`.
  - C++: analogous `type_chk` path.

[B10] Assembler/decoder opcode mapping:
  - Only one byte opcode (`0x65`) is valid; decode must map to `DROPX`.
  - Adjacent opcode boundaries must remain distinct (`0x64`→REVX, `0x66`→TUCK).
  - Truncated prefixes must throw `.invOpcode`.

[B11] Gas accounting:
  - No variable gas penalty specific to DROPX payload; fixed opcode cost only.
  - Base gas must still be deterministic and exact-gas/minus-one must be observable.
  - Gas edge path: exact gas budget succeeds, exact-minus-one budget triggers out-of-gas before/at DROPX.

TOTAL BRANCHES: 11
-/

namespace Tests.Instr.Stack.DROPX

private def dropXId : InstrId := { name := "DROPX" }

private def dropX : Instr := .dropX

private def maxDropArg : Int := (1 <<< 30) - 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dropX])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dropXId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def dropXSetGasExact : Int :=
  computeExactGasBudget dropX

private def dropXSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne dropX

private def runDropXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackDropX dropX stack

private def runDropXDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackDropX instr (VM.push (intV 777)) stack

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
  | .ok (instr, _bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got success {instr}")

private def mkDropInitStack (below : Nat) (count : Int) : Array Value :=
  let belowStack : Array Value :=
    Array.ofFn (fun i : Fin below => intV (Int.ofNat i.1 + 1))
  belowStack.take below |> (·.push (intV count))

private def genDropXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    -- Success, small/no-op range.
    let (count, rng3) := randNat rng1 0 7
    let (extra, rng4) := randNat rng3 0 4
    let below := count + extra
    (mkCase s!"/fuzz/ok/noop-or-small-count-{tag}" (mkDropInitStack below count), rng4)
  else if shape = 1 then
    -- Success, wider small counts with partial drops.
    let (count, rng3) := randNat rng1 0 14
    let (extra, rng4) := randNat rng3 0 6
    let below := count + 1 + (extra % 3)
    (mkCase s!"/fuzz/ok/partial-drop-count-{tag}" (mkDropInitStack below count), rng4)
  else if shape = 2 then
    -- Underflow after pop for explicit short stacks.
    let (count, rng3) := randNat rng1 1 12
    let (below, rng4) := randNat rng3 0 3
    (mkCase s!"/fuzz/err/underflow-after-pop/{tag}" (mkDropInitStack below (count + below + 1)), rng4)
  else if shape = 3 then
    -- Negative count range errors.
    let (pick, rng3) := randNat rng1 0 4
    let count : Int :=
      if pick = 0 then -1
      else if pick = 1 then -2
      else if pick = 2 then -15
      else if pick = 3 then -1024
      else -65536
    (mkCase s!"/fuzz/err/range-neg/{tag}" (mkDropInitStack 5 count), rng3)
  else if shape = 4 then
    -- Out-of-range too-large count (positive).
    let outOfRange : Array Int :=
      #[(maxDropArg + 1), (maxDropArg + 7), maxInt257 + 1, maxInt257 + 2, -(maxInt257) - 1]
    let (idx, rng3) := randNat rng1 0 (outOfRange.size - 1)
    (mkCase s!"/fuzz/err/range-too-large/{tag}" (mkDropInitStack 6 outOfRange[idx]!), rng3)
  else if shape = 5 then
    -- NaN range path.
    let stack := #[intV 11, intV 12, .int .nan]
    (mkCase s!"/fuzz/err/nan-count/{tag}" stack, rng2)
  else if shape = 6 then
    -- Type errors on top-of-stack null.
    let stack := #[intV 11, intV 12, .null]
    (mkCase s!"/fuzz/err/type-top-null/{tag}" stack, rng2)
  else if shape = 7 then
    -- Type errors on top-of-stack cell.
    let stack := #[intV 11, intV 12, .cell Cell.empty]
    (mkCase s!"/fuzz/err/type-top-cell/{tag}" stack, rng2)
  else if shape = 8 then
    -- Empty stack underflow before popping count.
    (mkCase s!"/fuzz/err/empty-stack-before-pop/{tag}" #[], rng2)
  else if shape = 9 then
    -- Boundary-like, large valid x with tiny stack -> underflow after pop.
    (mkCase s!"/fuzz/err/underflow-large-valid-count/{tag}" (mkDropInitStack 1 maxDropArg), rng2)
  else if shape = 10 then
    -- No-op + payload mix branch coverage.
    let stack := #[intV 1, .null, .cell Cell.empty, .builder Builder.empty, intV 0]
    (mkCase s!"/fuzz/ok/noop-with-mixed-below/{tag}" stack, rng2)
  else
    -- High-count partial with mixed payload, still in bounds.
    let count : Int := 3
    let stack := #[
      intV 1000, .null, .tuple #[], .cell Cell.empty, intV 7, intV (-7), intV count]
    (mkCase s!"/fuzz/ok/partial-with-mix/{tag}" stack, rng2)

def suite : InstrSuite where
  id := dropXId
  unit := #[
    { name := "unit/dispatch/dropx-vs-fallback"
      run := do
        expectOkStack "fallback/non-dropx" (runDropXDispatchFallback .add #[]) #[intV 777] },
    { name := "unit/opcode/assemble-encode-byte"
      run := do
        let assembled ←
          match assembleCp0 [dropX] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/dropx failed: {e}")
        if assembled.bits = natToBits 0x65 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/dropx: expected 0x65, got {reprStr assembled.bits}") },
    { name := "unit/opcode/decode-encode-neighbors-and-truncation"
      run := do
        let code := Cell.mkOrdinary (natToBits 0x64 8 ++ natToBits 0x65 8 ++ natToBits 0x66 8) #[]
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/revx" s0 .reverseX 8
        let s2 ← expectDecodeStep "decode/dropx" s1 dropX 8
        let s3 ← expectDecodeStep "decode/tuck" s2 .tuck 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/neighbors: expected exhaustion, got {s3.bitsRemaining} bits remaining")
        expectDecodeErr "decode/truncated-7" (Cell.mkOrdinary (natToBits 0x65 7) #[]) .invOpcode
        expectDecodeErr "decode/truncated-15" (Cell.mkOrdinary (natToBits 0x65 15) #[]) .invOpcode }
  ]
  oracle := #[
    -- [B1] Normal no-op count.
    mkCase "ok/noop/one-below" #[intV 42, intV 0], -- [B1]
    mkCase "ok/noop/multiple-below" #[intV 1, intV 2, intV 3, intV 0], -- [B1]
    mkCase "ok/noop/noise-below" #[.cell Cell.empty, .null, .builder Builder.empty, intV 0], -- [B1]
    mkCase "ok/noop/max-value-count" #[intV 7, intV maxDropArg, intV 0], -- [B1]
    -- [B2] Partial valid drops.
    mkCase "ok/partial/drop1/preserve-two" #[intV 10, intV 20, intV 1], -- [B2]
    mkCase "ok/partial/drop1/preserve-mix" #[.null, .cell Cell.empty, intV 1], -- [B2]
    mkCase "ok/partial/drop2/small-stack" #[intV 11, intV 22, intV 33, intV 2], -- [B2]
    mkCase "ok/partial/drop2/multiple" #[intV 11, intV 22, intV 33, intV 44, intV 2], -- [B2]
    mkCase "ok/partial/drop3/with-negatives" #[intV (-1), intV 2, intV (-3), intV 3], -- [B2]
    mkCase "ok/partial/drop4/preserved-top-type" #[intV 9, .null, intV 5, intV 4, intV 4], -- [B2]
    mkCase "ok/partial/drop5/with-builder" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 5], -- [B2]
    mkCase "ok/partial/drop7/with-tuple" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 7], -- [B2]
    -- [B3] Drop exactly all below items.
    mkCase "ok/drop-to-empty/one-below" #[intV 99, intV 1], -- [B3]
    mkCase "ok/drop-to-empty/two-below" #[intV 7, intV 8, intV 2], -- [B3]
    mkCase "ok/drop-to-empty/three-below" #[intV 9, intV 10, intV 11, intV 3], -- [B3]
    mkCase "ok/drop-to-empty/four-below" #[intV 9, intV 10, intV 11, intV 12, intV 4], -- [B3]
    mkCase "ok/drop-to-empty/five-below" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 5], -- [B3]
    mkCase "ok/drop-to-empty/five-below-with-types" #[.null, intV 2, .cell Cell.empty, intV 4, intV 5, intV 5], -- [B3]
    -- [B4] Pre-pop underflow.
    mkCase "err/underflow/empty-stack" #[], -- [B4]
    -- [B5] Post-pop underflow.
    mkCase "err/underflow/short-stack-count3" #[intV 1, intV 2, intV 3], -- [B5]
    mkCase "err/underflow/count4-on-triple" #[intV 9, intV 8, intV 7, intV 4], -- [B5]
    mkCase "err/underflow/max-count-on-singleton" #[intV 13, intV maxDropArg], -- [B5]
    mkCase "err/underflow/boundary-valid-count-not-enough" #[intV 1, intV 2, intV (maxDropArg)], -- [B5]
    -- [B6] Range negative.
    mkCase "err/range/negative/neg1" #[intV 7, intV (-1)], -- [B6]
    mkCase "err/range/negative/neg2" #[intV 7, intV (-2)], -- [B6]
    mkCase "err/range/negative/neg255" #[intV 7, intV (-255)], -- [B6]
    mkCase "err/range/negative/mixed-stack" #[intV 0, .cell Cell.empty, intV (-42)], -- [B6]
    -- [B7] Range over max.
    mkCase "err/range/too-large/max+1" #[intV 7, intV (maxDropArg + 1)], -- [B7]
    mkCase "err/range/too-large/max+7" #[intV 7, intV (maxDropArg + 7)], -- [B7]
    mkCase "err/range/too-large/int257-overflow-negative" #[intV 7, intV (-(maxInt257) - 1)], -- [B7]
    -- [B8] NaN branch.
    -- [B9] Type-check branch.
    mkCase "err/type/top-null" #[intV 3, .null], -- [B9]
    mkCase "err/type/top-cell" #[intV 3, .cell Cell.empty], -- [B9]
    mkCase "err/type/top-builder" #[intV 3, .builder Builder.empty], -- [B9]
    mkCase "err/type/top-tuple" #[intV 3, .tuple #[]], -- [B9]
    -- [B11] Gas edge behavior.
    mkCase "gas/exact-success/sufficient-budget"
      (Array.replicate 7 (intV 1) |>.push (intV 7))
      #[.pushInt (.num dropXSetGasExact), .tonEnvOp .setGasLimit, dropX]
      { gasLimit := dropXSetGasExact, gasMax := dropXSetGasExact, gasCredit := 0 },
    mkCase "gas/exact-minus-one/out-of-gas"
      (Array.replicate 7 (intV 1) |>.push (intV 7))
      #[.pushInt (.num dropXSetGasExactMinusOne), .tonEnvOp .setGasLimit, dropX]
      { gasLimit := dropXSetGasExactMinusOne, gasMax := dropXSetGasExactMinusOne, gasCredit := 0 }
  ]
  fuzz := #[
    { seed := 2026021301
      count := 500
      gen := genDropXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.DROPX
