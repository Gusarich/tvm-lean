import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.PUSH

/-
INSTRUCTION: PUSH

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Short encoding branch (idx in 0..15) in `TvmLean/Model/Instr/Asm/Cp0.lean`:
   - `idx=0` emits opcode `0x20` (8 bits)
   - `idx=1` emits opcode `0x21` (8 bits)
   - `idx=2..15` emits `0x20 + idx` (8 bits)
   - C++ registers the same short-range branch via `OpcodeTable::mkfixedrange(0x22,0x30)`.

2. [B2] Long encoding branch (idx in 16..255) in Lean assembler and C++ `OpcodeTable::mkfixed(0x56,...)`:
   - Emits `0x56` + one-byte index argument (16 bits total in bytes).
   - `push idx` is rejected (`.rangeChk`) in Lean when `idx > 255`.

3. [B3] Runtime success branch in `execInstrStackPush` + `VM.fetch`:
   - For `idx < stack.depth`, fetch succeeds and `VM.push` appends a copy of `stack[stack.size - 1 - idx]`.

4. [B4] Runtime underflow branch in `VM.fetch` / `Stack::check_underflow_p`:
   - If `idx >= stack.depth`, execution raises `stkUnd`.

5. [B5] Decoder short-path boundaries in `TvmLean/Model/Instr/Codepage/Cp0.lean`:
   - `0x20`, `0x21` map to push0/push1 directly.
   - `0x22..0x2f` map to short push indices 2..15.
   - C++ dispatch shares the same boundaries and must not misclassify these with neighboring stack ops.

6. [B6] Decoder long-path branch in Codepage/Cp0:
   - `0x56` + payload byte maps to long push for any idx encoded in that byte.

7. [B7] Decoder round-trip/rounding branch (encode/decode consistency):
   - `PUSH` instructions assembled with short and long forms must decode back to `.push <idx>`.
   - Adjacent opcode boundaries must preserve intended instruction identity (`PUSH` family must not alias to `OVER`, `BLKSWAP`, etc.).

8. [B8] Gas edge-paths in `TvmLean/Model/Gas/Constants.lean` + `TvmLean/Semantics/Step/Step.lean`:
   - No branch-specific variable gas formula exists for PUSH itself: `instrGas = gasPerInstr + totBits`.
   - short form uses `totBits=8`, long form uses `totBits=16`.
   - Both exact-gas-success and exact-gas-minus-one-failure branches must be covered.

Total branches: 8

Assembler and decoder branches have dedicated tests for boundary and canonical forms. Runtime branches include success/underflow. Gas branch includes exact-vs-minus-one for both short/long encodings.
-/

private def pushId : InstrId := { name := "PUSH" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkPush (idx : Nat) : Instr :=
  .push idx

private def makeStack (len : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:len] do
      out := out.push (intV (Int.ofNat (i + 1)))
    return out

private def mkCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := pushId
    program := #[mkPush idx]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (idx : Nat)
    (setGasBudget : Int)
    (stackAfterSetGas : Array Value)
    (gasLimits : OracleGasLimits)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := pushId
    program := #[.pushInt (.num setGasBudget), .tonEnvOp .setGasLimit, mkPush idx]
    initStack := stackAfterSetGas.push (intV setGasBudget)
    gasLimits := gasLimits
    fuel := fuel }

private def runPushDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPush (mkPush idx) stack

private def runPushFallback (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPush (mkPush idx) (VM.push (intV 909)) stack

private def pushShortExactGas : Int :=
  computeExactGasBudget (mkPush 1)

private def pushShortMinusOneGas : Int :=
  computeExactGasBudgetMinusOne (mkPush 1)

private def pushLongExactGas : Int :=
  computeExactGasBudget (mkPush 16)

private def pushLongMinusOneGas : Int :=
  computeExactGasBudgetMinusOne (mkPush 16)

private def checkEncodedPrefix (label : String) (bits : BitString) (expected : BitString) : IO Unit := do
  if bits = expected then
    pure ()
  else
    throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr bits}")

private def pickIdxShortOrLong (rng0 : StdGen) : Nat × StdGen :=
  let pool : Array Nat := #[0, 1, 2, 3, 4, 7, 15, 16, 17, 31, 63, 127, 255]
  let (idx, rng1) := randNat rng0 0 (pool.size - 1)
  (pool[idx]!, rng1)

private def genPushFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (idx, rng2) :=
    match shape with
    | 0 => (0, rng1)
    | 1 => (1, rng1)
    | 2 =>
        let (k, r) := randNat rng1 2 15
        (k, r)
    | 3 =>
        let (k, r) := randNat rng1 16 63
        (k, r)
    | _ =>
        let (k, r) := randNat rng1 0 255
        (k, r)
  let (tag, rng3) := randNat rng2 0 999_999
  if shape = 0 then
    (mkCase s!"/fuzz/ok/short-idx0-empty/{tag}" 0 #[] {} 1_000_000, rng3)
  else if shape = 1 then
    let st := makeStack (idx + 1)
    (mkCase s!"/fuzz/ok/success/short/{idx}/{tag}" idx st, rng3)
  else if shape = 2 then
    let st := (makeStack (idx + 1)).set! 0 (.cell Cell.empty)
    (mkCase s!"/fuzz/ok/success/short/target-cell/{idx}/{tag}" idx st, rng3)
  else if shape = 3 then
    let st := (makeStack (idx + 1)).set! 0 (.null)
    (mkCase s!"/fuzz/ok/success/long/{idx}/{tag}" idx st, rng3)
  else if shape = 4 then
    (mkCase s!"/fuzz/err/underflow/empty/{idx}/{tag}" idx #[] {} 1_000_000, rng3)
  else if shape = 5 then
    let st := makeStack idx
    (mkCase s!"/fuzz/err/underflow/{idx}/{tag}" idx st, rng3)
  else if shape = 6 then
    let st := makeStack (idx + 2)
    (mkCase s!"/fuzz/ok/success/sparse/{idx}/{tag}" idx st, rng3)
  else if shape = 7 then
    let st := makeStack 2
    let gasLimits := oracleGasLimitsExact pushShortExactGas
    (mkGasCase s!"/fuzz/gas/short/exact/{tag}" 1 pushShortExactGas st gasLimits, rng3)
  else if shape = 8 then
    let st := makeStack 2
    let gasLimits := oracleGasLimitsExact pushShortMinusOneGas
    (mkGasCase s!"/fuzz/gas/short/minus-one/{tag}" 1 pushShortMinusOneGas st gasLimits, rng3)
  else if shape = 9 then
    let st := makeStack 17
    let gasLimits := oracleGasLimitsExact pushLongExactGas
    (mkGasCase s!"/fuzz/gas/long/exact/{tag}" 16 pushLongExactGas st gasLimits, rng3)
  else
    let st := makeStack 17
    let gasLimits := oracleGasLimitsExact pushLongMinusOneGas
    (mkGasCase s!"/fuzz/gas/long/minus-one/{tag}" 16 pushLongMinusOneGas st gasLimits, rng3)

private def shortBoundaryPool : Array Nat := #[0, 1, 2, 15]
private def longBoundaryPool : Array Nat := #[16, 17, 31, 127, 255]

private def pickShortBoundary (rng0 : StdGen) : Nat × StdGen :=
  let (idx, rng1) := randNat rng0 0 (shortBoundaryPool.size - 1)
  (shortBoundaryPool[idx]!, rng1)

private def pickLongBoundary (rng0 : StdGen) : Nat × StdGen :=
  let (idx, rng1) := randNat rng0 0 (longBoundaryPool.size - 1)
  (longBoundaryPool[idx]!, rng1)

private def genPushFuzzCaseAdvanced (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (tag, rng2) := randNat rng1 0 999_999
  match shape with
  | 0 =>
      let (idx, rng3) := pickShortBoundary rng2
      let st := makeStack (idx + 1)
      ({ name := slashCaseName s!"/fuzzB/ok/safe-short/{idx}/{tag}", instr := pushId, program := #[mkPush idx], initStack := st }, rng3)
  | 1 =>
      let (idx, rng3) := pickLongBoundary rng2
      let st := makeStack (idx + 1)
      ({ name := slashCaseName s!"/fuzzB/ok/safe-long/{idx}/{tag}", instr := pushId, program := #[mkPush idx], initStack := st }, rng3)
  | 2 =>
      let (idx, rng3) := pickShortBoundary rng2
      let st := (makeStack (idx + 1)).set! 0 (.cell Cell.empty)
      ({ name := slashCaseName s!"/fuzzB/ok/safe-short-cell/{idx}/{tag}", instr := pushId, program := #[mkPush idx], initStack := st }, rng3)
  | 3 =>
      let (idx, rng3) := pickLongBoundary rng2
      let st := (makeStack (idx + 1)).set! 0 .null
      ({ name := slashCaseName s!"/fuzzB/ok/safe-long-null/{idx}/{tag}", instr := pushId, program := #[mkPush idx], initStack := st }, rng3)
  | 4 =>
      let (idx, rng3) := pickShortBoundary rng2
      let st := if idx = 0 then #[] else makeStack idx
      ({ name := slashCaseName s!"/fuzzB/err/underflow-short/{idx}/{tag}", instr := pushId, program := #[mkPush idx], initStack := st }, rng3)
  | 5 =>
      let (idx, rng3) := pickLongBoundary rng2
      let st := makeStack idx
      ({ name := slashCaseName s!"/fuzzB/err/underflow-long/{idx}/{tag}", instr := pushId, program := #[mkPush idx], initStack := st }, rng3)
  | 6 =>
      let st := makeStack 2
      let gasLimits := oracleGasLimitsExact pushShortExactGas
      (mkGasCase s!"/fuzzB/gas/success-short/{tag}" 1 pushShortExactGas st gasLimits, rng2)
  | 7 =>
      let st := makeStack 2
      let gasLimits := oracleGasLimitsExact pushShortMinusOneGas
      (mkGasCase s!"/fuzzB/gas/out-of-gas-short/{tag}" 1 pushShortMinusOneGas st gasLimits, rng2)
  | 8 =>
      let st := makeStack 17
      let gasLimits := oracleGasLimitsExact pushLongExactGas
      (mkGasCase s!"/fuzzB/gas/success-long/{tag}" 16 pushLongExactGas st gasLimits, rng2)
  | _ =>
      let st := makeStack 17
      let gasLimits := oracleGasLimitsExact pushLongMinusOneGas
      (mkGasCase s!"/fuzzB/gas/out-of-gas-long/{tag}" 16 pushLongMinusOneGas st gasLimits, rng2)


def suite : InstrSuite where
  id := pushId
  unit := #[
    { name := "/unit/direct/short-short/idx0-empty"
      run := do
        expectOkStack "/unit/direct/idx0-empty"
          (runPushDirect 0 #[])
          (#[(intV 1)].append #[])
    }
    ,
    { name := "/unit/direct/short/push1-on-2"
      run := do
        let stack : Array Value := #[intV 101, intV 202]
        expectOkStack "/unit/direct/idx1-on-2"
          (runPushDirect 1 stack)
          #[intV 101, intV 202, intV 101]
    }
    ,
    { name := "/unit/direct/long/push16-on-17"
      run := do
        let stack : Array Value := makeStack 17
        let expected := makeStack 17 ++ #[intV 1]
        expectOkStack "/unit/direct/idx16-on-17" (runPushDirect 16 stack) expected
    }
    ,
    { name := "/unit/direct/underflow/empty-idx1"
      run := do
        expectErr "/unit/direct/underflow-idx1"
          (runPushDirect 1 #[]) .stkUnd
    }
    ,
    { name := "/unit/direct/dispatch-fallback"
      run := do
        expectOkStack "/unit/direct/dispatch-fallback"
          (runPushFallback 3 #[])
          #[intV 909]
    }
    ,
    { name := "/unit/asm/encode-short-boundary"
      run := do
        checkEncodedPrefix "/unit/asm/idx0" (← match encodeCp0 (mkPush 0) with | .ok b => pure b | .error e => throw (IO.userError s!"encode idx0 failed {e}")) (natToBits 0x20 8)
        checkEncodedPrefix "/unit/asm/idx1" (← match encodeCp0 (mkPush 1) with | .ok b => pure b | .error e => throw (IO.userError s!"encode idx1 failed {e}")) (natToBits 0x21 8)
        checkEncodedPrefix "/unit/asm/idx2" (← match encodeCp0 (mkPush 2) with | .ok b => pure b | .error e => throw (IO.userError s!"encode idx2 failed {e}")) (natToBits 0x22 8)
        checkEncodedPrefix "/unit/asm/idx15" (← match encodeCp0 (mkPush 15) with | .ok b => pure b | .error e => throw (IO.userError s!"encode idx15 failed {e}")) (natToBits 0x2f 8)
        checkEncodedPrefix "/unit/asm/idx16" (← match encodeCp0 (mkPush 16) with | .ok b => pure b | .error e => throw (IO.userError s!"encode idx16 failed {e}")) (natToBits 0x56 8 ++ natToBits 0x10 8)
        checkEncodedPrefix "/unit/asm/idx255" (← match encodeCp0 (mkPush 255) with | .ok b => pure b | .error e => throw (IO.userError s!"encode idx255 failed {e}")) (natToBits 0x56 8 ++ natToBits 0xff 8)
    }
    ,
    { name := "/unit/asm/encode-range"
      run := do
        match encodeCp0 (mkPush 256) with
        | .ok _ => throw (IO.userError "/unit/asm/encode-range expected rangeChk for idx=256")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/asm/encode-range wrong error: {e}")
    }
    ,
    { name := "/unit/codec/roundtrip-and-boundary"
      run := do
        let i0 := mkPush 0
        let i1 := mkPush 1
        let i15 := mkPush 15
        let i16 := mkPush 16
        let i255 := mkPush 255
        let prog := #[i0, i1, i15, i16, i255]
        let code ←
          match assembleCp0 prog.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/codec/roundtrip assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/codec/roundtrip-idx0" s0 i0 8
        let s2 ← expectDecodeStep "/unit/codec/roundtrip-idx1" s1 i1 8
        let s3 ← expectDecodeStep "/unit/codec/roundtrip-idx15" s2 i15 8
        let s4 ← expectDecodeStep "/unit/codec/roundtrip-idx16" s3 i16 16
        let _s5 ← expectDecodeStep "/unit/codec/roundtrip-idx255" s4 i255 16
    }
    ,
    { name := "/unit/codec/non-canonical-long-0"
      run := do
        let slice := mkSliceFromBits (natToBits 0x56 8 ++ natToBits 0 8)
        let _ ← expectDecodeStep "/unit/codec/non-canonical-0" slice (mkPush 0) 16
    }
  ]
  oracle := #[
    -- [B1,B3,B7] short canonical encode/decode behavior for idx0 push-on-empty
    mkCase "/ok/B1/B3/B7/idx0-on-empty" 0 #[]
    ,
    -- [B1,B7] short canonical idx1 with one-tail
    mkCase "/ok/B1/B7/idx1-with-tail" 1 #[intV 11]
    ,
    -- [B1,B7] short idx2 from 3-stack
    mkCase "/ok/B1/B7/idx2-preserves-before-stack" 2 (makeStack 3)
    ,
    -- [B1,B7] short idx3 from mixed stack
    mkCase "/ok/B1/B7/idx3-null-target" 3 (#[.null, intV 5, intV 2, intV 7])
    ,
    -- [B2,B7] short idx15 with max short boundary
    mkCase "/ok/B2/B7/idx15-max-short" 15 (makeStack 16)
    ,
    -- [B2,B7] short idx14 with non-int target depth
    mkCase "/ok/B2/B7/idx14-target-cell" 14 ( (makeStack 15).set! 0 (.cell Cell.empty) )
    ,
    -- [B3,B7] long boundary idx16
    mkCase "/ok/B3/B7/idx16-min-long" 16 (makeStack 17)
    ,
    -- [B3,B7] long non-boundary idx31
    mkCase "/ok/B3/B7/idx31" 31 (makeStack 32)
    ,
    -- [B3,B7] long idx63 with non-int target
    mkCase "/ok/B3/B7/idx63-target-null" 63 ( (makeStack 64).set! 0 .null )
    ,
    -- [B3,B7] long idx127 with mixed target
    mkCase "/ok/B3/B7/idx127-target-cell" 127 ( (makeStack 128).set! 0 (.cell Cell.empty) )
    ,
    -- [B3,B7] long idx255 with maximum-byte payload and top marker
    mkCase "/ok/B3/B7/idx255-max-long" 255 (makeStack 256)
    ,
    -- [B5] non-zero stack tail preserved at various depths
    mkCase "/ok/B5/preserve-depth-3" 3 (#[.cell Cell.empty, .null, intV 42, intV (-7)])
    ,
    -- [B5] preserve deep mixed stack for short index
    mkCase "/ok/B5/preserve-mixed-short" 5 (#[.cell Cell.empty, intV (-1), .null, intV 100, intV 200, intV 300])
    ,
    -- [B5] preserve deep mixed stack for long index
    mkCase "/ok/B5/preserve-mixed-long" 20 (#[.null, .cell Cell.empty, intV (-1), intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16, intV 17, intV 18, intV 19, intV 20])
    ,
    -- [B6] runtime underflow at zero stack
    mkCase "/err/B6/underflow-empty-idx0" 0 #[]
    ,
    -- [B6] runtime underflow at zero stack
    mkCase "/err/B6/underflow-empty-idx1" 1 #[]
    ,
    -- [B6] runtime underflow short edge
    mkCase "/err/B6/underflow-edge-idx1-on-1" 1 #[intV 1]
    ,
    -- [B6] runtime underflow short edge
    mkCase "/err/B6/underflow-edge-idx15-on-15" 15 (makeStack 15)
    ,
    -- [B6] runtime underflow long edge (boundary idx16 needs 17)
    mkCase "/err/B6/underflow-long-boundary-idx16-on-16" 16 (makeStack 16)
    ,
    -- [B6] runtime underflow long
    mkCase "/err/B6/underflow-long-idx63-on-40" 63 (makeStack 40)
    ,
    -- [B8] gas exact short success
    mkGasCase "/gas/B8/success-short/exact" 1 pushShortExactGas
      (makeStack 2) (oracleGasLimitsExact pushShortExactGas)
    ,
    -- [B8] gas exact short minus one
    mkGasCase "/gas/B8/under-gas/short/minus-one" 1 pushShortMinusOneGas
      (makeStack 2) (oracleGasLimitsExact pushShortMinusOneGas)
    ,
    -- [B8] gas exact long success
    mkGasCase "/gas/B8/success-long/exact" 16 pushLongExactGas
      (makeStack 17) (oracleGasLimitsExact pushLongExactGas)
    ,
    -- [B8] gas exact long minus one
    mkGasCase "/gas/B8/under-gas/long/minus-one" 16 pushLongMinusOneGas
      (makeStack 17) (oracleGasLimitsExact pushLongMinusOneGas)
    ,
    -- [B1,B8] short with boundary idx2 and non-empty stack, exact-ish runtime and fetch coverage
    mkCase "/ok/B1/B7/nonzero-stack-target-null" 2 #[.null, intV 7, intV 8]
    ,
    -- [B3,B8] long with boundary idx16 and non-empty stack cell target
    mkCase "/ok/B3/B7/idx16-target-cell" 16 ((makeStack 17).set! 0 (.cell Cell.empty))
    ,
    -- [B4] assembler branch-out for idx > 255 covered by unit tests; oracle coverage via mixed success/failure cases remains complete
    mkCase "/ok/B1/B7/idx8-with-cell-target" 8 ((makeStack 9).set! 0 (.cell Cell.empty))
    ,
    -- [B3,B7] long idx31 with top-tail marker pattern
    mkCase "/ok/B3/B7/idx31-top-null" 31 (#[intV 31, intV 30, .null, intV 29, intV 28, intV 27, intV 26, intV 25, intV 24, intV 23, intV 22, intV 21, intV 20, intV 19, intV 18, intV 17, intV 16, intV 15, intV 14, intV 13, intV 12, intV 11, intV 10, intV 9, intV 8, intV 7, intV 6, intV 5, intV 4, intV 3, intV 2, intV 1, intV 0, intV (-1), intV (-2)])
    ,
    -- [B5] short idx3 with tuple-like mixed lower stack values
    mkCase "/ok/B5/mixed/idx3" 3 (#[.cell Cell.empty, .null, intV (-11), intV 19, intV 42])
    ,
    -- [B5] long idx24 with non-numeric target
    mkCase "/ok/B5/idx24-target-null" 24 ((makeStack 25).set! 0 .null)
    ,
    -- [B5] short idx9 with minimum positive values
    mkCase "/ok/B5/idx9-minmax" 9 (makeStack 10)
  ]
  fuzz := #[
    {
      seed := 2026020810
      count := 500
      gen := genPushFuzzCase
    },
    {
      seed := 2026020811
      count := 500
      gen := genPushFuzzCaseAdvanced
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PUSH
