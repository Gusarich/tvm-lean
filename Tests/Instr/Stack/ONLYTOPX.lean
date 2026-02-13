import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.ONLYTOPX

/-
INSTRUCTION: ONLYTOPX

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path:
   - `execInstrStackOnlyTopX` handles only `.onlyTopX`; all other opcodes go to `next`.
2. [B2] Runtime success with `x == depth`: no stack truncation, no copy and no extra gas path.
3. [B3] Runtime success with `0 < x < depth` and `x ≤ 255`: keeps only the top `x` items.
4. [B4] Runtime success with `x == 0`: drops all stack items.
5. [B5] Runtime success with `x == depth > 255`: keeps all stack items and does not trigger surcharge because `d = 0`.
6. [B6] Runtime success with `x > 255` and `x < depth`: keeps top `x` items and charges `x - 255` gas.
7. [B7] Runtime error, empty stack:
   - `check_underflow(1)` / `stack.check_underflow(1)` triggers `.stkUnd`.
8. [B8] Runtime type error:
   - top value for count is not an integer (`.typeChk`).
9. [B9] Runtime range-check failures when parsing count:
   - negative values
   - values above `(1 <<< 30) - 1`
   - `Int.nan`
10. [B10] Runtime underflow after count parse: `x > depth` triggers `.stkUnd`.
11. [B11] Assembler encoding:
    - fixed opcode `0x6a` with exactly 8 bits.
    - there is no argument parser/range branch in assembler (`.onlyTopX` has no immediate parameter).
12. [B12] Decoder behavior:
    - `0x6a` decodes to `.onlyTopX` and consumes 8 bits.
    - neighboring opcodes `0x69` and `0x6b` remain distinct.
    - truncated `7`-bit raw forms produce `.invOpcode`.
13. [B13] Gas accounting:
    - exact gas from `computeExactGasBudget` should succeed, exact-minus-one should fail.
    - variable surcharge branch exists for `x > 255`; e.g. `x = 256` needs `base + 1`.

TOTAL BRANCHES: 13

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any category without VM-runtime branches (none here) is listed explicitly as absent.
-/

private def onlyTopXId : InstrId :=
  { name := "ONLYTOPX" }

private def onlyTopXInstr : Instr := .onlyTopX
private def chkDepthInstr : Instr := .chkDepth
private def onlyXInstr : Instr := .onlyX

private def onlyTopXWord : Nat := 0x6a
private def chkDepthWord : Nat := 0x69
private def onlyXWord : Nat := 0x6b
private def invalidWord : Nat := 0x6c

private def maxArg : Int := (1 <<< 30) - 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[onlyTopXInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := onlyTopXId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (code : Cell)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := onlyTopXId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkIntStack (n : Nat) : Array Value := Id.run do
  let mut st : Array Value := #[]
  for i in [0:n] do
    st := st.push (intV (Int.ofNat (i + 1)))
  return st

private def mkNoiseStack (n : Nat) : Array Value := Id.run do
  let mut st : Array Value := #[]
  for i in [0:n] do
    st :=
      match i % 7 with
      | 0 => st.push (intV (Int.ofNat (i + 1)))
      | 1 => st.push .null
      | 2 => st.push (.cell Cell.empty)
      | 3 => st.push (.slice (mkSliceFromBits (natToBits 0xa5 8)))
      | 4 => st.push (.builder Builder.empty)
      | 5 => st.push (.tuple #[])
      | _ => st.push (.cont (.quit 0))
  return st

private def mkTopIntStack (below : Nat) (top : Int) : Array Value :=
  mkIntStack below ++ #[intV top]

private def mkTopNoiseStack (below : Nat) (top : Value) : Array Value :=
  mkNoiseStack below ++ #[top]

private def onlyTopXGasExact : Int :=
  computeExactGasBudget onlyTopXInstr

private def onlyTopXGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne onlyTopXInstr

private def onlyTopXGasWithPenalty (x : Int) : Int :=
  if x > 255 then onlyTopXGasExact + (x - 255) else onlyTopXGasExact

private def runOnlyTopXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackOnlyTopX onlyTopXInstr stack

private def runOnlyTopXDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackOnlyTopX instr (VM.push (intV 27103)) stack

private def expectDecodeErr
    (label : String)
    (bits : BitString)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits bits) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr} bits={bits}")

private def genOnlyTopXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (case0, rng2) : OracleCase × StdGen :=
    if shape = 0 then
      let (below, rng2) := randNat rng1 0 16
      ({ name := "fuzz/success/noop-0", instr := onlyTopXId, initStack := mkTopIntStack below 0 }, rng2)
    else if shape = 1 then
      let (below, rng2) := randNat rng1 0 24
      ({ name := "fuzz/success/depth-match-small", instr := onlyTopXId, initStack := mkTopIntStack below (Int.ofNat (below + 1)) }, rng2)
    else if shape = 2 then
      let (pick, rng2) := randNat rng1 0 2
      if pick = 0 then
        ({ name := "fuzz/success/depth-match-255", instr := onlyTopXId, initStack := mkTopIntStack 254 255 }, rng2)
      else if pick = 1 then
        ({ name := "fuzz/success/depth-match-256", instr := onlyTopXId, initStack := mkTopIntStack 255 256 }, rng2)
      else
        ({ name := "fuzz/success/depth-match-300", instr := onlyTopXId, initStack := mkTopIntStack 299 300 }, rng2)
    else if shape = 3 then
      let (x, rng2) := randNat rng1 1 8
      let (extra, rng3) := randNat rng2 1 16
      ({ name := s!"fuzz/success/trim-small-{x}", instr := onlyTopXId, initStack := mkTopIntStack (x + extra) (Int.ofNat x) }, rng3)
    else if shape = 4 then
      let (pick, rng2) := randNat rng1 0 2
      let (extra, rng3) := randNat rng2 1 64
      if pick = 0 then
        ({ name := "fuzz/success/trim-large-256", instr := onlyTopXId, initStack := mkTopIntStack (256 + extra) 256 }, rng3)
      else if pick = 1 then
        ({ name := "fuzz/success/trim-large-257", instr := onlyTopXId, initStack := mkTopIntStack (257 + extra) 257 }, rng3)
      else
        ({ name := "fuzz/success/trim-large-1024", instr := onlyTopXId, initStack := mkTopIntStack (1024 + extra) 1024 }, rng3)
    else if shape = 5 then
      ({ name := "fuzz/err/underflow-empty", instr := onlyTopXId, initStack := #[] }, rng1)
    else if shape = 6 then
      let (below, rng2) := randNat rng1 0 10
      let (extra, rng3) := randNat rng2 1 25
      ({ name := "fuzz/err/underflow-after-pop", instr := onlyTopXId, initStack := mkTopIntStack below (Int.ofNat (below + extra + 1)) }, rng3)
    else if shape = 7 then
      let (pick, rng2) := randNat rng1 0 5
      let (below, rng3) := randNat rng2 0 6
      let top : Value :=
        if pick = 0 then
          .null
        else if pick = 1 then
          (.cell Cell.empty)
        else if pick = 2 then
          .slice (mkSliceFromBits (natToBits 0xa5 8))
        else if pick = 3 then
          (.builder Builder.empty)
        else if pick = 4 then
          .tuple #[]
        else
          .cont (.quit 0)
      ({ name := "fuzz/err/type", instr := onlyTopXId, initStack := mkTopNoiseStack below top }, rng3)
    else if shape = 8 then
      let (below, rng2) := randNat rng1 0 9
      let (negAbs, rng3) := randNat rng2 1 4096
      ({ name := "fuzz/err/neg", instr := onlyTopXId, initStack := mkTopIntStack below (-Int.ofNat negAbs) }, rng3)
    else if shape = 9 then
      let (pick, rng2) := randNat rng1 0 2
      let (below, rng3) := randNat rng2 0 6
      let x : Int :=
        if pick = 0 then
          maxArg + 1
        else if pick = 1 then
          maxArg + 7
        else
          maxArg + 128
      ({ name := "fuzz/err/overflow", instr := onlyTopXId, initStack := mkTopIntStack below x }, rng3)
    else if shape = 10 then
      ({ name := "fuzz/err/nan", instr := onlyTopXId, initStack := mkTopNoiseStack 3 (.int .nan) }, rng1)
    else if shape = 11 then
      ({ name := "fuzz/decode/truncated-7", instr := onlyTopXId, codeCell? := some (Cell.mkOrdinary (natToBits onlyTopXWord 7)), initStack := #[] }, rng1)
    else if shape = 12 then
      ({
        name := "fuzz/gas/exact",
        instr := onlyTopXId,
        initStack := mkTopIntStack 32 3,
        program := #[.pushInt (.num onlyTopXGasExact), .tonEnvOp .setGasLimit, onlyTopXInstr],
        gasLimits := { gasLimit := onlyTopXGasExact, gasMax := onlyTopXGasExact, gasCredit := 0 }
      }, rng1)
    else
      let x : Int := 256
      let gas : Int := onlyTopXGasWithPenalty x
      ({
        name := "fuzz/gas/penalty",
        instr := onlyTopXId,
        initStack := mkTopIntStack 300 x,
        program := #[.pushInt (.num (gas - 1)), .tonEnvOp .setGasLimit, onlyTopXInstr],
        gasLimits := { gasLimit := gas - 1, gasMax := gas - 1, gasCredit := 0 }
      }, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleCases : Array OracleCase := #[
  -- [B2]
  mkCase "ok/noop/depth-1" (mkTopIntStack 0 1),
  -- [B2]
  mkCase "ok/noop/depth-2" (mkTopIntStack 1 2),
  -- [B2]
  mkCase "ok/noop/depth-3" (mkTopIntStack 2 3),
  -- [B2]
  mkCase "ok/noop/depth-4-mixed" (#[(.null), intV 11, .cell Cell.empty, intV 4]),
  -- [B3]
  mkCase "ok/trim/depth-4-x1" (mkTopIntStack 3 1),
  -- [B3]
  mkCase "ok/trim/depth-5-x2" (mkTopIntStack 4 2),
  -- [B3]
  mkCase "ok/trim/depth-6-x3" (mkNoiseStack 2 ++ mkTopIntStack 3 3),
  -- [B3]
  mkCase "ok/trim/depth-4-x127" (mkTopIntStack 3 127),
  -- [B4]
  mkCase "ok/zero/depth-1" (mkTopIntStack 0 0),
  -- [B4]
  mkCase "ok/zero/depth-3" (mkNoiseStack 2 ++ #[intV 0]),
  -- [B4]
  mkCase "ok/zero/depth-4-mixed" (#[(.null), (.cell Cell.empty), .builder Builder.empty, intV 0]),
  -- [B5]
  mkCase "ok/large-equal/depth-256" (mkTopIntStack 255 256),
  -- [B5]
  mkCase "ok/large-equal/depth-300" (mkTopIntStack 299 300),
  -- [B5]
  mkCase "ok/large-equal/noise" (mkNoiseStack 64 ++ mkIntStack 236 ++ #[intV 300]),
  -- [B6]
  mkCase "ok/trim-large/depth-300-x256" (mkTopIntStack 300 256),
  -- [B6]
  mkCase "ok/trim-large/depth-500-x257" (mkTopIntStack 500 257),
  -- [B6]
  mkCase "ok/trim-large/depth-1280-x1024" (mkTopIntStack 1280 1024),
  -- [B7]
  mkCase "err/underflow/empty" #[],
  -- [B10]
  mkCase "err/underflow/depth-1" (mkTopIntStack 1 2),
  -- [B10]
  mkCase "err/underflow/depth-3" (mkTopIntStack 2 7),
  -- [B8]
  mkCase "err/type/null" (#[(.null)]),
  -- [B8]
  mkCase "err/type/cell" (mkTopNoiseStack 2 (.cell Cell.empty)),
  -- [B8]
  mkCase "err/type/slice" (mkTopNoiseStack 2 (.slice (mkSliceFromBits (natToBits 0xa5 8)))),
  -- [B8]
  mkCase "err/type/builder" (mkTopNoiseStack 2 (.builder Builder.empty)),
  -- [B8]
  mkCase "err/type/tuple" (mkTopNoiseStack 2 (.tuple #[])),
  -- [B8]
  mkCase "err/type/cont" (mkTopNoiseStack 2 (.cont (.quit 0))),
  -- [B9]
  mkCase "err/range/negative-one" (mkTopIntStack 1 (-1)),
  -- [B9]
  mkCase "err/range/negative-large" (mkTopIntStack 2 (-Int.ofNat (1 <<< 16))),
  -- [B9]
  mkCase "err/range/overflow-plus-one" (mkTopIntStack 1 (maxArg + 1)),
  -- [B9]
  mkCase "err/range/overflow-large" (mkTopIntStack 2 (maxArg + 9999)),
  -- [B11]
  mkCase "asm/roundtrip" (mkTopIntStack 1 1),
  -- [B12]
  mkCaseCode "decode/roundtrip-single" (Cell.mkOrdinary (natToBits onlyTopXWord 8)) (mkTopIntStack 1 1),
  -- [B12]
  mkCaseCode "decode/neighbor-triple"
    (Cell.mkOrdinary (natToBits chkDepthWord 8 ++ natToBits onlyTopXWord 8 ++ natToBits onlyXWord 8))
    (mkTopIntStack 2 2 ++ #[intV 2]),
  -- [B12]
  mkCaseCode "decode/truncated" (Cell.mkOrdinary (natToBits onlyTopXWord 7)) (mkTopIntStack 1 1),
  -- [B12]
  mkCaseCode "decode/invalid-6c" (Cell.mkOrdinary (natToBits invalidWord 8)) (mkTopIntStack 1 1),
  -- [B13]
  mkCase "gas/exact-success"
    (mkTopIntStack 4 3)
    (#[.pushInt (.num onlyTopXGasExact), .tonEnvOp .setGasLimit, onlyTopXInstr])
    { gasLimit := onlyTopXGasExact, gasMax := onlyTopXGasExact, gasCredit := 0 },
  -- [B13]
  mkCase "gas/exact-minus-one"
    (mkTopIntStack 4 3)
    (#[.pushInt (.num onlyTopXGasExactMinusOne), .tonEnvOp .setGasLimit, onlyTopXInstr])
    { gasLimit := onlyTopXGasExactMinusOne, gasMax := onlyTopXGasExactMinusOne, gasCredit := 0 },
  -- [B13]
  mkCase "gas/penalty-256-success"
    (mkTopIntStack 300 256)
    (#[.pushInt (.num (onlyTopXGasWithPenalty 256)), .tonEnvOp .setGasLimit, onlyTopXInstr])
    { gasLimit := onlyTopXGasWithPenalty 256, gasMax := onlyTopXGasWithPenalty 256, gasCredit := 0 },
  -- [B13]
  mkCase "gas/penalty-256-fail"
    (mkTopIntStack 300 256)
    (#[.pushInt (.num (onlyTopXGasWithPenalty 256 - 1)), .tonEnvOp .setGasLimit, onlyTopXInstr])
    { gasLimit := onlyTopXGasWithPenalty 256 - 1, gasMax := onlyTopXGasWithPenalty 256 - 1, gasCredit := 0 }
]

def suite : InstrSuite where
  id := onlyTopXId
  unit := #[
    { name := "unit/asm/onlytopx-encodes-6a"
      run := do
        match assembleCp0 [onlyTopXInstr] with
        | .error e => throw (IO.userError s!"assembleCp0 failed: {e}")
        | .ok code =>
            if code.bits != natToBits onlyTopXWord 8 then
              throw (IO.userError s!"expected 0x6a, got {reprStr code.bits}") },
    { name := "unit/asm/onlytopx-decode-roundtrip"
      run := do
        let code1 ←
          match assembleCp0 [onlyTopXInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assembleCp0 failed: {e}")
        match decodeCp0WithBits (Slice.ofCell code1) with
        | .error e => throw (IO.userError s!"decode failed: {e}")
        | .ok (decoded, bits, _) =>
            if decoded != onlyTopXInstr then
              throw (IO.userError s!"decoded wrong opcode: {reprStr decoded}")
            if bits ≠ 8 then
              throw (IO.userError s!"expected 8 bits, got {bits}") },
    { name := "unit/decode/adjacent-opcodes"
      run := do
        let code := mkSliceFromBits (natToBits chkDepthWord 8 ++ natToBits onlyTopXWord 8 ++ natToBits onlyXWord 8)
        let s1 ← expectDecodeStep "decode/chkDepth" code chkDepthInstr 8
        let s2 ← expectDecodeStep "decode/onlyTopX" s1 onlyTopXInstr 8
        let s3 ← expectDecodeStep "decode/onlyX" s2 onlyXInstr 8
        if s3.bitsRemaining ≠ 0 then
          throw (IO.userError s!"decode/adjacent-opcodes: expected no extra bits, got {s3.bitsRemaining}") },
    { name := "unit/decode/truncated-7bits"
      run := expectDecodeErr "decode/truncated-7" (natToBits onlyTopXWord 7) .invOpcode },
    { name := "unit/direct/dispatch"
      run := do
        expectOkStack "dispatch/handled"
          (runOnlyTopXDirect (#[(intV 10), intV 11, intV 2]))
          (#[(intV 10), intV 11])
        expectOkStack "dispatch/fallback"
          (runOnlyTopXDispatchFallback .nop (#[(intV 7), intV 1]))
          (#[(intV 7), intV 1, intV 27103]) },
    { name := "unit/direct/range-nan"
      run := do
        expectErr "direct/range-nan"
          (runOnlyTopXDirect (mkTopNoiseStack 2 (.int .nan)))
          .rangeChk },
    { name := "unit/gas/budgets"
      run := do
        if onlyTopXGasExact ≤ 0 then
          throw (IO.userError "expected positive exact gas budget")
        if onlyTopXGasExactMinusOne ≠ onlyTopXGasExact - 1 then
          throw (IO.userError "exact-minus-one mismatch for ONLYTOPX gas helper")
        pure () }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := 2026022409
      count := 500
      gen := genOnlyTopXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.ONLYTOPX
