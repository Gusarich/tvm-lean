import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.CHKDEPTH

/-
INSTRUCTION: CHKDEPTH

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch match:
   - `execInstrStackChkDepth` handles only `.chkDepth`; all others fall through to `next`.

2. [B2] Runtime success path:
   - `popNatUpTo (2^30 - 1)` succeeds on the top value.
   - After popping count `x`, check `x ≤ st.stack.size`.
   - On success, no elements are dropped; execution is equivalent to `pop` + compare.

3. [B3] Runtime underflow before pop:
   - Empty stack at entry causes `.stkUnd` from `popInt`.

4. [B4] Runtime underflow after pop:
   - Non-empty stack and valid count where `x > st.stack.size - 1` after pop causes `.stkUnd`.

5. [B5] Runtime type error:
   - Top element is non-integer (`.typeChk`) when popping the check argument.

6. [B6] Runtime range-check failures:
   - `.nan` in top position is `.rangeChk`.
   - negative integers are `.rangeChk`.
   - values above `(1 <<< 30) - 1` are `.rangeChk`.

7. [B7] Assembler encoding:
   - `.chkDepth` has a fixed 8-bit encoding `0x69`.
   - there is no immediate argument and therefore no assembler range/parameter failure branch.

8. [B8] Decoder behavior:
   - single opcode `0x69` decodes to `.chkDepth` and consumes exactly 8 bits.
   - neighboring opcodes `0x68` (`DEPTH`) and `0x6a` (`ONLYTOPX`) are distinct.

9. [B9] Decoder malformed prefix:
   - truncated inputs (7-bit and 15-bit) must decode as `.invOpcode`.

10. [B10] Gas accounting:
   - fixed-cost dispatch via `instrGas` (no variable penalty): exact budget succeeds, exact-minus-one fails.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any category without VM-runtime branches would be explicitly listed as such; none are absent here.
-/

private def chkDepthId : InstrId :=
  { name := "CHKDEPTH" }

private def chkDepthInstr : Instr :=
  .chkDepth
private def depthInstr : Instr :=
  .depth

private def chkDepthWord : Nat := 0x69
private def depthWord : Nat := 0x68
private def onlyTopXWord : Nat := 0x6a
private def invalidWord : Nat := 0x6c
private def invalidWord2 : Nat := 0x6f

private def maxArg : Int := (1 <<< 30) - 1
private def dispatchSentinel : Int := 27103
private def errTypeSliceStack : Array Value :=
  #[.slice (mkSliceFromBits (natToBits 0xa5 8))]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[chkDepthInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := chkDepthId
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
    instr := chkDepthId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def chkDepthExpected (stack : Array Value) : Array Value :=
  stack.take (stack.size - 1)

private def runChkDepthDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackChkDepth chkDepthInstr stack

private def runChkDepthDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackChkDepth instr (VM.push (intV dispatchSentinel)) stack

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {instr} ({bits} bits)")

private def chkDepthGasExact : Int :=
  computeExactGasBudget chkDepthInstr

private def chkDepthGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne chkDepthInstr

private def mkNoiseStack (size : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:size] do
    let r : Nat := i % 7
    out :=
      if r = 0 then
        out.push (intV (Int.ofNat (i + 1)))
      else if r = 1 then
        out.push .null
      else if r = 2 then
        out.push (.cell Cell.empty)
      else if r = 3 then
        out.push (.slice (mkSliceFromBits (natToBits 0x7d 8)))
      else if r = 4 then
        out.push (.builder Builder.empty)
      else if r = 5 then
        out.push (.tuple #[])
      else
        out.push (.cont (.quit 0))
  return out

private def mkBoundarySize (n : Nat) : Array Value :=
  mkNoiseStack n

private def genChkDepthFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (tag, _rng2) := randNat rng1 0 999_999
  let (case0, rng3) : OracleCase × StdGen :=
    if shape = 0 then
      ({
        name := "fuzz/success/zero",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := mkBoundarySize 2 ++ #[intV 0]
      }, rng1)
    else if shape = 1 then
      ({
        name := "fuzz/success/small-below",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := mkBoundarySize 4 ++ #[intV 1]
      }, rng1)
    else if shape = 2 then
      ({
        name := "fuzz/success/boundary-remaining",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := mkBoundarySize 5 ++ #[intV 5]
      }, rng1)
    else if shape = 3 then
      ({
        name := "fuzz/success/empty-after-pop",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := mkBoundarySize 1 ++ #[intV 0]
      }, rng1)
    else if shape = 4 then
      ({
        name := "fuzz/err/underflow-after-pop",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := #[intV 1]
      }, rng1)
    else if shape = 5 then
      ({
        name := "fuzz/err/negative-range",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := #[intV (-7)]
      }, rng1)
    else if shape = 6 then
      ({
        name := "fuzz/err/nan-range",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := #[.int .nan]
      }, rng1)
    else if shape = 7 then
      ({
        name := "fuzz/err/type-null",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := #[.null]
      }, rng1)
    else if shape = 8 then
      ({
        name := "fuzz/err/type-cell",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := #[.cell Cell.empty]
      }, rng1)
    else if shape = 9 then
      ({
        name := "fuzz/err/underflow-empty",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := #[]
      }, rng1)
    else if shape = 10 then
      ({
        name := "fuzz/err/out-of-range-large",
        instr := chkDepthId,
        program := #[chkDepthInstr],
        initStack := mkBoundarySize 2 ++ #[intV (maxArg + 1)]
      }, rng1)
    else if shape = 11 then
      ({
        name := "fuzz/decode/invalid-trunc8",
        instr := chkDepthId,
        codeCell? := some (Cell.mkOrdinary (natToBits chkDepthWord 8 ++ natToBits 0x00 7)),
        initStack := #[intV 1]
      }, rng1)
    else if shape = 12 then
      ({
        name := "fuzz/decode/neighbor-boundary",
        instr := chkDepthId,
        codeCell? := some (Cell.mkOrdinary (natToBits depthWord 8 ++ natToBits chkDepthWord 8 ++ natToBits invalidWord 8)),
        initStack := #[intV 0]
      }, rng1)
    else
      ({
        name := "fuzz/gas/exact-minus-one",
        instr := chkDepthId,
        program := #[
          .pushInt (.num chkDepthGasExactMinusOne),
          .tonEnvOp .setGasLimit,
          chkDepthInstr
        ],
        initStack := #[intV 0],
        gasLimits := { gasLimit := chkDepthGasExactMinusOne, gasMax := chkDepthGasExactMinusOne, gasCredit := 0 }
      }, rng1)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleCases : Array OracleCase := #[
  -- [B2] success with no-op count.
  mkCase "ok/noop-1" (mkBoundarySize 2 ++ #[intV 0]),
  mkCase "ok/noop-2" (mkNoiseStack 5 ++ #[intV 0]),
  mkCase "ok/noop-mixed" (#[(.null), .cell Cell.empty, intV 11, intV 0]),
  mkCase "ok/noop-tail" (mkBoundarySize 1 ++ #[intV 0]),
  -- [B2] success with partial checks.
  mkCase "ok/partial-1" (mkBoundarySize 3 ++ #[intV 1]),
  mkCase "ok/partial-2" (mkBoundarySize 6 ++ #[intV 2]),
  mkCase "ok/partial-3" (mkBoundarySize 10 ++ #[intV 4]),
  mkCase "ok/partial-4" (#[intV 1, intV 2, intV 3, intV 4, intV 5]),
  -- [B2] boundary with count equal remaining size.
  mkCase "ok/boundary-empty-rest" (#[(intV 77), intV 0]),
  mkCase "ok/boundary-keep-two" (#[(.null), (intV 22), (.cell Cell.empty), intV 2]),
  mkCase "ok/boundary-all-types" (#[intV 1, .null, .cell Cell.empty, .tuple #[], .builder Builder.empty, intV 6]),
  -- [B4] underflow after pop.
  mkCase "err/underflow-after-pop-1" (mkBoundarySize 0 ++ #[intV 1]),
  mkCase "err/underflow-after-pop-2" (mkBoundarySize 1 ++ #[intV 5]),
  mkCase "err/underflow-after-pop-3" (mkBoundarySize 2 ++ #[intV 7]),
  mkCase "err/underflow-after-pop-4" (#[intV 2, intV 3, intV 1, intV 5]),
  -- [B3] underflow before pop.
  mkCase "err/underflow-empty" #[],
  -- [B5] top non-integer.
      mkCase "err/type-null" #[.null],
      mkCase "err/type-cell" #[.cell Cell.empty],
      mkCase "err/type-slice" errTypeSliceStack,
      mkCase "err/type-builder" #[.builder Builder.empty],
  mkCase "err/type-tuple" #[.tuple #[]],
  mkCase "err/type-cont" #[.cont (.quit 0)],
  -- [B6] range-check negative values.
  mkCase "err/range-negative-1" #[intV (-1)],
  mkCase "err/range-negative-1024" #[intV (-1024)],
  mkCase "err/range-negative-big" #[intV (- (Int.ofNat 1 <<< 20))],
  -- [B6] range-check above max.
  mkCase "err/range-above-30bit" #[intV (maxArg + 1)],
  mkCase "err/range-above-30bit-stack" (mkBoundarySize 2 ++ #[intV (maxArg + 7)]),
  mkCase "err/range-int257" #[intV maxInt257],
  -- [B7] encode fixed opcode.
  { name := "asm/roundtrip"
    instr := chkDepthId
    program := #[chkDepthInstr]
    initStack := #[intV 1]
    gasLimits := {}
  },
  -- [B8] decode boundaries.
  mkCaseCode "decode/roundtrip-three" (Cell.mkOrdinary (natToBits depthWord 8 ++ natToBits chkDepthWord 8 ++ natToBits onlyTopXWord 8)) (#[])
    (gasLimits := { gasLimit := 1_000_000, gasMax := 1_000_000, gasCredit := 0 }),
  mkCaseCode "decode/roundtrip-single"
    (Cell.mkOrdinary (natToBits chkDepthWord 8))
    #[intV 7]
    (gasLimits := { gasLimit := 1_000_000, gasMax := 1_000_000, gasCredit := 0 }),
  -- [B9] malformed decode through raw truncated prefixes (decode happens with initial stack on oracle execution).
  mkCaseCode "decode/invalid-7" (Cell.mkOrdinary (natToBits chkDepthWord 7)) #[]
    (gasLimits := { gasLimit := 1_000_000, gasMax := 1_000_000, gasCredit := 0 }),
  mkCaseCode "decode/invalid-15" (Cell.mkOrdinary (natToBits chkDepthWord 15)) #[]
    (gasLimits := { gasLimit := 1_000_000, gasMax := 1_000_000, gasCredit := 0 }),
  mkCaseCode "decode/invalid-6c" (Cell.mkOrdinary (natToBits invalidWord 8)) #[]
    (gasLimits := { gasLimit := 1_000_000, gasMax := 1_000_000, gasCredit := 0 }),
  -- [B10] exact gas accounting.
  { name := "gas/exact-success"
    instr := chkDepthId
    program := #[
      .pushInt (.num chkDepthGasExact),
      .tonEnvOp .setGasLimit,
      chkDepthInstr
    ]
    initStack := #[intV 0]
    gasLimits := { gasLimit := chkDepthGasExact, gasMax := chkDepthGasExact, gasCredit := 0 } },
  { name := "gas/exact-minus-one-fail"
    instr := chkDepthId
    program := #[
      .pushInt (.num chkDepthGasExactMinusOne),
      .tonEnvOp .setGasLimit,
      chkDepthInstr
    ]
    initStack := #[intV 0]
    gasLimits := { gasLimit := chkDepthGasExactMinusOne, gasMax := chkDepthGasExactMinusOne, gasCredit := 0 } }
]

def suite : InstrSuite where
  id := chkDepthId
  unit := #[
    { name := "unit/direct/dispatch/handled"
      run := do
        expectOkStack "handled" (runChkDepthDispatchFallback chkDepthInstr (#[(intV 1), intV 2, intV 0]) ) (chkDepthExpected #[intV 1, intV 2, intV 0]) },
    { name := "unit/direct/dispatch/fallback"
      run := do
        expectOkStack "fallback"
          (runChkDepthDispatchFallback .nop #[intV 1, intV 2])
          (#[intV 1, intV 2, intV dispatchSentinel]) },
    { name := "unit/direct/ok/noop"
      run := do
        expectOkStack "unit/noop/emptyAfterPop" (runChkDepthDirect (#[intV 1, intV 0])) #[intV 1]
        expectOkStack "unit/noop/repeated" (runChkDepthDirect (mkNoiseStack 3 ++ #[intV 0])) (mkNoiseStack 3)
        expectOkStack "unit/noop/with-types" (runChkDepthDirect (#[(.null), .cell Cell.empty, intV 42, intV 0])) (#[(.null), .cell Cell.empty, intV 42]) },
    { name := "unit/direct/ok/partial"
      run := do
        expectOkStack "unit/partial/one" (runChkDepthDirect (#[intV 11, intV 22, intV 33, intV 1])) (#[(intV 11), intV 22, intV 33]
        )
        expectOkStack "unit/partial/three" (runChkDepthDirect (#[intV 11, intV 22, intV 33, intV 44, intV 3])) (#[(intV 11), intV 22, intV 33, intV 44])
        expectOkStack "unit/partial/boundary-size" (runChkDepthDirect (#[intV 77, intV 0])) #[intV 77] },
    { name := "unit/direct/ok/boundary"
      run := do
        let full := #[intV 1, intV 2, intV 3, intV 4, intV 5]
        let withCount := full ++ #[intV 5]
        expectOkStack "unit/boundary-equal-remaining-size" (runChkDepthDirect withCount) full },
    { name := "unit/direct/err/underflow-empty"
      run := do
        expectErr "unit/underflow-empty" (runChkDepthDirect #[]) .stkUnd },
    { name := "unit/direct/err/underflow-after-pop"
      run := do
        expectErr "unit/underflow-short-1" (runChkDepthDirect (#[intV 1])) .stkUnd
        expectErr "unit/underflow-short-2" (runChkDepthDirect (#[intV 11, intV 12, intV 3])) .stkUnd },
    { name := "unit/direct/err/type"
      run := do
        expectErr "unit/type-null" (runChkDepthDirect #[.null]) .typeChk
        expectErr "unit/type-cell" (runChkDepthDirect #[.cell Cell.empty]) .typeChk
        expectErr "unit/type-slice" (runChkDepthDirect #[.slice (mkSliceFromBits (natToBits 0xa5 8))]) .typeChk },
    { name := "unit/direct/err/range"
      run := do
        expectErr "unit/range-negative" (runChkDepthDirect (#[intV (-3)])) .rangeChk
        expectErr "unit/range-nan" (runChkDepthDirect (#[.int .nan])) .rangeChk
        expectErr "unit/range-overflow" (runChkDepthDirect (#[intV (maxArg + 1)])) .rangeChk },
    { name := "unit/asm/encode"
      run := do
        let bits := Cell.mkOrdinary (natToBits chkDepthWord 8)
        let assembled ←
          match assembleCp0 [chkDepthInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/asm/encode: {e}")
        if assembled.bits ≠ bits.bits then
          throw (IO.userError s!"unit/asm/encode: expected {reprStr bits.bits}, got {reprStr assembled.bits}")
        else
          pure () },
    { name := "unit/decode/branches"
      run := do
        let code := mkSliceFromBits (natToBits depthWord 8 ++ natToBits chkDepthWord 8 ++ natToBits onlyTopXWord 8)
        let s1 ← expectDecodeStep "decode/depth" code depthInstr 8
        let s2 ← expectDecodeStep "decode/chkDepth" s1 chkDepthInstr 8
        let s3 ← expectDecodeStep "decode/onlyTopX" s2 .onlyTopX 8
        if s3.bitsRemaining ≠ 0 then
          throw (IO.userError s!"decode/branches: expected no extra bits, got {s3.bitsRemaining}")
        expectDecodeErr "decode/invalid-6c" (Slice.ofCell (Cell.mkOrdinary (natToBits invalidWord 8))) .invOpcode
        expectDecodeErr "decode/invalid-6f" (Slice.ofCell (Cell.mkOrdinary (natToBits invalidWord2 8))) .invOpcode
        expectDecodeErr "decode/truncated-7" (Slice.ofCell (Cell.mkOrdinary (natToBits chkDepthWord 7))) .invOpcode
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits chkDepthWord 15))) with
        | .ok (.nop, 8, _) => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/truncated-15: expected alias nop(8), got {reprStr instr} ({bits} bits)")
        | .error e =>
            throw (IO.userError s!"decode/truncated-15: expected alias nop(8), got error {e}") },
    { name := "unit/gas/limits"
      run := do
        if chkDepthGasExact ≤ 0 then
          throw (IO.userError "unit/gas/limits: unexpected non-positive gas budget")
        if chkDepthGasExactMinusOne ≠ chkDepthGasExact - 1 then
          throw (IO.userError "unit/gas/limits: exact-minus-one gas budget mismatch")
        let okStack := #[]
        expectOkStack "unit/gas/limits/run-on-empty-stack" (runChkDepthDirect #[intV 0]) okStack
    }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := 2026021301
      count := 500
      gen := genChkDepthFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.CHKDEPTH
