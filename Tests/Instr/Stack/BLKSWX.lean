import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.BLKSWX

/-
INSTRUCTION: BLKSWX

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path:
   - `execInstrStackBlkSwapX` matches `.blkSwapX`.
   - All other instructions dispatch through `next`.
2. [B2] Runtime success with rotation (`x > 0 ∧ y > 0`):
   - `y` and `x` are popped via `popNatUpTo`, then `total := x + y`.
   - If `total ≤ st.stack.size`, the top block is rearranged as:
     `front ++ top ++ below`, where
     `front := st.stack.take (n - total)`,
     `below := st.stack.extract (n - total) (n - y)`,
     `top := st.stack.extract (n - y) n`, and `n := st.stack.size`.
3. [B3] Runtime no-op with `x = 0`:
   - `pop` + checks pass, `x > 0 ∧ y > 0` is false, so payload stack is unchanged.
4. [B4] Runtime no-op with `y = 0`:
   - Same as [B3], same unchanged-final-stack behavior.
5. [B5] Runtime underflow:
   - After pops, if `total > st.stack.size`, execution throws `.stkUnd`.
6. [B6] Runtime arg-`y` range/type failures:
   - `y` must be int.
   - `.rangeChk` for `y < 0` or `y` too large.
   - `.typeChk` for non-int `y`.
7. [B7] Runtime arg-`x` range/type failures:
   - Same checks as [B6], applied to `x` after successfully popping `y`.
8. [B8] Assembler fixed encoding:
   - `.blkSwapX` always assembles to `0x63`.
9. [B9] No assembler parameter-validation branch:
   - `.blkSwapX` has no arguments, so there are no range/reject branches.
10. [B10] Decoder normal path:
    - raw `0x63` decodes to `.blkSwapX` consuming exactly 8 bits.
11. [B11] Decoder adjacency path:
    - `0x62` decodes to `.rollRev`.
    - `0x64` decodes to `.reverseX`.
12. [B12] Decoder truncation path:
    - 7-bit input is truncated and fails as `invOpcode`.
13. [B13] Base gas branch:
    - `computeExactGasBudget (.blkSwapX)` is the fixed baseline.
14. [B14] Variable gas branch:
    - `total > 255` consumes extra gas `(total - 255)`.
15. [B15] Gas edge branch:
    - exact gas succeeds, exact-minus-one fails (both base and variable-gas shapes).

TOTAL BRANCHES: 15

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def blkswxInstr : Instr := .blkSwapX
private def blkswxId : InstrId := { name := "BLKSWX" }

private def blkswxCode : Cell := Cell.mkOrdinary (natToBits 0x63 8) #[]
private def blkswxNeighborRollRev : Cell := Cell.mkOrdinary (natToBits 0x62 8) #[]
private def blkswxNeighborReverseX : Cell := Cell.mkOrdinary (natToBits 0x64 8) #[]
private def blkswxTrunc7 : Cell := Cell.mkOrdinary (natToBits 0x63 7) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkswxId
    program := #[blkswxInstr]
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
    instr := blkswxId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseWithProgram
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkswxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkIntStack (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    return out

private def withXYInt
    (payload : Array Value)
    (x : Int)
    (y : Int) : Array Value :=
  (payload.push (intV x)).push (intV y)

private def withXYValue
    (payload : Array Value)
    (x : Value)
    (y : Value) : Array Value :=
  (payload.push x).push y

private def valuePool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV 2,
    intV 5,
    intV 17,
    intV (-1),
    intV (-5),
    intV 255,
    intV (-255),
    .null,
    .cell Cell.empty,
    .slice (Slice.ofCell Cell.empty),
    .builder Builder.empty,
    .tuple #[],
    .cont (.quit 0)
  ]

private def pickValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (valuePool.size - 1)
  (valuePool[idx]!, rng1)

private def mkRandomStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in [0:n] do
      let (v, rng1) := pickValue rng
      out := out.push v
      rng := rng1
    return (out, rng)

private def expectedBlkSwapX (x y : Nat) (stack : Array Value) : Array Value :=
  if stack.size < 2 then
    #[]
  else
    let st : Array Value := stack.take (stack.size - 2)
    let total : Nat := x + y
    if total ≤ st.size then
      if x > 0 && y > 0 then
        let n : Nat := st.size
        let front : Array Value := st.take (n - total)
        let below : Array Value := st.extract (n - total) (n - y)
        let top : Array Value := st.extract (n - y) n
        front ++ top ++ below
      else
        st
    else
      st

private def blkswxExactGas : Int := computeExactGasBudget blkswxInstr
private def blkswxExactGasMinusOne : Int := computeExactGasBudgetMinusOne blkswxInstr
private def blkswxPenaltyTotal : Nat := 300
private def blkswxPenaltyGas : Int := blkswxExactGas + Int.ofNat (blkswxPenaltyTotal - 255)
private def blkswxPenaltyGasMinusOne : Int :=
  if blkswxPenaltyGas > 0 then blkswxPenaltyGas - 1 else 0

private def expectAssembleBlkSwx (label : String) : IO Unit := do
  match assembleCp0 [blkswxInstr] with
  | .ok code =>
      if code.bits = natToBits 0x63 8 then
        pure ()
      else
        throw (IO.userError s!"{label}: expected 0x63, got {reprStr code.bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected successful assemble, got {e}")

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, rest) =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {expectedInstr}, got {instr}")
      else if bits ≠ expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure rest

private def expectDecodeErr (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {instr} with {bits} bits")

private def runBlkSwxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackBlkSwapX blkswxInstr stack

private def runBlkSwxWithFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackBlkSwapX .add (VM.push (intV 777)) stack

private def genBlkSwxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (baseCase, rng2) :=
    match shape with
    | 0 =>
        (mkCase "fuzz/noop/x0-y0" (withXYInt (mkIntStack 4) 0 0), rng1)
    | 1 =>
        (mkCase "fuzz/noop/x0-y1" (withXYInt (mkIntStack 5) 0 1), rng1)
    | 2 =>
        (mkCase "fuzz/noop/x5-y0" (withXYInt (mkIntStack 7) 5 0), rng1)
    | 3 =>
        (mkCase "fuzz/rotate/x1-y1" (withXYInt (mkIntStack 5) 1 1), rng1)
    | 4 =>
        (mkCase "fuzz/rotate/x2-y3" (withXYInt (mkIntStack 8) 2 3), rng1)
    | 5 =>
        (mkCase "fuzz/rotate/x3-y2" (withXYInt (mkIntStack 10) 3 2), rng1)
    | 6 =>
        let (need, rng2) := randNat rng1 2 20
        let (payload, rng3) := mkRandomStack need rng2
        (mkCase (s!"fuzz/rotate/x{need}-y{need}") (withXYInt payload need need), rng3)
    | 7 =>
        (mkCase "fuzz/underflow/empty" #[], rng1)
    | 8 =>
        (mkCase "fuzz/underflow/one-item" #[intV 1], rng1)
    | 9 =>
        (mkCase "fuzz/underflow/short" (withXYInt (mkIntStack 2) 3 4), rng1)
    | 10 =>
        (mkCase "fuzz/err/y-negative" (withXYInt (mkIntStack 4) 2 (-1)), rng1)
    | 11 =>
        (mkCase "fuzz/err/y-too-large"
          (withXYInt (mkIntStack 4) 2 (maxInt257 + 1)), rng1)
    | 12 =>
        (mkCase "fuzz/err/y-null" (withXYValue (mkIntStack 4) (intV 2) .null), rng1)
    | 13 =>
        (mkCase "fuzz/err/y-cell" (withXYValue (mkIntStack 4) (intV 2) (.cell Cell.empty)), rng1)
    | 14 =>
        (mkCase "fuzz/err/x-negative" (withXYInt (mkIntStack 4) (-2) 2), rng1)
    | 15 =>
        (mkCase "fuzz/err/x-too-large"
          (withXYInt (mkIntStack 4) (maxInt257 + 1) 2), rng1)
    | 16 =>
        (mkCase "fuzz/err/x-null" (withXYValue (mkIntStack 4) .null (intV 2)), rng1)
    | 17 =>
        (mkCaseCode "fuzz/decode/valid-63" (mkIntStack 2) blkswxCode, rng1)
    | 18 =>
        (mkCaseCode "fuzz/decode/neighbor-62" #[] blkswxNeighborRollRev, rng1)
    | 19 =>
        (mkCaseCode "fuzz/decode/neighbor-64" #[] blkswxNeighborReverseX, rng1)
    | 20 =>
        (mkCaseCode "fuzz/decode/trunc7" #[] blkswxTrunc7, rng1)
    | _ =>
        (mkCase "fuzz/fallback" (mkIntStack 3), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := blkswxId
  unit := #[
    { name := "unit/dispatch/fallback-next"
      run := do
        expectOkStack "fallback/next"
          (runBlkSwxWithFallback #[intV 9, intV 10])
          (#[intV 9, intV 10, intV 777]) },
    { name := "unit/dispatch/match-noop"
      run := do
        let input := withXYInt (mkIntStack 3) 0 0
        expectOkStack "match/no-op"
          (runBlkSwxDirect input)
          (expectedBlkSwapX 0 0 input) },
    { name := "unit/dispatch/match-rotate"
      run := do
        let input := withXYInt (mkIntStack 4) 1 1
        expectOkStack "match/rotate"
          (runBlkSwxDirect input)
          (expectedBlkSwapX 1 1 input) },
    { name := "unit/dispatch/invalid-instr-fallback"
      run := do
        expectOkStack "dispatch/forward" (runBlkSwxWithFallback #[intV 9]) #[intV 9, intV 777] },
    { name := "unit/assemble/fixed"
      run := do
        expectAssembleBlkSwx "assemble-fixed" },
    { name := "unit/decode/valid-and-neighbors"
      run := do
        let _ ← expectDecodeStep "decode/63" (Slice.ofCell blkswxCode) blkswxInstr 8
        let _ ← expectDecodeStep "decode/62" (Slice.ofCell blkswxNeighborRollRev) .rollRev 8
        let _ ← expectDecodeStep "decode/64" (Slice.ofCell blkswxNeighborReverseX) .reverseX 8
        pure () },
    { name := "unit/decode/trunc-7"
      run := do
        expectDecodeErr "decode/trunc" blkswxTrunc7 },
    { name := "unit/runtime/range-and-type"
      run := do
        expectErr "range/y-negative"
          (runBlkSwxDirect (withXYInt (mkIntStack 4) 2 (-1)))
          .rangeChk
        expectErr "type/y-null"
          (runBlkSwxDirect (withXYValue (mkIntStack 4) (intV 2) .null))
          .typeChk
        expectErr "range/x-negative"
          (runBlkSwxDirect (withXYInt (mkIntStack 4) (-2) 2))
          .rangeChk
        expectErr "type/x-cell"
          (runBlkSwxDirect (withXYValue (mkIntStack 4) (.cell Cell.empty) (intV 2)))
          .typeChk
        expectErr "underflow/after-pop"
          (runBlkSwxDirect (withXYInt (mkIntStack 2) 2 2))
          .stkUnd }
  ]
  oracle := #[
    -- [B1]
    mkCaseWithProgram "oracle/dispatch/fallback" #[intV 11, intV 22] #[.add],
    -- [B3, B4]
    mkCase "oracle/noop/x0-y0" (withXYInt #[] 0 0),
    -- [B3]
    mkCase "oracle/noop/x0-y1" (withXYInt (mkIntStack 5) 0 1),
    -- [B4]
    mkCase "oracle/noop/x5-y0" (withXYInt (mkIntStack 8) 5 0),
    -- [B3, B4]
    mkCase "oracle/noop/x0-y100" (withXYInt (mkIntStack 10) 0 100),
    -- [B2]
    mkCase "oracle/rotate/x1-y1" (withXYInt (mkIntStack 4) 1 1),
    -- [B2]
    mkCase "oracle/rotate/x2-y3" (withXYInt (mkIntStack 10) 2 3),
    -- [B2]
    mkCase "oracle/rotate/x3-y2" (withXYInt (mkIntStack 12) 3 2),
    -- [B2]
    mkCase "oracle/rotate/x7-y4" (withXYInt (mkIntStack 20) 7 4),
    -- [B2]
    mkCase "oracle/rotate/x10-y10" (withXYInt (mkIntStack 32) 10 10),
    -- [B2]
    mkCase "oracle/rotate/x15-y15" (withXYInt (mkIntStack 40) 15 15),
    -- [B2]
    mkCase "oracle/rotate/x64-y64" (withXYInt (mkIntStack 140) 64 64),
    -- [B2]
    mkCase "oracle/rotate/x128-y128" (withXYInt (mkIntStack 300) 128 128),
    -- [B5]
    mkCase "oracle/underflow/empty" #[],
    -- [B5]
    mkCase "oracle/underflow/one-item" #[intV 1],
    -- [B5]
    mkCase "oracle/underflow/short" (withXYInt (mkIntStack 2) 3 4),
    -- [B5]
    mkCase "oracle/underflow/boundary" (withXYInt (mkIntStack 5) 8 8),
    -- [B6]
    mkCase "oracle/range/y-negative" (withXYInt (mkIntStack 4) 2 (-1)),
    -- [B6]
    mkCase "oracle/type/y-null" (withXYValue (mkIntStack 4) (intV 1) .null),
    -- [B6]
    mkCase "oracle/type/y-cell" (withXYValue (mkIntStack 4) (intV 1) (.cell Cell.empty)),
    -- [B7]
    mkCase "oracle/range/x-negative" (withXYInt (mkIntStack 4) (-2) 3),
    -- [B7]
    mkCase "oracle/type/x-null" (withXYValue (mkIntStack 4) .null (intV 1)),
    -- [B7]
    mkCase "oracle/type/x-cell" (withXYValue (mkIntStack 4) (.cell Cell.empty) (intV 1)),
    -- [B10]
    mkCaseCode "oracle/decode/valid-63" (mkIntStack 3) blkswxCode,
    -- [B11]
    mkCaseCode "oracle/decode/neighbor-62" #[] blkswxNeighborRollRev,
    -- [B11]
    mkCaseCode "oracle/decode/neighbor-64" #[] blkswxNeighborReverseX,
    -- [B12]
    mkCaseCode "oracle/decode/trunc7" #[] blkswxTrunc7,
    -- [B13]
    mkCaseWithProgram "oracle/gas/base-exact"
      (withXYInt (mkIntStack 4) 0 0)
      #[.pushInt (.num blkswxExactGas), .tonEnvOp .setGasLimit, blkswxInstr]
      (oracleGasLimitsExact blkswxExactGas),
    -- [B15]
    mkCaseWithProgram "oracle/gas/base-exact-minus-one"
      (withXYInt (mkIntStack 4) 0 0)
      #[.pushInt (.num blkswxExactGasMinusOne), .tonEnvOp .setGasLimit, blkswxInstr]
      (oracleGasLimitsExactMinusOne blkswxExactGas),
    -- [B14, B13]
    mkCaseWithProgram "oracle/gas/penalty-exact"
      (withXYInt (mkIntStack blkswxPenaltyTotal) (blkswxPenaltyTotal / 2) (blkswxPenaltyTotal / 2))
      #[.pushInt (.num blkswxPenaltyGas), .tonEnvOp .setGasLimit, blkswxInstr]
      (oracleGasLimitsExact blkswxPenaltyGas),
    -- [B14, B15]
    mkCaseWithProgram "oracle/gas/penalty-exact-minus-one"
      (withXYInt (mkIntStack blkswxPenaltyTotal) (blkswxPenaltyTotal / 2) (blkswxPenaltyTotal / 2))
      #[.pushInt (.num blkswxPenaltyGasMinusOne), .tonEnvOp .setGasLimit, blkswxInstr]
      (oracleGasLimitsExactMinusOne blkswxPenaltyGas)
  ]
  fuzz := #[
    { seed := 2026021309
      count := 500
      gen := genBlkSwxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.BLKSWX
