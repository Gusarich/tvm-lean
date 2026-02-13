import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCPUXC

/-
INSTRUCTION: XCPUXC

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success path:
   - guard: `st.stack.size > Nat.max (Nat.max x y) 1 ∧ z ≤ st.stack.size`
   - then `swap 1 x`, `fetch y`, `push`, `swap 0 1`, `swap 0 z`.
2. [B2] Runtime underflow path:
   - same combined condition fails when size is too small for `x`/`y` or for mandatory `z` check.
   - C++ path is `check_underflow_p(x,y,1).check_underflow(z)`; both branches map to `stkUnd`.
3. [B3] Runtime index-shape effects:
   - legal equalities among `x`, `y`, `z` (`x=y`, `x=z`, `y=z`) and `x=0` change swap/fetch outcome.
4. [B4] Runtime type behavior:
   - no payload type checks; null/cell/slice/builder/tuple/cont values remain valid.
5. [B5] Assembler success encoding:
   - `.xcpuxc x y z` is valid for all `x,y,z` in `0..15`, encoded as 24-bit `0x542xyz`.
6. [B6] Assembler range failures:
   - any argument outside `0..15` rejects with `.rangeChk`.
7. [B7] Decoder primary branch:
   - 24-bit prefix `0x542` decodes as `.xcpuxc`.
8. [B8] Decoder neighbor branch:
   - `0x540`, `0x541`, `0x543` decode to `XCHG3`, `XC2PU`, `XCPU2` respectively.
9. [B9] Decoder truncation branch:
   - under-length encodings (e.g. 8/15/23 bits) fail with `invOpcode`.
10. [B10] Gas behavior:
   - fixed-cost path; exact budget succeeds and exact-minus-one fails.

TOTAL BRANCHES: 10

Each oracle test below is tagged with the branch(es) it covers.
-/

private def xcpuxcId : InstrId := { name := "XCPUXC" }

private def sampleCell : Cell := Cell.ofUInt 8 0x7f
private def sampleSlice : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0xaa 8) #[])
private def sampleBuilder : Value := .builder Builder.empty

private def cpCode (pref x y z : Nat) : Nat :=
  (pref <<< 12) + (x <<< 8) + (y <<< 4) + z

private def mkRawCode (pref x y z : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (cpCode pref x y z) 24) #[]

private def xcpuxcCode (x y z : Nat) : Cell := mkRawCode 0x542 x y z
private def xchg3Code (x y z : Nat) : Cell := mkRawCode 0x540 x y z
private def xc2puCode (x y z : Nat) : Cell := mkRawCode 0x541 x y z
private def xcpu2Code (x y z : Nat) : Cell := mkRawCode 0x543 x y z

private def trunc8Code : Cell := Cell.mkOrdinary (natToBits 0x54 8) #[]
private def trunc15Code : Cell := Cell.mkOrdinary (natToBits (cpCode 0x542 2 3 4 >>> 1) 15) #[]
private def trunc23Code : Cell := Cell.mkOrdinary (natToBits (cpCode 0x542 2 3 4 >>> 1) 23) #[]

private def mkCase
    (name : String)
    (x y z : Nat)
    (stack : Array Value)
    (program : Array Instr := #[.xcpuxc x y z])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xcpuxcId
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
    instr := xcpuxcId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runXcpuxcDirect
    (x y z : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXcpuxc (.xcpuxc x y z) stack

private def requiredDepth (x y z : Nat) : Nat :=
  let needXY : Nat := max (max x y) 1 + 1
  max needXY z

private def xcpuxcGasExact : Int :=
  computeExactGasBudget (.xcpuxc 0 0 0)

private def xcpuxcGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xcpuxc 0 0 0)

private def decodeXcpuxc (x y z : Nat) : Except Excno (Instr × Nat × Slice) :=
  decodeCp0WithBits (Slice.ofCell (xcpuxcCode x y z))

private def expectAssembleRangeErr
    (label : String)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ => throw (IO.userError s!"{label}: expected rangeChk failure, got success")
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected rangeChk, got {e}")

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat := 24)
    (expectEmptyTail : Bool := true) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e => throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (i, bits, tail) =>
      if i != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr i}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if expectEmptyTail && tail.bitsRemaining + tail.refsRemaining ≠ 0 then
        throw (IO.userError s!"{label}: expected empty tail, got {reprStr tail}")
      else
        pure ()

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr i} ({bits} bits)")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng0 : StdGen) : α × StdGen :=
  let (idx, rng1) := randNat rng0 0 (pool.size - 1)
  (pool[idx]!, rng1)

private def idxBoundaryPool : Array Nat := #[0, 1, 2, 3, 4, 5, 7, 8, 14, 15]

private def valuePool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 2,
    intV (-2),
    intV 10,
    intV maxInt257,
    intV (maxInt257 - 1),
    intV minInt257,
    intV (minInt257 + 1),
    .null,
    .cell sampleCell,
    .slice sampleSlice,
    sampleBuilder,
    .tuple #[],
    .cont (.quit 0)
  ]

private def genStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in [0:n] do
      let (v, rng') := pickFromPool valuePool rng
      out := out.push v
      rng := rng'
    return (out, rng)

private def genXcpuxcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (case0, rng2) :=
    if shape = 0 then
      let (x, rng3) := pickFromPool idxBoundaryPool rng1
      let (y, rng4) := pickFromPool idxBoundaryPool rng3
      let (z, rng5) := pickFromPool idxBoundaryPool rng4
      let depth : Nat := requiredDepth x y z + 1
      let (stack, rng6) := genStack depth rng5
      (mkCase "fuzz/success/balanced" x y z stack, rng6)
    else if shape = 1 then
      let (y, rng3) := pickFromPool idxBoundaryPool rng1
      let (z, rng4) := pickFromPool idxBoundaryPool rng3
      let depth : Nat := requiredDepth 0 y z
      let (stack, rng5) := genStack depth rng4
      (mkCase "fuzz/success/x0" 0 y z stack, rng5)
    else if shape = 2 then
      let (x, rng3) := pickFromPool idxBoundaryPool rng1
      let (z, rng4) := pickFromPool idxBoundaryPool rng3
      let depth : Nat := requiredDepth x x z
      let (stack, rng5) := genStack depth rng4
      (mkCase "fuzz/success/x-eq-y" x x z stack, rng5)
    else if shape = 3 then
      let (x, rng3) := pickFromPool idxBoundaryPool rng1
      let (y, rng4) := pickFromPool idxBoundaryPool rng3
      let depth : Nat := requiredDepth x y y
      let (stack, rng5) := genStack depth rng4
      (mkCase "fuzz/success/x-eq-z" x y y stack, rng5)
    else if shape = 4 then
      let (x, rng3) := pickFromPool idxBoundaryPool rng1
      let (y, rng4) := pickFromPool idxBoundaryPool rng3
      let depth : Nat := requiredDepth x y y
      let (stack, rng5) := genStack depth rng4
      (mkCase "fuzz/success/y-eq-z" x y y stack, rng5)
    else if shape = 5 then
      let (x, rng3) := randNat rng1 0 15
      let (y, rng4) := randNat rng3 0 15
      let need : Nat := max (max x y) 1
      let (size, rng5) :=
        if need = 0 then
          (0, rng4)
        else
          let (d, rng6) := randNat rng4 0 (need - 1)
          (d, rng6)
      let (stack, rng6) := genStack size rng5
      (mkCase "fuzz/underflow/x-y-gate" x y 0 stack, rng6)
    else if shape = 6 then
      let x : Nat := 0
      let y : Nat := 0
      let depth : Nat := 2
      let z : Nat := depth + 1
      let (stack, rng3) := genStack depth rng1
      (mkCase "fuzz/underflow/z-only" x y z stack, rng3)
    else if shape = 7 then
      let (stack, rng3) := genStack 0 rng1
      (mkCase "fuzz/underflow/empty" 0 0 0 stack, rng3)
    else if shape = 8 then
      (mkCase "fuzz/asm/bad-x" 16 0 0 #[intV 7, intV 8], rng1)
    else if shape = 9 then
      (mkCase "fuzz/asm/bad-y" 0 16 0 #[intV 7, intV 8], rng1)
    else if shape = 10 then
      (mkCase "fuzz/asm/bad-z" 0 0 16 #[intV 7, intV 8], rng1)
    else if shape = 11 then
      (mkCaseCode "fuzz/decode/truncated8" #[] trunc8Code, rng1)
    else
      (mkCaseCode "fuzz/decode/truncated23" #[] trunc23Code, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := xcpuxcId
  unit := #[
    { name := "unit/dispatch/handler-run"
      run := do
        -- [B1]
        expectOkStack "runtime/x0-y0-z1"
          (runXcpuxcDirect 0 0 1 #[intV 11, intV 22])
          #[intV 22, intV 11, intV 22] },
    { name := "unit/runtime/underflow-empty"
      run := do
        -- [B2]
        expectErr "runtime/empty" (runXcpuxcDirect 0 0 0 #[]) .stkUnd },
    { name := "unit/runtime/underflow-z-only"
      run := do
        -- [B2]
        expectErr "runtime/z-only" (runXcpuxcDirect 0 0 3 #[intV 1, intV 2]) .stkUnd },
    { name := "unit/runtime/non-int"
      run := do
        -- [B4]
        expectOkStack "runtime/non-int"
          (runXcpuxcDirect 1 0 0 #[.null, .cell sampleCell, sampleBuilder, intV 7])
          #[.cell sampleCell, .null, sampleBuilder, intV 7, sampleBuilder] },
    { name := "unit/asm/range-x"
      run := do
        -- [B6]
        expectAssembleRangeErr "unit/asm/range-x" (.xcpuxc 16 0 0) },
    { name := "unit/asm/range-y"
      run := do
        -- [B6]
        expectAssembleRangeErr "unit/asm/range-y" (.xcpuxc 0 16 0) },
    { name := "unit/asm/range-z"
      run := do
        -- [B6]
        expectAssembleRangeErr "unit/asm/range-z" (.xcpuxc 0 0 16) },
    { name := "unit/asm/valid-boundary"
      run := do
        -- [B5][B7]
        expectDecodeOk "unit/asm/decode-boundary" (xcpuxcCode 15 15 15) (.xcpuxc 15 15 15) },
    { name := "unit/decode/neighbors-and-truncation"
      run := do
        -- [B8][B9]
        expectDecodeOk "unit/decode/xchg3" (xchg3Code 2 3 4) (.xchg3 2 3 4)
        expectDecodeOk "unit/decode/xc2pu" (xc2puCode 2 3 4) (.xc2pu 2 3 4)
        expectDecodeOk "unit/decode/xcpu2" (xcpu2Code 2 3 4) (.xcpu2 2 3 4)
        expectDecodeErr "unit/decode/truncated-8" trunc8Code .invOpcode
        expectDecodeErr "unit/decode/truncated-15" trunc15Code .invOpcode },
  ]
  oracle := #[
    -- [B1][B5] baseline successes and boundary-shaped successes.
    mkCase "ok/near-min/x0-y0-z0" 0 0 0 #[intV 1, intV 2],
    mkCase "ok/near-min/x0-y1-z0" 0 1 0 #[intV 3, intV 4, intV 5],
    mkCase "ok/near-min/x1-y0-z1" 1 0 1 #[intV 1, intV 2],
    mkCase "ok/near-min/x1-y1-z1" 1 1 1 #[intV 9, intV 8, intV 7],
    mkCase "ok/near-min/x2-y0-z3" 2 0 3 #[intV 10, intV 20, intV 30, intV 40],
    mkCase "ok/near-min/x4-y2-z1" 4 2 1 #[intV 11, intV 22, intV 33, intV 44, intV 55],
    mkCase "ok/near-min/x15-y14-z15" 15 14 15 #[intV 0, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16],
    mkCase "ok/type-mix/contains-non-int" 0 0 0 #[.null, .cell sampleCell, sampleBuilder, .tuple #[], intV 7, .cont (.quit 0)],

    -- [B3] index-shape edges.
    mkCase "ok/alias-x-eq-y" 4 4 1 #[intV 70, intV 80, intV 90, intV 100],
    mkCase "ok/alias-x-eq-z" 3 5 3 #[intV 5, intV 6, intV 7, intV 8, intV 9, intV 10],
    mkCase "ok/alias-y-eq-z" 2 1 1 #[intV 13, intV 14, intV 15, intV 16, intV 17],
    mkCase "ok/x0-y0-z1-boundary" 0 0 1 #[intV 31, intV 32],
    mkCase "ok/x0-y3-z0-boundary" 0 3 0 #[intV 1, intV 2, intV 3, intV 4],

    -- [B2] deep/mixed payload success cases.
    mkCase "ok/deep/mixed-types-1" 7 4 2 #[intV 1, .null, .cell sampleCell, .slice sampleSlice, intV 2, intV 3, .builder Builder.empty, .tuple #[], intV 4],
    mkCase "ok/deep/mixed-types-2" 9 1 11 #[intV 0, .cont (.quit 0), .cell sampleCell, .slice sampleSlice, .null, intV 42, intV 43],
    mkCase "ok/with-boundary-ints" 14 15 0 #[intV 0, intV 1, intV (-1), intV maxInt257, intV (maxInt257 - 1), intV minInt257, intV (minInt257 + 1), intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11],

    -- [B2] underflow paths.
    mkCase "err/underflow/empty" 0 0 0 #[],
    mkCase "err/underflow/one-item" 1 0 0 #[intV 1],
    mkCase "err/underflow/x-greater-than-depth" 5 1 0 #[intV 1, intV 2, intV 3, intV 4],
    mkCase "err/underflow/z-greater-than-depth" 0 0 4 #[intV 11, intV 22],
    mkCase "err/underflow/z-greater-than-depth-boundary" 1 1 8 #[intV 1, intV 2, intV 3, intV 4],


    -- [B7][B8][B9] decode behavior in oracle payloads.
    mkCaseCode "ok/decode/xcpuxc-raw" #[] (xcpuxcCode 2 7 9),
    mkCaseCode "ok/decode/neighbor-xchg3" #[] (xchg3Code 3 4 5),
    mkCaseCode "ok/decode/neighbor-xc2pu" #[] (xc2puCode 1 2 3),
    mkCaseCode "ok/decode/neighbor-xcpu2" #[] (xcpu2Code 4 5 6),
    mkCaseCode "err/decode/truncated8" #[] trunc8Code,
    mkCaseCode "err/decode/truncated15" #[] trunc15Code,
    mkCaseCode "err/decode/truncated23" #[] trunc23Code,

    -- [B10] gas exactness.
    mkCase "ok/gas/exact" 0 0 0 #[intV 11, intV 22] (program := #[.pushInt (.num xcpuxcGasExact), .tonEnvOp .setGasLimit, .xcpuxc 0 0 0])
      (oracleGasLimitsExact xcpuxcGasExact),
    mkCase "err/gas/exact-minus-one" 0 0 0 #[intV 11, intV 22] (program := #[.pushInt (.num xcpuxcGasExactMinusOne), .tonEnvOp .setGasLimit, .xcpuxc 0 0 0])
      (oracleGasLimitsExactMinusOne xcpuxcGasExactMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xcpuxcId
      count := 500
      gen := genXcpuxcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCPUXC
