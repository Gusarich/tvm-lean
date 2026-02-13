import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.BLKSWAP

/-
INSTRUCTION: BLKSWAP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success path: `st.stack.size >= x + y`.
   - For `x`, `y` in `1..16`, top block of `x + y` items is rotated so:
     `front := st.stack.take (n - total)`, `below := st.stack.extract (n - total) (n - y)`,
     `top := st.stack.extract (n - y) n`, final `front ++ top ++ below`.
   - No type checks in this path.
2. [B2] Runtime error path: stack underflow.
   - Throws `.stkUnd` whenever `x + y > st.stack.size`.
3. [B3] Assembler valid range path.
   - `.blkSwap x y` is only legal for `1 ≤ x ≤ 16`, `1 ≤ y ≤ 16`.
   - Encodes as fixed 16-bit `0x55` + `((x - 1) << 4) + (y - 1)`.
4. [B4] Assembler invalid-range path.
   - `x = 0` / `x > 16` and `y = 0` / `y > 16` must raise `.rangeChk`.
5. [B5] Decoder boundary path.
   - Exact decode for 16-bit prefixes `0x55xx` must yield `.blkSwap (((args>>4)&15)+1) (((args)&15)+1)`.
   - decode of `0x55ff` must return `(16, 16)` pair.
6. [B6] Decoder non-match path.
   - Neighboring opcodes such as `0x54...` and `0x56..` are decodable as different instructions.
7. [B7] Decoder truncation path.
   - 8-bit and 15-bit truncated encodings should decode as `invOpcode`.
8. [B8] Gas accounting boundary path.
   - No size-dependent gas in this instruction; fixed cost is `computeExactGasBudget`.
   - Exact-budget run must succeed, exact-minus-one must fail with out-of-gas.

TOTAL BRANCHES: 8

Branch coverage mapping for this suite:
- [B1] Runtime success rotation on valid depth.
- [B2] Runtime underflow.
- [B3] Assembler valid-parameter encoding.
- [B4] Assembler range error (`x`/`y` out of [1,16]).
- [B5] Decoder exact 16-bit `BLKSWAP`.
- [B6] Decoder neighbor-opcode non-match behavior.
- [B7] Decoder truncated-prefix rejection.
- [B8] Gas exact / exact-minus-one boundary.

No variable gas penalty category: only base fixed gas for this instruction.
-/

private def blkswapId : InstrId := { name := "BLKSWAP" }

private def blkSwapMinRaw : Cell :=
  Cell.mkOrdinary (natToBits 0x5500 16) #[]

private def blkSwapMaxRaw : Cell :=
  Cell.mkOrdinary (natToBits 0x55ff 16) #[]

private def blkSwapRawXchg3 : Cell :=
  Cell.mkOrdinary (natToBits 0x540123 24) #[]

private def blkSwapRawPush : Cell :=
  Cell.mkOrdinary (natToBits 0x5600 16) #[]

private def blkSwapRawTrunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0x55 8) #[]

private def blkSwapRawTrunc15 : Cell :=
  Cell.mkOrdinary (natToBits (0x550f >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (x : Nat)
    (y : Nat)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkswapId
    program := #[.blkSwap x y]
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
    instr := blkswapId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkswapId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def blkswapGasExact : Int :=
  computeExactGasBudget (.blkSwap 1 1)

private def blkswapGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.blkSwap 1 1)

private def runBlkswapDirect (x : Nat) (y : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackBlkSwap (.blkSwap x y) stack

private def expectedBlkSwap (x y : Nat) (stack : Array Value) : Array Value :=
  let n : Nat := stack.size
  let total : Nat := x + y
  let front : Array Value := stack.take (n - total)
  let below : Array Value := stack.extract (n - total) (n - y)
  let top : Array Value := stack.extract (n - y) n
  front ++ top ++ below

private def genValuePool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 17,
    intV (-17),
    intV maxInt257,
    intV minInt257,
    .null,
    .cell Cell.empty,
    .slice (Slice.ofCell Cell.empty),
    .builder Builder.empty,
    .tuple #[],
    .cont (.quit 0)
  ]

private def pickValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (genValuePool.size - 1)
  (genValuePool[idx]!, rng1)

private def genStack (depth : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in [0:depth] do
      let (v, rng') := pickValue rng
      out := out.push v
      rng := rng'
    return (out, rng)

private def intRangeStack (n : Nat) : Array Value :=
  (Array.range n).map fun i => intV (Int.ofNat i)

private def pickBoundaryArg (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 11
  if mode ≤ 4 then
    (1, rng1)
  else if mode ≤ 8 then
    (16, rng1)
  else
    randNat rng1 2 15

private def pickArbitraryArg (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 7
  if mode = 0 then
    (1, rng1)
  else if mode = 1 then
    (16, rng1)
  else
    randNat rng1 2 15

private def genBlkSwapFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[] 1 1, rng1)
    else if shape = 1 then
      let (x, rng2) := pickBoundaryArg rng1
      let (y, rng3) := pickBoundaryArg rng2
      (mkCase "fuzz/underflow/singleton" #[intV 1] x y, rng3)
    else if shape = 2 then
      let (x, rng2) := pickArbitraryArg rng1
      let (y, rng3) := pickArbitraryArg rng2
      (mkCase "fuzz/underflow/depth-boundary-1" (#[intV 11, intV 22]) x y, rng3)
    else if shape = 3 then
      let (x, rng2) := pickArbitraryArg rng1
      let (y, rng3) := pickArbitraryArg rng2
      let need : Nat := x + y
      let (stack, rng4) := genStack (need - 1) rng3
      (mkCase "fuzz/underflow/randomized" stack x y, rng4)
    else if shape = 4 then
      let (x, rng2) := pickBoundaryArg rng1
      let (y, rng3) := pickBoundaryArg rng2
      let (stack, rng4) := genStack (x + y) rng3
      (mkCase "fuzz/success/boundary" stack x y, rng4)
    else if shape = 5 then
      let (x, rng2) := pickArbitraryArg rng1
      let (y, rng3) := pickArbitraryArg rng2
      let (stack, rng4) := genStack (x + y + 4) rng3
      (mkCase "fuzz/success/randomized" stack x y, rng4)
    else if shape = 6 then
      let (x, rng2) := pickBoundaryArg rng1
      let (y, rng3) := pickBoundaryArg rng2
      let (stack, rng4) := genStack 32 rng3
      (mkCase "fuzz/success/deep-mix" stack x y, rng4)
    else if shape = 7 then
      let (x, rng2) := pickBoundaryArg rng1
      let (y, rng3) := pickBoundaryArg rng2
      let (stack, rng4) := genStack (x + y) rng3
      (mkCaseWithProgram
        "fuzz/success/mix-program"
        stack
        #[.blkSwap x y]
        {}, rng4)
    else if shape = 8 then
      (mkCase "fuzz/asm/bad-x-zero" #[] 0 1, rng1)
    else if shape = 9 then
      (mkCase "fuzz/asm/bad-x-sixteen-plus" #[] 17 1, rng1)
    else if shape = 10 then
      (mkCase "fuzz/asm/bad-y-zero" #[] 1 0, rng1)
    else if shape = 11 then
      (mkCase "fuzz/asm/bad-y-sixteen-plus" #[] 1 17, rng1)
    else if shape = 12 then
      let (tag, rng3) := randNat rng1 0 99
      if tag < 50 then
        (mkCaseCode (s!"fuzz/decode/truncated-8/{tag}") #[] blkSwapRawTrunc8, rng3)
      else
        (mkCaseCode (s!"fuzz/decode/truncated-15/{tag}") #[] blkSwapRawTrunc15, rng3)
    else if shape = 13 then
      (mkCaseCode "fuzz/decode/neighbor-xchg3" #[intV 11, intV 22, intV 33] blkSwapRawXchg3, rng1)
    else if shape = 14 then
      let (stack, rng3) := genStack 3 rng1
      (mkCaseCode "fuzz/decode/neighbor-push" stack blkSwapRawPush, rng3)
    else
      (mkCaseWithProgram
        "fuzz/gas/exact"
        (#[intV 1, intV 2])
        #[.pushInt (.num blkswapGasExact), .tonEnvOp .setGasLimit, .blkSwap 1 1]
        (oracleGasLimitsExact blkswapGasExact)
      , rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := blkswapId
  unit := #[
    { name := "unit/decode/blk-swap-min-decodes"
      run := do
        match decodeCp0WithBits (Slice.ofCell blkSwapMinRaw) with
        | .error e =>
            throw (IO.userError s!"decode BLKSWAP min failed: {e}")
        | .ok (instr, bits, _) =>
            if instr != .blkSwap 1 1 then
              throw (IO.userError s!"decode min expected blkSwap 1 1, got {reprStr instr}")
            if bits ≠ 16 then
              throw (IO.userError s!"decode min expected 16 bits, got {bits}")
            pure () }
    ,
    { name := "unit/decode/blk-swap-max-decodes"
      run := do
        match decodeCp0WithBits (Slice.ofCell blkSwapMaxRaw) with
        | .error e =>
            throw (IO.userError s!"decode BLKSWAP max failed: {e}")
        | .ok (instr, bits, _) =>
            if instr != .blkSwap 16 16 then
              throw (IO.userError s!"decode max expected blkSwap 16 16, got {reprStr instr}")
            if bits ≠ 16 then
              throw (IO.userError s!"decode max expected 16 bits, got {bits}")
            pure () }
    ,
    { name := "unit/decode/asm-roundtrip"
      run := do
        let code ←
          match assembleCp0 [(.blkSwap 16 4)] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble blkSwap failed: {e}")
        match decodeCp0WithBits (Slice.ofCell code) with
        | .error e => throw (IO.userError s!"decode roundtrip failed: {e}")
        | .ok (decoded, bits, _) =>
            let code' ←
              match assembleCp0 [decoded] with
              | .ok c => pure c
              | .error e => throw (IO.userError s!"re-assemble decoded blkSwap failed: {e}")
            if bits ≠ 16 then
              throw (IO.userError s!"roundtrip expected 16 bits, got {bits}")
            if code != code' then
              throw (IO.userError "roundtrip mismatch for BLKSWAP")
            pure () }
    ,
    { name := "unit/encode/asm-range-valid"
      run := do
        match assembleCp0 [(.blkSwap 16 16)] with
        | .ok c =>
            if c != blkSwapMaxRaw then
              throw (IO.userError "BLKSWAP(16,16) encoding changed")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"BLKSWAP(16,16) assembly failed: {e}") }
    ,
    { name := "unit/encode/asm-range-reject"
      run := do
        match assembleCp0 [(.blkSwap 0 1)] with
        | .ok _ => throw (IO.userError "BLKSWAP(0,1) unexpectedly assembled")
        | .error _ => pure ()
        match assembleCp0 [(.blkSwap 1 17)] with
        | .ok _ => throw (IO.userError "BLKSWAP(1,17) unexpectedly assembled")
        | .error _ => pure () }
    ,
    { name := "unit/runtime/rotation-small"
      run := do
        expectOkStack "rotate-1-1" (runBlkswapDirect 1 1 #[intV 7, intV 9])
          (expectedBlkSwap 1 1 #[intV 7, intV 9])
        expectOkStack "rotate-2-1" (runBlkswapDirect 2 1 #[intV 1, intV 2, intV 3, intV 4, intV 5])
          (expectedBlkSwap 2 1 #[intV 1, intV 2, intV 3, intV 4, intV 5])
        expectOkStack "rotate-max-16" (runBlkswapDirect 16 16 (intRangeStack 32))
          (expectedBlkSwap 16 16 (intRangeStack 32)) }
    ,
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "underflow-empty" (runBlkswapDirect 4 5 #[]) .stkUnd
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "ok/min-depth-1-1-size2" #[intV 11, intV 22] 1 1
    -- [B1, B3]
    , mkCase "ok/min-depth-1-1-size5" #[intV 1, intV 2, intV 3, intV 4, intV 5] 1 1
    -- [B1]
    , mkCase "ok/adjacent-top-1-2" #[intV 10, intV 20, intV 30, intV 40] 1 2
    -- [B1]
    , mkCase "ok/adjacent-top-2-1" #[intV 11, intV 22, intV 33, intV 44, intV 55] 2 1
    -- [B1]
    , mkCase "ok/deep-3-4" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7] 3 4
    -- [B1]
    , mkCase "ok/deep-5-1" #[intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13] 5 1
    -- [B1]
    , mkCase "ok/deep-8-2" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10] 8 2
    -- [B1]
    , mkCase "ok/boundary-stack-with-max-args" (intRangeStack 32) 16 16
    -- [B1, B4]
    , mkCase "ok/max-y16" (intRangeStack 17) 1 16
    -- [B1, B4]
    , mkCase "ok/max-x16" (intRangeStack 17) 16 1
    -- [B1, B4]
    , mkCase "ok/max-args" (intRangeStack 32) 16 16
    -- [B5]
    , mkCase "ok/mixed-types" #[
        .cell Cell.empty,
        .null,
        .builder Builder.empty,
        .slice (Slice.ofCell Cell.empty),
        .tuple #[],
        intV 11,
        .cont (.quit 0)
      ] 3 2
    -- [B5]
    , mkCase "ok/mixed-types-heavy" #[
        intV (-1),
        .builder Builder.empty,
        intV 7,
        .null,
        .cell Cell.empty,
        intV 99,
        .slice (Slice.ofCell Cell.empty),
        .tuple #[],
        .cont (.quit 0),
        intV 5
      ] 2 4
    -- [B2]
    , mkCase "err/underflow/empty" #[] 1 1
    -- [B2]
    , mkCase "err/underflow/singleton" #[intV 42] 1 1
    -- [B2]
    , mkCase "err/underflow/depth-one-less" #[intV 1, intV 2] 2 1
    -- [B2]
    , mkCase "err/underflow/boundary" (intRangeStack 31) 16 16
    -- [B2]
    , mkCase "err/underflow/random-stack" (intRangeStack 3) 4 16
    -- [B3]
    , mkCase "ok/asm/min-args" (intRangeStack 2) 1 1
    -- [B3]
    , mkCase "ok/asm/max-args" (intRangeStack 32) 16 16
    -- [B4]
    , mkCase "err/asm/bad-x-zero" #[] 0 1
    -- [B4]
    , mkCase "err/asm/bad-x-over" #[] 17 1
    -- [B4]
    , mkCase "err/asm/bad-y-zero" #[] 1 0
    -- [B4]
    , mkCase "err/asm/bad-y-over" #[] 1 17
    -- [B5]
    , mkCaseCode "ok/decode/min" (intRangeStack 2) blkSwapMinRaw
    -- [B5]
    , mkCaseCode "ok/decode/max" (intRangeStack 32) blkSwapMaxRaw
    -- [B6]
    , mkCaseCode "ok/decode/neighbor-xchg3" (#[intV 1, intV 2, intV 3]) blkSwapRawXchg3
    -- [B6]
    , mkCaseCode "ok/decode/neighbor-push" (intRangeStack 3) blkSwapRawPush
    -- [B7]
    , mkCaseCode "err/decode/trunc8" #[] blkSwapRawTrunc8
    -- [B7]
    , mkCaseCode "err/decode/trunc15" #[] blkSwapRawTrunc15
    -- [B8]
    , mkCaseWithProgram "gas/exact" (intRangeStack 3) #[
        .pushInt (.num blkswapGasExact),
        .tonEnvOp .setGasLimit,
        .blkSwap 1 1
      ] (oracleGasLimitsExact blkswapGasExact)
    -- [B8]
    , mkCaseWithProgram "gas/exact-minus-one" (intRangeStack 3) #[
        .pushInt (.num blkswapGasExactMinusOne),
        .tonEnvOp .setGasLimit,
        .blkSwap 1 1
      ] (oracleGasLimitsExactMinusOne blkswapGasExact)
  ]
  fuzz := #[
    { seed := 2026021601
      count := 500
      gen := genBlkSwapFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.BLKSWAP
