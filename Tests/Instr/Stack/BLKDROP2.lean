/-
INSTRUCTION: BLKDROP2

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch/match branch
   - `.blkdrop2 x y` matches and executes the BLKDROP2 body.
   - Any non-`.blkdrop2` instruction falls through to `next`.

2. [B2] Success path with `y = 0`
   - `total = x + y = x`.
   - Drops top `x` items (`bottom ++ []`), preserving lower stack prefix only.
   - Valid for small and boundary values such as `x = 1` and `x = 15`.

3. [B3] Success path with `y > 0`
   - `total = x + y`.
   - Drops `x` items below the top `y` elements:
     result is `bottom ++ top`, where
     `bottom := stack.take (size - total)` and
     `top := stack.extract (size - total + x) size`.
   - Verified with varied `x`/`y` and mixed-value stacks.

4. [B4] Success edge: exact-size frame (`x + y = stack.size`)
   - `keepBottom = 0` and only the selected slice/keep rule applies.
   - Preserves exact boundary behavior at full-frame drops.

5. [B5] Runtime error branch (`stkUnd`)
   - Underflow when `x + y > stack.size`.
   - `stkUnd` is raised immediately without partial mutation.

6. [B6] Assembler/decoder round-trip for valid boundaries
   - Canonical minimum/maximum encodings:
     `0x6c10` (`x=1,y=0`) and `0x6cff` (`x=15,y=15`) both decode/encode correctly.

7. [B7] Decode boundaries and aliasing/invalid-prefix behavior
   - Encodings outside fixed-range `0x6c10..0x6cff` (for example `0x6c0f`) must fail decode as `.invOpcode`.
   - Truncated prefixes `8`/`15` bits also fail decode.

8. [B8] Assembler encoding validity and rejection
   - `x = 0` is rejected by range-check because packed args must satisfy `args >= 0x10`.
   - `x > 15` and `y > 15` are rejected as `.rangeChk`.
   - No variable gas penalty; the opcode has fixed gas.

9. [B9] Gas edge case: exact budget
   - A stack frame with exact computed budget should succeed.

10. [B10] Gas edge case: exact budget minus one
    - One unit short of computed budget should fail with out-of-gas behavior.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn] to the branch(es) it covers.
-/

import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.BLKDROP2

private def blkdrop2Id : InstrId := { name := "BLKDROP2" }
private def dispatchSentinel : Int := 27183

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x6c 8) #[]
private def sliceA : Slice := Slice.ofCell cellA

private def blkdrop2MinCode : Cell :=
  Cell.mkOrdinary (natToBits 0x6c10 16) #[]
private def blkdrop2MaxCode : Cell :=
  Cell.mkOrdinary (natToBits 0x6cff 16) #[]
private def blkdrop2LowNibbleCode : Cell :=
  Cell.mkOrdinary (natToBits 0x6c0f 16) #[]
private def blkdrop2Truncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0x6c 8) #[]
private def blkdrop2Truncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0x6c10 >>> 1) 15) #[]

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    pure out

private def expectDecodeBlkdrop2
    (label : String)
    (code : Cell)
    (x y : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .blkdrop2 x y then
        throw (IO.userError s!"{label}: expected BLKDROP2 {x},{y}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected exhausted bits, got bits={rest.bitsRemaining}, refs={rest.refsRemaining}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected BLKDROP2 decode success, got {e}")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instruction {reprStr instr} ({bits} bits)")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def runBlkdrop2Direct (x y : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowBlkdrop2 (.blkdrop2 x y) stack

private def runBlkdrop2DirectFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowBlkdrop2 .add (VM.push (intV dispatchSentinel)) stack

private def mkCase
    (name : String)
    (x y : Nat)
    (stack : Array Value)
    (program : Array Instr := #[.blkdrop2 x y])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkdrop2Id
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
    instr := blkdrop2Id
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def blkdrop2ExactGas : Int := computeExactGasBudget (.blkdrop2 1 0)
private def blkdrop2ExactGasMinusOne : Int := computeExactGasBudgetMinusOne (.blkdrop2 1 0)

private def oracleCases : Array OracleCase := #[
  -- [B2] y = 0, top-drop-only behavior.
  mkCase "ok/top-drop/min/x1" 1 0 #[intV 1, intV 2, intV 3],
  mkCase "ok/top-drop/x2" 2 0 #[.null, intV 4, .cell cellA],
  mkCase "ok/top-drop/x3-with-mix" 3 0 #[intV 10, .slice sliceA, intV 20, .builder Builder.empty],
  mkCase "ok/top-drop/x15-empty-top" 15 0 (intStackAsc 15),
  mkCase "ok/top-drop/x15-extra-room" 15 0 (intStackAsc 17),

  -- [B2] Additional y = 0 coverage with mixed operands.
  mkCase "ok/top-drop/x1-y0-mixed"
    1 0 #[.tuple #[], intV 5, .builder Builder.empty, .cell cellA],
  mkCase "ok/top-drop/x2-y0-boundary" 2 0 (intStackAsc 5),
  mkCase "ok/top-drop/x4-noise-stack" 4 0 #[intV (-1), .slice sliceA, intV 7, intV 8, .cell cellA],

  -- [B3] y > 0 drop-middle behavior with preserved top segment.
  mkCase "ok/middle-drop/x1-y1" 1 1 #[intV 10, intV 20, intV 30],
  mkCase "ok/middle-drop/x2-y3-small" 2 3 #[intV 1, .cell cellA, intV 2, intV 3, intV 4, intV 5, intV 6],
  mkCase "ok/middle-drop/x3-y2" 3 2 #[.null, intV 11, .slice sliceA, intV 22, .builder Builder.empty, intV 33, intV 44],
  mkCase "ok/middle-drop/x1-y15" 1 15 (intStackAsc 16),
  mkCase "ok/middle-drop/x15-y1" 15 1 (intStackAsc 20),
  mkCase "ok/middle-drop/x15-y15" 15 15 (intStackAsc 36),
  mkCase "ok/middle-drop/x10-y12" 10 12 (intStackAsc 25),

  -- [B4] Exact-frame-success boundary tests.
  mkCase "ok/boundary/exact-top-drop-x4" 4 0 (intStackAsc 4),
  mkCase "ok/boundary/exact-middle-x2-y5" 2 5 (intStackAsc 7),
  mkCase "ok/boundary/exact-max-x15-y15" 15 15 (intStackAsc 30),

  -- [B5] Underflow (`stkUnd`) branch.
  mkCase "err/underflow/empty-x1-y0" 1 0 #[],
  mkCase "err/underflow/empty-x1-y1" 1 1 #[],
  mkCase "err/underflow/x2-y0-size1" 2 0 (intStackAsc 1),
  mkCase "err/underflow/x4-y2-size5" 4 2 (intStackAsc 5),
  mkCase "err/underflow/x8-y0-size7" 8 0 (intStackAsc 7),
  mkCase "err/underflow/x15-y15-size20" 15 15 (intStackAsc 20),
  mkCase "err/underflow/x3-y3-size2" 3 3 (intStackAsc 2),
  mkCase "err/underflow/x5-y1-size3" 5 1 (intStackAsc 3),

  -- [B6] Decode/encode boundary coverage for canonical min/max opcodes.
  mkCaseCode "ok/decode/raw-min" (intStackAsc 3) blkdrop2MinCode,
  mkCaseCode "ok/decode/raw-max" (intStackAsc 35) blkdrop2MaxCode,

  -- [B7] Decode invalid boundaries and truncated prefixes.
  mkCaseCode "err/decode/raw-low-nibble" #[] blkdrop2LowNibbleCode,
  mkCaseCode "err/decode/truncated-8" #[] blkdrop2Truncated8Code,
  mkCaseCode "err/decode/truncated-15" #[] blkdrop2Truncated15Code,

  -- [B9] Exact gas budget success and [B10] exact-minus-one out-of-gas.
  mkCase "gas/exact-cost-succeeds" 1 0 (intStackAsc 3)
    #[.blkdrop2 1 0]
    { gasLimit := blkdrop2ExactGas
      gasMax := blkdrop2ExactGas
      gasCredit := 0 },
  mkCase "gas/exact-minus-one-out-of-gas" 1 0 (intStackAsc 3)
    #[.blkdrop2 1 0]
    { gasLimit := blkdrop2ExactGasMinusOne
      gasMax := blkdrop2ExactGasMinusOne
      gasCredit := 0 },

  -- [B8] Decoder-facing assembler boundaries via valid opcode constants.
  mkCase "ok/encode-validate-min-boundary" 1 0 (intStackAsc 6),
  mkCase "ok/encode-validate-max-boundary" 15 15 (intStackAsc 6)
]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  if pool.isEmpty then
    (default, rng)
  else
    let (idx, rng') := randNat rng 0 (pool.size - 1)
    (pool[idx]!, rng')

private def blkdrop2SuccessPairPool : Array (Nat × Nat) :=
  #[(1, 0), (2, 0), (3, 0), (1, 1), (2, 3), (3, 2), (10, 12), (15, 1), (15, 15)]

private def blkdrop2UnderPairPool : Array (Nat × Nat) :=
  #[(1, 0), (1, 1), (2, 0), (4, 2), (8, 0), (15, 15)]

private def blkdrop2NoisePool : Array (Array Value) :=
  #[
    #[],
    #[.null],
    #[intV 42],
    #[.cell cellA],
    #[.slice sliceA],
    #[.builder Builder.empty],
    #[.tuple #[]]
  ]

private def blkdrop2DecodeCasePool : Array (String × Cell) :=
  #[
    ("fuzz/decode/ok-min", blkdrop2MinCode),
    ("fuzz/decode/ok-max", blkdrop2MaxCode),
    ("fuzz/decode/err-low-nibble", blkdrop2LowNibbleCode),
    ("fuzz/decode/err-trunc8", blkdrop2Truncated8Code),
    ("fuzz/decode/err-trunc15", blkdrop2Truncated15Code)
  ]

private def genBlkdrop2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (tag, rng2) := randNat rng1 0 999_999
  let (case0, rng3) :=
    if shape < 7 then
      let (pair, rng) := pickFromPool blkdrop2SuccessPairPool rng2
      let (extra, rng2) := randNat rng 0 4
      let (noise, rng3) := pickFromPool blkdrop2NoisePool rng2
      let total : Nat := pair.1 + pair.2
      let stack := (intStackAsc (total + extra)) ++ noise
      (mkCase s!"fuzz/ok/x{pair.1}-y{pair.2}-total{total}" pair.1 pair.2 stack, rng3)
    else if shape < 11 then
      let (pair, rng) := pickFromPool blkdrop2UnderPairPool rng2
      let total : Nat := pair.1 + pair.2
      let (shortfall, rng2) := if total > 0 then randNat rng 1 total else (1, rng)
      let stack := intStackAsc (total - shortfall)
      let (noise, rng3) := pickFromPool blkdrop2NoisePool rng2
      (mkCase s!"fuzz/underflow/x{pair.1}-y{pair.2}-total{total}" pair.1 pair.2 (stack ++ noise), rng3)
    else if shape < 12 then
      let (raw, rng) := pickFromPool blkdrop2DecodeCasePool rng2
      if raw.fst.startsWith "fuzz/decode/ok" then
        (mkCaseCode ("f" ++ raw.fst) (intStackAsc 4) raw.snd, rng)
      else
        (mkCaseCode ("f" ++ raw.fst) #[] raw.snd, rng)
    else
      let gasExact := computeExactGasBudget (.blkdrop2 1 0)
      let (exactMode, rng) := randNat rng2 0 1
      let gasLimits : OracleGasLimits :=
        if exactMode = 0 then
          { gasLimit := gasExact, gasMax := gasExact, gasCredit := 0 }
        else
          { gasLimit := gasExact - 1, gasMax := gasExact - 1, gasCredit := 0 }
      (mkCase (if exactMode = 0 then "fuzz/gas/exact" else "fuzz/gas/out-of-gas") 1 0
        (intStackAsc 3) (#[.blkdrop2 1 0]) gasLimits, rng)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := blkdrop2Id
  unit := #[
    { name := "unit/dispatch/fallback-add"
      run := do
        expectOkStack "fallback/untouched-add"
          (runBlkdrop2DirectFallback #[intV 11, intV 12, intV 13])
          #[intV 11, intV 12, intV 13, intV dispatchSentinel]
    } ,
    { name := "unit/dispatch/match"
      run := do
        expectOkStack "match/drop-top-one"
          (runBlkdrop2Direct 1 1 #[intV 1, intV 2, intV 3])
          #[intV 1, intV 3]
        expectOkStack "match/drop-top-zero"
          (runBlkdrop2Direct 3 0 #[intV 1, intV 2, intV 3, intV 4])
          #[intV 1]
        expectOkStack "match/drop-middle"
          (runBlkdrop2Direct 1 2 #[intV 10, intV 20, intV 30, intV 40])
          #[intV 10, intV 30, intV 40]
    } ,
    { name := "unit/operation/underflow"
      run := do
        expectErr "underflow/empty-x1-y1" (runBlkdrop2Direct 1 1 #[]) .stkUnd
        expectErr "underflow/short-stack" (runBlkdrop2Direct 2 2 #[intV 5]) .stkUnd
    } ,
    { name := "unit/opcode/encode-decode-boundaries"
      run := do
        let codeMin ←
          match assembleCp0 [ .blkdrop2 1 0 ] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/min failed: {e}")
        let codeMax ←
          match assembleCp0 [ .blkdrop2 15 15 ] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/max failed: {e}")
        expectDecodeBlkdrop2 "decode/min" codeMin 1 0
        expectDecodeBlkdrop2 "decode/max" codeMax 15 15
        if codeMin.bits = natToBits 0x6c10 16 then
          pure ()
        else
          throw (IO.userError s!"expected min opcode bits 0x6c10, got {reprStr codeMin.bits}")
        if codeMax.bits = natToBits 0x6cff 16 then
          pure ()
        else
          throw (IO.userError s!"expected max opcode bits 0x6cff, got {reprStr codeMax.bits}")

        match assembleCp0 [ .blkdrop2 0 1 ] with
        | .error .rangeChk => pure ()
        | .ok _ => throw (IO.userError "assemble/x0-y1: expected rangeChk, got success")
        | .error e => throw (IO.userError s!"assemble/x0-y1: expected rangeChk, got {e}")

        match assembleCp0 [ .blkdrop2 1 16 ] with
        | .error .rangeChk => pure ()
        | .ok _ => throw (IO.userError "assemble/x1-y16: expected rangeChk, got success")
        | .error e => throw (IO.userError s!"assemble/x1-y16: expected rangeChk, got {e}")

        expectDecodeErr "decode/low-nibble" blkdrop2LowNibbleCode .invOpcode
        expectDecodeErr "decode/truncated-8" blkdrop2Truncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" blkdrop2Truncated15Code .invOpcode
    } ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}")
    }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr blkdrop2Id
      count := 500
      gen := genBlkdrop2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.BLKDROP2
