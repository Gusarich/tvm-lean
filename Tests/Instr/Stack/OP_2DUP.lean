import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.OP_2DUP

/-
INSTRUCTION: 2DUP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success on exact or larger stack: with size >= 2, `execInstrStackTwoDup`
   duplicates stack position 1 and then position 1 again after the first push.
   For `[a, b]` this yields `[a, b, a, b]`; for `[a, b, c, d]` it yields `[a, b, c, d, c, d]`.
2. [B2] Runtime depth-boundary: the `size == 2` case is successful and is the
   smallest valid shape.
3. [B3] Runtime deep-stack shape preservation: values below the top pair are unchanged
   and only two elements are appended.
4. [B4] Value-kind behavior: integers, null, cells, slices, builders, tuples, and
   continuations are all duplicated without type checks.
5. [B5] Assembler encoding: `.twoDup` has no arguments and must encode to fixed
   single-byte opcode `0x5c`; there is no valid argument space to validate or reject.
6. [B6] Decoder behavior and aliasing: `0x5c` decodes to `.twoDup`, while neighboring
   fixed-byte opcodes decode to different instructions (`0x5b` → `.drop2`, `0x5d` → `.twoOver`).
7. [B7] Decoder boundary and exact-width behavior: decode consumes exactly 8 bits for
   `0x5c`; truncated bitstreams must raise `invOpcode`.
8. [B8] Gas accounting: no variable penalty is introduced by this op; base fixed gas is
   checked with exact-gas success and exact-minus-one failure.

MISSING CATEGORIES:
- No integer overflow/underflow arithmetic branches apply.
- No dynamic gas modifiers exist for this opcode family.

TOTAL BRANCHES: 8
Each oracle test below is tagged with the branch(es) it covers.
-/

private def twoDupId : InstrId := { name := "2DUP" }

private def twoDupInstr : Instr := .twoDup

private def noGas : OracleGasLimits := {}

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[]
private def cellB : Cell := Cell.mkOrdinary (natToBits 0x3c 6) #[]

private def sliceA : Slice := mkSliceFromBits (natToBits 0xa5 8)
private def sliceB : Slice := mkSliceFromBits (natToBits 0x55 8)

private def twoDupRaw8 : Cell := Cell.mkOrdinary (natToBits 0x5c 8) #[]
private def twoDupDrop2Raw8 : Cell := Cell.mkOrdinary (natToBits 0x5b 8) #[]
private def twoDupOverRaw8 : Cell := Cell.mkOrdinary (natToBits 0x5d 8) #[]
private def twoDupTruncatedRaw7 : Cell := Cell.mkOrdinary (natToBits 0x5c 7) #[]
private def invalidFFRaw : Cell := Cell.mkOrdinary (natToBits 0xff 8) #[]

private def twoDupExactGas : Int := computeExactGasBudget twoDupInstr

private def twoDupExactGasMinusOne : Int := computeExactGasBudgetMinusOne twoDupInstr

private def twoDupGasExact : OracleGasLimits := oracleGasLimitsExact twoDupExactGas

private def twoDupGasExactMinusOne : OracleGasLimits := oracleGasLimitsExact twoDupExactGasMinusOne

private def mkTwoDupCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[twoDupInstr])
    (gasLimits : OracleGasLimits := noGas)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := twoDupId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkTwoDupCodeCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := noGas)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := twoDupId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runTwoDupDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackTwoDup twoDupInstr stack

private def runTwoDupDirectWithNext (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackTwoDup .add (VM.push (intV 777)) stack

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
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} / {bits}")

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def twoDupNoisePool : Array Value :=
  #[
    .null,
    .cell cellA,
    .cell cellB,
    .builder Builder.empty,
    .slice sliceA,
    .slice sliceB,
    .tuple #[],
    q0,
    intV 0,
    intV 1,
    intV (-1),
    intV maxInt257,
    intV minInt257
  ]

private def genNoiseStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool twoDupNoisePool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def genTwoDupFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (base, rng2) : OracleCase × StdGen :=
    if shape = 0 then
      let (a, rng2) := pickInt257Boundary rng1
      let (b, rng3) := pickInt257Boundary rng2
      (mkTwoDupCase "fuzz/ok/boundary-2" #[intV a, intV b], rng3)
    else if shape = 1 then
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      (mkTwoDupCase "fuzz/ok/random-2" #[intV a, intV b], rng3)
    else if shape = 2 then
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      let (c, rng4) := pickFromPool twoDupNoisePool rng3
      (mkTwoDupCase "fuzz/ok/non-int-top-pair" #[c, intV a, intV b], rng4)
    else if shape = 3 then
      let (a, rng2) := pickInt257Boundary rng1
      let (b, rng3) := pickInt257Boundary rng2
      let (c, rng4) := pickInt257Boundary rng3
      let (d, rng5) := pickInt257Boundary rng4
      let (e, rng6) := pickFromPool twoDupNoisePool rng5
      (mkTwoDupCase "fuzz/ok/deep4" #[intV a, intV b, intV c, intV d, e], rng6)
    else if shape = 4 then
      let (below, rng3) := genNoiseStack 4 rng1
      let (a, rng4) := pickSigned257ish rng3
      let (b, rng5) := pickSigned257ish rng4
      (mkTwoDupCase "fuzz/ok/deep-noise" (below ++ #[intV a, intV b]), rng5)
    else if shape = 5 then
      let (below, rng2) := genNoiseStack 7 rng1
      (mkTwoDupCase "fuzz/ok/deep-7" below, rng2)
    else if shape = 6 then
      (mkTwoDupCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (a, rng2) := pickSigned257ish rng1
      (mkTwoDupCase "fuzz/err/underflow-one" #[intV a], rng2)
    else if shape = 8 then
      (mkTwoDupCase "fuzz/err/underflow-one-null" #[.null], rng1)
    else if shape = 9 then
      (mkTwoDupCase "fuzz/err/underflow-one-cell" #[.cell cellA], rng1)
    else if shape = 10 then
      (mkTwoDupCase "fuzz/err/underflow-one-builder" #[.builder Builder.empty], rng1)
    else if shape = 11 then
      (mkTwoDupCase "fuzz/gas/exact-success" #[intV 5, intV 6] (gasLimits := twoDupGasExact), rng1)
    else if shape = 12 then
      (mkTwoDupCase "fuzz/gas/exact-minus-one-out-of-gas"
        #[intV 5, intV 6] (gasLimits := twoDupGasExactMinusOne), rng1)
    else if shape = 13 then
      let (a, rng2) := pickInt257Boundary rng1
      let (b, rng3) := pickInt257Boundary rng2
      let (c, rng4) := pickFromPool twoDupNoisePool rng3
      let (d, rng5) := pickFromPool twoDupNoisePool rng4
      (mkTwoDupCase "fuzz/ok/deep-boundary"
        #[intV a, intV b, c, d], rng5)
    else
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      (mkTwoDupCase "fuzz/ok/deep-4-boundary"
        #[intV a, intV b], rng3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ base with name := s!"{base.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := twoDupId
  unit := #[
    { name := "unit/runtime/dispatch/exact/size-2"
      run := do
        expectOkStack "unit/runtime/dispatch/size-2" (runTwoDupDirect #[intV 1, intV 2]) #[intV 1, intV 2, intV 1, intV 2]
        expectOkStack "unit/runtime/dispatch/size-3" (runTwoDupDirect #[intV 9, intV 8, intV 7]) #[intV 9, intV 8, intV 7, intV 8, intV 7]
        expectOkStack "unit/runtime/dispatch/size-4"
          (runTwoDupDirect #[intV 1, intV 2, intV 3, intV 4]) #[intV 1, intV 2, intV 3, intV 4, intV 3, intV 4] }
    ,
    { name := "unit/runtime/dispatch/underflow-small"
      run := do
        expectErr "unit/runtime/dispatch/underflow-empty" (runTwoDupDirect #[]) .stkUnd
        expectErr "unit/runtime/dispatch/underflow-size-1" (runTwoDupDirect #[intV 1]) .stkUnd }
    ,
    { name := "unit/runtime/dispatch/fallback"
      run := do
        expectOkStack "unit/runtime/dispatch/fallback" (runTwoDupDirectWithNext #[]) #[intV 777] }
    ,
    { name := "unit/opcode/asm-encode-and-decode"
      run := do
        let assembled ←
          match assembleCp0 [twoDupInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/opcode/asm-encode: assemble failed: {e}")
        if assembled.bits != natToBits 0x5c 8 then
          throw (IO.userError s!"unit/opcode/asm-encode: expected 0x5c, got {reprStr assembled.bits}")
        let s0 : Slice := Slice.ofCell assembled
        let _ ← expectDecodeStep "unit/opcode/decode" s0 .twoDup 8
        let neigh : Slice := mkSliceFromBits (natToBits 0x5b 8 ++ natToBits 0x5c 8 ++ natToBits 0x5d 8)
        let s1 ← expectDecodeStep "unit/opcode/decode-neighbor-1" neigh .drop2 8
        let s2 ← expectDecodeStep "unit/opcode/decode-neighbor-2" s1 twoDupInstr 8
        let _ ← expectDecodeStep "unit/opcode/decode-neighbor-3" s2 .twoOver 8
        expectDecodeErr "unit/opcode/decode/truncated-7" twoDupTruncatedRaw7 .invOpcode
        expectDecodeErr "unit/opcode/decode/invalid-ff" invalidFFRaw .invOpcode
    }
  ]
  oracle := #[
    -- [B1]
    mkTwoDupCase "ok/size2/ascending" #[intV 1, intV 2],
    -- [B1]
    mkTwoDupCase "ok/size2/descending" #[intV 9, intV 4],
    -- [B1]
    mkTwoDupCase "ok/size2/boundaries" #[intV minInt257, intV maxInt257],
    -- [B1]
    mkTwoDupCase "ok/size2/boundary-shift" #[intV maxInt257, intV (maxInt257 - 1)],
    -- [B1]
    mkTwoDupCase "ok/size2/signed-mix" #[intV (-7), intV 42],
    -- [B1]
    mkTwoDupCase "ok/size2/zero" #[intV 0, intV 0],
    -- [B1,B4]
    mkTwoDupCase "ok/size2/null-cell" #[.null, .cell cellA],
    -- [B1,B4]
    mkTwoDupCase "ok/size2/slice-builder" #[.slice sliceA, .builder Builder.empty],
    -- [B1,B4]
    mkTwoDupCase "ok/size2/tuple-cont" #[.tuple #[], q0],
    -- [B1,B4]
    mkTwoDupCase "ok/size2/cell-slice" #[.cell cellB, .slice sliceB],
    -- [B2]
    mkTwoDupCase "err/underflow/empty" #[],
    -- [B2]
    mkTwoDupCase "err/underflow/one-int" #[intV 1],
    -- [B2]
    mkTwoDupCase "err/underflow/one-null" #[.null],
    -- [B2]
    mkTwoDupCase "err/underflow/one-cell" #[.cell cellA],
    -- [B2]
    mkTwoDupCase "err/underflow/one-builder" #[.builder Builder.empty],
    -- [B3]
    mkTwoDupCase "ok/size3/deeper-stack-1" #[intV 7, intV 8, intV 9],
    -- [B3]
    mkTwoDupCase "ok/size3/deeper-stack-2" #[.null, intV 11, intV 22],
    -- [B3]
    mkTwoDupCase "ok/size4/deeper-stack" #[intV 1, .null, .cell cellA, .builder Builder.empty],
    -- [B3]
    mkTwoDupCase "ok/size5/deeper-stack-noise" #[intV 1, intV 2, intV 3, .slice sliceA, intV 5],
    -- [B3,B4]
    mkTwoDupCase "ok/size6/deeper-stack-mixed" #[.cell cellA, .slice sliceA, intV (-1), .builder Builder.empty, q0, intV 55],
    -- [B1,B4]
    mkTwoDupCase "ok/size2/non-int-pair-1" #[q0, .cell cellA],
    -- [B1,B4]
    mkTwoDupCase "ok/size2/non-int-pair-2" #[.builder Builder.empty, .tuple #[]],
    -- [B4]
    mkTwoDupCase "ok/size2/non-int-dup-top" #[.tuple #[], .tuple #[]],
    -- [B5]
    mkTwoDupCodeCase "ok/raw/5c-executes-twoDup" #[intV 1, intV 2] twoDupRaw8,
    -- [B6]
    mkTwoDupCodeCase "ok/raw/5b-neighbor-left-not-twoDup" #[intV 1, intV 2, intV 3, intV 4] twoDupDrop2Raw8,
    -- [B6]
    mkTwoDupCodeCase "ok/raw/5d-neighbor-right-not-twoDup" #[intV 1, intV 2, intV 3, intV 4] twoDupOverRaw8,
    -- [B8]
    mkTwoDupCase "gas/exact-success" (#[intV 5, intV 6]) #[twoDupInstr] twoDupGasExact,
    -- [B8]
    mkTwoDupCase "gas/exact-minus-one-out-of-gas" (#[intV 7, intV 8]) #[twoDupInstr] twoDupGasExactMinusOne,
    -- [B1]
    mkTwoDupCase "ok/size2/near-limits" #[intV (maxInt257 - 1), intV (minInt257 + 1)],
    -- [B1,B3]
    mkTwoDupCase "ok/size7/deep-mixed" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7],
    -- [B1,B4]
    mkTwoDupCase "ok/size4/continuation-top" #[q0, intV 11, intV 12, intV 13],
    -- [B2]
    mkTwoDupCase "err/underflow/one-cont" #[q0],
    -- [B3]
    mkTwoDupCase "ok/size8/hetero" #[intV 1, .null, intV 3, .cell cellA, .slice sliceA, q0, .builder Builder.empty, intV 9]
  ]
  fuzz := #[
    { seed := 2026021301
      count := 500
      gen := genTwoDupFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.OP_2DUP
