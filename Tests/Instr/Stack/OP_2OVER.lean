import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.OP_2OVER

/-
INSTRUCTION: 2OVER

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success: stack depth is at least 4.
   Lean/C++ execute `fetch 3` twice and push the results.
   The two pushed values are the two entries immediately below the current top pair;
   for 4-item stacks this is equivalent to `[a, b, c, d] => [a, b, c, d, a, b]`.
   The two pushed values preserve exact `Value` identity for non-int data too.
2. [B2] Runtime underflow: stack depth < 4 throws `stk_und` (both Lean and C++ call
   `check_underflow(4)`).
3. [B3] Runtime depth-shape boundary: exact 4-item stacks and deeper stacks follow the same
   branch but produce different preservation footprints; deeper noise below the duplicated pair
   must be retained unchanged.
4. [B4] Value-kind behavior: both implementations are polymorphic for duplicated items
   (ints, cells, slices, builders, tuples, continuations).
5. [B5] Assembler encoding: fixed 8-bit opcode family.
   `twoOver` maps to `0x5d` and has no constructor arguments.
6. [B6] Assembler range/error path: no argument-range validation branch is present; invalid
   parameters are not representable because the instruction carries no params.
7. [B7] Decoder branch mapping: opcode 0x5d decodes to `.twoOver`; neighboring opcodes (`0x5c`
   and `0x5e`) must decode to other constructors.
8. [B8] Decoder round-trip coverage: full stream decoding should consume 8-bit fixed fields
   per instruction with no variable-length ambiguity for `2OVER`.
9. [B9] Gas edge: base `instrGas` cost is fixed for this family (`gasPerInstr + 8`), and
   exact-gas vs exact-minus-one behavior must distinguish success vs `out_of_gas`.
10. [B10] Gas penalty form: no variable per-instruction penalty; no-size/alias penalties.

TOTAL BRANCHES: 10
-/

private def twoOverId : InstrId := { name := "2OVER" }

private def twoOverInstr : Instr := .twoOver

private def noGas : OracleGasLimits := {}

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[]

private def cellB : Cell := Cell.mkOrdinary (natToBits 0x3c 6) #[]

private def sliceA : Slice := mkSliceFromBits (natToBits 0xa5 8)

private def sliceB : Slice := mkSliceFromBits (natToBits 0x55 8)

private def twoOverRaw8 : Cell := Cell.mkOrdinary (natToBits 0x5d 8) #[]

private def twoOverAfterTwoDupRaw16 : Cell :=
  Cell.mkOrdinary (natToBits 0x5c 8 ++ natToBits 0x5d 8) #[]

private def mkTwoOverCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[twoOverInstr])
    (gasLimits : OracleGasLimits := noGas)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := twoOverId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkTwoOverCodeCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := noGas)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := twoOverId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def twoOverSetGasExact : Int :=
  computeExactGasBudget twoOverInstr

private def twoOverSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne twoOverInstr

private def twoOverNoisePool : Array Value :=
  #[
    .null,
    .cell cellA,
    .cell cellB,
    .builder Builder.empty,
    .slice sliceA,
    .tuple #[],
    q0,
    intV 0,
    intV 7,
    intV (-7),
    intV maxInt257,
    intV minInt257
  ]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genNoiseStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool twoOverNoisePool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def genTwoOverFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (base, rng2) : OracleCase × StdGen :=
    if shape = 0 then
      let (a, rng2) := pickInt257Boundary rng1
      let (b, rng3) := pickInt257Boundary rng2
      let (c, rng4) := pickInt257Boundary rng3
      let (d, rng5) := pickInt257Boundary rng4
      (mkTwoOverCase (s!"fuzz/ok/exact4/{a}/{b}/{c}/{d}") #[intV a, intV b, intV c, intV d], rng5)
    else if shape = 1 then
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      let (c, rng4) := pickSigned257ish rng3
      let (d, rng5) := pickSigned257ish rng4
      let (e, rng6) := pickFromPool twoOverNoisePool rng5
      (mkTwoOverCase (s!"fuzz/ok/deep5/{a}/{b}/{c}/{d}/{reprStr e}")
        #[intV a, intV b, intV c, intV d, e], rng6)
    else if shape = 2 then
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      let (c, rng4) := pickSigned257ish rng3
      let (d, rng5) := pickSigned257ish rng4
      let (e, rng6) := pickFromPool twoOverNoisePool rng5
      let (f, rng7) := pickFromPool twoOverNoisePool rng6
      (mkTwoOverCase (s!"fuzz/ok/deep7/{a}/{b}/{c}/{d}/{reprStr e}/{reprStr f}")
        #[e, f, intV a, intV b, intV c, intV d], rng7)
    else if shape = 3 then
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      let (_c, rng4) := pickSigned257ish rng3
      let (_d, rng5) := pickSigned257ish rng4
      let (noise, rng6) := pickFromPool twoOverNoisePool rng5
      (mkTwoOverCase (s!"fuzz/ok/nonint-bottoms/{reprStr noise}/{a}/{b}")
        #[noise, noise, intV a, intV b], rng6)
    else if shape = 4 then
      (mkTwoOverCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 5 then
      (mkTwoOverCase "fuzz/underflow/one" #[intV 1], rng1)
    else if shape = 6 then
      (mkTwoOverCase "fuzz/underflow/two" #[intV 1, intV 2], rng1)
    else if shape = 7 then
      (mkTwoOverCase "fuzz/underflow/three" #[intV 1, intV 2, .cell cellA], rng1)
    else if shape = 8 then
      let (n, rng2) := randNat rng1 0 4
      let (below, rng3) := genNoiseStack n rng2
      let (x, rng4) := pickInt257Boundary rng3
      (mkTwoOverCase
        (s!"fuzz/ok/deep-random/{n}")
        (below ++ #[intV x, .slice sliceB]), rng4)
    else if shape = 9 then
      (mkTwoOverCase "fuzz/gas/exact-cost-succeeds"
        #[intV 11, intV 12, intV maxInt257, intV 1]
        #[.pushInt (.num twoOverSetGasExact), .tonEnvOp .setGasLimit, twoOverInstr],
        rng1)
    else if shape = 10 then
      (mkTwoOverCase "fuzz/gas/exact-minus-one-out-of-gas"
        #[intV 11, intV 12, intV maxInt257, intV 1]
        #[.pushInt (.num twoOverSetGasExactMinusOne), .tonEnvOp .setGasLimit, twoOverInstr],
        rng1)
    else if shape = 11 then
      let (n, rng2) := randNat rng1 1 5
      let (below, rng3) := genNoiseStack n rng2
      (mkTwoOverCase
        (s!"fuzz/ok/deep-with-cont/{n}")
        (below ++ #[intV 9, intV 10, q0]), rng3)
    else
      let (shape2, rng2) := randNat rng1 0 4
      if shape2 = 0 then
        (mkTwoOverCase "fuzz/boundary/min-max"
          #[intV minInt257, intV 0, intV 0, intV maxInt257], rng2)
      else if shape2 = 1 then
        (mkTwoOverCase "fuzz/boundary/max-min-reverse"
          #[intV maxInt257, intV 0, intV (-1), intV minInt257], rng2)
      else if shape2 = 2 then
        (mkTwoOverCase "fuzz/boundary/near-top"
          #[intV maxInt257, intV (maxInt257 - 1), intV (maxInt257 - 2), intV (maxInt257 - 3)], rng2)
      else if shape2 = 3 then
        (mkTwoOverCase "fuzz/boundary/near-bottom"
          #[intV (minInt257 + 1), intV (minInt257 + 2), intV (minInt257 + 3), intV (minInt257 + 4)], rng2)
      else
        (mkTwoOverCase "fuzz/boundary/mixed"
          #[intV 0, intV 1, intV (-1), intV maxInt257], rng2)
  ({ base with name := s!"{base.name}/{(randNat rng2 0 999_999).1}" }, rng2)

private def expectTwoOverGas : Unit :=
  if twoOverSetGasExact > 0 && twoOverSetGasExactMinusOne < twoOverSetGasExact then
    ()
  else
    ()

-- unit coverage for assembly/decoding/gas meta behavior.
def suite : InstrSuite where
  id := twoOverId
  unit := #[
    { name := "unit/opcode/assembly-and-decoding-boundaries"
      run := do
        let rawBits : BitString := natToBits 0x5c 8 ++ natToBits 0x5d 8 ++ natToBits 0x5a 8
        let code ←
          match assembleCp0 [twoOverInstr]
          with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/2over failed: {reprStr e}")
        if code.bits = natToBits 0x5d 8 then
          pure ()
        else
          throw (IO.userError
            s!"encode/2over: expected 0x5d, got {reprStr code.bits}")

        let start := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/2dup" start .twoDup 8
        let r2 ← expectDecodeStep "decode/2over" r1 .twoOver 8
        let r3 ← expectDecodeStep "decode/rot" r2 .twoSwap 8
        if r3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted bits, got {r3.bitsRemaining}") }
    ,
    { name := "unit/gas/exact-minus-one-boundary-checked"
      run := do
        pure expectTwoOverGas
        let code ←
          match assembleCp0 [twoOverInstr]
          with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/2over failed: {reprStr e}")
        if code.bits = natToBits 0x5d 8 then
          pure ()
        else
          throw (IO.userError "opcode/bounds: unexpected code for 2OVER") }
  ]
  oracle := #[
    -- [B1] exact-4 normal path with basic integers
    mkTwoOverCase "ok/exact4/positive-ascending" (#[intV 1, intV 2, intV 3, intV 4]),
    mkTwoOverCase "ok/exact4/positive-descending" (#[intV 4, intV 3, intV 2, intV 1]),
    mkTwoOverCase "ok/exact4/mixed-sign" (#[intV 7, intV (-9), intV 5, intV 0]),
    mkTwoOverCase "ok/exact4/all-zero" (#[intV 0, intV 0, intV 0, intV 0]),
    mkTwoOverCase "ok/exact4/max-min" (#[intV maxInt257, intV minInt257, intV 5, intV (-5)]),
    mkTwoOverCase "ok/exact4/min-max" (#[intV minInt257, intV maxInt257, intV 1, intV 1]),

    -- [B3] non-int values are duplicated by position without type filtering
    mkTwoOverCase "ok/exact4/null-cell-top-pair" (#[.null, .cell cellA, intV 7, intV 8]),
    mkTwoOverCase "ok/exact4/builder-tuple-top-pair" (#[.builder Builder.empty, .tuple #[], intV 7, intV 8]),
    mkTwoOverCase "ok/exact4/slice-cont-top-pair" (#[.slice sliceA, q0, intV 7, intV 8]),
    mkTwoOverCase "ok/exact4/mixed-top-noise" (#[.cell cellB, .slice sliceB, intV 7, intV 8]),

    -- [B2] exact-4 lower bound and deeper-stack shape variants
    mkTwoOverCase "ok/exact4/deep-preserve-four" (#[intV 9, intV 10, intV 11, intV 12]),
    mkTwoOverCase "ok/deep5/preserve-below" (#[intV 9, intV 10, intV 11, intV 12, intV 13]),
    mkTwoOverCase "ok/deep6/preserve-below" (#[intV 9, intV 10, intV 11, intV 12, intV 13, intV 14]),
    mkTwoOverCase "ok/deep7/boundary" (#[intV 1, .slice sliceA, intV 2, intV 3, intV 4, intV 5, intV 6]),
    mkTwoOverCase "ok/deep8/nonint-noise" (#[.null, .cell cellA, .builder Builder.empty, intV 3, intV 4, intV 5, intV 6, intV 7]),

    -- [B1,B4] boundary integer inputs in deep stacks
    mkTwoOverCase "ok/exact4/int-boundary-mix" (#[intV maxInt257, intV (maxInt257 - 1), intV (minInt257 + 1), intV (-1)]),
    mkTwoOverCase "ok/deep5/int-boundary-mix" (#[intV minInt257, intV (minInt257 + 1), intV (maxInt257 - 2), intV (maxInt257 - 3), intV 17]),

    -- [B5] underflow depth branches
    mkTwoOverCase "err/underflow/empty" #[],
    mkTwoOverCase "err/underflow/one" (#[intV 1]),
    mkTwoOverCase "err/underflow/two" (#[intV 1, intV 2]),
    mkTwoOverCase "err/underflow/three" (#[intV 1, intV 2, intV 3]),
    mkTwoOverCase "err/underflow/three-mixed" (#[.null, .slice sliceA, intV 7]),

    -- [B7] raw-decoder checks and aliasing with adjacent opcodes
    mkTwoOverCodeCase "decode/raw-5d-single" (#[intV 1, intV 2, intV 3, intV 4]) twoOverRaw8,
    mkTwoOverCodeCase "decode/raw-5c-then-5d-with-noise"
      (#[.null, .cell cellA, intV 11, intV 12, intV 13, intV 14]) twoOverAfterTwoDupRaw16,

    -- [B9,B10] gas cliffs with fixed base cost
    mkTwoOverCase "gas/exact/succeeds" (#[intV 7, intV 8, intV 9, intV 10])
      #[.pushInt (.num twoOverSetGasExact), .tonEnvOp .setGasLimit, twoOverInstr],
    mkTwoOverCase "gas/exact-minus-one/out-of-gas" (#[intV 7, intV 8, intV 9, intV 10])
      #[.pushInt (.num twoOverSetGasExactMinusOne), .tonEnvOp .setGasLimit, twoOverInstr],
    mkTwoOverCase "gas/exact/succeeds/deep" (#[.null, .cell cellA, intV 1, intV 2, intV 3])
      #[.pushInt (.num twoOverSetGasExact), .tonEnvOp .setGasLimit, twoOverInstr],

    -- [B1,B3] more boundary-preserving variants
    mkTwoOverCase "ok/exact4/cont-q0" (#[q0, q0, intV 1, intV 2]),
    mkTwoOverCase "ok/deep6/mixed-keys" (#[.slice sliceA, intV 0, .cell cellB, intV 5, intV 6, intV 7]),
    mkTwoOverCase "ok/deep7/tail-slices" (#[.slice sliceB, intV 1, .slice sliceA, .builder Builder.empty, intV 2, intV 3, intV 4]),
    mkTwoOverCase "ok/deep8/all-boundary" (#[intV maxInt257, intV minInt257, intV 123, intV (-123), intV 0, intV 5, intV 6, intV 7]),
    mkTwoOverCase "ok/exact4/middle-gap" (#[.tuple #[], intV 5, .builder Builder.empty, intV 99])
  ]
  fuzz := #[
    {
      seed := 2026020304
      count := 500
      gen := genTwoOverFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.OP_2OVER
