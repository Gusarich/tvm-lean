import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QDIV

/-
QDIV branch-map notes (Lean + C++ reference):
- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, opcode wiring in `register_div_ops`).

Branch/terminal counts used for this suite:
- Lean: 6 branch sites / 14 terminal outcomes
  (dispatch arm; `addMode` pop split; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with 4 arms; non-num `d=3` split).
- C++: 4 branch sites / 10 aligned terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add execution split + `d` switch).

QDIV specialization:
- opcode family `0xb7a90` args4 = `0x4`
- fixed params: `d=1`, `roundMode=-1` (floor), `addMode=false`, `quiet=true`.

Key risk areas covered:
- floor semantics across sign combinations and near-zero fractions;
- quiet division-by-zero and quiet overflow (`minInt257 / -1`) producing NaN;
- pop/error order (`y` pops before `x`, underflow before type on short stacks);
- NaN and out-of-range inputs injected via program only (`PUSHINT`);
- exact gas boundary via `SETGASLIMIT` exact vs exact-minus-one budgets.
-/

private def qdivId : InstrId := { name := "QDIV" }

private def qdivInstr : Instr := .divMod 1 (-1) false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qdivInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qdivId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qdivInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQdivDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qdivInstr stack

private def runQdivDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 606)) stack

private def qdivSetGasExact : Int :=
  computeExactGasBudget qdivInstr

private def qdivSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qdivInstr

private def qdivNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def qdivDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def qdivOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonZeroBoundary (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickInt257Boundary rng0
  (if v = 0 then 1 else v, rng1)

private def pickOutOfRange (rng : StdGen) : Int × StdGen :=
  pickFromPool qdivOutOfRangePool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genQdivFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  -- Controlled zero-divisor rate: shapes 0 and 1 are dedicated `y = 0` cases (2/20 = 10%).
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero-random" #[intV x, intV 0], r2)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero-boundary" #[intV x, intV 0], r2)
    else if shape = 2 then
      let (x, r2) := pickFromPool qdivNumeratorPool rng1
      let (y, r3) := pickFromPool qdivDenominatorPool r2
      (mkCase s!"fuzz/shape-{shape}/rounding/sign-pool" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/rounding/random-nonzero" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/rounding/boundary-nonzero" #[intV x, intV y], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (neg, r3) := randBool r2
      let y : Int := if neg then -1 else 1
      (mkCase s!"fuzz/shape-{shape}/rounding/exact-div-by-one" #[intV x, intV y], r3)
    else if shape = 6 then
      let (negNum, r2) := randBool rng1
      let (negDen, r3) := randBool r2
      let x : Int := if negNum then -1 else 1
      let y : Int := if negDen then -2 else 2
      (mkCase s!"fuzz/shape-{shape}/rounding/near-zero-floor" #[intV x, intV y], r3)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-min-div-neg-one" #[intV minInt257, intV (-1)], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/boundary/max-div-one" #[intV maxInt257, intV 1], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/boundary/min-div-one" #[intV minInt257, intV 1], rng1)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-first" #[.null], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (top, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, top], r3)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[xLike, intV y], r3)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[xLike, yLike], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program" #[.num x, .nan], r2)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program" #[.nan, .num y], r2)
    else if shape = 18 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program" #[.nan, .nan], rng1)
    else
      let (variant, r2) := randNat rng1 0 2
      if variant = 0 then
        let (x, r3) := pickSigned257ish r2
        let (yo, r4) := pickOutOfRange r3
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/range-y-via-program" #[.num x, .num yo], r4)
      else if variant = 1 then
        let (xo, r3) := pickOutOfRange r2
        let (y, r4) := pickNonZeroBoundary r3
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/range-x-via-program" #[.num xo, .num y], r4)
      else
        let (xo, r3) := pickOutOfRange r2
        let (yo, r4) := pickOutOfRange r3
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/range-both-via-program" #[.num xo, .num yo], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qdivId
  unit := #[
    { name := "unit/rounding/floor-sign-and-near-zero"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 2),
            (-7, 3, -3),
            (7, -3, -3),
            (-7, -3, 2),
            (1, 2, 0),
            (-1, 2, -1),
            (1, -2, -1),
            (-1, -2, 0),
            (5, 2, 2),
            (-5, 2, -3),
            (5, -2, -3),
            (-5, -2, 2),
            (42, 7, 6),
            (-42, 7, -6),
            (42, -7, -6),
            (-42, -7, 6)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runQdivDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/rounding/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257),
            (maxInt257, -1, -maxInt257),
            (minInt257, 1, minInt257),
            (minInt257 + 1, -1, maxInt257),
            (maxInt257, 2, (pow2 255) - 1),
            (minInt257, 2, -(pow2 255)),
            (minInt257, -2, pow2 255),
            (0, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runQdivDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/quiet/divzero-and-overflow-produce-nan"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero" (runQdivDirect #[intV 5, intV 0]) #[.int .nan]
        expectOkStack "quiet/divzero/zero-over-zero" (runQdivDirect #[intV 0, intV 0]) #[.int .nan]
        expectOkStack "quiet/overflow/min-div-neg-one" (runQdivDirect #[intV minInt257, intV (-1)]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQdivDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQdivDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-first" (runQdivDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQdivDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQdivDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQdivDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQdivDispatchFallback #[]) #[intV 606] }
  ]
  oracle := #[
    mkCase "rounding/floor/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "rounding/floor/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "rounding/floor/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "rounding/floor/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "rounding/floor/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "rounding/floor/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "rounding/floor/pos-pos-near-zero" #[intV 1, intV 2],
    mkCase "rounding/floor/neg-neg-near-zero" #[intV (-1), intV (-2)],
    mkCase "exact/pos-pos" #[intV 42, intV 7],
    mkCase "exact/neg-pos" #[intV (-42), intV 7],
    mkCase "exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "exact/zero-numerator" #[intV 0, intV (-5)],
    mkCase "boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "boundary/max-div-two" #[intV maxInt257, intV 2],
    mkCase "boundary/min-div-two" #[intV minInt257, intV 2],
    mkCase "boundary/min-div-neg-two" #[intV minInt257, intV (-2)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0],
    mkCase "quiet/overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[.num 5, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 5],
    mkCaseFromIntVals "quiet/nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "quiet/range/y-out-of-range-via-program" #[.num 5, .num (maxInt257 + 1)],
    mkCaseFromIntVals "quiet/range/x-out-of-range-via-program" #[.num (minInt257 - 1), .num 3],
    mkCaseFromIntVals "quiet/range/both-out-of-range-via-program" #[.num (pow2 257), .num (-(pow2 257))],
    mkCase "error-order/range-before-type-via-program" #[.null]
      #[.pushInt (.num (maxInt257 + 1)), qdivInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first" #[intV 1, .null],
    mkCase "type/pop-x-second" #[.null, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qdivSetGasExact), .tonEnvOp .setGasLimit, qdivInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qdivSetGasExactMinusOne), .tonEnvOp .setGasLimit, qdivInstr]
  ]
  fuzz := #[
    { seed := 2026020821
      count := 700
      gen := genQdivFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QDIV
