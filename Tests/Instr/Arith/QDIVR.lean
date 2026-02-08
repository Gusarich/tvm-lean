import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QDIVR

/-
QDIVR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, `roundMode = 0`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `dump_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest-rounding adjustment)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Lean-vs-C++ terminal mapping used for this suite:
- dispatch arm (`.divMod` vs fallback `next`);
- arity guard (`check_underflow(2)`) before any pop/type checks;
- pop order (`y` first, then `x`) for type-check ordering;
- nearest rounding (`roundMode = 0`) including half ties (ties to +∞);
- quiet funnels for div-by-zero / overflow / NaN (`push_int_quiet(..., quiet=true)`);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QDIVR` (exact vs exact-minus-one).

QDIVR specialization:
- opcode family `0xb7a90` args4 = `0x5`;
- fixed params: `d=1`, `roundMode=0`, `addMode=false`, `quiet=true`.

Key risk areas covered:
- rounding-mode-specific nearest behavior across sign/tie combinations;
- error ordering: underflow before type on arity<2, then `y` pop before `x`;
- quiet NaN propagation and quiet overflow (`minInt257 / -1`) -> NaN;
- oracle serialization hygiene: NaN/out-of-range cases injected via program.
-/

private def qdivrId : InstrId := { name := "QDIVR" }

private def qdivrInstr : Instr := .divMod 1 0 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qdivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qdivrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qdivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQdivrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qdivrInstr stack

private def runQdivrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 905)) stack

private def qdivrSetGasExact : Int :=
  computeExactGasBudget qdivrInstr

private def qdivrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qdivrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def roundDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def tieOddPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def outOfRangeHighPool : Array Int :=
  #[maxInt257 + 1, maxInt257 + 2, pow2 257]

private def outOfRangeLowPool : Array Int :=
  #[minInt257 - 1, minInt257 - 2, -(pow2 257)]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQdivrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickFromPool tieOddPool rng1
      (mkCase s!"fuzz/shape-{shape}/ok/tie-den-pos-two" #[intV x, intV 2], r2)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieOddPool rng1
      (mkCase s!"fuzz/shape-{shape}/ok/tie-den-neg-two" #[intV x, intV (-2)], r2)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-min-div-neg-one"
        #[intV minInt257, intV (-1)], rng1)
    else if shape = 6 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok/exact-den-pos-one" #[intV x, intV 1], r2)
    else if shape = 7 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok/exact-den-neg-one" #[intV x, intV (-1)], r2)
    else if shape = 8 then
      let (y, r2) := pickNonZeroInt rng1
      (mkCase s!"fuzz/shape-{shape}/ok/zero-numerator" #[intV 0, intV y], r2)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-first" #[.null], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, nonInt], r3)
    else if shape = 13 then
      let (y, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[nonInt, intV y], r3)
    else if shape = 14 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[xLike, yLike], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/y-via-program" #[.num x, .nan], r2)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/x-via-program" #[.nan, .num y], r2)
    else if shape = 17 then
      let (x, r2) := pickFromPool outOfRangeHighPool rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-high-before-qdivr"
        #[.num x, .num 7], r2)
    else
      let (y, r2) := pickFromPool outOfRangeLowPool rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-low-before-qdivr"
        #[.num 7, .num y], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qdivrId
  unit := #[
    { name := "unit/round/nearest-sign-combos-and-half-ties"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 2),
            (-7, 3, -2),
            (7, -3, -2),
            (-7, -3, 2),
            (5, 2, 3),
            (-5, 2, -2),
            (5, -2, -2),
            (-5, -2, 3),
            (1, 2, 1),
            (-1, 2, 0),
            (1, -2, 0),
            (-1, -2, 1),
            (42, 7, 6),
            (-42, 7, -6),
            (42, -7, -6),
            (-42, -7, 6)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runQdivrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/round/nearest-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257),
            (maxInt257, -1, -maxInt257),
            (minInt257, 1, minInt257),
            (minInt257 + 1, -1, maxInt257),
            (maxInt257, 2, pow2 255),
            (minInt257, 2, -(pow2 255)),
            (minInt257, -2, pow2 255),
            (0, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}/{y}" (runQdivrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/quiet/divzero-overflow-and-nan-funnel"
      run := do
        expectOkStack "quiet/divzero" (runQdivrDirect #[intV 5, intV 0]) #[.int .nan]
        expectOkStack "quiet/overflow-min-div-neg-one"
          (runQdivrDirect #[intV minInt257, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/nan-x" (runQdivrDirect #[.int .nan, intV 3]) #[.int .nan]
        expectOkStack "quiet/nan-y" (runQdivrDirect #[intV 3, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan-both" (runQdivrDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQdivrDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQdivrDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQdivrDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQdivrDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQdivrDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQdivrDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQdivrDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first"
          (runQdivrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQdivrDispatchFallback #[]) #[intV 905] }
  ]
  oracle := #[
    mkCase "ok/round/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ok/round/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ok/round/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ok/round/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ok/round/tie/pos-pos-half" #[intV 5, intV 2],
    mkCase "ok/round/tie/neg-pos-half" #[intV (-5), intV 2],
    mkCase "ok/round/tie/pos-neg-half" #[intV 5, intV (-2)],
    mkCase "ok/round/tie/neg-neg-half" #[intV (-5), intV (-2)],
    mkCase "ok/round/tie/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "ok/round/tie/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "ok/round/tie/neg-neg-near-zero" #[intV (-1), intV (-2)],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV (-5)],
    mkCase "ok/boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/boundary/max-div-two-half-up" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/min-div-two" #[intV minInt257, intV 2],
    mkCase "ok/boundary/min-div-neg-two" #[intV minInt257, intV (-2)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[.num 5, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 5],
    mkCaseFromIntVals "quiet/nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-range-high-before-qdivr" #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-low-before-qdivr" #[.num 7, .num (minInt257 - 1)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "type/y-cell-top" #[intV 1, .cell Cell.empty],
    mkCase "type/x-cell-second" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qdivrSetGasExact), .tonEnvOp .setGasLimit, qdivrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qdivrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qdivrInstr]
  ]
  fuzz := #[
    { seed := 2026020806
      count := 700
      gen := genQdivrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QDIVR
