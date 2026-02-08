import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMINMAX

/-
QMINMAX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Minmax.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_minmax`, opcode wiring in `register_other_arith_ops` for mode=7)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 9 branch points / 9 terminal outcomes
  (opcode dispatch; explicit `checkUnderflow 2`; two `popInt` type checks;
   finite-vs-NaN split; compare/swap split; first and second quiet `pushIntQuiet` paths).
- C++: 7 branch points / 9 aligned terminal outcomes
  (`QMINMAX` registration to `exec_minmax(mode=7)`; underflow guard; two `pop_int` checks;
   validity fold + compare/swap; first and second quiet `push_int_quiet` paths).

Terminal outcomes covered:
- success with finite sorted pair `[min, max]`,
- success with quiet NaN pair propagation,
- success with quiet out-of-range folding to NaN (direct-handler regression checks),
- `stkUnd`,
- `typeChk` on first pop,
- `typeChk` on second pop,
- `outOfGas` at exact-minus-one gas boundary.

Key risk areas:
- stack pop order (`top` then `second`) affects type-check ordering;
- underflow must win before type checks for singleton/empty stacks;
- quiet mode must never throw `intOv` on NaN or out-of-range push results;
- output ordering must stay `[min, max]` across sign/equality/boundary inputs;
- deterministic gas edge for `PUSHINT n; SETGASLIMIT; QMINMAX`.
-/

private def qminmaxId : InstrId := { name := "QMINMAX" }

private def qminmaxInstr : Instr := .qminmax

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qminmaxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qminmaxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qminmaxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQminmaxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMinmax qminmaxInstr stack

private def runQminmaxDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMinmax .qmax (VM.push (intV 611)) stack

private def qminmaxSetGasExact : Int :=
  computeExactGasBudget qminmaxInstr

private def qminmaxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qminmaxInstr

private def genQminmaxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-boundary" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-random" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-equal" #[intV x, intV x], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-right-zero" #[intV x, intV 0], r2)
    else if shape = 6 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-left-zero" #[intV 0, intV y], r2)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow-one-non-int" #[.null], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-top-first" #[intV x, .null], r2)
    else if shape = 11 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-second" #[.null, intV y], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-via-program"
        #[IntVal.num x, IntVal.nan], r2)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow-empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qminmaxId
  unit := #[
    { name := "unit/direct/ordered-output-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 3, 3, 7),
            (3, 7, 3, 7),
            (7, -3, -3, 7),
            (-7, 3, -7, 3),
            (-7, -3, -7, -3),
            (17, 17, 17, 17),
            (-17, -17, -17, -17),
            (maxInt257, minInt257, minInt257, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let lo := c.2.2.1
          let hi := c.2.2.2
          expectOkStack s!"qminmax({x},{y})" (runQminmaxDirect #[intV x, intV y]) #[intV lo, intV hi] }
    ,
    { name := "unit/direct/quiet-nan-and-range-folding"
      run := do
        expectOkStack "nan-left" (runQminmaxDirect #[.int .nan, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "nan-right" (runQminmaxDirect #[intV 1, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "high-out-of-range-folds-second" (runQminmaxDirect #[intV 0, intV (maxInt257 + 1)]) #[intV 0, .int .nan]
        expectOkStack "low-out-of-range-folds-first" (runQminmaxDirect #[intV 0, intV (minInt257 - 1)]) #[.int .nan, intV 0]
        expectOkStack "both-high-out-of-range-fold-to-nan-pair"
          (runQminmaxDirect #[intV (maxInt257 + 2), intV (maxInt257 + 1)]) #[.int .nan, .int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQminmaxDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQminmaxDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQminmaxDirect #[.null]) .stkUnd
        expectErr "type/pop-top-first" (runQminmaxDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-second" (runQminmaxDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-pop-top-first" (runQminmaxDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qminmax-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQminmaxDispatchFallback #[]) #[intV 611] }
  ]
  oracle := #[
    mkCase "ok/order/ascending" #[intV 3, intV 7],
    mkCase "ok/order/descending" #[intV 7, intV 3],
    mkCase "ok/sign/pos-neg" #[intV 7, intV (-3)],
    mkCase "ok/sign/neg-pos" #[intV (-7), intV 3],
    mkCase "ok/sign/neg-neg" #[intV (-7), intV (-3)],
    mkCase "ok/equal/positive" #[intV 42, intV 42],
    mkCase "ok/equal/negative" #[intV (-42), intV (-42)],
    mkCase "ok/zero/right-zero" #[intV 222, intV 0],
    mkCase "ok/zero/left-zero" #[intV 0, intV 222],
    mkCase "boundary/in-range/max-min" #[intV maxInt257, intV minInt257],
    mkCase "boundary/in-range/min-max" #[intV minInt257, intV maxInt257],
    mkCase "boundary/in-range/max-max" #[intV maxInt257, intV maxInt257],
    mkCase "boundary/in-range/min-min" #[intV minInt257, intV minInt257],
    mkCase "boundary/in-range/max-near-max" #[intV maxInt257, intV (maxInt257 - 1)],
    mkCase "boundary/in-range/min-near-min" #[intV minInt257, intV (minInt257 + 1)],
    mkCase "boundary/in-range/max-zero" #[intV maxInt257, intV 0],
    mkCase "boundary/in-range/min-zero" #[intV minInt257, intV 0],
    mkCaseFromIntVals "nan/top-via-program" #[IntVal.num 42, IntVal.nan],
    mkCaseFromIntVals "nan/second-via-program" #[IntVal.nan, IntVal.num 42],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-top-null" #[intV 1, .null],
    mkCase "type/pop-second-null" #[.null, intV 1],
    mkCase "type/pop-top-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-top-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qminmaxSetGasExact), .tonEnvOp .setGasLimit, qminmaxInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qminmaxSetGasExactMinusOne), .tonEnvOp .setGasLimit, qminmaxInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 600
      gen := genQminmaxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMINMAX
