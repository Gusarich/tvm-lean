import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMAX

/-
QMAX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Qmax.lean`
  - `TvmLean/Semantics/Exec/Common.lean` (`VM.checkUnderflow`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_minmax`, opcode wiring in `register_other_arith_ops` for `QMAX` mode=5)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.hpp` (`Stack::check_underflow`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 8 branch points / 8 terminal outcomes
  (opcode dispatch; explicit `checkUnderflow 2`; two `popInt` type checks;
   finite-vs-NaN operand fold; numeric compare/swap split; quiet `pushIntQuiet`
   NaN-vs-num and signed-257 fit behavior).
- C++: 7 branch points / 8 aligned terminal outcomes
  (`QMAX` mapped to `exec_minmax(mode=5)`; `check_underflow(2)` guard;
   two `pop_int` type checks; validity fold + compare/swap; quiet push overflow/NaN path).

Terminal outcomes covered by oracle:
- success with finite in-range result,
- success with NaN result (input NaN propagation),
- success with NaN result (selected out-of-range numeric result),
- `stkUnd`,
- `typeChk` (top-pop and second-pop order),
- `outOfGas` at exact-minus-one gas boundary.

Key risk areas:
- underflow must fire before type checks for arity<2 (including single non-int stack);
- pop order is top first (`x`), then second (`y`), impacting error-ordering;
- quiet semantics must never throw `intOv` for NaN/overflow output;
- range check applies only to selected MAX result (unselected out-of-range low input may still succeed);
- deterministic gas thresholds for `PUSHINT n; SETGASLIMIT; QMAX`.
-/

private def qmaxId : InstrId := { name := "QMAX" }

private def qmaxInstr : Instr := .qmax

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmaxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmaxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmaxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQmaxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQmax qmaxInstr stack

private def runQmaxDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQmax .max (VM.push (intV 905)) stack

private def qmaxSetGasExact : Int :=
  computeExactGasBudget qmaxInstr

private def qmaxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmaxInstr

private def genQmaxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-boundary" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-right-zero" #[intV x, intV 0], r2)
    else if shape = 5 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-left-zero" #[intV 0, intV y], r2)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-equal-inputs" #[intV x, intV x], r2)
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
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-right-via-program"
        #[IntVal.num x, IntVal.nan], r2)
    else if shape = 13 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-left-via-program"
        #[IntVal.nan, IntVal.num y], r2)
    else if shape = 14 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-overflow-selected-high"
        #[IntVal.num (maxInt257 + 1), IntVal.num 0], rng1)
    else if shape = 15 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/out-of-range-unselected-low"
        #[IntVal.num (minInt257 - 1), IntVal.num 7], rng1)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow-empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmaxId
  unit := #[
    { name := "unit/direct/finite-sign-zero-equality-and-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 7),
            (7, -3, 7),
            (-7, 3, 3),
            (-7, -3, -3),
            (123, 0, 123),
            (0, 123, 123),
            (17, 17, 17),
            (-17, -17, -17),
            (maxInt257, minInt257, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"qmax({x},{y})" (runQmaxDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-and-selected-overflow-push-nan"
      run := do
        expectOkStack "nan-left" (runQmaxDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan-right" (runQmaxDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "selected-high-overflow-left" (runQmaxDirect #[intV (maxInt257 + 1), intV 0]) #[.int .nan]
        expectOkStack "selected-high-overflow-right" (runQmaxDirect #[intV 0, intV (maxInt257 + 1)]) #[.int .nan]
        expectOkStack "both-low-overflow" (runQmaxDirect #[intV (minInt257 - 2), intV (minInt257 - 1)]) #[.int .nan]
        expectOkStack "out-of-range-unselected-low-left" (runQmaxDirect #[intV (minInt257 - 1), intV 5]) #[intV 5]
        expectOkStack "out-of-range-unselected-low-right" (runQmaxDirect #[intV 5, intV (minInt257 - 1)]) #[intV 5] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQmaxDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQmaxDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQmaxDirect #[.null]) .stkUnd
        expectErr "type/pop-top-first" (runQmaxDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-second" (runQmaxDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-pop-top-first" (runQmaxDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qmax-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmaxDispatchFallback #[]) #[intV 905] }
  ]
  oracle := #[
    mkCase "ok/zero/zero-zero" #[intV 0, intV 0],
    mkCase "ok/sign/pos-pos" #[intV 17, intV 5],
    mkCase "ok/sign/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/sign/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/sign/neg-neg" #[intV (-17), intV (-5)],
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
    mkCaseFromIntVals "nan/right-operand-via-program" #[IntVal.num 42, IntVal.nan],
    mkCaseFromIntVals "nan/left-operand-via-program" #[IntVal.nan, IntVal.num 42],
    mkCaseFromIntVals "nan/both-operands-via-program" #[IntVal.nan, IntVal.nan],
    mkCaseFromIntVals "quiet-overflow/selected-high-left-via-program"
      #[IntVal.num (maxInt257 + 1), IntVal.num 0],
    mkCaseFromIntVals "quiet-overflow/selected-high-right-via-program"
      #[IntVal.num 0, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "quiet-overflow/both-high-via-program"
      #[IntVal.num (maxInt257 + 2), IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "quiet-overflow/both-low-via-program"
      #[IntVal.num (minInt257 - 2), IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "boundary/out-of-range-unselected-low-left-via-program"
      #[IntVal.num (minInt257 - 1), IntVal.num 5],
    mkCaseFromIntVals "boundary/out-of-range-unselected-low-right-via-program"
      #[IntVal.num 5, IntVal.num (minInt257 - 1)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-top-null" #[intV 1, .null],
    mkCase "type/pop-second-null" #[.null, intV 1],
    mkCase "type/pop-top-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-top-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qmaxSetGasExact), .tonEnvOp .setGasLimit, qmaxInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qmaxSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmaxInstr]
  ]
  fuzz := #[
    { seed := 2026020806
      count := 600
      gen := genQmaxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMAX
