import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QNEQ

/-
QNEQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.qneq`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp`, opcode wiring in `register_int_cmp_ops` with mode `0x787`, `quiet=true`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch map used for this suite:
- Lean: 8 branch points / 9 terminal outcomes
  (dispatch to `.contExt`; dispatch to `.qneq`; `checkUnderflow 2`;
   two `popInt` type checks; `x/y` NaN-vs-finite split;
   finite compare split (`a ≠ b` true/false)).
- C++: 6 branch points / 9 aligned terminal outcomes
  (`QNEQ` mapped to `exec_cmp(..., mode=0x787, quiet=true)`;
   `check_underflow(2)`; two `pop_int` checks; invalid fold;
   compare class `{<,=,>}` mapped to `{-1,0,-1}`).

Key risk areas:
- underflow must fire before type checks on arity<2 stacks;
- pop order is `y` then `x`, so type-check ordering must match;
- quiet NaN propagation must succeed (`NaN` result, no `intOv`);
- finite truth-table mapping must return `-1` for `≠`, `0` for `=`;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QNEQ`.
-/

private def qneqId : InstrId := { name := "QNEQ" }

private def qneqInstr : Instr := .contExt .qneq

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qneqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qneqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qneqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQneqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qneqInstr stack

private def runQneqDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 706)) stack

private def qneqSetGasExact : Int :=
  computeExactGasBudget qneqInstr

private def qneqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qneqInstr

private def genQneqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-random" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-boundary" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-equal-inputs" #[intV x, intV x], r2)
    else if shape = 5 then
      let (base, r2) := pickInt257Boundary rng1
      let (dir, r3) := randNat r2 0 1
      let y :=
        if base = minInt257 then minInt257 + 1
        else if base = maxInt257 then maxInt257 - 1
        else if dir = 0 then base - 1 else base + 1
      (mkCase s!"fuzz/shape-{shape}/ok-near-neighbor" #[intV base, intV y], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-right-zero" #[intV x, intV 0], r2)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-left-zero" #[intV 0, intV y], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/error-order-one-non-int-underflow-first" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-first" #[intV x, .null], r2)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-second" #[.null, intV y], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-y-via-program" #[.num x, .nan], r2)
    else
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-x-via-program" #[.nan, .num y], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qneqId
  unit := #[
    { name := "unit/ok/finite-sign-equality-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (2, 1, -1),
            (1, 2, -1),
            (-7, -7, 0),
            (-7, -8, -1),
            (-8, -7, -1),
            (1, -1, -1),
            (-1, 1, -1),
            (minInt257, minInt257, 0),
            (maxInt257, maxInt257, 0),
            (minInt257, maxInt257, -1),
            (maxInt257, minInt257, -1),
            (maxInt257 - 1, maxInt257, -1),
            (minInt257 + 1, minInt257, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"qneq({x},{y})" (runQneqDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/ok/quiet-nan-propagates"
      run := do
        expectOkStack "quiet-nan/x" (runQneqDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "quiet-nan/y" (runQneqDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "quiet-nan/both" (runQneqDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQneqDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQneqDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-first" (runQneqDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQneqDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQneqDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first"
          (runQneqDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qneq-falls-through"
      run := do
        expectOkStack "fallback/non-contExt"
          (runQneqDispatchFallback .add #[]) #[intV 706]
        expectOkStack "fallback/other-contExt"
          (runQneqDispatchFallback (.contExt .condSel) #[]) #[intV 706] }
  ]
  oracle := #[
    mkCase "ok/equal/zero-zero" #[intV 0, intV 0],
    mkCase "ok/equal/positive" #[intV 17, intV 17],
    mkCase "ok/equal/negative" #[intV (-17), intV (-17)],
    mkCase "ok/not-equal/pos-pos" #[intV 17, intV 25],
    mkCase "ok/not-equal/neg-neg" #[intV (-17), intV (-25)],
    mkCase "ok/not-equal/neg-pos" #[intV (-1), intV 1],
    mkCase "ok/not-equal/pos-neg" #[intV 1, intV (-1)],
    mkCase "ok/boundary/min-eq-min" #[intV minInt257, intV minInt257],
    mkCase "ok/boundary/max-eq-max" #[intV maxInt257, intV maxInt257],
    mkCase "ok/boundary/min-ne-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/boundary/max-ne-min" #[intV maxInt257, intV minInt257],
    mkCase "ok/boundary/max-minus-one-ne-max" #[intV (maxInt257 - 1), intV maxInt257],
    mkCase "ok/boundary/min-plus-one-ne-min" #[intV (minInt257 + 1), intV minInt257],
    mkCaseFromIntVals "quiet-nan/pushnan-y-via-program" #[.num 42, .nan],
    mkCaseFromIntVals "quiet-nan/pushnan-x-via-program" #[.nan, .num 42],
    mkCaseFromIntVals "quiet-nan/double-pushnan-via-program" #[.nan, .nan],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qneqSetGasExact), .tonEnvOp .setGasLimit, qneqInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qneqSetGasExactMinusOne), .tonEnvOp .setGasLimit, qneqInstr]
  ]
  fuzz := #[
    { seed := 2026020816
      count := 600
      gen := genQneqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QNEQ
