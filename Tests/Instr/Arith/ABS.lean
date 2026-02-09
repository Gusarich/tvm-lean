import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ABS

/-
ABS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Abs.lean` (`execInstrArithAbs`)
  - `TvmLean/Semantics/Exec/Arith.lean` (dispatch chain includes `execInstrArithAbs`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb60b` decodes to `.abs false`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_abs`, `register_other_arith_ops` wiring for `ABS`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 5 branch points / 7 terminal outcomes
  (handler dispatch; pop underflow/type/success; NaN-vs-num split; sign split for nums;
   non-quiet push split: in-range success vs `intOv` overflow/NaN).
- C++: 5 branch points / 7 aligned terminal outcomes
  (`ABS` bound to `exec_abs(..., quiet=false)`; underflow/type checks in `pop_int`;
   valid-vs-invalid int and sign branch; `push_int_quiet(..., false)` success vs `int_ov`).

Mapped terminal outcomes covered:
- finite success for positive/negative/zero and boundary-neighbor operands;
- `intOv` from `minInt257` overflow on negation;
- `intOv` from NaN injected via program prelude (`PUSHINT .nan`);
- `stkUnd`;
- `typeChk`;
- non-matching dispatch falls through to `next`.

Key risk areas covered:
- unary pop-order/error-order: underflow before type, and only top operand consumed;
- signed-257 cliff around `minInt257`, `minInt257 + 1`, `minInt257 + 2`, `maxInt257`;
- NaN and out-of-range integer injection done via program prelude only (never raw `initStack`);
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; ABS` (exact vs exact-minus-one).
-/

private def absId : InstrId := { name := "ABS" }

private def absInstr : Instr := .abs false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[absInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := absId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[absInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runAbsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithAbs absInstr stack

private def runAbsDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithAbs .negate (VM.push (intV 5150)) stack

private def absSetGasExact : Int :=
  computeExactGasBudget absInstr

private def absSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne absInstr

private def genAbsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/ok-random" #[intV x], r2)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"/fuzz/shape-{shape}/ok-boundary" #[intV x], r2)
    else if shape = 2 then
      (mkCase s!"/fuzz/shape-{shape}/intov-min-int257-overflow" #[intV minInt257], rng1)
    else if shape = 3 then
      (mkCase s!"/fuzz/shape-{shape}/ok-near-min-plus-one" #[intV (minInt257 + 1)], rng1)
    else if shape = 4 then
      (mkCase s!"/fuzz/shape-{shape}/ok-near-min-plus-two" #[intV (minInt257 + 2)], rng1)
    else if shape = 5 then
      (mkCase s!"/fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/type-top-null" #[.null], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/type-top-cell" #[.cell Cell.empty], rng1)
    else if shape = 8 then
      let (x0, r2) := pickSigned257ish rng1
      let x := if x0 = minInt257 then minInt257 + 1 else x0
      (mkCase s!"/fuzz/shape-{shape}/pop-order-top-int-below-null-untouched" #[.null, intV x], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order-top-null-below-int-type-first" #[intV x, .null], r2)
    else if shape = 10 then
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/intov-nan-via-program" #[.nan], rng1)
    else if shape = 11 then
      let (delta, r2) := randNat rng1 1 64
      let n := maxInt257 + Int.ofNat delta
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order-pushint-overflow-high-before-op" #[.num n], r2)
    else if shape = 12 then
      let (delta, r2) := randNat rng1 1 64
      let n := minInt257 - Int.ofNat delta
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order-pushint-overflow-low-before-op" #[.num n], r2)
    else if shape = 13 then
      let (x0, r2) := pickSigned257ish rng1
      let x := if x0 = minInt257 then minInt257 + 1 else x0
      (mkCase s!"/fuzz/shape-{shape}/ok-tail-int-below-top-int" #[intV 11, intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickInt257Boundary rng1
      let y := if x = maxInt257 then maxInt257 - 1 else x
      (mkCase s!"/fuzz/shape-{shape}/ok-max-neighbor" #[intV y], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order-top-null-with-below-int" #[intV x, .null], r2)
    else
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/intov-nan-via-program-with-tail" #[.num 77, .nan], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := absId
  unit := #[
    { name := "/unit/ok/finite-sign-zero-and-boundary"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, 0),
            (17, 17),
            (-17, 17),
            (maxInt257, maxInt257),
            (maxInt257 - 1, maxInt257 - 1),
            (minInt257 + 1, maxInt257),
            (minInt257 + 2, maxInt257 - 1)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"/unit/abs/{x}" (runAbsDirect #[intV x]) #[intV expected] }
    ,
    { name := "/unit/error/intov-overflow-from-min-int257"
      run := do
        expectErr "/unit/intov/min-int257" (runAbsDirect #[intV minInt257]) .intOv }
    ,
    { name := "/unit/error-order/underflow-type-and-top-pop-order"
      run := do
        expectErr "/unit/underflow/empty" (runAbsDirect #[]) .stkUnd
        expectErr "/unit/type/top-null" (runAbsDirect #[.null]) .typeChk
        expectErr "/unit/type/top-cell" (runAbsDirect #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/top-null-below-int-type-first"
          (runAbsDirect #[intV (-8), .null]) .typeChk
        expectOkStack "/unit/pop-order/top-int-below-null-untouched"
          (runAbsDirect #[.null, intV (-8)]) #[.null, intV 8] }
    ,
    { name := "/unit/dispatch/non-abs-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runAbsDispatchFallback #[]) #[intV 5150] }
  ]
  oracle := #[
    mkCase "/ok/finite/zero" #[intV 0],
    mkCase "/ok/finite/positive" #[intV 23],
    mkCase "/ok/finite/negative" #[intV (-23)],
    mkCase "/ok/finite/with-tail" #[intV 9, intV (-2)],
    mkCase "/boundary/in-range/max-int257" #[intV maxInt257],
    mkCase "/boundary/in-range/min-plus-one" #[intV (minInt257 + 1)],
    mkCase "/boundary/in-range/min-plus-two" #[intV (minInt257 + 2)],
    mkCase "/intov/overflow/min-int257" #[intV minInt257],
    mkCaseFromIntVals "/intov/nan-via-program" #[.nan],
    mkCaseFromIntVals "/intov/nan-via-program-with-tail" #[.num 77, .nan],
    mkCaseFromIntVals "/error-order/pushint-overflow-high-before-op" #[.num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-high-before-op-with-tail"
      #[.num 11, .num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-low-before-op" #[.num (minInt257 - 1)],
    mkCase "/underflow/empty" #[],
    mkCase "/type/top-null" #[.null],
    mkCase "/type/top-cell" #[.cell Cell.empty],
    mkCase "/error-order/top-null-below-int-type-first" #[intV (-8), .null],
    mkCase "/pop-order/top-int-below-null-untouched" #[.null, intV (-8)],
    mkCase "/gas/exact-cost-succeeds" #[intV (-7)]
      #[.pushInt (.num absSetGasExact), .tonEnvOp .setGasLimit, absInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV (-7)]
      #[.pushInt (.num absSetGasExactMinusOne), .tonEnvOp .setGasLimit, absInstr]
  ]
  fuzz := #[
    { seed := 2026020888
      count := 650
      gen := genAbsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ABS
