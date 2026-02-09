import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QABS

/-
QABS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Abs.lean` (`execInstrArithAbs`)
  - `TvmLean/Semantics/Exec/Arith.lean` (dispatch chain includes `execInstrArithAbs`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7b60b` decodes to `.abs true`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_abs`, `register_other_arith_ops` wiring for `QABS`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 5 branch points / 7 terminal outcomes
  (handler dispatch; pop underflow/type/success; NaN-vs-num split; sign split for nums;
   quiet push split: in-range num vs overflow/out-of-range-to-NaN vs NaN passthrough).
- C++: 5 branch points / 7 aligned terminal outcomes
  (`QABS` bound to `exec_abs(..., quiet=true)`; underflow/type checks in `pop_int`;
   `x->is_valid() && x->sgn() < 0` sign branch; `push_int_quiet` finite vs quiet-NaN).

Mapped terminal outcomes covered:
- finite success for positive/negative/zero and boundary neighbors;
- quiet NaN from `minInt257` overflow;
- quiet NaN passthrough from `PUSHINT .nan`;
- quiet NaN from out-of-range integer injected via `PUSHINT n`;
- `stkUnd`;
- `typeChk`;
- non-matching dispatch falls through to `next`.

Key risk areas covered:
- unary error ordering: underflow before type on empty stack; type from top element first;
- only top operand is consumed, lower stack tail remains untouched on success;
- signed-257 boundary behavior around `minInt257`, `minInt257 + 1`, `maxInt257`;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QABS` (exact vs exact-minus-one).
-/

private def qabsId : InstrId := { name := "QABS" }

private def qabsInstr : Instr := .abs true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qabsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qabsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qabsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQabsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithAbs qabsInstr stack

private def runQabsDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithAbs .negate (VM.push (intV 4242)) stack

private def qabsSetGasExact : Int :=
  computeExactGasBudget qabsInstr

private def qabsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qabsInstr

private def genQabsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-random" #[intV x], r2)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x], r2)
    else if shape = 2 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow-min-int257" #[intV minInt257], rng1)
    else if shape = 3 then
      (mkCase s!"fuzz/shape-{shape}/ok-near-min-plus-one" #[intV (minInt257 + 1)], rng1)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/ok-near-min-plus-two" #[intV (minInt257 + 2)], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/type-top-null" #[.null], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/type-top-cell" #[.cell Cell.empty], rng1)
    else if shape = 8 then
      let (x0, r2) := pickSigned257ish rng1
      let x := if x0 = minInt257 then minInt257 + 1 else x0
      (mkCase s!"fuzz/shape-{shape}/error-order-top-int-below-null-untouched" #[.null, intV x], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-top-null-below-int-type-first" #[intV x, .null], r2)
    else if shape = 10 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-via-program" #[.nan], rng1)
    else if shape = 11 then
      let (delta, r2) := randNat rng1 1 64
      let n := maxInt257 + Int.ofNat delta
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-range-high-via-program" #[.num n], r2)
    else if shape = 12 then
      let (delta, r2) := randNat rng1 1 64
      let n := minInt257 - Int.ofNat delta
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-range-low-via-program" #[.num n], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-tail-int-below-top-int" #[intV 11, intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-max-neighbor" #[intV (if x = maxInt257 then maxInt257 - 1 else x)], r2)
    else
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-via-program-with-tail" #[.num 77, .nan], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qabsId
  unit := #[
    { name := "unit/ok/finite-sign-zero-and-boundary"
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
          expectOkStack s!"abs/{x}" (runQabsDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/ok/quiet-overflow-min-int257-to-nan"
      run := do
        expectOkStack "overflow/min-int257" (runQabsDirect #[intV minInt257]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-top-pop-order"
      run := do
        expectErr "underflow/empty" (runQabsDirect #[]) .stkUnd
        expectErr "type/top-null" (runQabsDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runQabsDirect #[.cell Cell.empty]) .typeChk
        expectErr "error-order/top-null-below-int-type-first" (runQabsDirect #[intV (-8), .null]) .typeChk
        expectOkStack "error-order/top-int-below-null-untouched"
          (runQabsDirect #[.null, intV (-8)]) #[.null, intV 8] }
    ,
    { name := "unit/dispatch/non-qabs-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQabsDispatchFallback #[]) #[intV 4242] }
  ]
  oracle := #[
    mkCase "ok/finite/zero" #[intV 0],
    mkCase "ok/finite/positive" #[intV 23],
    mkCase "ok/finite/negative" #[intV (-23)],
    mkCase "ok/finite/with-tail" #[intV 9, intV (-2)],
    mkCase "boundary/in-range/max-int257" #[intV maxInt257],
    mkCase "boundary/in-range/min-plus-one" #[intV (minInt257 + 1)],
    mkCase "boundary/in-range/min-plus-two" #[intV (minInt257 + 2)],
    mkCase "quiet-overflow/min-int257-to-nan" #[intV minInt257],
    mkCaseFromIntVals "quiet-nan/via-program" #[.nan],
    mkCaseFromIntVals "quiet-nan/via-program-with-tail" #[.num 77, .nan],
    mkCaseFromIntVals "quiet-range/high-via-program" #[.num (maxInt257 + 1)],
    mkCaseFromIntVals "quiet-range/low-via-program" #[.num (minInt257 - 1)],
    mkCase "underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-null-below-int-type-first" #[intV (-8), .null],
    mkCase "error-order/top-int-below-null-untouched" #[.null, intV (-8)],
    mkCase "gas/exact-cost-succeeds" #[intV (-7)]
      #[.pushInt (.num qabsSetGasExact), .tonEnvOp .setGasLimit, qabsInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV (-7)]
      #[.pushInt (.num qabsSetGasExactMinusOne), .tonEnvOp .setGasLimit, qabsInstr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 600
      gen := genQabsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QABS
