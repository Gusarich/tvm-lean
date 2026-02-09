import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QSUB

/-
QSUB branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Qsub.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_sub`, opcode wiring in `register_add_mul_ops` for `QSUB` with `quiet=true`).

Branch counts used for this suite:
- Lean: 7 branch points / 7 terminal outcomes
  (opcode dispatch; underflow guard; two `popInt` type checks; `IntVal.sub` finite-vs-NaN;
   `pushIntQuiet` quiet NaN-vs-num and signed-257 fit split).
- C++: 5 branch points / 7 aligned terminal outcomes
  (registration to `exec_sub(..., quiet=true)`; underflow guard; two `pop_int` checks;
   `push_int_quiet` finite vs NaN/overflow in quiet mode).

Key risk areas:
- underflow must be checked before type checks on singleton stacks (C++ `check_underflow(2)` parity);
- pop order is `y` then `x`, so type-error ordering must match oracle;
- quiet behavior: NaN inputs and signed-257 overflow results must push NaN (not throw);
- signed 257-bit boundary off-by-one around `[-2^256, 2^256-1]`;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QSUB`.
-/

private def qsubId : InstrId := { name := "QSUB" }

private def qsubInstr : Instr := .qsub

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qsubInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qsubId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qsubInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQsubDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQsub qsubInstr stack

private def runQsubDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQsub .add (VM.push (intV 31337)) stack

private def qsubSetGasExact : Int :=
  computeExactGasBudget qsubInstr

private def qsubSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qsubInstr

private def genQsubFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-left" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-right" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-both" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-random" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow-high" #[intV maxInt257, intV (-1)], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow-low" #[intV minInt257, intV 1], rng1)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-y-zero" #[intV x, intV 0], r2)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-x-zero" #[intV 0, intV y], r2)
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
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-x-via-program" #[.nan, .num y], r2)
    else
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-both-via-program" #[.nan, .nan], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qsubId
  unit := #[
    { name := "unit/ok/finite-sign-zero-and-near-boundary"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 4),
            (7, -3, 10),
            (-7, 3, -10),
            (-7, -3, -4),
            (0, 123, -123),
            (123, 0, 123),
            (maxInt257, 1, maxInt257 - 1),
            (minInt257, -1, minInt257 + 1),
            (maxInt257 - 1, -1, maxInt257),
            (minInt257 + 1, 1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}-{y}" (runQsubDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/ok/quiet-overflow-and-nan-produce-nan"
      run := do
        expectOkStack "quiet-overflow/max-minus-neg-one" (runQsubDirect #[intV maxInt257, intV (-1)]) #[.int .nan]
        expectOkStack "quiet-overflow/min-minus-one" (runQsubDirect #[intV minInt257, intV 1]) #[.int .nan]
        expectOkStack "quiet-overflow/max-minus-min" (runQsubDirect #[intV maxInt257, intV minInt257]) #[.int .nan]
        expectOkStack "quiet-overflow/min-minus-max" (runQsubDirect #[intV minInt257, intV maxInt257]) #[.int .nan]
        expectOkStack "quiet-nan/x" (runQsubDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "quiet-nan/y" (runQsubDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "quiet-nan/both" (runQsubDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-on-short-stacks"
      run := do
        expectErr "empty-underflow" (runQsubDirect #[]) .stkUnd
        expectErr "one-int-underflow" (runQsubDirect #[intV 1]) .stkUnd
        expectErr "one-non-int-underflow-first" (runQsubDirect #[.null]) .stkUnd }
    ,
    { name := "unit/error/type-order-on-two-args"
      run := do
        expectErr "type/pop-y-first-null" (runQsubDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQsubDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQsubDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQsubDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "type/both-non-int-pop-y-first" (runQsubDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qsub-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQsubDispatchFallback #[]) #[intV 31337] }
  ]
  oracle := #[
    mkCase "ok/finite/zero-zero" #[intV 0, intV 0],
    mkCase "ok/finite/pos-pos" #[intV 17, intV 5],
    mkCase "ok/finite/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/finite/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/finite/neg-neg" #[intV (-17), intV (-5)],
    mkCase "ok/finite/zero-right" #[intV 222, intV 0],
    mkCase "ok/finite/zero-left" #[intV 0, intV 222],
    mkCase "boundary/in-range/max-minus-zero" #[intV maxInt257, intV 0],
    mkCase "boundary/in-range/min-minus-zero" #[intV minInt257, intV 0],
    mkCase "boundary/in-range/max-minus-one" #[intV maxInt257, intV 1],
    mkCase "boundary/in-range/min-minus-neg-one" #[intV minInt257, intV (-1)],
    mkCase "boundary/in-range/max-near-minus-neg-one" #[intV (maxInt257 - 1), intV (-1)],
    mkCase "boundary/in-range/min-near-minus-one" #[intV (minInt257 + 1), intV 1],
    mkCase "quiet-overflow/max-minus-neg-one-becomes-nan" #[intV maxInt257, intV (-1)],
    mkCase "quiet-overflow/min-minus-one-becomes-nan" #[intV minInt257, intV 1],
    mkCase "quiet-overflow/max-minus-min-becomes-nan" #[intV maxInt257, intV minInt257],
    mkCase "quiet-overflow/min-minus-max-becomes-nan" #[intV minInt257, intV maxInt257],
    mkCaseFromIntVals "quiet-nan/pushnan-y-via-program" #[.num 42, .nan],
    mkCaseFromIntVals "quiet-nan/pushnan-x-via-program" #[.nan, .num 42],
    mkCaseFromIntVals "quiet-nan/double-pushnan-via-program" #[.nan, .nan],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qsubSetGasExact), .tonEnvOp .setGasLimit, qsubInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qsubSetGasExactMinusOne), .tonEnvOp .setGasLimit, qsubInstr]
  ]
  fuzz := #[
    { seed := 2026020809
      count := 600
      gen := genQsubFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QSUB
