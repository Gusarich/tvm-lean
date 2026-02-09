import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QNEGATE

/-
QNEGATE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Qnegate.lean` (`execInstrArithQnegate`)
  - `TvmLean/Semantics/Exec/Arith.lean` (handler dispatch chain)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (opcode `0xb7a3` decode)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_negate`, opcode wiring in `register_add_mul_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 4 branch points / 6 terminal outcomes
  (opcode dispatch; `popInt` underflow/type/success; `IntVal` NaN-vs-num split;
   quiet `pushIntQuiet` signed-257 fit split on numeric negation).
- C++: 4 branch points / 6 aligned terminal outcomes
  (`QNEGATE` binds `exec_negate(..., quiet=true)`; `check_underflow(1)`;
   `pop_int` type check; `push_int_quiet` finite success vs quiet-NaN outcomes).

Mapped terminal outcomes covered:
- success with finite result;
- success with NaN from NaN input;
- success with NaN from signed-257 overflow (`-minInt257`);
- `stkUnd`;
- `typeChk`;
- non-matching dispatch fallthrough to `next`.

Key risk areas covered:
- quiet-mode overflow/NaN must push NaN (never throw `intOv`);
- pop/error ordering: underflow before type, and only top operand is consumed;
- signed-257 boundary behavior (`minInt257`, neighbors, `maxInt257`);
- exact gas boundary behavior for `PUSHINT n; SETGASLIMIT; QNEGATE`.
-/

private def qnegateId : InstrId := { name := "QNEGATE" }

private def qnegateInstr : Instr := .qnegate

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qnegateInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qnegateId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qnegateInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQnegateDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQnegate qnegateInstr stack

private def runQnegateDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQnegate .negate (VM.push (intV 905)) stack

private def qnegateSetGasExact : Int :=
  computeExactGasBudget qnegateInstr

private def qnegateSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qnegateInstr

private def genQnegateFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
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
      let (x0, r2) := pickInt257Boundary rng1
      let x :=
        if x0 = minInt257 then minInt257 + 1
        else if x0 = maxInt257 then maxInt257 - 1
        else x0
      (mkCase s!"fuzz/shape-{shape}/ok-near-boundary" #[intV x], r2)
    else if shape = 4 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-via-program" #[IntVal.nan], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/type-top-null" #[.null], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/type-top-cell" #[.cell Cell.empty], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-top-int-below-null" #[.null, intV x], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-top-null-below-int" #[intV x, .null], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-top-cell-below-int" #[intV x, .cell Cell.empty], r2)
    else
      let (x0, r2) := pickSigned257ish rng1
      let x := if x0 = minInt257 then minInt257 + 1 else x0
      (mkCase s!"fuzz/shape-{shape}/ok-safe-random" #[intV x], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qnegateId
  unit := #[
    { name := "unit/direct/finite-sign-zero-and-boundary"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, 0),
            (17, -17),
            (-17, 17),
            (maxInt257, -(maxInt257)),
            (maxInt257 - 1, -(maxInt257 - 1)),
            (minInt257 + 1, maxInt257),
            (minInt257 + 2, maxInt257 - 1)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"negate {x}" (runQnegateDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-overflow-and-nan-push-nan"
      run := do
        expectOkStack "min-overflow->nan" (runQnegateDirect #[intV minInt257]) #[.int .nan]
        expectOkStack "nan->nan" (runQnegateDirect #[.int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQnegateDirect #[]) .stkUnd
        expectErr "type/top-null" (runQnegateDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runQnegateDirect #[.cell Cell.empty]) .typeChk
        expectErr "error-order/top-null-below-cell" (runQnegateDirect #[.cell Cell.empty, .null]) .typeChk
        expectOkStack "error-order/top-int-below-null-untouched"
          (runQnegateDirect #[.null, intV 9]) #[.null, intV (-9)] }
    ,
    { name := "unit/dispatch/non-qnegate-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQnegateDispatchFallback #[]) #[intV 905] }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/positive" #[intV 23],
    mkCase "ok/negative" #[intV (-23)],
    mkCase "boundary/max-int257" #[intV maxInt257],
    mkCase "boundary/min-plus-one" #[intV (minInt257 + 1)],
    mkCase "near-boundary/max-minus-one" #[intV (maxInt257 - 1)],
    mkCase "near-boundary/min-plus-two" #[intV (minInt257 + 2)],
    mkCase "quiet-overflow/min-int257-pushes-nan" #[intV minInt257],
    mkCase "underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-non-int-with-below-non-int" #[.cell Cell.empty, .null],
    mkCase "error-order/top-int-below-non-int-untouched" #[.null, intV 9],
    mkCaseFromIntVals "nan/operand-via-program" #[IntVal.nan],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num qnegateSetGasExact), .tonEnvOp .setGasLimit, qnegateInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num qnegateSetGasExactMinusOne), .tonEnvOp .setGasLimit, qnegateInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 600
      gen := genQnegateFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QNEGATE
