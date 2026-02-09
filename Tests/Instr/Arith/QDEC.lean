import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QDEC

/-
QDEC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Qdec.lean` (`execInstrArithQdec`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_dec`, `QDEC` wiring in `register_add_mul_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 5 branch points / 6 terminal outcomes
  (opcode dispatch; stack pop underflow; top-item type check; `IntVal.dec` num-vs-NaN;
   quiet push split: in-range num vs overflow-to-NaN vs NaN passthrough).
- C++: 5 branch points / 6 aligned terminal outcomes
  (`QDEC` dispatch to `exec_dec(..., quiet=true)`; `check_underflow(1)`;
   `pop_int` type check; `push_int_quiet` in-range vs overflow vs NaN).

Key risk areas covered:
- quiet overflow at `minInt257 - 1` must push NaN (not throw `intOv`);
- quiet NaN input propagation must stay successful;
- underflow/type ordering for unary pop (`empty` vs `one non-int`);
- signed-257 boundary off-by-one around `minInt257 + 1` / `maxInt257`;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QDEC`.
-/

private def qdecId : InstrId := { name := "QDEC" }

private def qdecInstr : Instr := .qdec

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qdecInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qdecId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qdecInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQdecDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQdec qdecInstr stack

private def runQdecDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQdec .dec (VM.push (intV 5051)) stack

private def qdecSetGasExact : Int :=
  computeExactGasBudget qdecInstr

private def qdecSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qdecInstr

private def genQdecFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-random" #[intV x], r2)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x], r2)
    else if shape = 2 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow-min-to-nan" #[intV minInt257], rng1)
    else if shape = 3 then
      (mkCase s!"fuzz/shape-{shape}/ok-near-min-plus-one" #[intV (minInt257 + 1)], rng1)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/ok-near-max" #[intV maxInt257], rng1)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-tail-preserved" #[intV 9, intV x], r2)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/type-top-null" #[.null], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/type-top-cell" #[.cell Cell.empty], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/type-top-null-with-tail" #[intV 7, .null], rng1)
    else if shape = 10 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-via-program" #[.nan], rng1)
    else
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan-via-program-with-tail"
        #[.num 42, .nan], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qdecId
  unit := #[
    { name := "unit/ok/finite-sign-zero-and-boundaries"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, -1),
            (1, 0),
            (17, 16),
            (-1, -2),
            (-17, -18),
            (maxInt257, maxInt257 - 1),
            (minInt257 + 1, minInt257),
            (minInt257 + 2, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"{x}-1" (runQdecDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/ok/quiet-overflow-and-nan-become-nan"
      run := do
        expectOkStack "quiet-overflow/min-to-nan" (runQdecDirect #[intV minInt257]) #[.int .nan]
        expectOkStack "quiet-nan-input" (runQdecDirect #[.int .nan]) #[.int .nan] }
    ,
    { name := "unit/ok/tail-preserved"
      run := do
        expectOkStack "tail-kept" (runQdecDirect #[intV 99, intV 0]) #[intV 99, intV (-1)] }
    ,
    { name := "unit/error/underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runQdecDirect #[]) .stkUnd
        expectErr "type/top-null" (runQdecDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runQdecDirect #[.cell Cell.empty]) .typeChk
        expectErr "error-order/top-null-with-tail" (runQdecDirect #[intV 7, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qdec-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQdecDispatchFallback #[]) #[intV 5051] }
  ]
  oracle := #[
    mkCase "ok/zero-to-neg-one" #[intV 0],
    mkCase "ok/positive-to-prev" #[intV 17],
    mkCase "ok/negative-to-prev" #[intV (-17)],
    mkCase "ok/finite-with-tail" #[intV 3, intV 1],
    mkCase "boundary/max-to-max-minus-one" #[intV maxInt257],
    mkCase "boundary/min-plus-one-to-min" #[intV (minInt257 + 1)],
    mkCase "boundary/min-plus-two-to-min-plus-one" #[intV (minInt257 + 2)],
    mkCase "quiet-overflow/min-to-nan" #[intV minInt257],
    mkCaseFromIntVals "quiet-nan/pushnan-via-program" #[.nan],
    mkCaseFromIntVals "quiet-nan/pushnan-via-program-with-tail" #[.num 42, .nan],
    mkCase "underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-null-with-tail" #[intV 7, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num qdecSetGasExact), .tonEnvOp .setGasLimit, qdecInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num qdecSetGasExactMinusOne), .tonEnvOp .setGasLimit, qdecInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 600
      gen := genQdecFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QDEC
