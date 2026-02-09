import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QSUBR

/-
QSUBR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Qsubr.lean`
  - `TvmLean/Semantics/Exec/Common.lean` (`checkUnderflow`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_subr`, opcode wiring in `register_add_mul_ops` for `QSUBR` with `quiet=true`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 7 branch points / 7 terminal outcomes
  (opcode dispatch; explicit underflow guard; two `popInt` type checks; `IntVal.sub`
   finite-vs-NaN; `pushIntQuiet` quiet NaN-vs-num and signed-257 fit split).
- C++: 5 branch points / 7 aligned terminal outcomes
  (registration to `exec_subr(..., quiet=true)`; `check_underflow(2)`; two `pop_int`
   type checks; `push_int_quiet` finite vs NaN/overflow in quiet mode).

Lean-vs-C++ mismatch fixed for this task:
- Lean previously missed the C++-equivalent pre-pop `check_underflow(2)` in QSUBR,
  which could surface `typeChk` on singleton non-int stacks instead of `stkUnd`.
  The handler now checks underflow first.

Key risk areas:
- reverse operand order must remain `y - x` (not `x - y`);
- underflow must be checked before any per-operand type checks;
- pop order (`y` first, then `x`) determines type-error ordering;
- quiet behavior: NaN inputs and signed-257 overflow must push NaN, not throw;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QSUBR`.
-/

private def qsubrId : InstrId := { name := "QSUBR" }

private def qsubrInstr : Instr := .qsubr

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qsubrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qsubrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qsubrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQsubrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQsubr qsubrInstr stack

private def runQsubrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQsubr .add (VM.push (intV 424242)) stack

private def qsubrSetGasExact : Int :=
  computeExactGasBudget qsubrInstr

private def qsubrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qsubrInstr

private def genQsubrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-left" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-right" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-both" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/random" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/high" #[intV (-1), intV maxInt257], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/low" #[intV 1, intV minInt257], rng1)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/y-zero" #[intV x, intV 0], r2)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/x-zero" #[intV 0, intV y], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-first" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, .null], r2)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[.null, intV y], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/y-via-program" #[.num x, .nan], r2)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/x-via-program" #[.nan, .num y], r2)
    else
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet-nan/both-via-program" #[.nan, .nan], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qsubrId
  unit := #[
    { name := "unit/ok/reverse-subtraction-sign-zero-and-boundary"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (3, 10, 7),
            (10, 3, -7),
            (-7, 3, 10),
            (7, -3, -10),
            (-9, -11, -2),
            (0, 123, 123),
            (123, 0, -123),
            (1, maxInt257, maxInt257 - 1),
            (-1, minInt257, minInt257 + 1),
            (1, minInt257 + 1, minInt257),
            (-1, maxInt257 - 1, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{y}-{x}" (runQsubrDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/ok/quiet-overflow-and-nan-produce-nan"
      run := do
        expectOkStack "quiet-overflow/max-minus-neg-one" (runQsubrDirect #[intV (-1), intV maxInt257]) #[.int .nan]
        expectOkStack "quiet-overflow/min-minus-one" (runQsubrDirect #[intV 1, intV minInt257]) #[.int .nan]
        expectOkStack "quiet-overflow/max-minus-min" (runQsubrDirect #[intV minInt257, intV maxInt257]) #[.int .nan]
        expectOkStack "quiet-overflow/min-minus-max" (runQsubrDirect #[intV maxInt257, intV minInt257]) #[.int .nan]
        expectOkStack "quiet-nan/y" (runQsubrDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "quiet-nan/x" (runQsubrDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "quiet-nan/both" (runQsubrDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-on-short-stacks"
      run := do
        expectErr "empty-underflow" (runQsubrDirect #[]) .stkUnd
        expectErr "one-int-underflow" (runQsubrDirect #[intV 1]) .stkUnd
        expectErr "one-non-int-underflow-first" (runQsubrDirect #[.null]) .stkUnd
        expectErr "one-cell-underflow-first" (runQsubrDirect #[.cell Cell.empty]) .stkUnd }
    ,
    { name := "unit/error/type-order-on-two-args"
      run := do
        expectErr "type/pop-y-first-null" (runQsubrDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQsubrDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQsubrDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQsubrDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "type/both-non-int-pop-y-first" (runQsubrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qsubr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQsubrDispatchFallback #[]) #[intV 424242] }
  ]
  oracle := #[
    mkCase "ok/finite/zero-zero" #[intV 0, intV 0],
    mkCase "ok/finite/pos-pos" #[intV 5, intV 17],
    mkCase "ok/finite/pos-neg" #[intV 5, intV (-17)],
    mkCase "ok/finite/neg-pos" #[intV (-5), intV 17],
    mkCase "ok/finite/neg-neg" #[intV (-5), intV (-17)],
    mkCase "ok/finite/zero-right" #[intV 222, intV 0],
    mkCase "ok/finite/zero-left" #[intV 0, intV 222],
    mkCase "boundary/in-range/max-minus-zero" #[intV 0, intV maxInt257],
    mkCase "boundary/in-range/min-minus-zero" #[intV 0, intV minInt257],
    mkCase "boundary/in-range/max-minus-one" #[intV 1, intV maxInt257],
    mkCase "boundary/in-range/min-minus-neg-one" #[intV (-1), intV minInt257],
    mkCase "boundary/in-range/min-plus-one-to-min" #[intV 1, intV (minInt257 + 1)],
    mkCase "boundary/in-range/max-minus-one-to-max" #[intV (-1), intV (maxInt257 - 1)],
    mkCase "quiet-overflow/max-minus-neg-one-becomes-nan" #[intV (-1), intV maxInt257],
    mkCase "quiet-overflow/min-minus-one-becomes-nan" #[intV 1, intV minInt257],
    mkCase "quiet-overflow/max-minus-min-becomes-nan" #[intV minInt257, intV maxInt257],
    mkCase "quiet-overflow/min-minus-max-becomes-nan" #[intV maxInt257, intV minInt257],
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
      #[.pushInt (.num qsubrSetGasExact), .tonEnvOp .setGasLimit, qsubrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qsubrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qsubrInstr]
  ]
  fuzz := #[
    { seed := 2026020810
      count := 600
      gen := genQsubrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QSUBR
