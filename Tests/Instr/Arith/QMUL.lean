import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMUL

/-
QMUL branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Qmul.lean`
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mul`, opcode binding for `QMUL` in `register_add_mul_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.hpp`
    (`check_underflow`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 7 branch points / 7 terminal outcomes
  (opcode dispatch; explicit `checkUnderflow(2)`; two `popInt` type checks;
   `IntVal.mul` finite-vs-NaN; `pushIntQuiet` NaN-vs-num and signed-257 fit check).
- C++: 6 branch points / 7 aligned terminal outcomes
  (opcode binding to `exec_mul(..., quiet=true)`; `check_underflow`;
   two `pop_int` type checks; bigint validity; quiet push overflow/NaN handling).

Key risk areas:
- Underflow must win over type checks for single-element stacks (`check_underflow(2)` ordering).
- Quiet semantics: NaN inputs and 257-bit overflow must produce NaN (never `intOv`).
- Signed-257 boundary behavior near `[-2^256, 2^256 - 1]` (`min * -1`, `max * 2`).
- Operand pop order (`y` then `x`) determines which type-check branch fires first.
- Exact gas boundary for `PUSHINT n; SETGASLIMIT; QMUL` (exact vs exact-minus-one).
-/

private def qmulId : InstrId := { name := "QMUL" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.qmul])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmulId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runQmulDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQmul .qmul stack

private def runQmulDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQmul .mul (VM.push (intV 777)) stack

private def qmulSetGasExact : Int :=
  computeExactGasBudget .qmul

private def qmulSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .qmul

private def genQmulFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let ((x, y), rng3) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 1), r2)
    else if shape = 5 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, -1), r2)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let (negMul, r3) := randBool r2
      let x0 := if useMax then maxInt257 else minInt257
      let y0 := if negMul then -2 else 2
      ((x0, y0), r3)
    else if shape = 7 then
      let (x0, r2) := pickSigned257ish rng1
      let (useNeg, r3) := randBool r2
      let y0 := if useNeg then -2 else 2
      ((x0, y0), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
  let (tag, rng4) := randNat rng3 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV y], rng4)

def suite : InstrSuite where
  id := qmulId
  unit := #[
    { name := "unit/direct/finite-sign-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 21),
            (7, -3, -21),
            (-7, 3, -21),
            (-7, -3, 21),
            (0, 123, 0),
            (123, 0, 0),
            (maxInt257, 1, maxInt257),
            (minInt257, 1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}*{y}" (runQmulDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/near-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, -1, -maxInt257),
            (minInt257 + 1, -1, maxInt257),
            (maxInt257 - 1, 1, maxInt257 - 1),
            (minInt257 + 1, 1, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}*{y}" (runQmulDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-overflow-yields-nan"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (maxInt257, 2),
            (minInt257, -1),
            (minInt257, 2),
            (maxInt257, -2)
          ]
        for c in checks do
          let x := c.1
          let y := c.2
          expectOkStack s!"{x}*{y}" (runQmulDirect #[intV x, intV y]) #[.int .nan] }
    ,
    { name := "unit/direct/error-order-underflow-and-type"
      run := do
        expectErr "underflow/empty" (runQmulDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runQmulDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int-before-type" (runQmulDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQmulDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQmulDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-y-first" (runQmulDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-qmul-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmulDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "ok/pos-pos" #[intV 17, intV 25],
    mkCase "ok/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/neg-neg" #[intV (-17), intV (-5)],
    mkCase "ok/zero-right" #[intV 222, intV 0],
    mkCase "ok/zero-left" #[intV 0, intV 222],
    mkCase "ok/max-times-zero" #[intV maxInt257, intV 0],
    mkCase "ok/min-times-zero" #[intV minInt257, intV 0],
    mkCase "ok/max-times-one" #[intV maxInt257, intV 1],
    mkCase "ok/min-times-one" #[intV minInt257, intV 1],
    mkCase "ok/max-times-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/min-plus-one-times-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/max-minus-one-times-one" #[intV (maxInt257 - 1), intV 1],
    mkCase "ok/min-plus-one-times-one" #[intV (minInt257 + 1), intV 1],
    mkCase "overflow/max-times-two-quiet-nan" #[intV maxInt257, intV 2],
    mkCase "overflow/min-times-neg-one-quiet-nan" #[intV minInt257, intV (-1)],
    mkCase "overflow/min-times-two-quiet-nan" #[intV minInt257, intV 2],
    mkCase "overflow/max-times-neg-two-quiet-nan" #[intV maxInt257, intV (-2)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/single-non-int-order" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qmulSetGasExact), .tonEnvOp .setGasLimit, .qmul],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qmulSetGasExactMinusOne), .tonEnvOp .setGasLimit, .qmul],
    mkCase "nan/y-via-pushnan" #[intV 42] #[.pushInt .nan, .qmul],
    mkCase "nan/x-via-pushnan" #[intV 42] #[.pushInt .nan, .xchg0 1, .qmul]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 600
      gen := genQmulFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMUL
