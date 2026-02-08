import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADD

/-
ADD branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Add.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_add`, opcode registration in `register_add_mul_ops`).

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (opcode dispatch; two `popInt` failure points; `IntVal.add` finite-vs-NaN;
   `pushIntQuiet` NaN-vs-num and signed-257 fit check).
- C++: 5 branch points / 8 aligned terminal outcomes
  (registration binds ADD to `exec_add(..., quiet=false)`; underflow check;
   two `pop_int` type checks; `push_int_quiet` signed-257 fit check with non-quiet throw).

Key risk areas:
- NaN propagation must fail with `intOv` in non-quiet ADD.
- Signed 257-bit boundary off-by-one (`[-2^256, 2^256-1]`).
- Operand pop order (`y` then `x`) changes which type-check path is hit first.
- Zero/sign combinations should not regress around boundary-adjacent values.
- Gas-boundary checks should be deterministic in both Lean and `runvmx`
  (`PUSHINT n; SETGASLIMIT; ADD` with exact and exact-minus-one budgets).
-/

private def addId : InstrId := { name := "ADD" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.add])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := addId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAddDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithAdd .add stack

private def addSetGasExact : Int :=
  computeExactGasBudget .add

private def addSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .add

private def genAddFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  let ((x, y), rng3) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else
      let (y0, r2) := pickSigned257ish rng1
      ((0, y0), r2)
  (mkCase s!"fuzz/shape-{shape}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := addId
  unit := #[
    { name := "unit/finite-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, -3, 4),
            (-7, 3, -4),
            (-9, -11, -20),
            (0, 123, 123),
            (123, 0, 123),
            (maxInt257, minInt257, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}+{y}" (runAddDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/near-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, -1, maxInt257 - 1),
            (minInt257, 1, minInt257 + 1),
            (maxInt257 - 1, 1, maxInt257),
            (minInt257 + 1, -1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}+{y}" (runAddDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/overflow-boundaries-throw-intov"
      run := do
        expectErr "max+1" (runAddDirect #[intV maxInt257, intV 1]) .intOv
        expectErr "min-1" (runAddDirect #[intV minInt257, intV (-1)]) .intOv }
    ,
    { name := "unit/nan-and-pop-order-type-errors"
      run := do
        expectErr "nan+1" (runAddDirect #[.int .nan, intV 1]) .intOv
        expectErr "pop-y-first" (runAddDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second" (runAddDirect #[.null, intV 1]) .typeChk }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "ok/pos-pos" #[intV 17, intV 25],
    mkCase "ok/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/neg-neg" #[intV (-17), intV (-5)],
    mkCase "ok/zero-right" #[intV 222, intV 0],
    mkCase "ok/zero-left" #[intV 0, intV 222],
    mkCase "ok/max-plus-zero" #[intV maxInt257, intV 0],
    mkCase "ok/min-plus-zero" #[intV minInt257, intV 0],
    mkCase "ok/max-plus-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/min-plus-one" #[intV minInt257, intV 1],
    mkCase "ok/max-minus-one-plus-one" #[intV (maxInt257 - 1), intV 1],
    mkCase "ok/min-plus-one-plus-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/max-plus-min" #[intV maxInt257, intV minInt257],
    mkCase "overflow/max-plus-one" #[intV maxInt257, intV 1],
    mkCase "overflow/min-minus-one" #[intV minInt257, intV (-1)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "type/error-order-both-non-int" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num addSetGasExact), .tonEnvOp .setGasLimit, .add],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num addSetGasExactMinusOne), .tonEnvOp .setGasLimit, .add],
    mkCase "nan/pushnan-propagates-intov" #[intV 42] #[.pushInt .nan, .add]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := genAddFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADD
