import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MIN

/-
MIN branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Min.lean`
  - `TvmLean/Model/Value/IntVal.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_minmax`, opcode wiring in `register_other_arith_ops` for MIN mode=2).

Branch counts used for this suite:
- Lean: 8 branch points / 8 terminal outcomes
  (opcode dispatch; explicit `checkUnderflow 2`; two `popInt` type checks;
   `IntVal.min` finite-vs-NaN and `≤` split; `pushIntQuiet` NaN-vs-num and signed-257 fit check).
- C++: 6 branch points / 8 aligned terminal outcomes
  (MIN registration to `exec_minmax(mode=2)`; underflow guard; two `pop_int` type checks;
   NaN validity fold + compare/swap; `push_int_quiet` signed-257 fit check).

Terminal outcomes covered by oracle:
- success (finite in-range result),
- `stkUnd`,
- `typeChk` (top-pop and second-pop ordering),
- `intOv` from NaN propagation,
- `intOv` from out-of-range numeric result at push,
- `outOfGas` at exact-minus-one gas boundary.

Key risk areas:
- pop order (top first) controls error-ordering for mixed-type inputs;
- underflow must precede type checks for single-item stacks;
- non-quiet MIN must throw `intOv` on NaN (never push NaN);
- range check applies to the selected result only (out-of-range inputs can still succeed);
- signed-257 edge behavior when the selected minimum lies outside `[-2^256, 2^256-1]`;
- deterministic gas boundaries for `PUSHINT n; SETGASLIMIT; MIN`.
-/

private def minId : InstrId := { name := "MIN" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.min])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := minId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMinDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMin .min stack

private def minSetGasExact : Int :=
  computeExactGasBudget .min

private def minSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .min

private def genMinFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  let ((x, y), rng2) :=
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
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else if shape = 5 then
      let (y0, r2) := pickSigned257ish rng1
      ((0, y0), r2)
    else
      let (x0, r2) := pickSigned257ish rng1
      ((x0, x0), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := minId
  unit := #[
    { name := "unit/ok/sign-zero-and-equality"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 3),
            (7, -3, -3),
            (-7, 3, -7),
            (-7, -3, -7),
            (123, 0, 0),
            (0, 123, 0),
            (17, 17, 17),
            (-17, -17, -17),
            (maxInt257, minInt257, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"min({x},{y})" (runMinDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/boundary/near-edges-and-unselected-out-of-range"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, maxInt257 - 1, maxInt257 - 1),
            (minInt257, minInt257 + 1, minInt257),
            (maxInt257 - 1, maxInt257, maxInt257 - 1),
            (minInt257 + 1, minInt257 + 2, minInt257 + 1),
            (maxInt257 + 1, -5, -5),
            (5, maxInt257 + 1, 5)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"min({x},{y})" (runMinDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error/intov-from-nan-and-out-of-range-result"
      run := do
        expectErr "nan-left" (runMinDirect #[.int .nan, intV 1]) .intOv
        expectErr "nan-right" (runMinDirect #[intV 1, .int .nan]) .intOv
        expectErr "both-high-out-of-range" (runMinDirect #[intV (maxInt257 + 2), intV (maxInt257 + 1)]) .intOv
        expectErr "both-low-out-of-range" (runMinDirect #[intV (minInt257 - 2), intV (minInt257 - 1)]) .intOv
        expectErr "selected-low-out-of-range" (runMinDirect #[intV (minInt257 - 1), intV 0]) .intOv }
    ,
    { name := "unit/error-order/underflow-and-pop-type-ordering"
      run := do
        expectErr "underflow-empty" (runMinDirect #[]) .stkUnd
        expectErr "underflow-one-int" (runMinDirect #[intV 1]) .stkUnd
        expectErr "type-pop-top-first" (runMinDirect #[intV 1, .null]) .typeChk
        expectErr "type-pop-second" (runMinDirect #[.null, intV 1]) .typeChk
        expectErr "type-both-non-int-top-first" (runMinDirect #[.cell Cell.empty, .null]) .typeChk }
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
    mkCase "boundary/out-of-range-unselected/high-x-selected-y" #[]
      #[.pushInt (.num (maxInt257 + 1)), .pushInt (.num (-5)), .min],
    mkCase "boundary/out-of-range-unselected/high-y-selected-x" #[]
      #[.pushInt (.num 5), .pushInt (.num (maxInt257 + 1)), .min],
    mkCase "overflow/out-of-range-result/both-high" #[]
      #[.pushInt (.num (maxInt257 + 2)), .pushInt (.num (maxInt257 + 1)), .min],
    mkCase "overflow/out-of-range-result/both-low" #[]
      #[.pushInt (.num (minInt257 - 2)), .pushInt (.num (minInt257 - 1)), .min],
    mkCase "overflow/out-of-range-result/selected-low" #[]
      #[.pushInt (.num (minInt257 - 1)), .pushInt (.num 0), .min],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-top-null" #[intV 1, .null],
    mkCase "type/pop-second-null" #[.null, intV 1],
    mkCase "type/pop-top-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-top-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num minSetGasExact), .tonEnvOp .setGasLimit, .min],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num minSetGasExactMinusOne), .tonEnvOp .setGasLimit, .min],
    mkCase "nan/pushnan-top-propagates-intov" #[intV 42] #[.pushInt .nan, .min],
    mkCase "nan/pushnan-second-propagates-intov" #[intV 42] #[.pushInt .nan, .xchg0 1, .min]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 500
      gen := genMinFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MIN
