import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MINMAX

/-
MINMAX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Minmax.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_minmax`, opcode wiring in `register_other_arith_ops` for MINMAX mode=6).

Branch counts used for this suite:
- Lean: 9 branch points / 10 terminal outcomes
  (opcode dispatch; explicit `checkUnderflow 2`; two `popInt` type checks;
   finite-vs-NaN split; compare/swap split; first and second `pushIntQuiet` NaN/fit splits).
- C++: 7 branch points / 10 aligned terminal outcomes
  (MINMAX registration to `exec_minmax(mode=6)`; underflow guard; two `pop_int` type checks;
   validity fold + compare/swap; first and second `push_int_quiet` fit behavior).

Terminal outcomes covered by oracle:
- success (finite in-range sorted pair),
- `stkUnd`,
- `typeChk` (top-pop and second-pop ordering),
- `intOv` from NaN propagation,
- `intOv` from out-of-range first-push result,
- `intOv` from out-of-range second-push result,
- `outOfGas` at exact-minus-one gas boundary.

Key risk areas:
- pair result order must always be `[min, max]` regardless of input order;
- underflow must win over type checks for singleton stacks;
- top-of-stack pop order controls type-error ordering for mixed/non-int pairs;
- NaN funnels to non-quiet `pushIntQuiet` and must throw `intOv`;
- signed-257 range checks are applied independently to both pushed outputs;
- deterministic gas boundaries for `PUSHINT n; SETGASLIMIT; MINMAX`.
-/

private def minmaxId : InstrId := { name := "MINMAX" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.minmax])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := minmaxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMinmaxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMinmax .minmax stack

private def minmaxSetGasExact : Int :=
  computeExactGasBudget .minmax

private def minmaxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .minmax

private def inSigned257Range (n : Int) : Bool :=
  minInt257 ≤ n && n ≤ maxInt257

private def genMinmaxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
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
      ((x0, x0), r2)
    else if shape = 5 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else if shape = 6 then
      let (y0, r2) := pickSigned257ish rng1
      ((0, y0), r2)
    else if shape = 7 then
      let (y0, r2) := pickSigned257ish rng1
      ((maxInt257 + 1, y0), r2)
    else if shape = 8 then
      let (y0, r2) := pickSigned257ish rng1
      ((minInt257 - 1, y0), r2)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (high, r3) := randBool r2
      if high then
        ((x0, maxInt257 + 1), r3)
      else
        ((x0, minInt257 - 1), r3)
  let xInRange := inSigned257Range x
  let yInRange := inSigned257Range y
  let kind :=
    if !xInRange || !yInRange then
      if x < minInt257 || y < minInt257 then
        "overflow-low"
      else
        "overflow-high"
    else if x = y then
      "equal"
    else if x ≤ y then
      "ordered"
    else
      "reordered"
  let (tag, rng3) := randNat rng2 0 999_999
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.num y]
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" stack (progPrefix.push .minmax), rng3)

def suite : InstrSuite where
  id := minmaxId
  unit := #[
    { name := "unit/ok/pair-order-and-sign-equality"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 3, 3, 7),
            (3, 7, 3, 7),
            (7, -3, -3, 7),
            (-7, 3, -7, 3),
            (-7, -3, -7, -3),
            (17, 17, 17, 17),
            (-17, -17, -17, -17),
            (maxInt257, minInt257, minInt257, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let lo := c.2.2.1
          let hi := c.2.2.2
          expectOkStack s!"minmax({x},{y})" (runMinmaxDirect #[intV x, intV y]) #[intV lo, intV hi] }
    ,
    { name := "unit/boundary/in-range-near-edges"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, maxInt257 - 1, maxInt257 - 1, maxInt257),
            (minInt257, minInt257 + 1, minInt257, minInt257 + 1),
            (maxInt257 - 1, maxInt257, maxInt257 - 1, maxInt257),
            (minInt257 + 1, minInt257 + 2, minInt257 + 1, minInt257 + 2),
            (maxInt257, 0, 0, maxInt257),
            (minInt257, 0, minInt257, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let lo := c.2.2.1
          let hi := c.2.2.2
          expectOkStack s!"minmax-boundary({x},{y})" (runMinmaxDirect #[intV x, intV y]) #[intV lo, intV hi] }
    ,
    { name := "unit/error/intov-from-nan-and-range-overflow"
      run := do
        expectErr "nan-left" (runMinmaxDirect #[.int .nan, intV 1]) .intOv
        expectErr "nan-right" (runMinmaxDirect #[intV 1, .int .nan]) .intOv
        expectErr "both-high-out-of-range" (runMinmaxDirect #[intV (maxInt257 + 2), intV (maxInt257 + 1)]) .intOv
        expectErr "both-low-out-of-range" (runMinmaxDirect #[intV (minInt257 - 2), intV (minInt257 - 1)]) .intOv
        expectErr "first-push-low-out-of-range" (runMinmaxDirect #[intV 0, intV (minInt257 - 1)]) .intOv
        expectErr "second-push-high-out-of-range" (runMinmaxDirect #[intV 0, intV (maxInt257 + 1)]) .intOv }
    ,
    { name := "unit/error-order/underflow-and-pop-type-ordering"
      run := do
        expectErr "underflow-empty" (runMinmaxDirect #[]) .stkUnd
        expectErr "underflow-one-int" (runMinmaxDirect #[intV 1]) .stkUnd
        expectErr "underflow-one-non-int-first" (runMinmaxDirect #[.null]) .stkUnd
        expectErr "type-pop-top-first" (runMinmaxDirect #[intV 1, .null]) .typeChk
        expectErr "type-pop-second" (runMinmaxDirect #[.null, intV 1]) .typeChk
        expectErr "type-both-non-int-top-first" (runMinmaxDirect #[.cell Cell.empty, .null]) .typeChk }
  ]
  oracle := #[
    mkCase "ok/order/ascending" #[intV 3, intV 7],
    mkCase "ok/order/descending" #[intV 7, intV 3],
    mkCase "ok/sign/pos-neg" #[intV 7, intV (-3)],
    mkCase "ok/sign/neg-pos" #[intV (-7), intV 3],
    mkCase "ok/sign/neg-neg" #[intV (-7), intV (-3)],
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
    mkCase "boundary/in-range/max-zero" #[intV maxInt257, intV 0],
    mkCase "boundary/in-range/min-zero" #[intV minInt257, intV 0],
    mkCase "overflow/out-of-range/first-push-low" #[]
      #[.pushInt (.num 0), .pushInt (.num (minInt257 - 1)), .minmax],
    mkCase "overflow/out-of-range/second-push-high" #[]
      #[.pushInt (.num 0), .pushInt (.num (maxInt257 + 1)), .minmax],
    mkCase "overflow/out-of-range/both-high" #[]
      #[.pushInt (.num (maxInt257 + 2)), .pushInt (.num (maxInt257 + 1)), .minmax],
    mkCase "overflow/out-of-range/both-low" #[]
      #[.pushInt (.num (minInt257 - 2)), .pushInt (.num (minInt257 - 1)), .minmax],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-top-null" #[intV 1, .null],
    mkCase "type/pop-second-null" #[.null, intV 1],
    mkCase "type/pop-top-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-top-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num minmaxSetGasExact), .tonEnvOp .setGasLimit, .minmax],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num minmaxSetGasExactMinusOne), .tonEnvOp .setGasLimit, .minmax],
    mkCase "nan/pushnan-top-propagates-intov" #[intV 42] #[.pushInt .nan, .minmax],
    mkCase "nan/pushnan-second-propagates-intov" #[intV 42] #[.pushInt .nan, .xchg0 1, .minmax]
  ]
  fuzz := #[
    { seed := 2026020810
      count := 600
      gen := genMinmaxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MINMAX
