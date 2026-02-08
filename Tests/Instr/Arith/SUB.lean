import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.SUB

/-
SUB branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Sub.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_sub`, opcode registration in `register_add_mul_ops`).

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (opcode dispatch; explicit `checkUnderflow 2`; two `popInt` type paths;
   `IntVal.sub` finite-vs-NaN; `pushIntQuiet` NaN-vs-num and signed-257 fit check).
- C++: 5 branch points / 8 aligned terminal outcomes
  (registration binds SUB to `exec_sub(..., quiet=false)`; underflow guard;
   two `pop_int` type checks; `push_int_quiet` signed-257 fit check with non-quiet throw).

Terminal outcomes mapped in oracle:
- success with finite in-range result;
- `.intOv` from NaN propagation;
- `.intOv` from signed 257-bit overflow/underflow;
- `.typeChk` at first pop (`y`) and second pop (`x`);
- `.stkUnd` from stack size < 2 (including one-non-int ordering case);
- out-of-gas via precise `SETGASLIMIT` boundary.

Key divergence risk areas:
- Underflow must be checked before type checks when stack size < 2.
- Operand pop order is `y` then `x`; this controls type/error ordering.
- Signed 257-bit boundary off-by-one (`[-2^256, 2^256-1]`).
- NaN must throw `intOv` for non-quiet SUB.
- Gas-boundary checks must be deterministic for `PUSHINT n; SETGASLIMIT; SUB`.
-/

private def subId : InstrId := { name := "SUB" }

private def intV (n : Int) : Value :=
  .int (.num n)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.sub])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := subId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSubDirect (stack : Array Value) : Except Excno (Array Value) :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithSub .sub (pure ())).run st0
  match res with
  | .ok _ => .ok st1.stack
  | .error e => .error e

private def expectOkStack (label : String) (res : Except Excno (Array Value)) (expected : Array Value) : IO Unit := do
  match res with
  | .ok st =>
      if st == expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectErr (label : String) (res : Except Excno (Array Value)) (expected : Excno) : IO Unit := do
  match res with
  | .ok st =>
      throw (IO.userError s!"{label}: expected error {expected}, got stack {reprStr st}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def subGasForInstr (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def subSetGasNeed (n : Int) : Int :=
  subGasForInstr (.pushInt (.num n))
    + subGasForInstr (.tonEnvOp .setGasLimit)
    + subGasForInstr .sub
    + implicitRetGasPrice

private def subSetGasFixedPoint (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := subSetGasNeed n
      if n' = n then n else subSetGasFixedPoint n' k

private def subSetGasExact : Int :=
  subSetGasFixedPoint 64 16

private def subSetGasExactMinusOne : Int :=
  if subSetGasExact > 0 then subSetGasExact - 1 else 0

private def genSubFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
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
    else if shape = 5 then
      let (y0, r2) := pickSigned257ish rng1
      ((0, y0), r2)
    else
      let (x0, r2) := pickInt257Boundary rng1
      let (delta, r3) := randNat r2 0 1
      ((x0, if delta = 0 then 1 else -1), r3)
  (mkCase s!"fuzz/shape-{shape}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := subId
  unit := #[
    { name := "unit/finite-sign-and-zero-invariants"
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
            (maxInt257, maxInt257, 0),
            (minInt257, minInt257, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}-{y}" (runSubDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/near-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257 - 1),
            (minInt257, -1, minInt257 + 1),
            (maxInt257 - 1, -1, maxInt257),
            (minInt257 + 1, 1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}-{y}" (runSubDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/overflow-underflow-boundaries-throw-intov"
      run := do
        expectErr "max-(-1)" (runSubDirect #[intV maxInt257, intV (-1)]) .intOv
        expectErr "min-1" (runSubDirect #[intV minInt257, intV 1]) .intOv
        expectErr "max-min" (runSubDirect #[intV maxInt257, intV minInt257]) .intOv
        expectErr "min-max" (runSubDirect #[intV minInt257, intV maxInt257]) .intOv }
    ,
    { name := "unit/nan-and-pop-order-type-errors"
      run := do
        expectErr "nan-1" (runSubDirect #[.int .nan, intV 1]) .intOv
        expectErr "1-nan" (runSubDirect #[intV 1, .int .nan]) .intOv
        expectErr "pop-y-first" (runSubDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second" (runSubDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-first" (runSubDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/underflow-precedes-type-with-single-arg"
      run := do
        expectErr "empty" (runSubDirect #[]) .stkUnd
        expectErr "one-int" (runSubDirect #[intV 1]) .stkUnd
        expectErr "one-non-int" (runSubDirect #[.null]) .stkUnd }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "ok/pos-pos" #[intV 17, intV 5],
    mkCase "ok/pos-neg" #[intV 17, intV (-5)],
    mkCase "ok/neg-pos" #[intV (-17), intV 5],
    mkCase "ok/neg-neg" #[intV (-17), intV (-5)],
    mkCase "ok/zero-right" #[intV 222, intV 0],
    mkCase "ok/zero-left" #[intV 0, intV 222],
    mkCase "ok/max-minus-zero" #[intV maxInt257, intV 0],
    mkCase "ok/min-minus-zero" #[intV minInt257, intV 0],
    mkCase "ok/max-minus-one" #[intV maxInt257, intV 1],
    mkCase "ok/min-minus-neg-one" #[intV minInt257, intV (-1)],
    mkCase "ok/max-minus-one-plus-neg-one" #[intV (maxInt257 - 1), intV (-1)],
    mkCase "ok/min-plus-one-minus-one" #[intV (minInt257 + 1), intV 1],
    mkCase "boundary/max-minus-max" #[intV maxInt257, intV maxInt257],
    mkCase "boundary/min-minus-min" #[intV minInt257, intV minInt257],
    mkCase "overflow/max-minus-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "overflow/max-minus-min" #[intV maxInt257, intV minInt257],
    mkCase "underflow/min-minus-one" #[intV minInt257, intV 1],
    mkCase "underflow/min-minus-max" #[intV minInt257, intV maxInt257],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num subSetGasExact), .tonEnvOp .setGasLimit, .sub],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num subSetGasExactMinusOne), .tonEnvOp .setGasLimit, .sub],
    mkCase "nan/pushnan-y-propagates-intov" #[intV 42] #[.pushInt .nan, .sub],
    mkCase "nan/pushnan-x-propagates-intov" #[intV 42] #[.pushInt .nan, .xchg0 1, .sub]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := genSubFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.SUB
