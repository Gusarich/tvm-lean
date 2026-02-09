import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.AND

/-
AND branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/And.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_and`, opcode registration in `register_bitwise_ops`);
  stack primitive behavior from `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
  (`check_underflow`, `pop_int`, `push_int_quiet`).

Branch counts used for this suite:
- Lean: 7 branch points / 8 terminal outcomes
  (opcode dispatch; two `popInt` failure points; NaN left-vs-right-vs-finite split;
   two `intToBitsTwos` conversions; final `pushIntQuiet` non-quiet path).
- C++: 5 branch points / 8 aligned terminal outcomes
  (opcode registration binds AND to `exec_and(..., quiet=false)`; `check_underflow(2)`;
   two `pop_int` type checks; result validity path through `push_int_quiet`).

Key divergence risk areas:
- Underflow-vs-type ordering: C++ checks underflow before any `pop_int`.
- Operand pop order (`y` first, then `x`) controls type-check ordering.
- Two's-complement behavior for negatives near 257-bit edges.
- Patterned high-bit operands (`2^255`, `minInt257`, `maxInt257`) at sign boundary.
- Exact gas boundary behavior for `PUSHINT n; SETGASLIMIT; AND`.
-/

private def andId : InstrId := { name := "AND" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.and_])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := andId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAndDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithAnd .and_ stack

private def runAndDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithAnd .add (VM.push (intV 777)) stack

private def andSetGasExact : Int :=
  computeExactGasBudget .and_

private def andSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .and_

private def genAndFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let ((x, y), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, -1), r2)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, x0), r2)
    else if shape = 5 then
      let (x0, r2) := pickInt257Boundary rng1
      ((x0, 1), r2)
    else if shape = 6 then
      let (x0, r2) := pickInt257Boundary rng1
      ((x0, pow2 255), r2)
    else if shape = 7 then
      let (x0, r2) := pickInt257Boundary rng1
      ((x0, minInt257), r2)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := andId
  unit := #[
    { name := "unit/twos-complement-identities"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 0, 0),
            (-7, 0, 0),
            (7, -1, 7),
            (-7, -1, -7),
            (7, 7, 7),
            (-7, -7, -7),
            (-5, 3, 3),
            (-7, -3, -7),
            (maxInt257, -1, maxInt257),
            (minInt257, -1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} and {y}" (runAndDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/bit-pattern-boundaries"
      run := do
        let bit255 := pow2 255
        let bit254 := pow2 254
        let checks : Array (Int × Int × Int) :=
          #[
            (minInt257, maxInt257, 0),
            (maxInt257, minInt257, 0),
            (maxInt257, 1, 1),
            (minInt257, 1, 0),
            (bit255, bit254, 0),
            (maxInt257, bit255, bit255),
            (minInt257, bit255, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"pattern {x} and {y}" (runAndDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error-ordering-underflow-type-and-nan"
      run := do
        expectErr "empty-underflow" (runAndDirect #[]) .stkUnd
        expectErr "one-int-underflow" (runAndDirect #[intV 1]) .stkUnd
        expectErr "one-non-int-underflow-first" (runAndDirect #[.null]) .stkUnd
        expectErr "pop-y-first-null" (runAndDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second-null" (runAndDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-pop-y-first" (runAndDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "nan-x-intov" (runAndDirect #[.int .nan, intV 1]) .intOv
        expectErr "nan-y-intov" (runAndDirect #[intV 1, .int .nan]) .intOv }
    ,
    { name := "unit/dispatch/non-and-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runAndDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "identity/left-and-zero" #[intV 222, intV 0],
    mkCase "identity/right-and-zero" #[intV 0, intV 222],
    mkCase "identity/self-positive" #[intV 12345, intV 12345],
    mkCase "identity/self-negative" #[intV (-12345), intV (-12345)],
    mkCase "identity/neg-one-with-positive" #[intV 123, intV (-1)],
    mkCase "identity/neg-one-with-negative" #[intV (-123), intV (-1)],
    mkCase "negative/mixed-sign-a" #[intV (-5), intV 3],
    mkCase "negative/both-negative" #[intV (-7), intV (-3)],
    mkCase "boundary/max-and-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "boundary/min-and-neg-one" #[intV minInt257, intV (-1)],
    mkCase "boundary/min-and-max" #[intV minInt257, intV maxInt257],
    mkCase "pattern/high-bit-pair" #[intV (pow2 255), intV (pow2 254)],
    mkCase "pattern/max-and-high-bit" #[intV maxInt257, intV (pow2 255)],
    mkCase "pattern/min-and-high-bit" #[intV minInt257, intV (pow2 255)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "nan/y-via-pushnan" #[intV 42] #[.pushInt .nan, .and_],
    mkCase "nan/x-via-pushnan" #[intV 42] #[.pushInt .nan, .xchg0 1, .and_],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num andSetGasExact), .tonEnvOp .setGasLimit, .and_],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num andSetGasExactMinusOne), .tonEnvOp .setGasLimit, .and_]
  ]
  fuzz := #[
    { seed := 2026020808
      count := 500
      gen := genAndFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.AND
