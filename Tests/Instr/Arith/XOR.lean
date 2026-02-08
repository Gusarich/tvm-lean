import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.XOR

/-
XOR branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Xor.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_xor`, opcode registration in `register_bitwise_ops`);
  stack primitive behavior from `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
  (`check_underflow`, `pop_int`, `push_int_quiet`).

Branch counts used for this suite:
- Lean: 7 branch points / 8 terminal outcomes
  (opcode dispatch; two `popInt` failure points; NaN left-vs-right-vs-finite split;
   two `intToBitsTwos` conversions; final `pushIntQuiet` non-quiet path).
- C++: 5 branch points / 8 aligned terminal outcomes
  (opcode registration binds XOR to `exec_xor(..., quiet=false)`; `check_underflow(2)`;
   two `pop_int` type checks; result validity path through `push_int_quiet`).

Key divergence risk areas:
- Underflow-vs-type ordering: C++ checks underflow before any `pop_int`.
- Operand pop order (`y` first, then `x`) controls type-check ordering.
- Two's-complement behavior for negatives (`x XOR -1 = ~x = -x-1`) near 257-bit edges.
- Exact gas boundary behavior for `PUSHINT n; SETGASLIMIT; XOR`.
-/

private def xorId : InstrId := { name := "XOR" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.xor])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xorId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runXorDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithXor .xor stack

private def xorSetGasExact : Int :=
  computeExactGasBudget .xor

private def xorSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .xor

private def genXorFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  let ((x, y), rng3) :=
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
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      ((x0, y0), r3)
  let (tag, rng4) := randNat rng3 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV y], rng4)

def suite : InstrSuite where
  id := xorId
  unit := #[
    { name := "unit/twos-complement-identities"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 0, 7),
            (-7, 0, -7),
            (7, 7, 0),
            (-7, -7, 0),
            (7, -1, -8),
            (-7, -1, 6),
            (-5, 3, -8),
            (-7, -3, 4),
            (maxInt257, -1, minInt257),
            (minInt257, -1, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} xor {y}" (runXorDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/bit-pattern-boundaries"
      run := do
        let bit255 := pow2 255
        let bit254 := pow2 254
        let checks : Array (Int × Int × Int) :=
          #[
            (minInt257, maxInt257, -1),
            (maxInt257, 1, maxInt257 - 1),
            (minInt257, 1, minInt257 + 1),
            (bit255, bit254, bit255 + bit254),
            (maxInt257, bit255, bit255 - 1),
            (minInt257, bit255, -bit255)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"pattern {x} xor {y}" (runXorDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error-ordering-underflow-type-and-nan"
      run := do
        expectErr "empty-underflow" (runXorDirect #[]) .stkUnd
        expectErr "one-int-underflow" (runXorDirect #[intV 1]) .stkUnd
        expectErr "one-non-int-underflow-first" (runXorDirect #[.null]) .stkUnd
        expectErr "pop-y-first-null" (runXorDirect #[intV 1, .null]) .typeChk
        expectErr "pop-x-second-null" (runXorDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-pop-y-first" (runXorDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "nan-x-intov" (runXorDirect #[.int .nan, intV 1]) .intOv
        expectErr "nan-y-intov" (runXorDirect #[intV 1, .int .nan]) .intOv }
  ]
  oracle := #[
    mkCase "ok/zero-zero" #[intV 0, intV 0],
    mkCase "identity/left-zero" #[intV 222, intV 0],
    mkCase "identity/right-zero" #[intV 0, intV 222],
    mkCase "identity/self-positive" #[intV 12345, intV 12345],
    mkCase "identity/self-negative" #[intV (-12345), intV (-12345)],
    mkCase "identity/neg-one-with-positive" #[intV 123, intV (-1)],
    mkCase "identity/neg-one-with-negative" #[intV (-123), intV (-1)],
    mkCase "negative/mixed-sign-a" #[intV (-5), intV 3],
    mkCase "negative/both-negative" #[intV (-7), intV (-3)],
    mkCase "boundary/max-xor-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "boundary/min-xor-neg-one" #[intV minInt257, intV (-1)],
    mkCase "boundary/min-xor-max" #[intV minInt257, intV maxInt257],
    mkCase "pattern/high-bit-pair" #[intV (pow2 255), intV (pow2 254)],
    mkCase "pattern/max-xor-high-bit" #[intV maxInt257, intV (pow2 255)],
    mkCase "pattern/min-xor-high-bit" #[intV minInt257, intV (pow2 255)],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "nan/y-via-pushnan" #[intV 42] #[.pushInt .nan, .xor],
    mkCase "nan/x-via-pushnan" #[intV 42] #[.pushInt .nan, .xchg0 1, .xor],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num xorSetGasExact), .tonEnvOp .setGasLimit, .xor],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num xorSetGasExactMinusOne), .tonEnvOp .setGasLimit, .xor]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 500
      gen := genXorFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.XOR
