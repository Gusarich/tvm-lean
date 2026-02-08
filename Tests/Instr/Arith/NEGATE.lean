import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.NEGATE

/-
NEGATE branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Negate.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_negate`, opcode mapping in `register_add_mul_ops`).

Branch map and terminal outcomes:
- Lean: 4 branch points / 6 terminal outcomes
  - opcode dispatch: `.negate` path vs `next` passthrough;
  - `VM.popInt`: underflow / type error / success;
  - popped `IntVal`: `.nan` vs `.num`;
  - numeric `VM.pushIntQuiet ... false`: fits 257-bit (success) vs overflow (`.intOv`).
- C++: 4 branch points / 6 aligned terminal outcomes
  - opcode registration binds NEGATE to `exec_negate(st, quiet=false)`;
  - `stack.check_underflow(1)`: ok vs `stk_und`;
  - `stack.pop_int()`: int vs `type_chk`;
  - `stack.push_int_quiet(-x, false)`: in-range success vs `int_ov` (NaN or signed-257 overflow).

Key divergence risk areas:
- NaN handling: non-quiet NEGATE must throw `intOv` (not push NaN).
- Signed 257-bit boundary: `minInt257` negation must overflow, while neighbors must succeed.
- Unary pop/error ordering: only top stack item participates; lower stack entries must remain untouched.
- Gas edge behavior in oracle mode: exact cost succeeds, exact-minus-one fails with out-of-gas.
-/

private def negateId : InstrId := { name := "NEGATE" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.negate])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := negateId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runNegateDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithNegate .negate stack

private def negateSetGasExact : Int :=
  computeExactGasBudget .negate

private def negateSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .negate

private def genNegateFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 3
  let (x, rng2) :=
    if shape = 0 then
      pickInt257Boundary rng1
    else if shape = 1 then
      pickSigned257ish rng1
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let x1 :=
        if x0 = maxInt257 then maxInt257 - 1
        else if x0 = minInt257 then minInt257 + 1
        else x0
      (x1, r2)
    else
      pickSigned257ish rng1
  (mkCase s!"fuzz/shape-{shape}" #[intV x], rng2)

def suite : InstrSuite where
  id := negateId
  unit := #[
    { name := "unit/sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, 0),
            (17, -17),
            (-17, 17),
            (maxInt257, -(maxInt257)),
            (maxInt257 - 1, -(maxInt257 - 1)),
            (minInt257 + 1, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"negate {x}" (runNegateDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/overflow-and-nan-intov"
      run := do
        expectErr "min-overflow" (runNegateDirect #[intV minInt257]) .intOv
        expectErr "nan-intov" (runNegateDirect #[.int .nan]) .intOv }
    ,
    { name := "unit/type-underflow-and-pop-order"
      run := do
        expectErr "empty-underflow" (runNegateDirect #[]) .stkUnd
        expectErr "top-null" (runNegateDirect #[.null]) .typeChk
        expectErr "top-cell" (runNegateDirect #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-with-below-non-int" (runNegateDirect #[.cell Cell.empty, .null]) .typeChk
        expectOkStack "top-int-keeps-below" (runNegateDirect #[.null, intV 9]) #[.null, intV (-9)] }
    ,
    { name := "unit/near-boundary-successes"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (minInt257 + 2, maxInt257 - 1),
            (maxInt257 - 2, -(maxInt257 - 2))
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"near-boundary {x}" (runNegateDirect #[intV x]) #[intV expected] }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/positive" #[intV 23],
    mkCase "ok/negative" #[intV (-23)],
    mkCase "boundary/max-int257" #[intV maxInt257],
    mkCase "boundary/min-plus-one" #[intV (minInt257 + 1)],
    mkCase "near-boundary/max-minus-one" #[intV (maxInt257 - 1)],
    mkCase "near-boundary/min-plus-two" #[intV (minInt257 + 2)],
    mkCase "overflow/min-int257" #[intV minInt257],
    mkCase "underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "type/top-non-int-with-below-int" #[intV 1, .null],
    mkCase "error-order/top-non-int-with-below-non-int" #[.cell Cell.empty, .null],
    mkCase "error-order/top-int-below-non-int-untouched" #[.null, intV 9],
    mkCase "nan/operand-nan" #[] #[.pushInt .nan, .negate],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num negateSetGasExact), .tonEnvOp .setGasLimit, .negate],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num negateSetGasExactMinusOne), .tonEnvOp .setGasLimit, .negate]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := genNegateFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.NEGATE
