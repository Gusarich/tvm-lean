import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.INC

/-
INC branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Inc.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_inc`, opcode registration in `register_add_mul_ops`).

Branch points and terminal outcomes used for this suite:
- Lean (`execInstrArithInc`):
  - dispatch (`.inc` vs fallthrough to `next`);
  - `VM.popInt` (`stkUnd` | `typeChk` | int value);
  - `IntVal.inc` (`num -> num` | `nan -> nan`);
  - `VM.pushIntQuiet quiet=false`
    (`ok push` | `intOv` on NaN | `intOv` on signed-257 overflow).
  - `.inc` terminals: success, `stkUnd`, `typeChk`, `intOv`(NaN), `intOv`(overflow).
- C++ (`exec_inc(..., quiet=false)`):
  - `stack.check_underflow(1)` (`stk_und` | continue);
  - `stack.pop_int()` (`type_chk` | int/NaN value);
  - `stack.push_int_quiet(..., false)`
    (success | `int_ov` on NaN | `int_ov` on out-of-range).
  - terminals align: success, `stkUnd`, `typeChk`, `intOv`(NaN), `intOv`(overflow).

Key divergence risk areas:
- Non-quiet NaN path must throw `intOv`, not push NaN.
- Signed-257 upper-bound off-by-one (`maxInt257 + 1`) on result push.
- Near-boundary non-overflow (`maxInt257 - 1`, `minInt257`, `minInt257 + 1`).
- Unary pop error ordering (`empty -> stkUnd`, single non-int -> `typeChk`).
- Gas boundary for `PUSHINT n; SETGASLIMIT; INC` exact vs exact-minus-one.
-/

private def incId : InstrId := { name := "INC" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.inc])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := incId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runIncDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithInc .inc stack

private def incSetGasExact : Int :=
  computeExactGasBudget .inc

private def incSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .inc

private def genIncFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 4
  let (x, rng2) :=
    if shape = 0 then
      pickInt257Boundary rng1
    else if shape = 1 then
      pickSigned257ish rng1
    else if shape = 2 then
      let (which, r2) := randNat rng1 0 3
      let x0 :=
        if which = 0 then maxInt257
        else if which = 1 then maxInt257 - 1
        else if which = 2 then minInt257
        else minInt257 + 1
      (x0, r2)
    else if shape = 3 then
      let (which, r2) := randNat rng1 0 2
      let x0 :=
        if which = 0 then (0 : Int)
        else if which = 1 then (1 : Int)
        else (-1 : Int)
      (x0, r2)
    else
      pickSigned257ish rng1
  (mkCase s!"fuzz/shape-{shape}" #[intV x], rng2)

def suite : InstrSuite where
  id := incId
  unit := #[
    { name := "unit/sign-zero-and-near-boundary-successes"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, 1),
            (7, 8),
            (-7, -6),
            (maxInt257 - 1, maxInt257),
            (minInt257, minInt257 + 1),
            (minInt257 + 1, minInt257 + 2)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"inc({x})" (runIncDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/overflow-max-plus-one-throws-intov"
      run := do
        expectErr "inc(maxInt257)" (runIncDirect #[intV maxInt257]) .intOv }
    ,
    { name := "unit/nan-operand-throws-intov"
      run := do
        expectErr "inc(nan)" (runIncDirect #[.int .nan]) .intOv }
    ,
    { name := "unit/underflow-type-and-error-order"
      run := do
        expectErr "empty-stack" (runIncDirect #[]) .stkUnd
        expectErr "null-top" (runIncDirect #[.null]) .typeChk
        expectErr "cell-top" (runIncDirect #[.cell Cell.empty]) .typeChk }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/positive" #[intV 37],
    mkCase "ok/negative" #[intV (-37)],
    mkCase "ok/near-boundary-max-minus-one" #[intV (maxInt257 - 1)],
    mkCase "ok/near-boundary-min" #[intV minInt257],
    mkCase "ok/near-boundary-min-plus-one" #[intV (minInt257 + 1)],
    mkCase "boundary/max-minus-two" #[intV (maxInt257 - 2)],
    mkCase "overflow/max-plus-one" #[intV maxInt257],
    mkCase "stack-underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "error-order/type-on-single-non-int-cell" #[.cell Cell.empty],
    mkCase "nan/pushnan-intov" #[] #[.pushInt .nan, .inc],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num incSetGasExact), .tonEnvOp .setGasLimit, .inc],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num incSetGasExactMinusOne), .tonEnvOp .setGasLimit, .inc]
  ]
  fuzz := #[
    { seed := 2026020802
      count := 500
      gen := genIncFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.INC
