import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.DEC

/-
DEC branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Dec.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_dec`, opcode registration in `register_add_mul_ops`).

Branch counts used for this suite:
- Lean: 4 branch points / 6 terminal outcomes
  (opcode dispatch; `VM.popInt` underflow/type/success; `IntVal.dec` num-vs-NaN;
   `VM.pushIntQuiet` signed-257 fit check and non-quiet NaN/overflow throw).
- C++: 4 branch points / 6 terminal outcomes
  (registration binds DEC to `exec_dec(..., quiet=false)`; `check_underflow(1)`;
   `pop_int` type check; `push_int_quiet(..., false)` signed-257 fit check).

Mapped terminal outcomes (both sides):
- success: finite decrement result in `[-2^256, 2^256 - 1]`;
- error: stack underflow (`stkUnd`/`stk_und`);
- error: type check on top stack item (`typeChk`/`type_chk`);
- error: integer overflow (`intOv`/`int_ov`) from NaN propagation or `minInt257 - 1`.

Key divergence risk areas:
- boundary off-by-one at `minInt257` (must fail) vs `minInt257 + 1` (must succeed);
- NaN propagation under non-quiet DEC (`intOv`, not silent NaN push);
- error ordering with extra tail values (top item type-check is decisive);
- exact gas boundary around implicit RET using `PUSHINT n; SETGASLIMIT; DEC`.
-/

private def decId : InstrId := { name := "DEC" }

private def decInstr : Instr := .dec

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[decInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := decId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDecDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDec .dec stack

private def decSetGasExact : Int :=
  computeExactGasBudget decInstr

private def decSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne decInstr

private def genDecFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 4
  let (x, rng2) :=
    if shape = 0 then
      pickInt257Boundary rng1
    else if shape = 1 then
      pickSigned257ish rng1
    else if shape = 2 then
      let (which, rng2) := randNat rng1 0 3
      if which = 0 then
        (minInt257, rng2)
      else if which = 1 then
        (minInt257 + 1, rng2)
      else if which = 2 then
        (maxInt257, rng2)
      else
        (maxInt257 - 1, rng2)
    else if shape = 3 then
      let (x0, rng2) := pickSigned257ish rng1
      (if x0 = 0 then 1 else x0, rng2)
    else
      let (x0, rng2) := pickSigned257ish rng1
      (if x0 = 0 then -1 else x0, rng2)
  (mkCase s!"fuzz/shape-{shape}" #[intV x], rng2)

def suite : InstrSuite where
  id := decId
  unit := #[
    { name := "unit/finite-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, -1),
            (1, 0),
            (17, 16),
            (-1, -2),
            (-17, -18),
            (maxInt257, maxInt257 - 1),
            (minInt257 + 2, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"{x}-1" (runDecDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/near-boundary-successes"
      run := do
        expectOkStack "max-1" (runDecDirect #[intV maxInt257]) #[intV (maxInt257 - 1)]
        expectOkStack "min+1-1" (runDecDirect #[intV (minInt257 + 1)]) #[intV minInt257]
        expectOkStack "tail-preserved" (runDecDirect #[intV 99, intV 0]) #[intV 99, intV (-1)] }
    ,
    { name := "unit/min-boundary-overflow-throws-intov"
      run := do
        expectErr "min-1" (runDecDirect #[intV minInt257]) .intOv }
    ,
    { name := "unit/nan-underflow-type-and-error-order"
      run := do
        expectErr "nan-1" (runDecDirect #[.int .nan]) .intOv
        expectErr "underflow-empty" (runDecDirect #[]) .stkUnd
        expectErr "type-top-null" (runDecDirect #[.null]) .typeChk
        expectErr "type-top-null-with-tail" (runDecDirect #[intV 7, .null]) .typeChk }
  ]
  oracle := #[
    mkCase "ok/zero-to-neg-one" #[intV 0],
    mkCase "ok/positive-to-prev" #[intV 17],
    mkCase "ok/negative-to-prev" #[intV (-17)],
    mkCase "boundary/max-to-max-minus-one" #[intV maxInt257],
    mkCase "boundary/min-plus-one-to-min" #[intV (minInt257 + 1)],
    mkCase "boundary/min-plus-two-to-min-plus-one" #[intV (minInt257 + 2)],
    mkCase "overflow/min-to-intov" #[intV minInt257],
    mkCase "underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-null-with-int-tail" #[intV 7, .null],
    mkCase "error-order/top-null-with-nonint-tail" #[.cell Cell.empty, .null],
    mkCase "nan/pushnan-via-program" #[] #[.pushInt .nan, decInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num decSetGasExact), .tonEnvOp .setGasLimit, decInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num decSetGasExactMinusOne), .tonEnvOp .setGasLimit, decInstr]
  ]
  fuzz := #[
    { seed := 2026020802
      count := 500
      gen := genDecFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.DEC
