import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMOD

/-
MULMOD branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa98` decode to `.mulDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, opcode wiring in `register_div_ops`)

Branch/terminal coverage target for this suite:
- Lean MULMOD specialization (`.mulDivMod 2 (-1) false false`):
  dispatch/fallback; arity gate (`need=3`); pop order/type gates (`z`, `y`, `x`);
  numeric-vs-NaN split; divisor-zero split; non-quiet push range/NaN funnel.
- C++ MULMOD path (non-add, floor mode):
  invalid-op remap guard; underflow gate; pop/type path; divisor-zero path;
  modulo path with non-quiet `push_int_quiet` overflow/NaN throw funnel.

Key risk areas covered:
- floor remainder sign semantics after multiplication (`x*y mod z`);
- strict pop and error ordering (`stkUnd` before type on short stacks; `z→y→x`);
- non-quiet NaN and out-of-range numeric inputs injected via program only;
- divisor-zero to non-quiet `.intOv`;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; MULMOD`.
-/

private def mulmodId : InstrId := { name := "MULMOD" }

private def mulmodInstr : Instr := .mulDivMod 2 (-1) false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkMulmodCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push mulmodInstr) gasLimits fuel

private def runMulmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod mulmodInstr stack

private def runMulmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 31337)) stack

private def expectAssembleErr
    (label : String)
    (program : List Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

private def mulmodSetGasExact : Int :=
  computeExactGasBudget mulmodInstr

private def mulmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def mulmodDivisorBoundaryPool : Array Int :=
  #[-3, -2, -1, 1, 2, 3, maxInt257, maxInt257 - 1, minInt257, minInt257 + 1]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickMulmodDivisorBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool mulmodDivisorBoundaryPool rng

private def pickMulmodDivisorMixed (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickMulmodDivisorBoundary rng1
  else
    pickNonZeroInt rng1

private def mulmodOutOfRangePool : Array Int :=
  #[pow2 256, pow2 256 + 1, -(pow2 256) - 1]

private def pickOutOfRangeInt (rng : StdGen) : Int × StdGen :=
  pickFromPool mulmodOutOfRangePool rng

private def pickMulmodNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def genMulmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickMulmodDivisorBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-all" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickMulmodDivisorMixed r3
      (mkCase s!"fuzz/shape-{shape}/ok-random" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickMulmodDivisorMixed r3
      (mkCase s!"fuzz/shape-{shape}/ok-mixed-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/divzero" #[intV x, intV y, intV 0], r3)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickMulmodDivisorMixed r2
      (mkCase s!"fuzz/shape-{shape}/exact-zero-x" #[intV 0, intV y, intV z], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickMulmodDivisorMixed r2
      (mkCase s!"fuzz/shape-{shape}/exact-zero-y" #[intV x, intV 0, intV z], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-arg" #[intV x], r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two-args" #[intV x, intV y], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zLike, r4) := pickMulmodNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-z-first" #[intV x, intV y, zLike], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickMulmodNonInt r2
      let (z, r4) := pickMulmodDivisorMixed r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-second" #[intV x, yLike, intV z], r4)
    else if shape = 11 then
      let (xLike, r2) := pickMulmodNonInt rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickMulmodDivisorMixed r3
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-third" #[xLike, intV y, intV z], r4)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let (pos, r5) := randNat r4 0 2
      let vals :=
        if pos = 0 then
          #[IntVal.nan, IntVal.num y, IntVal.num z]
        else if pos = 1 then
          #[IntVal.num x, IntVal.nan, IntVal.num z]
        else
          #[IntVal.num x, IntVal.num y, IntVal.nan]
      (mkMulmodCaseFromIntVals s!"fuzz/shape-{shape}/nan-via-program-pos-{pos}" vals, r5)
    else if shape = 13 then
      let (xHuge, r2) := pickOutOfRangeInt rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkMulmodCaseFromIntVals
        s!"fuzz/shape-{shape}/out-of-range-x-via-program"
        #[IntVal.num xHuge, IntVal.num y, IntVal.num z], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zHuge, r4) := pickOutOfRangeInt r3
      (mkMulmodCaseFromIntVals
        s!"fuzz/shape-{shape}/out-of-range-z-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.num zHuge], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-fallback" #[intV x, intV y, intV z], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulmodId
  unit := #[
    { name := "unit/direct/floor-sign-and-product-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 5, 3, 2),
            (-7, 5, 3, 1),
            (7, -5, 3, 1),
            (-7, -5, 3, 2),
            (7, 5, -3, -1),
            (-7, 5, -3, -2),
            (7, -5, -3, -2),
            (-7, -5, -3, -1),
            (0, 123, 7, 0),
            (123, 0, 7, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"({x}*{y}) mod {z}"
                (runMulmodDirect #[intV x, intV y, intV z])
                #[intV expected] }
    ,
    { name := "unit/direct/boundary-and-zero-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, 0),
            (maxInt257, 1, -1, 0),
            (maxInt257, 1, 2, 1),
            (maxInt257, 1, -2, -1),
            (minInt257, 1, 1, 0),
            (minInt257, 1, -1, 0),
            (minInt257, 1, 2, 0),
            (minInt257, 1, -2, 0),
            (minInt257 + 1, 1, 2, 1),
            (minInt257 + 1, 1, -2, -1)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"({x}*{y}) mod {z}"
                (runMulmodDirect #[intV x, intV y, intV z])
                #[intV expected] }
    ,
    { name := "unit/error/divzero-pop-order-and-underflow-ordering"
      run := do
        expectErr "divzero/nonzero-over-zero" (runMulmodDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "underflow/empty" (runMulmodDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runMulmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runMulmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/single-non-int-underflow-first" (runMulmodDirect #[.null]) .stkUnd
        expectErr "error-order/two-items-underflow-before-z-type" (runMulmodDirect #[intV 1, .null]) .stkUnd
        expectErr "type/pop-z-first" (runMulmodDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulmodDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMulmodDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-y-before-x-when-z-int"
          (runMulmodDirect #[.cell Cell.empty, .null, intV 2]) .typeChk }
    ,
    { name := "unit/program-injection/out-of-range-pushint-rangechk"
      run := do
        expectAssembleErr "pushint/out-of-range-positive"
          [.pushInt (.num (pow2 300)), mulmodInstr] .rangeChk
        expectAssembleErr "pushint/out-of-range-negative"
          [.pushInt (.num (-(pow2 300))), mulmodInstr] .rangeChk }
    ,
    { name := "unit/dispatch/non-mulmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runMulmodDispatchFallback #[]) #[intV 31337] }
  ]
  oracle := #[
    mkCase "ok/sign/pos-pos-pos-divisor-inexact" #[intV 7, intV 5, intV 3],
    mkCase "ok/sign/neg-pos-pos-divisor-inexact" #[intV (-7), intV 5, intV 3],
    mkCase "ok/sign/pos-neg-pos-divisor-inexact" #[intV 7, intV (-5), intV 3],
    mkCase "ok/sign/neg-neg-pos-divisor-inexact" #[intV (-7), intV (-5), intV 3],
    mkCase "ok/sign/pos-pos-neg-divisor-inexact" #[intV 7, intV 5, intV (-3)],
    mkCase "ok/sign/neg-pos-neg-divisor-inexact" #[intV (-7), intV 5, intV (-3)],
    mkCase "ok/sign/pos-neg-neg-divisor-inexact" #[intV 7, intV (-5), intV (-3)],
    mkCase "ok/sign/neg-neg-neg-divisor-inexact" #[intV (-7), intV (-5), intV (-3)],
    mkCase "ok/exact/zero-x" #[intV 0, intV 123, intV 7],
    mkCase "ok/exact/zero-y" #[intV 123, intV 0, intV 7],
    mkCase "ok/exact/zero-times-zero" #[intV 0, intV 0, intV 7],
    mkCase "ok/exact/max-times-one-mod-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "ok/exact/min-times-one-mod-one" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/exact/max-times-one-mod-neg-one" #[intV maxInt257, intV 1, intV (-1)],
    mkCase "ok/exact/min-times-one-mod-neg-one" #[intV minInt257, intV 1, intV (-1)],
    mkCase "ok/boundary/max-times-one-mod-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-times-one-mod-neg-two" #[intV maxInt257, intV 1, intV (-2)],
    mkCase "ok/boundary/min-times-one-mod-two" #[intV minInt257, intV 1, intV 2],
    mkCase "ok/boundary/min-times-one-mod-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "ok/boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 1, intV 2],
    mkCase "ok/boundary/min-plus-one-mod-neg-two" #[intV (minInt257 + 1), intV 1, intV (-2)],
    mkCase "ok/boundary/max-minus-one-mod-two" #[intV (maxInt257 - 1), intV 1, intV 2],
    mkCase "intov/divzero/nonzero-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "intov/divzero/zero-over-zero" #[intV 0, intV 0, intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/single-non-int-underflow-first" #[.null],
    mkCase "error-order/two-items-underflow-before-z-type" #[intV 1, .null],
    mkCase "type/pop-z-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-y-before-x-when-z-int" #[.cell Cell.empty, .null, intV 2],
    mkMulmodCaseFromIntVals "nan/z-via-program" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkMulmodCaseFromIntVals "nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkMulmodCaseFromIntVals "nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkMulmodCaseFromIntVals "overflow/input-x-out-of-range-via-program"
      #[IntVal.num (pow2 256), IntVal.num 5, IntVal.num 7],
    mkMulmodCaseFromIntVals "overflow/input-z-out-of-range-via-program"
      #[IntVal.num 7, IntVal.num 5, IntVal.num (-(pow2 256) - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodSetGasExact), .tonEnvOp .setGasLimit, mulmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulmodInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genMulmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMOD
