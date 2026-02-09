import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULDIVC

/-
QMULDIVC branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
    (`execInstrArithMulDivMod`, `.mulDivMod d roundMode addMode quiet`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, quiet NaN/overflow normalization)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb7a98` QMUL{DIV,MOD,DIVMOD} decode, args4=`0x6` for QMULDIVC)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean generic `.mulDivMod` handler: 7 branch sites / 16 terminal outcomes
  (dispatch path; add-mode arity split; non-add arity split; divisor-zero split;
   round-mode validation split; `d` switch; non-`num` operand split).
- C++ `exec_muldivmod` path: 5 branch sites / 11 aligned outcomes
  (opcode/remap guard, underflow guard, add-vs-non-add pop path, `d` switch,
   quiet-vs-throw normalization at result push).

QMULDIVC specialization:
- `.mulDivMod 1 1 false true` (`d=1`, `roundMode=ceil`, `addMode=false`, `quiet=true`)
- reachable outcomes include successful quotient push, `stkUnd`, `typeChk`,
  and quiet NaN funnels from divzero / NaN operands / quotient overflow.

Key risk areas covered:
- ceil quotient semantics across all sign combinations and near-zero fractions;
- quiet-mode NaN normalization (divzero, overflow, NaN operands, out-of-range quotient);
- strict pop and error ordering (`z` then `y` then `x`, underflow before any pop);
- serialization-safe NaN/out-of-range operand injection through program prelude only;
- exact gas boundary via `PUSHINT n; SETGASLIMIT; QMULDIVC`.
-/

private def qmuldivcId : InstrId := { name := "QMULDIVC" }

private def qmuldivcInstr : Instr := .mulDivMod 1 1 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuldivcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmuldivcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qmuldivcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programTail) gasLimits fuel

private def runQmuldivcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuldivcInstr stack

private def runQmuldivcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 3326)) stack

private def qmuldivcSetGasExact : Int :=
  computeExactGasBudget qmuldivcInstr

private def qmuldivcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuldivcInstr

private def ceilFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def ceilDivisorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def genQmuldivcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 25
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/ok/boundary-boundary-nonzero"
        #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/ok/random-random-nonzero"
        #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickFromPool ceilDivisorPool r3
      (mkCase s!"/fuzz/shape-{shape}/ok/boundary-x-small-z"
        #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/ok/boundary-y-nonzero-z"
        #[intV x, intV y, intV z], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero" #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool ceilFactorPool rng1
      let (y, r3) := pickFromPool ceilFactorPool r2
      let (z, r4) := pickFromPool ceilDivisorPool r3
      (mkCase s!"/fuzz/shape-{shape}/ok/ceil-small-pools"
        #[intV x, intV y, intV z], r4)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-times-negone-div-one"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-times-max-div-one"
        #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-times-min-div-one"
        #[intV minInt257, intV minInt257, intV 1], rng1)
    else if shape = 9 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"/fuzz/shape-{shape}/ok/zero-left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"/fuzz/shape-{shape}/ok/zero-right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 11 then
      let (x, r2) := pickFromPool ceilFactorPool rng1
      let (y, r3) := pickFromPool ceilFactorPool r2
      (mkCase s!"/fuzz/shape-{shape}/ok/divisor-one-identity" #[intV x, intV y, intV 1], r3)
    else if shape = 12 then
      let (x, r2) := pickFromPool ceilFactorPool rng1
      let (y, r3) := pickFromPool ceilFactorPool r2
      (mkCase s!"/fuzz/shape-{shape}/ok/divisor-neg-one-sign-flip"
        #[intV x, intV y, intV (-1)], r3)
    else if shape = 13 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zLike, r4) := pickNonIntLike r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, zLike], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second" #[intV x, yLike, intV z], r4)
    else if shape = 18 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xLike, intV y, intV z], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/type-y-before-divzero-funnel"
        #[intV x, yLike, intV 0], r3)
    else if shape = 20 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num y, .num z], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[.num x, .nan, .num z], r3)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[.num x, .num y, .nan], r3)
    else if shape = 23 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[.num x, .num y, .num z], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[.num x, .num y, .num z], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-z-before-op"
        #[.num x, .num y, .num z], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuldivcId
  unit := #[
    { name := "/unit/direct/ceil-sign-zero-and-exact-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 11),
            (-7, 3, 2, -10),
            (7, -3, 2, -10),
            (-7, -3, 2, 11),
            (5, 5, 2, 13),
            (-5, 5, 2, -12),
            (5, -5, 2, -12),
            (-5, -5, 2, 13),
            (-1, 1, 2, 0),
            (1, -1, 2, 0),
            (-1, -1, 2, 1),
            (0, 9, 5, 0),
            (9, 0, 5, 0),
            (42, 6, 7, 36),
            (-42, 6, 7, -36),
            (42, -6, 7, -36),
            (-42, -6, 7, 36)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"/unit/direct/ceil/{x}/{y}/{z}"
                (runQmuldivcDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "/unit/direct/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, maxInt257),
            (maxInt257, -1, 1, -maxInt257),
            (minInt257, 1, 1, minInt257),
            (minInt257, -1, -1, minInt257),
            (minInt257 + 1, -1, -1, minInt257 + 1),
            (maxInt257, 1, 2, pow2 255),
            (maxInt257, -1, 2, 1 - (pow2 255)),
            (minInt257, 1, 2, -(pow2 255)),
            (minInt257, 1, -2, pow2 255),
            (minInt257 + 1, -1, 2, pow2 255)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"/unit/direct/boundary/{x}/{y}/{z}"
                (runQmuldivcDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "/unit/direct/quiet-nan-on-divzero-overflow-and-nan-inputs"
      run := do
        expectOkStack "/unit/direct/quiet/divzero/nonzero-over-zero"
          (runQmuldivcDirect #[intV 5, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/direct/quiet/divzero/zero-over-zero"
          (runQmuldivcDirect #[intV 0, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/direct/quiet/overflow/min-times-negone-div-one"
          (runQmuldivcDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan]
        expectOkStack "/unit/direct/quiet/overflow/max-times-max-div-one"
          (runQmuldivcDirect #[intV maxInt257, intV maxInt257, intV 1]) #[.int .nan]
        expectOkStack "/unit/direct/quiet/nan-x"
          (runQmuldivcDirect #[.int .nan, intV 5, intV 3]) #[.int .nan]
        expectOkStack "/unit/direct/quiet/nan-y"
          (runQmuldivcDirect #[intV 5, .int .nan, intV 3]) #[.int .nan]
        expectOkStack "/unit/direct/quiet/nan-z"
          (runQmuldivcDirect #[intV 5, intV 7, .int .nan]) #[.int .nan]
        expectOkStack "/unit/direct/quiet/out-of-range-operand-x"
          (runQmuldivcDirect #[intV (maxInt257 + 1), intV 1, intV 1]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-and-pop-sequencing"
      run := do
        expectErr "/unit/error/underflow-empty"
          (runQmuldivcDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-one-arg"
          (runQmuldivcDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-args"
          (runQmuldivcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-two-items"
          (runQmuldivcDirect #[.cell Cell.empty, .null]) .stkUnd
        expectErr "/unit/error/type-pop-z-first"
          (runQmuldivcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type-pop-y-second"
          (runQmuldivcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type-pop-x-third"
          (runQmuldivcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error-order/pop-z-before-y-when-both-non-int"
          (runQmuldivcDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-after-z-int"
          (runQmuldivcDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "/unit/error-order/type-before-divzero-funnel"
          (runQmuldivcDirect #[intV 1, .null, intV 0]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmuldivcDispatchFallback #[]) #[intV 3326] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "/ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "/ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "/ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "/ok/ceil/sign/neg-pos-near-zero" #[intV (-1), intV 1, intV 2],
    mkCase "/ok/ceil/sign/pos-neg-near-zero" #[intV 1, intV (-1), intV 2],
    mkCase "/ok/ceil/sign/neg-neg-near-zero" #[intV (-1), intV (-1), intV 2],
    mkCase "/ok/ceil/sign/pos-pos-half" #[intV 5, intV 5, intV 2],
    mkCase "/ok/ceil/sign/neg-pos-half" #[intV (-5), intV 5, intV 2],
    mkCase "/ok/ceil/sign/pos-neg-half" #[intV 5, intV (-5), intV 2],
    mkCase "/ok/ceil/sign/neg-neg-half" #[intV (-5), intV (-5), intV 2],
    mkCase "/ok/exact/pos-pos" #[intV 42, intV 6, intV 7],
    mkCase "/ok/exact/neg-pos" #[intV (-42), intV 6, intV 7],
    mkCase "/ok/exact/pos-neg" #[intV 42, intV (-6), intV 7],
    mkCase "/ok/exact/neg-neg" #[intV (-42), intV (-6), intV 7],
    mkCase "/ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "/ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "/ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-negone-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "/ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-times-negone-div-negone" #[intV minInt257, intV (-1), intV (-1)],
    mkCase "/ok/boundary/min-plus-one-times-negone-div-negone"
      #[intV (minInt257 + 1), intV (-1), intV (-1)],
    mkCase "/ok/boundary/max-times-one-div-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "/ok/boundary/max-times-negone-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "/ok/boundary/min-times-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "/ok/boundary/min-times-one-div-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/min-plus-one-times-negone-div-two"
      #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "/quiet/divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "/quiet/overflow/min-times-negone-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "/quiet/overflow/max-times-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "/quiet/overflow/max-times-max-div-negone" #[intV maxInt257, intV maxInt257, intV (-1)],
    mkCase "/quiet/overflow/min-times-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-int-before-missing-y" #[intV 1],
    mkCase "/underflow/two-ints-before-missing-x" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-type-with-two-items" #[.cell Cell.empty, .null],
    mkCase "/type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/type-before-divzero-funnel" #[intV 5, .null, intV 0],
    mkCaseFromIntVals "/quiet/nan/z-via-program"
      #[.num 5, .num 7, .nan],
    mkCaseFromIntVals "/quiet/nan/y-via-program"
      #[.num 5, .nan, .num 7],
    mkCaseFromIntVals "/quiet/nan/x-via-program"
      #[.nan, .num 5, .num 7],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/x"
      #[.num (pow2 257), .num 5, .num 7],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/y"
      #[.num 5, .num (-(pow2 257)), .num 7],
    mkCaseFromIntVals "/error-order/pushint-overflow-before-op/z"
      #[.num 5, .num 7, .num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivcSetGasExact), .tonEnvOp .setGasLimit, qmuldivcInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuldivcInstr]
  ]
  fuzz := #[
    { seed := 2026020836
      count := 700
      gen := genQmuldivcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULDIVC
