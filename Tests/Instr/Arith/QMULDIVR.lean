import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULDIVR

/-
QMULDIVR branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest mode `roundMode = 0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (quiet 24-bit `0xb7a98` args4 decode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest-rounding adjustment)

Branch/terminal counts used for this suite (QMULDIVR specialization):
- Lean (`execInstrArithMulDivMod`, `d=1`, `roundMode=0`, `add=false`, `quiet=true`):
  7 branch sites / 14 terminal outcomes
  (dispatch arm; arity gate; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch; non-num (`NaN`) split).
- Lean (`pushIntQuiet` on quotient result): 2 branch sites / 3 outcomes
  (num-vs-NaN; signed-257 fit-vs-quiet-NaN funnel).
- C++ (`exec_muldivmod` + `push_int_quiet`): 8 branch sites / 16 aligned outcomes
  (opcode remap/arity checks; pop/type paths; divisor-zero funnel;
   nearest-rounding tie adjustment; quiet result push fit-vs-NaN).

Key risk areas covered:
- nearest-rounding of `(x * y) / z` across sign mixes and exact half ties;
- quiet funnels for division-by-zero, overflow, and NaN operands (must push NaN);
- pop/error ordering (`z` then `y` then `x`) and underflow-before-type;
- large intermediate products that reduce back into signed-257 range after division;
- oracle serialization hygiene: NaN/out-of-range ints injected via program prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QMULDIVR`.
-/

private def qmuldivrId : InstrId := { name := "QMULDIVR" }

private def qmuldivrInstr : Instr := .mulDivMod 1 0 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuldivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmuldivrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmuldivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQmuldivrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuldivrInstr stack

private def runQmuldivrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 3315)) stack

private def qmuldivrSetGasExact : Int :=
  computeExactGasBudget qmuldivrInstr

private def qmuldivrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuldivrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def tieFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQmuldivrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/ok/boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/ok/random"
        #[IntVal.num x, IntVal.num y, IntVal.num z], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/divzero"
        #[IntVal.num x, IntVal.num y, IntVal.num 0], r3)
    else if shape = 3 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/ok/tie-z-two"
        #[IntVal.num x, IntVal.num y, IntVal.num 2], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/ok/tie-z-neg-two"
        #[IntVal.num x, IntVal.num y, IntVal.num (-2)], r3)
    else if shape = 5 then
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/overflow-min-times-neg-one-div-one"
        #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 1], rng1)
    else if shape = 6 then
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/overflow-max-times-max-div-one"
        #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1], rng1)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/ok/zero-left-factor"
        #[IntVal.num 0, IntVal.num y, IntVal.num z], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/ok/zero-right-factor"
        #[IntVal.num x, IntVal.num 0, IntVal.num z], r3)
    else if shape = 9 then
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/ok/huge-intermediate-reduces"
        #[IntVal.num maxInt257, IntVal.num 2, IntVal.num 2], rng1)
    else if shape = 10 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-ints" #[intV x, intV y], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, zLike], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second" #[intV x, yLike, intV z], r4)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xLike, intV y, intV z], r4)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num z], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num z], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 19 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-range-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num z], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-range-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num z], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-range-z-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num zOut], r4)
    else
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/overflow-min-times-min-div-one"
        #[IntVal.num minInt257, IntVal.num minInt257, IntVal.num 1], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuldivrId
  unit := #[
    { name := "/unit/round/nearest-sign-combos-and-half-ties"
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
            (1, 1, 2, 1),
            (-1, 1, 2, 0),
            (1, -1, 2, 0),
            (-1, -1, 2, 1),
            (42, 6, 7, 36),
            (-42, 6, 7, -36),
            (42, -6, 7, -36),
            (-42, -6, 7, 36)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"/unit/check/({x}*{y})/{z}"
            (runQmuldivrDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "/unit/round/boundary-successes-and-huge-intermediate-reduction"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, maxInt257),
            (maxInt257, -1, 1, -maxInt257),
            (minInt257, 1, 1, minInt257),
            (minInt257, -1, -1, minInt257),
            (minInt257 + 1, -1, -1, -maxInt257),
            (maxInt257, 1, 2, pow2 255),
            (maxInt257, -1, 2, -(pow2 255) + 1),
            (minInt257, 1, 2, -(pow2 255)),
            (minInt257, 1, -2, pow2 255),
            (minInt257 + 1, -1, 2, pow2 255),
            (maxInt257, 2, 2, maxInt257),
            (minInt257, -1, -1, minInt257),
            (0, -7, 3, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"/unit/check/({x}*{y})/{z}"
            (runQmuldivrDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "/unit/quiet/divzero-overflow-and-nan-funnel"
      run := do
        expectOkStack "/unit/check/quiet/divzero/nonzero-product-over-zero"
          (runQmuldivrDirect #[intV 5, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/check/quiet/divzero/zero-product-over-zero"
          (runQmuldivrDirect #[intV 0, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/check/quiet/overflow/min-times-neg-one-div-one"
          (runQmuldivrDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan]
        expectOkStack "/unit/check/quiet/overflow/max-times-max-div-one"
          (runQmuldivrDirect #[intV maxInt257, intV maxInt257, intV 1]) #[.int .nan]
        expectOkStack "/unit/check/quiet/overflow/min-times-min-div-one"
          (runQmuldivrDirect #[intV minInt257, intV minInt257, intV 1]) #[.int .nan]
        expectOkStack "/unit/check/quiet/nan-x"
          (runQmuldivrDirect #[.int .nan, intV 7, intV 3]) #[.int .nan]
        expectOkStack "/unit/check/quiet/nan-y"
          (runQmuldivrDirect #[intV 7, .int .nan, intV 3]) #[.int .nan]
        expectOkStack "/unit/check/quiet/nan-z"
          (runQmuldivrDirect #[intV 7, intV 3, .int .nan]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/check/underflow/empty"
          (runQmuldivrDirect #[]) .stkUnd
        expectErr "/unit/check/underflow/one-int"
          (runQmuldivrDirect #[intV 1]) .stkUnd
        expectErr "/unit/check/underflow/two-ints"
          (runQmuldivrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/check/error-order/one-non-int-underflow-first"
          (runQmuldivrDirect #[.null]) .stkUnd
        expectErr "/unit/check/type/pop-z-first"
          (runQmuldivrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/check/type/pop-y-second"
          (runQmuldivrDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/check/type/pop-x-third"
          (runQmuldivrDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/check/error-order/pop-z-before-y-when-both-non-int"
          (runQmuldivrDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/check/error-order/pop-y-before-x-after-z-int"
          (runQmuldivrDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/check/dispatch/fallback"
          (runQmuldivrDispatchFallback #[]) #[intV 3315] }
  ]
  oracle := #[
    mkCaseFromIntVals "/ok/round/sign/pos-pos-inexact" #[IntVal.num 7, IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "/ok/round/sign/neg-pos-inexact" #[IntVal.num (-7), IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "/ok/round/sign/pos-neg-inexact" #[IntVal.num 7, IntVal.num (-3), IntVal.num 2],
    mkCaseFromIntVals "/ok/round/sign/neg-neg-inexact" #[IntVal.num (-7), IntVal.num (-3), IntVal.num 2],
    mkCaseFromIntVals "/ok/round/tie/pos-pos-half" #[IntVal.num 5, IntVal.num 5, IntVal.num 2],
    mkCaseFromIntVals "/ok/round/tie/neg-pos-half" #[IntVal.num (-5), IntVal.num 5, IntVal.num 2],
    mkCaseFromIntVals "/ok/round/tie/pos-neg-half" #[IntVal.num 5, IntVal.num (-5), IntVal.num 2],
    mkCaseFromIntVals "/ok/round/tie/neg-neg-half" #[IntVal.num (-5), IntVal.num (-5), IntVal.num 2],
    mkCaseFromIntVals "/ok/round/tie/neg-pos-near-zero" #[IntVal.num (-1), IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "/ok/round/tie/pos-neg-near-zero" #[IntVal.num 1, IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "/ok/round/tie/neg-neg-near-zero" #[IntVal.num (-1), IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "/ok/exact/pos-pos" #[IntVal.num 42, IntVal.num 6, IntVal.num 7],
    mkCaseFromIntVals "/ok/exact/neg-pos" #[IntVal.num (-42), IntVal.num 6, IntVal.num 7],
    mkCaseFromIntVals "/ok/exact/pos-neg" #[IntVal.num 42, IntVal.num (-6), IntVal.num 7],
    mkCaseFromIntVals "/ok/exact/neg-neg" #[IntVal.num (-42), IntVal.num (-6), IntVal.num 7],
    mkCaseFromIntVals "/ok/exact/zero-left-factor" #[IntVal.num 0, IntVal.num 17, IntVal.num 5],
    mkCaseFromIntVals "/ok/exact/zero-right-factor" #[IntVal.num 17, IntVal.num 0, IntVal.num 5],
    mkCaseFromIntVals "/ok/boundary/max-times-one-div-one" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/boundary/max-times-neg-one-div-one" #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "/ok/boundary/min-times-one-div-one" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/boundary/min-times-neg-one-div-neg-one"
      #[IntVal.num minInt257, IntVal.num (-1), IntVal.num (-1)],
    mkCaseFromIntVals "/ok/boundary/min-plus-one-times-neg-one-div-neg-one"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num (-1)],
    mkCaseFromIntVals "/ok/boundary/max-times-one-div-two-round-up"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "/ok/boundary/max-times-neg-one-div-two-round-up"
      #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "/ok/boundary/min-times-one-div-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "/ok/boundary/min-times-one-div-neg-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num (-2)],
    mkCaseFromIntVals "/ok/boundary/min-plus-one-times-neg-one-div-two-round-up"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "/ok/boundary/huge-intermediate-reduces-max-times-two-div-two"
      #[IntVal.num maxInt257, IntVal.num 2, IntVal.num 2],
    mkCaseFromIntVals "/quiet/divzero/nonzero-product-over-zero" #[IntVal.num 5, IntVal.num 7, IntVal.num 0],
    mkCaseFromIntVals "/quiet/divzero/zero-product-over-zero" #[IntVal.num 0, IntVal.num 7, IntVal.num 0],
    mkCaseFromIntVals "/quiet/overflow/min-times-neg-one-div-one" #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "/quiet/overflow/max-times-max-div-one" #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1],
    mkCaseFromIntVals "/quiet/overflow/max-times-max-div-neg-one"
      #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num (-1)],
    mkCaseFromIntVals "/quiet/overflow/min-times-min-div-one" #[IntVal.num minInt257, IntVal.num minInt257, IntVal.num 1],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-int-before-missing-y" #[intV 1],
    mkCase "/underflow/two-ints-before-missing-x" #[intV 1, intV 2],
    mkCase "/type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "/quiet/nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "/quiet/nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 3],
    mkCaseFromIntVals "/quiet/nan/z-via-program" #[IntVal.num 5, IntVal.num 3, IntVal.nan],
    mkCaseFromIntVals "/error-order/pushint-range-x-before-qmuldivr"
      #[IntVal.num (maxInt257 + 1), IntVal.num 2, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-range-y-before-qmuldivr"
      #[IntVal.num 2, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-range-z-before-qmuldivr"
      #[IntVal.num 2, IntVal.num 3, IntVal.num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivrSetGasExact), .tonEnvOp .setGasLimit, qmuldivrInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuldivrInstr]
  ]
  fuzz := #[
    { seed := 2026020816
      count := 700
      gen := genQmuldivrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULDIVR
