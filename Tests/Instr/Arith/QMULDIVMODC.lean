import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULDIVMODC

/-
QMULDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
    (`execInstrArithMulDivMod`, `.mulDivMod d roundMode addMode quiet`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type ordering)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (24-bit quiet decode `0xb7a98 + args4` to `.mulDivMod`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean generic `.mulDivMod`: 6 branch sites / 14 terminal outcomes
  (dispatch guard; stack-depth gate; add/non-add pop path; numeric-vs-NaN split;
   divisor-zero split; `d` result-shape switch).
- Lean QMULDIVMODC specialization: 6 branch sites / 8 reachable terminal outcomes
  (success pair; quiet divzero pair; quiet NaN pair; quiet overflow shape `q=NaN,r=0`;
   `stkUnd`; pop-`z` type; pop-`y` type; pop-`x` type).
- C++ quiet `exec_muldivmod`: 5 branch sites / 11 aligned terminal outcomes
  (opcode-args guard, underflow guard, add-mode remap gate, operand pop/type path,
   `d` switch with `DIVMOD` dual push under quiet overflow behavior).

Key risk areas covered:
- ceil quotient/remainder behavior for mixed-sign products and near-zero fractions;
- quiet funnels for divzero, NaN operands, and quotient overflow;
- pop/error ordering (`z`, then `y`, then `x`) and underflow-before-type precedence;
- oracle serialization safety: NaN/out-of-range operands injected only via program prelude;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qmuldivmodcId : InstrId := { name := "QMULDIVMODC" }

private def qmuldivmodcInstr : Instr := .mulDivMod 3 1 false true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuldivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmuldivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmuldivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programSuffix) gasLimits fuel

private def runQMulDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuldivmodcInstr stack

private def runQMulDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 9031)) stack

private def qmuldivmodcSetGasExact : Int :=
  computeExactGasBudget qmuldivmodcInstr

private def qmuldivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuldivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def ceilFactorPool : Array Int :=
  #[-11, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 11]

private def ceilDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def classifyQMulDivModC (x y z : Int) : String :=
  let tmp := x * y
  if z = 0 then
    "quiet-divzero"
  else
    let (q, r) := divModRound tmp z 1
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else if q = 0 then
      "near-zero"
    else
      "inexact"

private def mkFiniteFuzzCase (shape : Nat) (tag : Nat) (x y z : Int) : OracleCase :=
  let kind := classifyQMulDivModC x y z
  mkCase s!"/fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV z]

private def genQMulDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x0, r3) := pickInt257Boundary rng2
    let (y0, r4) := pickInt257Boundary r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 1 then
    let (x0, r3) := pickInt257Boundary rng2
    let (y0, r4) := pickSigned257ish r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 2 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickInt257Boundary r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 3 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 4 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkFiniteFuzzCase shape tag x0 y0 0, r4)
  else if shape = 5 then
    let (x0, r3) := pickFromPool ceilFactorPool rng2
    let (y0, r4) := pickFromPool ceilFactorPool r3
    let (z0, r5) := pickFromPool ceilDivisorPool r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 6 then
    (mkFiniteFuzzCase shape tag minInt257 (-1) 1, rng2)
  else if shape = 7 then
    (mkFiniteFuzzCase shape tag minInt257 1 (-1), rng2)
  else if shape = 8 then
    (mkFiniteFuzzCase shape tag maxInt257 maxInt257 1, rng2)
  else if shape = 9 then
    (mkFiniteFuzzCase shape tag minInt257 minInt257 1, rng2)
  else if shape = 10 then
    let (y0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkFiniteFuzzCase shape tag 0 y0 z0, r4)
  else if shape = 11 then
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkFiniteFuzzCase shape tag x0 0 z0, r4)
  else if shape = 12 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkFiniteFuzzCase shape tag x0 y0 1, r4)
  else if shape = 13 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkFiniteFuzzCase shape tag x0 y0 (-1), r4)
  else if shape = 14 then
    (mkCase s!"/fuzz/shape-{shape}/underflow-empty-{tag}" #[], rng2)
  else if shape = 15 then
    let (x0, r3) := pickSigned257ish rng2
    (mkCase s!"/fuzz/shape-{shape}/underflow-one-{tag}" #[intV x0], r3)
  else if shape = 16 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkCase s!"/fuzz/shape-{shape}/underflow-two-{tag}" #[intV x0, intV y0], r4)
  else if shape = 17 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    let (zLike, r5) := pickNonInt r4
    (mkCase s!"/fuzz/shape-{shape}/type-pop-z-first-{tag}" #[intV x0, intV y0, zLike], r5)
  else if shape = 18 then
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    let (yLike, r5) := pickNonInt r4
    (mkCase s!"/fuzz/shape-{shape}/type-pop-y-second-{tag}" #[intV x0, yLike, intV z0], r5)
  else if shape = 19 then
    let (y0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    let (xLike, r5) := pickNonInt r4
    (mkCase s!"/fuzz/shape-{shape}/type-pop-x-third-{tag}" #[xLike, intV y0, intV z0], r5)
  else if shape = 20 then
    (mkCase s!"/fuzz/shape-{shape}/error-order-z-before-y-{tag}"
      #[intV 1, .cell Cell.empty, .null], rng2)
  else if shape = 21 then
    (mkCase s!"/fuzz/shape-{shape}/error-order-y-before-x-{tag}"
      #[.null, .cell Cell.empty, intV 1], rng2)
  else if shape = 22 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkInputCase s!"/fuzz/shape-{shape}/quiet-nan-z-via-program-{tag}"
      #[IntVal.num x0, IntVal.num y0, IntVal.nan], r4)
  else if shape = 23 then
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkInputCase s!"/fuzz/shape-{shape}/quiet-nan-y-via-program-{tag}"
      #[IntVal.num x0, IntVal.nan, IntVal.num z0], r4)
  else if shape = 24 then
    let (y0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkInputCase s!"/fuzz/shape-{shape}/quiet-nan-x-via-program-{tag}"
      #[IntVal.nan, IntVal.num y0, IntVal.num z0], r4)
  else if shape = 25 then
    let (xOut, r3) := pickInt257OutOfRange rng2
    let (y0, r4) := pickSigned257ish r3
    let (z0, r5) := pickNonZeroInt r4
    (mkInputCase s!"/fuzz/shape-{shape}/range-x-via-program-{tag}"
      #[IntVal.num xOut, IntVal.num y0, IntVal.num z0], r5)
  else if shape = 26 then
    let (x0, r3) := pickSigned257ish rng2
    let (yOut, r4) := pickInt257OutOfRange r3
    let (z0, r5) := pickNonZeroInt r4
    (mkInputCase s!"/fuzz/shape-{shape}/range-y-via-program-{tag}"
      #[IntVal.num x0, IntVal.num yOut, IntVal.num z0], r5)
  else if shape = 27 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    let (zOut, r5) := pickInt257OutOfRange r4
    (mkInputCase s!"/fuzz/shape-{shape}/range-z-via-program-{tag}"
      #[IntVal.num x0, IntVal.num y0, IntVal.num zOut], r5)
  else if shape = 28 then
    let (xOut, r3) := pickInt257OutOfRange rng2
    let (yOut, r4) := pickInt257OutOfRange r3
    let (zOut, r5) := pickInt257OutOfRange r4
    (mkInputCase s!"/fuzz/shape-{shape}/range-all-via-program-{tag}"
      #[IntVal.num xOut, IntVal.num yOut, IntVal.num zOut], r5)
  else
    let (x0, r3) := pickFromPool ceilFactorPool rng2
    let (y0, r4) := pickFromPool ceilFactorPool r3
    let (z0, r5) := pickFromPool ceilDivisorPool r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)

def suite : InstrSuite where
  id := qmuldivmodcId
  unit := #[
    { name := "/unit/ok/ceil-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 11, -1),
            (-7, 3, 2, -10, -1),
            (7, -3, 2, -10, -1),
            (-7, -3, 2, 11, -1),
            (7, 3, -2, -10, 1),
            (-7, 3, -2, 11, 1),
            (7, -3, -2, 11, 1),
            (-7, -3, -2, -10, 1),
            (5, 5, 2, 13, -1),
            (-5, 5, 2, -12, -1),
            (5, -5, 2, -12, -1),
            (-5, -5, 2, 13, -1),
            (-1, 1, 2, 0, -1),
            (1, -1, 2, 0, -1),
            (-1, -1, 2, 1, -1),
            (0, 9, 5, 0, 0),
            (9, 0, 5, 0, 0),
            (42, 6, 7, 36, 0),
            (-42, 6, 7, -36, 0),
            (42, -6, 7, -36, 0),
            (-42, -6, 7, 36, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"/unit/ok/ceil/{x}/{y}/{z}"
            (runQMulDivModCDirect #[intV x, intV y, intV z])
            #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, maxInt257, 0),
            (maxInt257, -1, 1, -maxInt257, 0),
            (minInt257, 1, 1, minInt257, 0),
            (minInt257, -1, -1, minInt257, 0),
            (minInt257 + 1, -1, -1, -maxInt257, 0),
            (maxInt257, 1, 2, pow2 255, -1),
            (maxInt257, -1, 2, 1 - (pow2 255), -1),
            (minInt257, 1, 2, -(pow2 255), 0),
            (minInt257, 1, -2, pow2 255, 0),
            (minInt257 + 1, -1, 2, pow2 255, -1),
            (maxInt257, 1, -2, 1 - (pow2 255), 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"/unit/ok/boundary/{x}/{y}/{z}"
            (runQMulDivModCDirect #[intV x, intV y, intV z])
            #[intV q, intV r] }
    ,
    { name := "/unit/quiet/divzero-overflow-and-below-preservation"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQMulDivModCDirect #[intV 5, intV 7, intV 0])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQMulDivModCDirect #[intV 0, intV 7, intV 0])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow/min-times-negone-div-one"
          (runQMulDivModCDirect #[intV minInt257, intV (-1), intV 1])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-times-one-div-negone"
          (runQMulDivModCDirect #[intV minInt257, intV 1, intV (-1)])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/max-times-max-div-one"
          (runQMulDivModCDirect #[intV maxInt257, intV maxInt257, intV 1])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-times-min-div-one"
          (runQMulDivModCDirect #[intV minInt257, intV minInt257, intV 1])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/below-stack-preserved"
          (runQMulDivModCDirect #[.null, intV 7, intV 3, intV 2])
          #[.null, intV 11, intV (-1)] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow-empty" (runQMulDivModCDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-one-int" (runQMulDivModCDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-ints" (runQMulDivModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/order-underflow-before-type-with-two-items"
          (runQMulDivModCDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/error/type-pop-z-first"
          (runQMulDivModCDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type-pop-y-second"
          (runQMulDivModCDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type-pop-x-third"
          (runQMulDivModCDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error/order-pop-z-before-y-when-both-non-int"
          (runQMulDivModCDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error/order-pop-y-before-x-after-z-int"
          (runQMulDivModCDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQMulDivModCDispatchFallback #[]) #[intV 9031] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "/ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "/ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "/ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "/ok/ceil/sign/pos-pos-neg-divisor" #[intV 7, intV 3, intV (-2)],
    mkCase "/ok/ceil/sign/neg-pos-neg-divisor" #[intV (-7), intV 3, intV (-2)],
    mkCase "/ok/ceil/near-zero/neg-pos" #[intV (-1), intV 1, intV 2],
    mkCase "/ok/ceil/near-zero/pos-neg" #[intV 1, intV (-1), intV 2],
    mkCase "/ok/exact/pos-pos" #[intV 42, intV 6, intV 7],
    mkCase "/ok/exact/neg-pos" #[intV (-42), intV 6, intV 7],
    mkCase "/ok/exact/pos-neg" #[intV 42, intV (-6), intV 7],
    mkCase "/ok/exact/neg-neg" #[intV (-42), intV (-6), intV 7],
    mkCase "/ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "/ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "/ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-neg-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "/ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-times-neg-one-div-neg-one" #[intV minInt257, intV (-1), intV (-1)],
    mkCase "/ok/boundary/min-plus-one-times-neg-one-div-neg-one"
      #[intV (minInt257 + 1), intV (-1), intV (-1)],
    mkCase "/ok/boundary/max-times-one-div-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "/ok/boundary/min-times-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "/ok/boundary/min-times-one-div-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/max-times-one-div-neg-two" #[intV maxInt257, intV 1, intV (-2)],
    mkCase "/quiet/divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "/quiet/overflow/min-times-neg-one-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "/quiet/overflow/min-times-one-div-neg-one" #[intV minInt257, intV 1, intV (-1)],
    mkCase "/quiet/overflow/max-times-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "/quiet/overflow/min-times-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-int-before-missing-y" #[intV 1],
    mkCase "/underflow/two-ints-before-missing-x" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "/type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkInputCase "/quiet/nan/z-via-program" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInputCase "/quiet/nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkInputCase "/quiet/nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkInputCase "/quiet/nan/all-via-program" #[IntVal.nan, IntVal.nan, IntVal.nan],
    mkInputCase "/error-order/pushint-out-of-range-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 1, IntVal.num 1],
    mkInputCase "/error-order/pushint-out-of-range-low-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (minInt257 - 1)],
    mkInputCase "/error-order/pushint-out-of-range-pow2-257-before-op"
      #[IntVal.num (pow2 257), IntVal.num 1, IntVal.num 1],
    mkInputCase "/error-order/pushint-out-of-range-neg-pow2-257-before-op"
      #[IntVal.num 1, IntVal.num (-(pow2 257)), IntVal.num 1],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivmodcSetGasExact), .tonEnvOp .setGasLimit, qmuldivmodcInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuldivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020841
      count := 700
      gen := genQMulDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULDIVMODC
