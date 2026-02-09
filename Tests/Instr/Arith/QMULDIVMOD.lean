import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULDIVMOD

/-
QMULDIVMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
    (`execInstrArithMulDivMod`, `.mulDivMod d roundMode addMode quiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, mode `-1` floor semantics)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb7a98` + args4 decode to quiet `.mulDivMod`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean generic `.mulDivMod`: 7 branch sites / 16 terminal outcomes
  (dispatch guard, add/non-add arity split, operand-shape split, divisor-zero split,
   round-mode validity, `d` switch, non-num `d=3` split).
- C++ `exec_muldivmod`: 5 branch sites / 11 terminal outcomes
  (version gate for add-remap registration, invalid-opcode guard, underflow guard,
   add/non-add pop path, result-shape switch by `d`).

QMULDIVMOD specialization under test:
- fixed params: `d=3`, `roundMode=-1` (floor), `addMode=false`, `quiet=true`.

Key risk areas covered:
- floor quotient/remainder sign semantics and output order (`q`, then `r`);
- quiet funnels for divisor-zero, NaN inputs, and quotient overflow (`NaN, 0`);
- strict underflow-before-type behavior (`need=3` short-circuit before pops);
- pop/type order (`z`, then `y`, then `x`) on mixed-type stacks;
- 257-bit boundary arithmetic and exact/inexact remainder classifications;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QMULDIVMOD`;
- oracle serialization hygiene: NaN/out-of-range inputs injected via program prelude.
-/

private def qmuldivmodId : InstrId := { name := "QMULDIVMOD" }

private def qmuldivmodInstr : Instr := .mulDivMod 3 (-1) false true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuldivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmuldivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmuldivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQMulDivModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuldivmodInstr stack

private def runQMulDivModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 4707)) stack

private def qmuldivmodSetGasExact : Int :=
  computeExactGasBudget qmuldivmodInstr

private def qmuldivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuldivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def smallFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def smallDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQMulDivMod (x y z : Int) : String :=
  if z = 0 then
    "divzero"
  else
    let tmp : Int := x * y
    let (q, r) := divModRound tmp z (-1)
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQMulDivModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulDivMod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulDivMod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-signed" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulDivMod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-signed" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/divzero/random" #[intV x, intV y, intV 0], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool smallFactorPool rng1
      let (y, r3) := pickFromPool smallFactorPool r2
      let (z, r4) := pickFromPool smallDivisorPool r3
      let kind := classifyQMulDivMod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/small-sign-mix" #[intV x, intV y, intV z], r4)
    else if shape = 5 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow/min-times-negone"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow/max-times-max"
        #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow/min-times-min"
        #[intV minInt257, intV minInt257, intV 1], rng1)
    else if shape = 8 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQMulDivMod 0 y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQMulDivMod x 0 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQMulDivMod x y 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/divisor-one" #[intV x, intV y, intV 1], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQMulDivMod x y (-1)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/divisor-neg-one" #[intV x, intV y, intV (-1)], r3)
    else if shape = 12 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, zBad], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let (yBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second" #[intV x, yBad, intV z], r4)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let (xBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xBad, intV y, intV z], r4)
    else if shape = 18 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/z-before-y-when-both-non-int"
        #[intV 1, .cell Cell.empty, .null], rng1)
    else if shape = 19 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/y-before-x-after-z-int"
        #[.null, .cell Cell.empty, intV 1], rng1)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[.num x, .num y, .nan], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[.num x, .nan, .num z], r3)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num y, .num z], r3)
    else if shape = 23 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/range/x-via-program"
        #[.num xOut, .num y, .num z], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/range/y-via-program"
        #[.num x, .num yOut, .num z], r4)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/range/z-via-program"
        #[.num x, .num y, .num zOut], r4)
    else if shape = 26 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/range/all-via-program"
        #[.num xOut, .num yOut, .num zOut], r4)
    else if shape = 27 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickFromPool smallDivisorPool r3
      let kind := classifyQMulDivMod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-divisor-pool" #[intV x, intV y, intV z], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulDivMod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/fallback" #[intV x, intV y, intV z], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuldivmodId
  unit := #[
    { name := "/unit/ok/floor-sign-remainder-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 10, 1),
            (-7, 3, 2, -11, 1),
            (7, -3, 2, -11, 1),
            (-7, -3, 2, 10, 1),
            (7, 3, -2, -11, -1),
            (-7, 3, -2, 10, -1),
            (7, -3, -2, 10, -1),
            (-7, -3, -2, -11, -1),
            (5, 5, 2, 12, 1),
            (-5, 5, 2, -13, 1),
            (5, -5, 2, -13, 1),
            (-5, -5, 2, 12, 1),
            (-1, 1, 2, -1, 1),
            (1, -1, 2, -1, 1),
            (-1, -1, 2, 0, 1),
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
          expectOkStack s!"/unit/ok/({x}*{y})/{z}"
            (runQMulDivModDirect #[intV x, intV y, intV z])
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
            (maxInt257, 1, 2, (pow2 255) - 1, 1),
            (maxInt257, -1, 2, -(pow2 255), 1),
            (minInt257, 1, 2, -(pow2 255), 0),
            (minInt257, 1, -2, pow2 255, 0),
            (minInt257 + 1, -1, 2, (pow2 255) - 1, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"/unit/ok/boundary/({x}*{y})/{z}"
            (runQMulDivModDirect #[intV x, intV y, intV z])
            #[intV q, intV r] }
    ,
    { name := "/unit/quiet/divzero-and-overflow-funnels"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQMulDivModDirect #[intV 5, intV 7, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQMulDivModDirect #[intV 0, intV 7, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow/min-times-neg-one-over-one"
          (runQMulDivModDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-times-one-over-neg-one"
          (runQMulDivModDirect #[intV minInt257, intV 1, intV (-1)]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/max-times-max-over-one"
          (runQMulDivModDirect #[intV maxInt257, intV maxInt257, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-times-min-over-one"
          (runQMulDivModDirect #[intV minInt257, intV minInt257, intV 1]) #[.int .nan, intV 0] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow/empty" (runQMulDivModDirect #[]) .stkUnd
        expectErr "/unit/error/underflow/one-item" (runQMulDivModDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow/two-items-with-non-int"
          (runQMulDivModDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/error/type/pop-z-first"
          (runQMulDivModDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type/pop-y-second"
          (runQMulDivModDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type/pop-x-third"
          (runQMulDivModDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error/order-z-before-y-when-both-non-int"
          (runQMulDivModDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error/order-y-before-x-after-z-int"
          (runQMulDivModDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQMulDivModDispatchFallback #[]) #[intV 4707] }
  ]
  oracle := #[
    mkCase "/ok/floor/sign/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "/ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "/ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "/ok/floor/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "/ok/floor/sign/pos-pos-neg-divisor" #[intV 7, intV 3, intV (-2)],
    mkCase "/ok/floor/sign/neg-pos-neg-divisor" #[intV (-7), intV 3, intV (-2)],
    mkCase "/ok/floor/sign/pos-neg-neg-divisor" #[intV 7, intV (-3), intV (-2)],
    mkCase "/ok/floor/sign/neg-neg-neg-divisor" #[intV (-7), intV (-3), intV (-2)],
    mkCase "/ok/floor/near-zero/neg-over-pos" #[intV (-1), intV 1, intV 2],
    mkCase "/ok/floor/near-zero/pos-over-neg" #[intV 1, intV 1, intV (-2)],
    mkCase "/ok/floor/near-zero/neg-over-neg" #[intV (-1), intV (-1), intV 2],
    mkCase "/ok/exact/positive-product" #[intV 42, intV 6, intV 7],
    mkCase "/ok/exact/negative-product" #[intV (-42), intV 6, intV 7],
    mkCase "/ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "/ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "/ok/boundary/max-times-one-over-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-negone-over-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "/ok/boundary/min-times-one-over-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-times-negone-over-negone" #[intV minInt257, intV (-1), intV (-1)],
    mkCase "/ok/boundary/min-plus-one-times-negone-over-negone"
      #[intV (minInt257 + 1), intV (-1), intV (-1)],
    mkCase "/ok/boundary/max-times-one-over-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "/ok/boundary/max-times-negone-over-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "/ok/boundary/min-times-one-over-two" #[intV minInt257, intV 1, intV 2],
    mkCase "/ok/boundary/min-times-one-over-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/min-plus-one-times-negone-over-two"
      #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "/quiet/overflow/min-times-negone-over-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "/quiet/overflow/min-times-one-over-negone" #[intV minInt257, intV 1, intV (-1)],
    mkCase "/quiet/overflow/max-times-max-over-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "/quiet/overflow/min-times-min-over-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-item" #[intV 1],
    mkCase "/underflow/two-items-with-non-int" #[.null, .cell Cell.empty],
    mkCase "/type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "/quiet/nan-z-via-program" #[.num 5, .num 7, .nan],
    mkCaseFromIntVals "/quiet/nan-y-via-program" #[.num 5, .nan, .num 3],
    mkCaseFromIntVals "/quiet/nan-x-via-program" #[.nan, .num 5, .num 3],
    mkCaseFromIntVals "/quiet/nan-all-via-program" #[.nan, .nan, .nan],
    mkCaseFromIntVals "/error-order/pushint-overflow-high-x-before-op"
      #[.num (maxInt257 + 1), .num 5, .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-low-x-before-op"
      #[.num (minInt257 - 1), .num 5, .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-high-y-before-op"
      #[.num 5, .num (maxInt257 + 1), .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-low-y-before-op"
      #[.num 5, .num (minInt257 - 1), .num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-high-z-before-op"
      #[.num 5, .num 7, .num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-low-z-before-op"
      #[.num 5, .num 7, .num (minInt257 - 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-all-before-op"
      #[.num (pow2 257), .num (-(pow2 257)), .num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivmodSetGasExact), .tonEnvOp .setGasLimit, qmuldivmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuldivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020831
      count := 700
      gen := genQMulDivModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULDIVMOD
