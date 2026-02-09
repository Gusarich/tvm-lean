import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULDIVMOD

/-
MULDIVMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa98` + args4 decode wiring)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, opcode registration in `register_div_ops`)

Branch counts used for this suite:
- Lean generic `.mulDivMod`: 7 branch sites / 16 terminal outcomes
  (dispatch arm; add-mode pop split; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch; non-num `d==3` split).
- C++ `exec_muldivmod`: 5 branch sites / 11 terminal outcomes
  (versioned add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add pop path; `d`-dependent result-shape switch).

MULDIVMOD specialization:
- fixed opcode form `.mulDivMod 3 (-1) false false` (floor mode, non-add, non-quiet),
  terminal outcomes reached by this suite: `ok`, `stkUnd`, `typeChk`,
  `intOv` (divisor zero), `intOv` (NaN funnel), `intOv` (quotient overflow).

Key risk areas covered:
- floor quotient/remainder semantics and output order (`q` then `r`);
- pop/error ordering (`z`, then `y`, then `x`) with underflow guard precedence;
- non-quiet NaN and out-of-range input injection via program-only `PUSHINT`;
- 257-bit boundary overflow (`minInt257 * (-1) / 1`, large-product quotients);
- exact gas threshold for `PUSHINT n; SETGASLIMIT; MULDIVMOD`.
-/

private def muldivmodId : InstrId := { name := "MULDIVMOD" }

private def muldivmodInstr : Instr := .mulDivMod 3 (-1) false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muldivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muldivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push muldivmodInstr) gasLimits fuel

private def runMuldivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod muldivmodInstr stack

private def runMuldivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 3310)) stack

private def muldivmodSetGasExact : Int :=
  computeExactGasBudget muldivmodInstr

private def muldivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muldivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def floorFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def floorDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def outOfRangeInputPool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def classifyMuldivmod (x y z : Int) : String :=
  if z = 0 then
    "divzero"
  else
    let t : Int := x * y
    let (q, r) := divModRound t z (-1)
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if t = 0 then
      "zero"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genMuldivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (case0, rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let (z0, r4) := pickNonZeroInt r3
      let kind := classifyMuldivmod x0 y0 z0
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-boundary"
        #[intV x0, intV y0, intV z0], r4)
    else if shape = 1 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      let kind := classifyMuldivmod x0 y0 z0
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-signed"
        #[intV x0, intV y0, intV z0], r4)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      let (z0, r4) := pickNonZeroInt r3
      let kind := classifyMuldivmod x0 y0 z0
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-boundary"
        #[intV x0, intV y0, intV z0], r4)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      let kind := classifyMuldivmod x0 y0 z0
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-signed"
        #[intV x0, intV y0, intV z0], r4)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let kind := classifyMuldivmod x0 y0 0
      (mkCase s!"fuzz/shape-{shape}/{kind}/divisor-zero"
        #[intV x0, intV y0, intV 0], r3)
    else if shape = 5 then
      let (x0, r2) := pickFromPool floorFactorPool rng1
      let (y0, r3) := pickFromPool floorFactorPool r2
      let (z0, r4) := pickFromPool floorDivisorPool r3
      let kind := classifyMuldivmod x0 y0 z0
      (mkCase s!"fuzz/shape-{shape}/{kind}/small-floor"
        #[intV x0, intV y0, intV z0], r4)
    else if shape = 6 then
      let kind := classifyMuldivmod minInt257 (-1) 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/min-neg-one-div-one"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 7 then
      let kind := classifyMuldivmod maxInt257 maxInt257 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/max-max-div-one"
        #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 8 then
      let kind := classifyMuldivmod minInt257 minInt257 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/min-min-div-one"
        #[intV minInt257, intV minInt257, intV 1], rng1)
    else if shape = 9 then
      let (x0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickNonZeroInt r2
      let kind := classifyMuldivmod x0 0 z0
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-right-factor"
        #[intV x0, intV 0, intV z0], r3)
    else if shape = 10 then
      let (y0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickNonZeroInt r2
      let kind := classifyMuldivmod 0 y0 z0
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-left-factor"
        #[intV 0, intV y0, intV z0], r3)
    else if shape = 11 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/program-z"
        #[IntVal.num x0, IntVal.num y0, IntVal.nan], r3)
    else if shape = 12 then
      let (x0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/program-y"
        #[IntVal.num x0, IntVal.nan, IntVal.num z0], r3)
    else if shape = 13 then
      let (y0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/program-x"
        #[IntVal.nan, IntVal.num y0, IntVal.num z0], r3)
    else if shape = 14 then
      let (oor, r2) := pickFromPool outOfRangeInputPool rng1
      let (y0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/program-x"
        #[IntVal.num oor, IntVal.num y0, IntVal.num z0], r4)
    else if shape = 15 then
      let (x0, r2) := pickSigned257ish rng1
      let (oor, r3) := pickFromPool outOfRangeInputPool r2
      let (z0, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/program-y"
        #[IntVal.num x0, IntVal.num oor, IntVal.num z0], r4)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (oor, r4) := pickFromPool outOfRangeInputPool r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/program-z"
        #[IntVal.num x0, IntVal.num y0, IntVal.num oor], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := muldivmodId
  unit := #[
    { name := "unit/floor/sign-remainder-and-output-order"
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
            (1, 1, -2, -1, -1),
            (-1, 1, -2, 0, -1),
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
          expectOkStack s!"({x}*{y})/{z}"
            (runMuldivmodDirect #[intV x, intV y, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/floor/boundary-successes"
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
            (minInt257 + 1, -1, 2, (pow2 255) - 1, 1),
            (maxInt257, 0, 1, 0, 0),
            (minInt257, 0, -7, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})/{z}"
            (runMuldivmodDirect #[intV x, intV y, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/error/intov-from-divzero-and-overflow"
      run := do
        expectErr "divzero/nonzero-product-over-zero"
          (runMuldivmodDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "divzero/zero-product-over-zero"
          (runMuldivmodDirect #[intV 0, intV 7, intV 0]) .intOv
        expectErr "overflow/min-times-neg-one-div-one"
          (runMuldivmodDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/min-times-one-div-neg-one"
          (runMuldivmodDirect #[intV minInt257, intV 1, intV (-1)]) .intOv
        expectErr "overflow/max-times-max-div-one"
          (runMuldivmodDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-times-min-div-one"
          (runMuldivmodDirect #[intV minInt257, intV minInt257, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runMuldivmodDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runMuldivmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items-top-non-int" (runMuldivmodDirect #[intV 1, .null]) .stkUnd
        expectErr "type/pop-z-first" (runMuldivmodDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMuldivmodDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMuldivmodDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-z-before-y-when-both-non-int"
          (runMuldivmodDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-z-int"
          (runMuldivmodDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMuldivmodDispatchFallback #[]) #[intV 3310] }
  ]
  oracle := #[
    mkCase "ok/floor/sign/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "ok/floor/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "ok/floor/sign/pos-pos-neg-divisor" #[intV 7, intV 3, intV (-2)],
    mkCase "ok/floor/sign/neg-pos-neg-divisor" #[intV (-7), intV 3, intV (-2)],
    mkCase "ok/floor/sign/pos-neg-neg-divisor" #[intV 7, intV (-3), intV (-2)],
    mkCase "ok/floor/sign/neg-neg-neg-divisor" #[intV (-7), intV (-3), intV (-2)],
    mkCase "ok/floor/near-zero/neg-over-pos" #[intV (-1), intV 1, intV 2],
    mkCase "ok/floor/near-zero/pos-over-neg" #[intV 1, intV 1, intV (-2)],
    mkCase "ok/floor/near-zero/neg-over-neg" #[intV (-1), intV (-1), intV 2],
    mkCase "ok/exact/positive-product" #[intV 42, intV 6, intV 7],
    mkCase "ok/exact/negative-product" #[intV (-42), intV 6, intV 7],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "ok/boundary/max-times-neg-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/boundary/min-times-neg-one-div-neg-one" #[intV minInt257, intV (-1), intV (-1)],
    mkCase "ok/boundary/min-plus-one-times-neg-one-div-neg-one"
      #[intV (minInt257 + 1), intV (-1), intV (-1)],
    mkCase "ok/boundary/max-times-one-div-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-times-neg-one-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "ok/boundary/min-times-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "ok/boundary/min-times-one-div-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "ok/boundary/min-plus-one-times-neg-one-div-two"
      #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "overflow/min-times-neg-one-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "overflow/min-times-one-div-neg-one" #[intV minInt257, intV 1, intV (-1)],
    mkCase "overflow/max-times-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "overflow/min-times-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items-top-non-int" #[intV 1, .null],
    mkCase "type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "nan/program/z" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "nan/program/y" #[IntVal.num 5, IntVal.nan, IntVal.num 3],
    mkCaseFromIntVals "nan/program/x" #[IntVal.nan, IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "range/program/x-high" #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "range/program/x-low" #[IntVal.num (minInt257 - 1), IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "range/program/y-high" #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 3],
    mkCaseFromIntVals "range/program/y-low" #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 3],
    mkCaseFromIntVals "range/program/z-high" #[IntVal.num 5, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "range/program/z-low" #[IntVal.num 5, IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivmodSetGasExact), .tonEnvOp .setGasLimit, muldivmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, muldivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020814
      count := 700
      gen := genMuldivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULDIVMOD
