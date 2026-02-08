import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULDIVMODR

/-
MULDIVMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `0` nearest/ties-to-+∞)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa98` args4 decode to `.mulDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (generic `.mulDivMod`): 8 branch sites / 18 terminal outcomes
  (dispatch/fallback, stack arity check, add-mode pop split, numeric-vs-NaN split,
   divisor-zero split, round-mode validity split, `d` switch, non-num `d=3` split).
- C++ (`exec_muldivmod`): 5 branch sites / 11 terminal outcomes
  (global-version add-remap gate, invalid-opcode guard, underflow guard,
   add vs non-add pop path, `d` switch push shape).

MULDIVMODR specialization:
- opcode args4=`0xd` under `0xa98` family;
- fixed params: `d=3`, `roundMode=0` (nearest), `addMode=false`, `quiet=false`.

Key risk areas covered:
- nearest rounding tie behavior and output order (`q` then `r`) across sign mixes;
- pop/error ordering (`z`, then `y`, then `x`; underflow before type on short stacks);
- non-quiet div-by-zero and overflow funnels to `intOv`;
- signed-257 boundary behavior around `minInt257`, `maxInt257`, and `±2` divisors;
- exact gas boundary behavior (`PUSHINT n; SETGASLIMIT; MULDIVMODR`);
- NaN and out-of-range operands injected via program only (never initial stack).
-/

private def muldivmodrId : InstrId := { name := "MULDIVMODR" }

private def muldivmodrInstr : Instr := .mulDivMod 3 0 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muldivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muldivmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[muldivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runMulDivModRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod muldivmodrInstr stack

private def runMulDivModRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 9090)) stack

private def muldivmodrSetGasExact : Int :=
  computeExactGasBudget muldivmodrInstr

private def muldivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muldivmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1]

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (outOfRangeProgramPool.size - 1)
  (outOfRangeProgramPool[idx]!, rng')

private def classifyMulDivModR (x y z : Int) : String :=
  let tmp : Int := x * y
  if z = 0 then
    "divzero"
  else
    let (q, r) := divModRound tmp z 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs z then
      "tie"
    else
      "inexact"

private def genMulDivModRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyMulDivModR x y z
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyMulDivModR x y z
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-signed" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyMulDivModR x y z
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-signed" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/divzero/random" #[intV x, intV y, intV 0], r3)
    else if shape = 4 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (z, r3) := pickFromPool tieDenominatorPool r2
      (mkCase s!"fuzz/shape-{shape}/tie/from-pool" #[intV t, intV 1, intV z], r3)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/overflow/min-times-negone" #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/overflow/max-times-max" #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/zero/left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/zero/right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyMulDivModR x y 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/z-one" #[intV x, intV y, intV 1], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyMulDivModR x y (-1)
      (mkCase s!"fuzz/shape-{shape}/{kind}/z-neg-one" #[intV x, intV y, intV (-1)], r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/tie/max-over-two" #[intV maxInt257, intV 1, intV 2], rng1)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/exact/min-over-two" #[intV minInt257, intV 1, intV 2], rng1)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-z-first" #[intV 1, intV x, .null], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-second" #[intV x, .cell Cell.empty, intV 1], r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-z"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-x"
        #[IntVal.nan, IntVal.num y, IntVal.num z], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-y"
        #[IntVal.num x, IntVal.num huge, IntVal.num z], r4)
    else if shape = 19 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-x"
        #[IntVal.num huge, IntVal.num y, IntVal.num z], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-z"
        #[IntVal.num x, IntVal.num y, IntVal.num huge], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-y"
        #[IntVal.num x, IntVal.nan, IntVal.num z], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := muldivmodrId
  unit := #[
    { name := "unit/ok/nearest-rounding-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 4, 9, -1),
            (-7, 5, 4, -9, 1),
            (7, -5, 4, -9, 1),
            (-7, -5, 4, 9, -1),
            (5, 1, 2, 3, -1),
            (-5, 1, 2, -2, -1),
            (5, 1, -2, -2, 1),
            (-5, 1, -2, 3, 1),
            (1, 1, 2, 1, -1),
            (-1, 1, 2, 0, -1),
            (1, 1, -2, 0, 1),
            (-1, 1, -2, 1, 1),
            (42, 6, 7, 36, 0),
            (-42, 6, 7, -36, 0),
            (0, 99, 5, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, q, r) =>
              expectOkStack s!"({x}*{y})/{z}"
                (runMulDivModRDirect #[intV x, intV y, intV z])
                #[intV q, intV r] }
    ,
    { name := "unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, maxInt257, 0),
            (maxInt257, -1, 1, -maxInt257, 0),
            (minInt257, 1, 1, minInt257, 0),
            (minInt257 + 1, -1, 1, maxInt257, 0),
            (maxInt257, 1, 2, pow2 255, -1),
            (maxInt257, -1, 2, -(pow2 255) + 1, -1),
            (minInt257, 1, 2, -(pow2 255), 0),
            (minInt257, 1, -2, pow2 255, 0),
            (minInt257 + 1, -1, 2, pow2 255, -1)
          ]
        for c in checks do
          match c with
          | (x, y, z, q, r) =>
              expectOkStack s!"({x}*{y})/{z}"
                (runMulDivModRDirect #[intV x, intV y, intV z])
                #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runMulDivModRDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "divzero/zero-over-zero"
          (runMulDivModRDirect #[intV 0, intV 7, intV 0]) .intOv
        expectErr "overflow/min-times-negone-over-one"
          (runMulDivModRDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/max-times-max-over-one"
          (runMulDivModRDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-times-min-over-one"
          (runMulDivModRDirect #[intV minInt257, intV minInt257, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runMulDivModRDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runMulDivModRDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runMulDivModRDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type"
          (runMulDivModRDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-z-first"
          (runMulDivModRDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second"
          (runMulDivModRDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third"
          (runMulDivModRDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-z-before-y-when-both-non-int"
          (runMulDivModRDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/pop-y-before-x-after-z-int"
          (runMulDivModRDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulDivModRDispatchFallback #[]) #[intV 9090] }
  ]
  oracle := #[
    mkCase "ok/round/inexact-pos-pos" #[intV 7, intV 5, intV 4],
    mkCase "ok/round/inexact-neg-pos" #[intV (-7), intV 5, intV 4],
    mkCase "ok/round/inexact-pos-neg" #[intV 7, intV 5, intV (-4)],
    mkCase "ok/round/inexact-neg-neg" #[intV (-7), intV 5, intV (-4)],
    mkCase "ok/tie/pos-pos" #[intV 5, intV 1, intV 2],
    mkCase "ok/tie/neg-pos" #[intV (-5), intV 1, intV 2],
    mkCase "ok/tie/pos-neg" #[intV 5, intV 1, intV (-2)],
    mkCase "ok/tie/neg-neg" #[intV (-5), intV 1, intV (-2)],
    mkCase "ok/tie/near-zero-neg-pos" #[intV (-1), intV 1, intV 2],
    mkCase "ok/tie/near-zero-pos-neg" #[intV 1, intV 1, intV (-2)],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 6, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 6, intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV 6, intV (-7)],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV 6, intV (-7)],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "ok/boundary/max-times-one-over-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "ok/boundary/max-times-negone-over-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/boundary/min-times-one-over-one" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/boundary/min-plus-one-times-negone-over-one" #[intV (minInt257 + 1), intV (-1), intV 1],
    mkCase "ok/boundary/max-times-one-over-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-times-negone-over-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "ok/boundary/min-times-one-over-two" #[intV minInt257, intV 1, intV 2],
    mkCase "ok/boundary/min-times-one-over-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "ok/boundary/min-plus-one-times-negone-over-two" #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "overflow/min-times-negone-over-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "overflow/max-times-max-over-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "overflow/min-times-min-over-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "type/pop-z-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/underflow-before-type" #[.null, .cell Cell.empty],
    mkCase "error-order/pop-z-before-y-when-both-non-int" #[intV 1, .null, .cell Cell.empty],
    mkCase "error-order/pop-y-before-x-after-z-int" #[.null, .cell Cell.empty, intV 1],
    mkInputCase "nan/program-z" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInputCase "nan/program-y" #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkInputCase "nan/program-x" #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkInputCase "overflow/program-x-out-of-range" #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 7],
    mkInputCase "overflow/program-y-out-of-range" #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 7],
    mkInputCase "overflow/program-z-out-of-range" #[IntVal.num 5, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 4]
      #[.pushInt (.num muldivmodrSetGasExact), .tonEnvOp .setGasLimit, muldivmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 4]
      #[.pushInt (.num muldivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, muldivmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020809
      count := 700
      gen := genMulDivModRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULDIVMODR
