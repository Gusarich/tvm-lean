import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULDIVMODR

/-
QMULDIVMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `0` nearest/ties-to-+∞)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7a98` args4 decode to quiet `.mulDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (`PUSHINT` NaN/out-of-range injection path)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean (generic `.mulDivMod`): 8 branch sites / 18 terminal outcomes
  (dispatch arm, stack-arity gate, add-mode pop split, operand-shape split,
   divisor-zero split, round-mode validity split, `d` switch with 4 arms,
   non-num `d=3` split).
- C++ (`exec_muldivmod`): 5 branch sites / 11 terminal outcomes
  (global-version add-remap gate, invalid-opcode guard, underflow guard,
   add vs non-add pop path, `d` switch push shape).

QMULDIVMODR specialization:
- opcode args4=`0xd` under quiet `0xb7a98` family;
- fixed params: `d=3`, `roundMode=0` (nearest), `addMode=false`, `quiet=true`.

Key risk areas covered:
- nearest rounding ties and `(q,r)` ordering across sign combinations;
- quiet funnels for divisor-zero, NaN operands, and 257-bit quotient overflow;
- pop/type error ordering (`z`, then `y`, then `x`; underflow before type on short stacks);
- oracle serialization hygiene for NaN/out-of-range values via program prelude only;
- exact gas cliff around `SETGASLIMIT` exact vs exact-minus-one.
-/

private def qmuldivmodrId : InstrId := { name := "QMULDIVMODR" }

private def qmuldivmodrInstr : Instr := .mulDivMod 3 0 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuldivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmuldivmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[qmuldivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runQMulDivModRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuldivmodrInstr stack

private def runQMulDivModRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 5050)) stack

private def qmuldivmodrSetGasExact : Int :=
  computeExactGasBudget qmuldivmodrInstr

private def qmuldivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuldivmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def roundDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQMulDivModR (x y z : Int) : String :=
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

private def genQMulDivModRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulDivModR x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulDivModR x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-signed" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulDivModR x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-signed" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero-random" #[intV x, intV y, intV 0], r3)
    else if shape = 4 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (z, r3) := pickFromPool tieDenominatorPool r2
      let kind := classifyQMulDivModR t 1 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-from-pool" #[intV t, intV 1, intV z], r3)
    else if shape = 5 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-times-negone"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-times-max"
        #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQMulDivModR 0 y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQMulDivModR x 0 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQMulDivModR x y 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/z-one" #[intV x, intV y, intV 1], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQMulDivModR x y (-1)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/z-neg-one" #[intV x, intV y, intV (-1)], r3)
    else if shape = 11 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickFromPool roundDenominatorPool r3
      let kind := classifyQMulDivModR x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-round-den" #[intV x, intV y, intV z], r4)
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
      let (x, r2) := pickSigned257ish rng1
      let (zBad, r3) := pickNonInt r2
      let (yBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/error-order-z-before-y"
        #[intV x, yBad, zBad], r4)
    else if shape = 19 then
      let (z, r2) := pickNonZeroInt rng1
      let (xBad, r3) := pickNonInt r2
      let (yBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/error-order-y-before-x"
        #[xBad, yBad, intV z], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-z"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-y"
        #[IntVal.num x, IntVal.nan, IntVal.num z], r3)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-x"
        #[IntVal.nan, IntVal.num y, IntVal.num z], r3)
    else if shape = 23 then
      let (huge, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/out-of-range/program-x"
        #[IntVal.num huge, IntVal.num y, IntVal.num z], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (huge, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/out-of-range/program-y"
        #[IntVal.num x, IntVal.num huge, IntVal.num z], r4)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (huge, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/out-of-range/program-z"
        #[IntVal.num x, IntVal.num y, IntVal.num huge], r4)
    else if shape = 26 then
      let (hugeX, r2) := pickInt257OutOfRange rng1
      let (hugeY, r3) := pickInt257OutOfRange r2
      let (hugeZ, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/out-of-range/program-all"
        #[IntVal.num hugeX, IntVal.num hugeY, IntVal.num hugeZ], r4)
    else
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuldivmodrId
  unit := #[
    { name := "/unit/ok/nearest-rounding-and-output-order"
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
                (runQMulDivModRDirect #[intV x, intV y, intV z])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-successes"
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
                (runQMulDivModRDirect #[intV x, intV y, intV z])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/quiet-divzero-nan-and-overflow-funnels"
      run := do
        expectOkStack "/quiet/divzero/nonzero-over-zero"
          (runQMulDivModRDirect #[intV 5, intV 7, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/divzero/zero-over-zero"
          (runQMulDivModRDirect #[intV 0, intV 7, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/overflow/min-times-negone-over-one"
          (runQMulDivModRDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan, intV 0]
        expectOkStack "/quiet/overflow/max-times-max-over-one"
          (runQMulDivModRDirect #[intV maxInt257, intV maxInt257, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/quiet/nan/z-top"
          (runQMulDivModRDirect #[intV 9, intV 7, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/y-second"
          (runQMulDivModRDirect #[intV 9, .int .nan, intV 7]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/x-third"
          (runQMulDivModRDirect #[.int .nan, intV 9, intV 7]) #[.int .nan, .int .nan] }
    ,
    { name := "/unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "/underflow/empty" (runQMulDivModRDirect #[]) .stkUnd
        expectErr "/underflow/one-arg" (runQMulDivModRDirect #[intV 1]) .stkUnd
        expectErr "/underflow/two-args" (runQMulDivModRDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/error-order/underflow-before-type"
          (runQMulDivModRDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/type/pop-z-first"
          (runQMulDivModRDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/type/pop-y-second"
          (runQMulDivModRDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/type/pop-x-third"
          (runQMulDivModRDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/error-order/pop-z-before-y-when-both-non-int"
          (runQMulDivModRDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "/error-order/pop-y-before-x-after-z-int"
          (runQMulDivModRDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQMulDivModRDispatchFallback #[]) #[intV 5050] }
  ]
  oracle := #[
    mkCase "/ok/round/inexact-pos-pos" #[intV 7, intV 5, intV 4],
    mkCase "/ok/round/inexact-neg-pos" #[intV (-7), intV 5, intV 4],
    mkCase "/ok/round/inexact-pos-neg" #[intV 7, intV 5, intV (-4)],
    mkCase "/ok/round/inexact-neg-neg" #[intV (-7), intV 5, intV (-4)],
    mkCase "/ok/tie/pos-pos" #[intV 5, intV 1, intV 2],
    mkCase "/ok/tie/neg-pos" #[intV (-5), intV 1, intV 2],
    mkCase "/ok/tie/pos-neg" #[intV 5, intV 1, intV (-2)],
    mkCase "/ok/tie/neg-neg" #[intV (-5), intV 1, intV (-2)],
    mkCase "/ok/tie/near-zero-neg-pos" #[intV (-1), intV 1, intV 2],
    mkCase "/ok/tie/near-zero-pos-neg" #[intV 1, intV 1, intV (-2)],
    mkCase "/ok/exact/pos-pos" #[intV 42, intV 6, intV 7],
    mkCase "/ok/exact/neg-pos" #[intV (-42), intV 6, intV 7],
    mkCase "/ok/exact/pos-neg" #[intV 42, intV 6, intV (-7)],
    mkCase "/ok/exact/neg-neg" #[intV (-42), intV 6, intV (-7)],
    mkCase "/ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "/ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "/ok/boundary/max-times-one-over-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-negone-over-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "/ok/boundary/min-times-one-over-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-plus-one-times-negone-over-one" #[intV (minInt257 + 1), intV (-1), intV 1],
    mkCase "/ok/boundary/max-times-one-over-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "/ok/boundary/max-times-negone-over-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "/ok/boundary/min-times-one-over-two" #[intV minInt257, intV 1, intV 2],
    mkCase "/ok/boundary/min-times-one-over-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/min-plus-one-times-negone-over-two" #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "/quiet/overflow/min-times-negone-over-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "/quiet/overflow/max-times-max-over-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "/quiet/overflow/min-times-min-over-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/type/pop-z-first" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "/error-order/underflow-before-type" #[.null, .cell Cell.empty],
    mkCase "/error-order/pop-z-before-y-when-both-non-int" #[intV 1, .null, .cell Cell.empty],
    mkCase "/error-order/pop-y-before-x-after-z-int" #[.null, .cell Cell.empty, intV 1],
    mkInputCase "/quiet/nan/program-z" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInputCase "/quiet/nan/program-y" #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkInputCase "/quiet/nan/program-x" #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkInputCase "/quiet/out-of-range/program-x-high" #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 7],
    mkInputCase "/quiet/out-of-range/program-x-low" #[IntVal.num (minInt257 - 1), IntVal.num 5, IntVal.num 7],
    mkInputCase "/quiet/out-of-range/program-y-high" #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 7],
    mkInputCase "/quiet/out-of-range/program-y-low" #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 7],
    mkInputCase "/quiet/out-of-range/program-z-high" #[IntVal.num 5, IntVal.num 7, IntVal.num (pow2 257)],
    mkInputCase "/quiet/out-of-range/program-z-low" #[IntVal.num 5, IntVal.num 7, IntVal.num (-(pow2 257))],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 4]
      #[.pushInt (.num qmuldivmodrSetGasExact), .tonEnvOp .setGasLimit, qmuldivmodrInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 4]
      #[.pushInt (.num qmuldivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuldivmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 700
      gen := genQMulDivModRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULDIVMODR
