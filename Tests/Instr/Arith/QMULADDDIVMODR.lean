import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULADDDIVMODR

/-
QMULADDDIVMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `0` nearest/ties-to-+∞)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7a98` args4 decode to quiet `.mulDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (generic `.mulDivMod`): 8 branch sites / 18 terminal outcomes
  (dispatch arm, stack-arity gate, add-mode pop split, operand-shape split,
   divisor-zero split, round-mode validity split, `d` switch with 4 arms,
   non-num `d=3` split).
- C++ (`exec_muldivmod`): 5 branch sites / 11 terminal outcomes
  (global-version add-remap gate, invalid-opcode guard, underflow guard,
   add vs non-add pop path, `d` switch push shape).

QMULADDDIVMODR specialization:
- opcode args4=`0x1` under quiet `0xb7a98` family;
- fixed params: `d=3`, `roundMode=0` (nearest), `addMode=true`, `quiet=true`.

Key risk areas covered:
- nearest rounding ties after `x*y + w` across sign combinations;
- quiet funnels for divisor-zero, NaN operands, and 257-bit quotient overflow;
- pop/type error ordering (`z`, `w`, `y`, `x`; underflow before type on short stack);
- oracle serialization hygiene for NaN/out-of-range values via program prelude only;
- exact gas cliff around `SETGASLIMIT` exact vs exact-minus-one.
-/

private def qmuladddivmodrId : InstrId := { name := "QMULADDDIVMODR" }

private def qmuladddivmodrInstr : Instr := .mulDivMod 3 0 true true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuladddivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmuladddivmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[qmuladddivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runQMulAddDivModRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuladddivmodrInstr stack

private def runQMulAddDivModRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 7171)) stack

private def qmuladddivmodrSetGasExact : Int :=
  computeExactGasBudget qmuladddivmodrInstr

private def qmuladddivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuladddivmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQMulAddDivModR (x y w z : Int) : String :=
  let tmp : Int := x * y + w
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

private def genQMulAddDivModRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickInt257Boundary r3
      let (z, r5) := pickNonZeroInt r4
      let kind := classifyQMulAddDivModR x y w z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-all" #[intV x, intV y, intV w, intV z], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      let kind := classifyQMulAddDivModR x y w z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-all" #[intV x, intV y, intV w, intV z], r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero-random" #[intV x, intV y, intV w, intV 0], r4)
    else if shape = 3 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (z, r3) := pickFromPool tieDenominatorPool r2
      let kind := classifyQMulAddDivModR t 1 0 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-w-zero" #[intV t, intV 1, intV 0, intV z], r3)
    else if shape = 4 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (z, r3) := pickFromPool tieDenominatorPool r2
      let kind := classifyQMulAddDivModR t 1 1 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-w-one" #[intV t, intV 1, intV 1, intV z], r3)
    else if shape = 5 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-times-two" #[intV maxInt257, intV 2, intV 0, intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-times-two" #[intV minInt257, intV 2, intV 0, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-over-negone" #[intV minInt257, intV 1, intV 0, intV (-1)], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-times-max" #[intV maxInt257, intV maxInt257, intV 0, intV 1], rng1)
    else if shape = 9 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulAddDivModR 0 y w z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-x" #[intV 0, intV y, intV w, intV z], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQMulAddDivModR x 0 w z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-y" #[intV x, intV 0, intV w, intV z], r4)
    else if shape = 11 then
      let (xRaw, r2) := pickSigned257ish rng1
      let x := if xRaw = minInt257 then minInt257 + 1 else xRaw
      let (z, r3) := pickFromPool roundDenominatorPool r2
      let kind := classifyQMulAddDivModR x 1 (-x) z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/cancel-product-with-addend" #[intV x, intV 1, intV (-x), intV z], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let kind := classifyQMulAddDivModR x y w 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/z-one" #[intV x, intV y, intV w, intV 1], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let kind := classifyQMulAddDivModR x y w (-1)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/z-neg-one" #[intV x, intV y, intV w, intV (-1)], r4)
    else if shape = 14 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickFromPool roundDenominatorPool r4
      let kind := classifyQMulAddDivModR x y w z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-round-den" #[intV x, intV y, intV w, intV z], r5)
    else if shape = 15 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"/fuzz/shape-{shape}/underflow/three-args" #[intV x, intV y, intV w], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (zBad, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, intV w, zBad], r5)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let (wBad, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-w-second" #[intV x, intV y, wBad, intV z], r5)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let (yBad, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-third" #[intV x, yBad, intV w, intV z], r5)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let (xBad, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-fourth" #[xBad, intV y, intV w, intV z], r5)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-z"
        #[IntVal.num x, IntVal.num y, IntVal.num w, IntVal.nan], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-w"
        #[IntVal.num x, IntVal.num y, IntVal.nan, IntVal.num z], r4)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-y"
        #[IntVal.num x, IntVal.nan, IntVal.num w, IntVal.num z], r4)
    else if shape = 26 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-x"
        #[IntVal.nan, IntVal.num y, IntVal.num w, IntVal.num z], r4)
    else if shape = 27 then
      let (huge, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-x"
        #[IntVal.num huge, IntVal.num y, IntVal.num w, IntVal.num z], r5)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (huge, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-y"
        #[IntVal.num x, IntVal.num huge, IntVal.num w, IntVal.num z], r5)
    else if shape = 29 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (huge, r4) := pickInt257OutOfRange r3
      let (z, r5) := pickNonZeroInt r4
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-w"
        #[IntVal.num x, IntVal.num y, IntVal.num huge, IntVal.num z], r5)
    else if shape = 30 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-z"
        #[IntVal.num x, IntVal.num y, IntVal.num w, IntVal.num huge], r5)
    else if shape = 31 then
      let (hugeX, r2) := pickInt257OutOfRange rng1
      let (hugeY, r3) := pickInt257OutOfRange r2
      let (hugeW, r4) := pickInt257OutOfRange r3
      let (hugeZ, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-all"
        #[IntVal.num hugeX, IntVal.num hugeY, IntVal.num hugeW, IntVal.num hugeZ], r5)
    else
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuladddivmodrId
  unit := #[
    { name := "/unit/ok/nearest-rounding-signs-and-ties"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 3, 4, 10, -2),
            (7, 5, 2, 4, 9, 1),
            (-7, 5, 0, 4, -9, 1),
            (7, -5, 0, 4, -9, 1),
            (-7, -5, 0, 4, 9, -1),
            (5, 1, 0, 2, 3, -1),
            (-5, 1, 0, 2, -2, -1),
            (5, 1, 0, -2, -2, 1),
            (-5, 1, 0, -2, 3, 1),
            (-1, 1, 0, 2, 0, -1),
            (1, 1, 0, -2, 0, 1),
            (4, 3, 1, 2, 7, -1)
          ]
        for c in checks do
          match c with
          | (x, y, w, z, q, r) =>
              expectOkStack s!"({x}*{y}+{w})/{z}"
                (runQMulAddDivModRDirect #[intV x, intV y, intV w, intV z])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 1, maxInt257, 0),
            (maxInt257, 1, -1, 1, maxInt257 - 1, 0),
            (minInt257, 1, 1, 1, minInt257 + 1, 0),
            (minInt257 + 1, 1, 0, -1, maxInt257, 0),
            (maxInt257, 1, 0, 2, pow2 255, -1),
            (minInt257, 1, 0, 2, -(pow2 255), 0),
            (minInt257, 1, 0, -2, pow2 255, 0)
          ]
        for c in checks do
          match c with
          | (x, y, w, z, q, r) =>
              expectOkStack s!"({x}*{y}+{w})/{z}"
                (runQMulAddDivModRDirect #[intV x, intV y, intV w, intV z])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/quiet-divzero-nan-and-overflow-funnels"
      run := do
        expectOkStack "/quiet/divzero/nonzero-over-zero"
          (runQMulAddDivModRDirect #[intV 5, intV 7, intV 1, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/divzero/zero-over-zero"
          (runQMulAddDivModRDirect #[intV 0, intV 0, intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/overflow/max-times-two-over-one"
          (runQMulAddDivModRDirect #[intV maxInt257, intV 2, intV 0, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/quiet/overflow/min-times-two-over-one"
          (runQMulAddDivModRDirect #[intV minInt257, intV 2, intV 0, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/quiet/overflow/min-over-negone"
          (runQMulAddDivModRDirect #[intV minInt257, intV 1, intV 0, intV (-1)]) #[.int .nan, intV 0]
        expectOkStack "/quiet/overflow/max-times-max-over-one"
          (runQMulAddDivModRDirect #[intV maxInt257, intV maxInt257, intV 0, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/quiet/nan/z-top"
          (runQMulAddDivModRDirect #[intV 5, intV 7, intV 1, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/w-second"
          (runQMulAddDivModRDirect #[intV 5, intV 7, .int .nan, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/y-third"
          (runQMulAddDivModRDirect #[intV 5, .int .nan, intV 1, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/x-fourth"
          (runQMulAddDivModRDirect #[.int .nan, intV 5, intV 1, intV 1]) #[.int .nan, .int .nan] }
    ,
    { name := "/unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "/underflow/empty" (runQMulAddDivModRDirect #[]) .stkUnd
        expectErr "/underflow/one-arg" (runQMulAddDivModRDirect #[intV 1]) .stkUnd
        expectErr "/underflow/two-args" (runQMulAddDivModRDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/underflow/three-args" (runQMulAddDivModRDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/error-order/underflow-before-type-with-three-items"
          (runQMulAddDivModRDirect #[.null, .cell Cell.empty, intV 1]) .stkUnd
        expectErr "/type/pop-z-first" (runQMulAddDivModRDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/type/pop-w-second" (runQMulAddDivModRDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/type/pop-y-third" (runQMulAddDivModRDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "/type/pop-x-fourth" (runQMulAddDivModRDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/error-order/pop-z-before-w-when-both-non-int"
          (runQMulAddDivModRDirect #[intV 1, intV 2, .null, .cell Cell.empty]) .typeChk
        expectErr "/error-order/pop-w-before-y-when-z-int"
          (runQMulAddDivModRDirect #[intV 1, .null, .cell Cell.empty, intV 2]) .typeChk
        expectErr "/error-order/pop-y-before-x-when-zw-int"
          (runQMulAddDivModRDirect #[.null, .cell Cell.empty, intV 1, intV 2]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQMulAddDivModRDispatchFallback #[]) #[intV 7171] }
  ]
  oracle := #[
    mkCase "/ok/round/inexact-pos-pos" #[intV 7, intV 5, intV 2, intV 4],
    mkCase "/ok/round/inexact-neg-pos" #[intV (-7), intV 5, intV 0, intV 4],
    mkCase "/ok/round/inexact-pos-neg" #[intV 7, intV 5, intV 0, intV (-4)],
    mkCase "/ok/round/inexact-neg-neg" #[intV (-7), intV 5, intV 0, intV (-4)],
    mkCase "/ok/tie/pos-over-pos-two" #[intV 5, intV 1, intV 0, intV 2],
    mkCase "/ok/tie/neg-over-pos-two" #[intV (-5), intV 1, intV 0, intV 2],
    mkCase "/ok/tie/pos-over-neg-two" #[intV 5, intV 1, intV 0, intV (-2)],
    mkCase "/ok/tie/neg-over-neg-two" #[intV (-5), intV 1, intV 0, intV (-2)],
    mkCase "/ok/tie/near-zero-neg-pos" #[intV (-1), intV 1, intV 0, intV 2],
    mkCase "/ok/tie/near-zero-pos-neg" #[intV 1, intV 1, intV 0, intV (-2)],
    mkCase "/ok/exact/pos-product-over-two" #[intV 4, intV 3, intV 0, intV 2],
    mkCase "/ok/exact/neg-product-over-two" #[intV (-4), intV 3, intV 0, intV 2],
    mkCase "/ok/exact/zero-product-plus-w" #[intV 0, intV 99, intV 7, intV 7],
    mkCase "/ok/exact/addend-cancels-product" #[intV 42, intV 1, intV (-42), intV 3],
    mkCase "/ok/boundary/max-times-one-over-one" #[intV maxInt257, intV 1, intV 0, intV 1],
    mkCase "/ok/boundary/max-times-one-plus-negone-over-one" #[intV maxInt257, intV 1, intV (-1), intV 1],
    mkCase "/ok/boundary/min-times-one-plus-one-over-one" #[intV minInt257, intV 1, intV 1, intV 1],
    mkCase "/ok/boundary/min-plus-one-over-negone" #[intV (minInt257 + 1), intV 1, intV 0, intV (-1)],
    mkCase "/ok/boundary/max-over-two-rounds-up" #[intV maxInt257, intV 1, intV 0, intV 2],
    mkCase "/ok/boundary/min-over-two-exact" #[intV minInt257, intV 1, intV 0, intV 2],
    mkCase "/ok/boundary/min-over-neg-two-exact" #[intV minInt257, intV 1, intV 0, intV (-2)],
    mkCase "/quiet/overflow/max-times-two-over-one" #[intV maxInt257, intV 2, intV 0, intV 1],
    mkCase "/quiet/overflow/min-times-two-over-one" #[intV minInt257, intV 2, intV 0, intV 1],
    mkCase "/quiet/overflow/min-over-negone" #[intV minInt257, intV 1, intV 0, intV (-1)],
    mkCase "/quiet/overflow/max-times-max-over-one" #[intV maxInt257, intV maxInt257, intV 0, intV 1],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 5, intV 7, intV 1, intV 0],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 0],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/type/pop-z-first" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/pop-w-second" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/pop-y-third" #[intV 1, .null, intV 2, intV 3],
    mkCase "/type/pop-x-fourth" #[.null, intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-type-with-three-items" #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/pop-z-before-w-when-both-non-int" #[intV 1, intV 2, .null, .cell Cell.empty],
    mkCase "/error-order/pop-w-before-y-when-z-int" #[intV 1, .null, .cell Cell.empty, intV 2],
    mkCase "/error-order/pop-y-before-x-when-zw-int" #[.null, .cell Cell.empty, intV 1, intV 2],
    mkInputCase "/quiet/nan/program-z" #[IntVal.num 5, IntVal.num 7, IntVal.num 1, IntVal.nan],
    mkInputCase "/quiet/nan/program-w" #[IntVal.num 5, IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkInputCase "/quiet/nan/program-y" #[IntVal.num 5, IntVal.nan, IntVal.num 1, IntVal.num 1],
    mkInputCase "/quiet/nan/program-x" #[IntVal.nan, IntVal.num 5, IntVal.num 1, IntVal.num 1],
    mkInputCase "/error-order/pushint-range/program-x" #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-range/program-y" #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-range/program-w" #[IntVal.num 5, IntVal.num 7, IntVal.num (pow2 257), IntVal.num 1],
    mkInputCase "/error-order/pushint-range/program-z" #[IntVal.num 5, IntVal.num 7, IntVal.num 1, IntVal.num (-(pow2 257))],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3, intV 4]
      #[.pushInt (.num qmuladddivmodrSetGasExact), .tonEnvOp .setGasLimit, qmuladddivmodrInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3, intV 4]
      #[.pushInt (.num qmuladddivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuladddivmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genQMulAddDivModRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULADDDIVMODR
