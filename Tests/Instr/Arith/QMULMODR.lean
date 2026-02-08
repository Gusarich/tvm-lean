import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULMODR

/-
QMULMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest mode `roundMode=0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb7a98` args4 decode for quiet `.mulDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (`PUSHINT` NaN/range prelude path)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest-mode tie adjustment)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean (`execInstrArithMulDivMod` specialized to
  `d=2`, `roundMode=0`, `add=false`, `quiet=true`):
  7 branch sites / 14 terminal outcomes
  (dispatch arm; arity gate; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch; non-num split).
- Lean (`pushIntQuiet` at result push): 2 branch sites / 3 outcomes
  (num-vs-NaN; signed-257 fit-vs-quiet-NaN funnel).
- C++ (`exec_muldivmod` + `push_int_quiet`): 8 branch sites / 15 aligned outcomes
  (opcode remap/guard paths; underflow gate; pop/type paths; divisor-zero/NaN funnels;
   quiet push fit-vs-NaN handling).

Key risk areas covered:
- nearest-rounding remainders for sign mixes and half ties (`±2` divisors);
- quiet funnels for divisor-zero and NaN operands (must push NaN, not throw `intOv`);
- pop/type ordering (`z`, then `y`, then `x`) and underflow-before-type on short stacks;
- oracle serialization hygiene for NaN and out-of-range integers via `PUSHINT` prelude only;
- exact gas cliff around `PUSHINT n; SETGASLIMIT; QMULMODR`.
-/

private def qmulmodrId : InstrId := { name := "QMULMODR" }

private def qmulmodrInstr : Instr := .mulDivMod 2 0 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmulmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQmulmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmulmodrInstr stack

private def runQmulmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 6060)) stack

private def expectQmulmodr
    (label : String)
    (x y z expected : Int) : IO Unit :=
  expectOkStack label (runQmulmodrDirect #[intV x, intV y, intV z]) #[intV expected]

private def qmulmodrSetGasExact : Int :=
  computeExactGasBudget qmulmodrInstr

private def qmulmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def tieFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def tieDivisorPool : Array Int :=
  #[-2, 2]

private def nearestFactorPool : Array Int :=
  #[-11, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 11]

private def nearestDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQmulmodr (x y z : Int) : String :=
  if z = 0 then
    "divzero"
  else
    let (_, r) := divModRound (x * y) z 0
    if !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if Int.natAbs r * 2 = Int.natAbs z then
      "tie"
    else
      "inexact"

private def genQmulmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmulmodr x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmulmodr x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-signed" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmulmodr x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-signed" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero-random" #[intV x, intV y, intV 0], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      let (z, r4) := pickFromPool tieDivisorPool r3
      let kind := classifyQmulmodr x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-pool" #[intV x, intV y, intV z], r4)
    else if shape = 5 then
      let (x, r2) := pickFromPool nearestFactorPool rng1
      let (y, r3) := pickFromPool nearestFactorPool r2
      let (z, r4) := pickFromPool nearestDivisorPool r3
      let kind := classifyQmulmodr x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/nearest-pool" #[intV x, intV y, intV z], r4)
    else if shape = 6 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQmulmodr 0 y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQmulmodr x 0 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQmulmodr x y 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/z-one" #[intV x, intV y, intV 1], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQmulmodr x y (-1)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/z-neg-one" #[intV x, intV y, intV (-1)], r3)
    else if shape = 10 then
      let kind := classifyQmulmodr maxInt257 maxInt257 2
      (mkCase s!"/fuzz/shape-{shape}/{kind}/max-times-max-over-two" #[intV maxInt257, intV maxInt257, intV 2], rng1)
    else if shape = 11 then
      let kind := classifyQmulmodr minInt257 minInt257 2
      (mkCase s!"/fuzz/shape-{shape}/{kind}/min-times-min-over-two" #[intV minInt257, intV minInt257, intV 2], rng1)
    else if shape = 12 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-ints" #[intV x, intV y], r3)
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
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-z-before-y"
        #[intV x, yBad, zBad], r4)
    else if shape = 19 then
      let (z, r2) := pickNonZeroInt rng1
      let (xBad, r3) := pickNonInt r2
      let (yBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x"
        #[xBad, yBad, intV z], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num z], r3)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num z], r3)
    else if shape = 23 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-range-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num z], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-range-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num z], r4)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-range-z-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num zOut], r4)
    else if shape = 26 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-range-all-before-op"
        #[IntVal.num xOut, IntVal.num yOut, IntVal.num zOut], r4)
    else
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulmodrId
  unit := #[
    { name := "/unit/round/nearest-sign-tie-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, -1),
            (-7, 3, 2, -1),
            (7, -3, 2, -1),
            (-7, -3, 2, -1),
            (7, 3, -2, 1),
            (-7, 3, -2, 1),
            (1, 1, 2, -1),
            (-1, 1, 2, -1),
            (1, 1, -2, 1),
            (-1, 1, -2, 1),
            (5, 5, 2, -1),
            (-5, 5, 2, -1),
            (42, 6, 7, 0),
            (-42, 6, 7, 0),
            (0, 9, 5, 0),
            (9, 0, 5, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectQmulmodr s!"/unit/check/({x}*{y})%{z}" x y z expected }
    ,
    { name := "/unit/round/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, 0),
            (maxInt257, -1, 1, 0),
            (minInt257, 1, 1, 0),
            (minInt257, -1, -1, 0),
            (maxInt257, 1, 2, -1),
            (maxInt257, -1, 2, -1),
            (minInt257, 1, 2, 0),
            (minInt257, 1, -2, 0),
            (minInt257 + 1, -1, 2, -1),
            (maxInt257, maxInt257, 2, -1),
            (minInt257, minInt257, 2, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectQmulmodr s!"/unit/check/({x}*{y})%{z}" x y z expected }
    ,
    { name := "/unit/quiet/divzero-and-nan-funnel"
      run := do
        expectOkStack "/unit/check/quiet/divzero/nonzero-product-over-zero"
          (runQmulmodrDirect #[intV 5, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/check/quiet/divzero/zero-product-over-zero"
          (runQmulmodrDirect #[intV 0, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/check/quiet/nan/z-top"
          (runQmulmodrDirect #[intV 9, intV 7, .int .nan]) #[.int .nan]
        expectOkStack "/unit/check/quiet/nan/y-second"
          (runQmulmodrDirect #[intV 9, .int .nan, intV 7]) #[.int .nan]
        expectOkStack "/unit/check/quiet/nan/x-third"
          (runQmulmodrDirect #[.int .nan, intV 9, intV 7]) #[.int .nan]
        expectOkStack "/unit/check/quiet/nan/all"
          (runQmulmodrDirect #[.int .nan, .int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/check/underflow/empty" (runQmulmodrDirect #[]) .stkUnd
        expectErr "/unit/check/underflow/one-int" (runQmulmodrDirect #[intV 1]) .stkUnd
        expectErr "/unit/check/underflow/two-ints" (runQmulmodrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/check/error-order/underflow-before-type-with-two-items"
          (runQmulmodrDirect #[intV 1, .null]) .stkUnd
        expectErr "/unit/check/type/pop-z-first"
          (runQmulmodrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/check/type/pop-y-second"
          (runQmulmodrDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/check/type/pop-x-third"
          (runQmulmodrDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/check/error-order/pop-z-before-y-when-both-non-int"
          (runQmulmodrDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/check/error-order/pop-y-before-x-after-z-int"
          (runQmulmodrDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/check/dispatch/fallback"
          (runQmulmodrDispatchFallback #[]) #[intV 6060] }
  ]
  oracle := #[
    mkInputCase "/ok/round/inexact-pos-pos" #[IntVal.num 7, IntVal.num 3, IntVal.num 2],
    mkInputCase "/ok/round/inexact-neg-pos" #[IntVal.num (-7), IntVal.num 3, IntVal.num 2],
    mkInputCase "/ok/round/inexact-pos-neg" #[IntVal.num 7, IntVal.num (-3), IntVal.num 2],
    mkInputCase "/ok/round/inexact-neg-neg" #[IntVal.num (-7), IntVal.num (-3), IntVal.num 2],
    mkInputCase "/ok/round/inexact-pos-pos-negdivisor" #[IntVal.num 7, IntVal.num 3, IntVal.num (-2)],
    mkInputCase "/ok/round/inexact-neg-pos-negdivisor" #[IntVal.num (-7), IntVal.num 3, IntVal.num (-2)],
    mkInputCase "/ok/tie/one-over-two" #[IntVal.num 1, IntVal.num 1, IntVal.num 2],
    mkInputCase "/ok/tie/neg-one-over-two" #[IntVal.num (-1), IntVal.num 1, IntVal.num 2],
    mkInputCase "/ok/tie/one-over-neg-two" #[IntVal.num 1, IntVal.num 1, IntVal.num (-2)],
    mkInputCase "/ok/tie/neg-one-over-neg-two" #[IntVal.num (-1), IntVal.num 1, IntVal.num (-2)],
    mkInputCase "/ok/tie/five-times-five-over-two" #[IntVal.num 5, IntVal.num 5, IntVal.num 2],
    mkInputCase "/ok/tie/neg-five-times-five-over-two" #[IntVal.num (-5), IntVal.num 5, IntVal.num 2],
    mkInputCase "/ok/exact/pos-pos" #[IntVal.num 42, IntVal.num 6, IntVal.num 7],
    mkInputCase "/ok/exact/neg-pos" #[IntVal.num (-42), IntVal.num 6, IntVal.num 7],
    mkInputCase "/ok/exact/pos-neg" #[IntVal.num 42, IntVal.num (-6), IntVal.num 7],
    mkInputCase "/ok/exact/neg-neg" #[IntVal.num (-42), IntVal.num (-6), IntVal.num 7],
    mkInputCase "/ok/exact/zero-left-factor" #[IntVal.num 0, IntVal.num 17, IntVal.num 5],
    mkInputCase "/ok/exact/zero-right-factor" #[IntVal.num 17, IntVal.num 0, IntVal.num 5],
    mkInputCase "/ok/boundary/max-times-one-mod-one" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1],
    mkInputCase "/ok/boundary/max-times-neg-one-mod-one" #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 1],
    mkInputCase "/ok/boundary/min-times-one-mod-one" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1],
    mkInputCase "/ok/boundary/min-times-neg-one-mod-neg-one"
      #[IntVal.num minInt257, IntVal.num (-1), IntVal.num (-1)],
    mkInputCase "/ok/boundary/max-times-one-mod-two"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 2],
    mkInputCase "/ok/boundary/max-times-neg-one-mod-two"
      #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 2],
    mkInputCase "/ok/boundary/min-times-one-mod-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 2],
    mkInputCase "/ok/boundary/min-times-one-mod-neg-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num (-2)],
    mkInputCase "/ok/boundary/min-plus-one-negated-mod-two"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num 2],
    mkInputCase "/ok/boundary/max-times-max-mod-two"
      #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 2],
    mkInputCase "/ok/boundary/min-times-min-mod-two"
      #[IntVal.num minInt257, IntVal.num minInt257, IntVal.num 2],
    mkInputCase "/quiet/divzero/nonzero-product-over-zero"
      #[IntVal.num 5, IntVal.num 7, IntVal.num 0],
    mkInputCase "/quiet/divzero/zero-product-over-zero"
      #[IntVal.num 0, IntVal.num 7, IntVal.num 0],
    mkInputCase "/quiet/nan/z-via-program"
      #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInputCase "/quiet/nan/y-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkInputCase "/quiet/nan/x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkInputCase "/quiet/nan/all-via-program"
      #[IntVal.nan, IntVal.nan, IntVal.nan],
    mkInputCase "/error-order/pushint-range-x-before-qmulmodr"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 7],
    mkInputCase "/error-order/pushint-range-y-before-qmulmodr"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 7],
    mkInputCase "/error-order/pushint-range-z-before-qmulmodr"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (pow2 257)],
    mkInputCase "/error-order/pushint-range-all-before-qmulmodr"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (maxInt257 + 2)],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-type-with-two-items" #[intV 1, .null],
    mkCase "/type/pop-z-first" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-z-int" #[.null, .cell Cell.empty, intV 1],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodrSetGasExact), .tonEnvOp .setGasLimit, qmulmodrInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020819
      count := 700
      gen := genQmulmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULMODR
