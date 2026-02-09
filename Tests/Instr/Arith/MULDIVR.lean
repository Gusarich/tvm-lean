import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULDIVR

/-
MULDIVR branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, `roundMode = 0` path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (0xa98 args4 decode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest-round adjustment)

Branch/terminal counts used for this suite:
- Lean (`execInstrArithMulDivMod` generic): 7 branch sites / 16 terminal outcomes
  (dispatch arm; add-mode arity; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with 4 arms; non-num `d=3` split).
- Lean (`divModRound`, `roundMode=0`): 4 branch sites / 7 terminal outcomes
  (zero-divisor guard; mode-dispatch chain; nearest-adjust predicate split
   for positive vs negative divisor).
- C++ (`exec_muldivmod` + nearest-round helper): 7 branch sites / 16 aligned outcomes
  (opcode decode/remap guard; underflow guard; add/non-add path; `d` switch;
   nearest-round threshold adjustment including half-tie behavior).

MULDIVR specialization:
- opcode family `0xa98` args4 = `0x5`
- fixed params: `d=1`, `roundMode=0`, `addMode=false`, `quiet=false`.

Key risk areas covered:
- nearest rounding of `(x*y)/z` across sign mixes and half-tie boundaries;
- pop/error ordering (`z`, then `y`, then `x`);
- non-quiet NaN and out-of-range funnels (`intOv`) via program injection only;
- signed-257 overflow edge cases (`minInt257 * -1 / 1`, huge products);
- exact gas boundary under `PUSHINT n; SETGASLIMIT; MULDIVR`.
-/

private def muldivrId : InstrId := { name := "MULDIVR" }

private def muldivrInstr : Instr := .mulDivMod 1 0 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muldivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muldivrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[muldivrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runMulDivrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod muldivrInstr stack

private def runMulDivrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 3305)) stack

private def muldivrSetGasExact : Int :=
  computeExactGasBudget muldivrInstr

private def muldivrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muldivrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def outOfRangePool : Array Int :=
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

private def genMulDivrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-random"
        #[IntVal.num x, IntVal.num y, IntVal.num z], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/divzero"
        #[IntVal.num x, IntVal.num y, IntVal.num 0], r3)
    else if shape = 3 then
      let (x, r2) := pickFromPool roundFactorPool rng1
      let (y, r3) := pickFromPool roundFactorPool r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/tie-z-pos-two"
        #[IntVal.num x, IntVal.num y, IntVal.num 2], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool roundFactorPool rng1
      let (y, r3) := pickFromPool roundFactorPool r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/tie-z-neg-two"
        #[IntVal.num x, IntVal.num y, IntVal.num (-2)], r3)
    else if shape = 5 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/overflow-min-neg1-div1"
        #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 1], rng1)
    else if shape = 6 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/overflow-max-max-div1"
        #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1], rng1)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-zero-left-factor"
        #[IntVal.num 0, IntVal.num y, IntVal.num z], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok-zero-right-factor"
        #[IntVal.num x, IntVal.num 0, IntVal.num z], r3)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow-two-ints" #[intV x, intV y], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-z-first" #[intV x, intV y, .null], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-second" #[intV x, .cell Cell.empty, intV z], r3)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-third" #[.null, intV y, intV z], r3)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num z], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num z], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-z-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 18 then
      let (oor, r2) := pickFromPool outOfRangePool rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-x-via-program"
        #[IntVal.num oor, IntVal.num y, IntVal.num z], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (oor, r4) := pickFromPool outOfRangePool r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-z-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.num oor], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := muldivrId
  unit := #[
    { name := "unit/round/sign-combos-and-half-ties"
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
          expectOkStack s!"({x}*{y})/{z}" (runMulDivrDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "unit/round/boundary-successes"
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
            (0, -7, 3, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"({x}*{y})/{z}" (runMulDivrDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "unit/error/intov-divzero-overflow-and-nan"
      run := do
        expectErr "divzero/nonzero-product-over-zero" (runMulDivrDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "divzero/zero-product-over-zero" (runMulDivrDirect #[intV 0, intV 7, intV 0]) .intOv
        expectErr "overflow/min-times-neg-one-div-one" (runMulDivrDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/max-times-max-div-one" (runMulDivrDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-times-min-div-one" (runMulDivrDirect #[intV minInt257, intV minInt257, intV 1]) .intOv
        expectErr "nan/x" (runMulDivrDirect #[.int .nan, intV 7, intV 3]) .intOv
        expectErr "nan/y" (runMulDivrDirect #[intV 7, .int .nan, intV 3]) .intOv
        expectErr "nan/z" (runMulDivrDirect #[intV 7, intV 3, .int .nan]) .intOv }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulDivrDirect #[]) .stkUnd
        expectErr "underflow/one-int-before-missing-y" (runMulDivrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-ints-before-missing-x" (runMulDivrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/non-int-short-stack-before-type" (runMulDivrDirect #[.null]) .stkUnd
        expectErr "type/pop-z-first" (runMulDivrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulDivrDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMulDivrDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-z-before-y-when-both-non-int"
          (runMulDivrDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-z-int"
          (runMulDivrDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulDivrDispatchFallback #[]) #[intV 3305] }
  ]
  oracle := #[
    mkCaseFromIntVals "ok/round/sign/pos-pos-inexact" #[IntVal.num 7, IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "ok/round/sign/neg-pos-inexact" #[IntVal.num (-7), IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "ok/round/sign/pos-neg-inexact" #[IntVal.num 7, IntVal.num (-3), IntVal.num 2],
    mkCaseFromIntVals "ok/round/sign/neg-neg-inexact" #[IntVal.num (-7), IntVal.num (-3), IntVal.num 2],
    mkCaseFromIntVals "ok/round/tie/pos-pos-half" #[IntVal.num 5, IntVal.num 5, IntVal.num 2],
    mkCaseFromIntVals "ok/round/tie/neg-pos-half" #[IntVal.num (-5), IntVal.num 5, IntVal.num 2],
    mkCaseFromIntVals "ok/round/tie/pos-neg-half" #[IntVal.num 5, IntVal.num (-5), IntVal.num 2],
    mkCaseFromIntVals "ok/round/tie/neg-neg-half" #[IntVal.num (-5), IntVal.num (-5), IntVal.num 2],
    mkCaseFromIntVals "ok/round/tie/neg-pos-near-zero" #[IntVal.num (-1), IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/round/tie/pos-neg-near-zero" #[IntVal.num 1, IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "ok/round/tie/neg-neg-near-zero" #[IntVal.num (-1), IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "ok/exact/pos-pos" #[IntVal.num 42, IntVal.num 6, IntVal.num 7],
    mkCaseFromIntVals "ok/exact/neg-pos" #[IntVal.num (-42), IntVal.num 6, IntVal.num 7],
    mkCaseFromIntVals "ok/exact/pos-neg" #[IntVal.num 42, IntVal.num (-6), IntVal.num 7],
    mkCaseFromIntVals "ok/exact/neg-neg" #[IntVal.num (-42), IntVal.num (-6), IntVal.num 7],
    mkCaseFromIntVals "ok/exact/zero-left-factor" #[IntVal.num 0, IntVal.num 17, IntVal.num 5],
    mkCaseFromIntVals "ok/exact/zero-right-factor" #[IntVal.num 17, IntVal.num 0, IntVal.num 5],
    mkCaseFromIntVals "ok/boundary/max-times-one-div-one" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/boundary/max-times-neg-one-div-one" #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "ok/boundary/min-times-one-div-one" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/boundary/min-times-neg-one-div-neg-one"
      #[IntVal.num minInt257, IntVal.num (-1), IntVal.num (-1)],
    mkCaseFromIntVals "ok/boundary/min-plus-one-times-neg-one-div-neg-one"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num (-1)],
    mkCaseFromIntVals "ok/boundary/max-times-one-div-two-round-up"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/boundary/max-times-neg-one-div-two-round-up"
      #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "ok/boundary/min-times-one-div-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/boundary/min-times-one-div-neg-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num (-2)],
    mkCaseFromIntVals "ok/boundary/min-plus-one-times-neg-one-div-two-round-up"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "divzero/nonzero-product-over-zero" #[IntVal.num 5, IntVal.num 7, IntVal.num 0],
    mkCaseFromIntVals "divzero/zero-product-over-zero" #[IntVal.num 0, IntVal.num 7, IntVal.num 0],
    mkCaseFromIntVals "overflow/min-times-neg-one-div-one" #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "overflow/max-times-max-div-one" #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1],
    mkCaseFromIntVals "overflow/max-times-max-div-neg-one" #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num (-1)],
    mkCaseFromIntVals "overflow/min-times-min-div-one" #[IntVal.num minInt257, IntVal.num minInt257, IntVal.num 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int-before-missing-y" #[intV 1],
    mkCase "underflow/two-ints-before-missing-x" #[intV 1, intV 2],
    mkCase "type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 3],
    mkCaseFromIntVals "nan/z-via-program" #[IntVal.num 5, IntVal.num 3, IntVal.nan],
    mkCaseFromIntVals "range/x-out-of-range-via-program" #[IntVal.num (maxInt257 + 1), IntVal.num 2, IntVal.num 1],
    mkCaseFromIntVals "range/y-out-of-range-via-program" #[IntVal.num 2, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "range/z-out-of-range-via-program" #[IntVal.num 2, IntVal.num 3, IntVal.num (pow2 257)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivrSetGasExact), .tonEnvOp .setGasLimit, muldivrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivrSetGasExactMinusOne), .tonEnvOp .setGasLimit, muldivrInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 700
      gen := genMulDivrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULDIVR
