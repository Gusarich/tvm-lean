import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMODR

/-
QMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest-mode ties)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (`PUSHINT` NaN/range program injections)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp` (`exec_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp` (`AnyIntView::mod_div_any`, round_mode=0)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean `execInstrArithDivMod`: 6 branch sites / 14 terminal outcomes
  (dispatch arm; add-mode arity split; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with non-num fallback split).
- C++ `exec_divmod`: 4 branch sites / 10 terminal outcomes
  (add-remap gate; invalid-opcode guard; underflow guard; add/non-add split + `d` switch).

QMODR specialization:
- quiet QDIV/MOD opcode family `0xb7a90`, args4=`0x9`;
- fixed parameters are `d=2`, `roundMode=0` (nearest, ties to +∞),
  `addMode=false`, `quiet=true`.

Key risk areas covered:
- nearest-tie remainder behavior across sign combinations;
- quiet funnels for divisor-zero and NaN operands (must produce NaN, not `intOv`);
- stack error ordering (arity guard before type checks; `y` pops before `x`);
- signed-257 boundary behavior, especially `minInt257 / -1` (remainder must stay finite);
- oracle serialization hygiene for NaN/out-of-range values via program injection;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qmodrId : InstrId := { name := "QMODR" }

private def qmodrInstr : Instr := .divMod 2 0 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qmodrInstr stack

private def runQmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 904)) stack

private def qmodrSetGasExact : Int :=
  computeExactGasBudget qmodrInstr

private def qmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmodrInstr

private def expectQmodr
    (label : String)
    (x y r : Int) : IO Unit :=
  expectOkStack label (runQmodrDirect #[intV x, intV y]) #[intV r]

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundNumeratorPool : Array Int :=
  #[-11, -9, -8, -7, -5, -3, -1, 0, 1, 3, 5, 7, 8, 9, 11]

private def roundDenominatorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def tiePairPool : Array (Int × Int) :=
  #[(1, 2), (-1, 2), (1, -2), (-1, -2), (5, 2), (-5, 2), (5, -2), (-5, -2)]

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1, pow2 257, -(pow2 257)]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickTiePair (rng : StdGen) : (Int × Int) × StdGen :=
  let (idx, rng') := randNat rng 0 (tiePairPool.size - 1)
  (tiePairPool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQmodr (x y : Int) : String :=
  if y = 0 then
    "divzero"
  else
    let (_, r) := divModRound x y 0
    if !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genQmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-nonzero" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-nonzero" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero" #[intV x, intV 0], r2)
    else if shape = 3 then
      let ((x, y), r2) := pickTiePair rng1
      let kind := classifyQmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/tie-pool" #[intV x, intV y], r2)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromPool roundDenominatorPool r2
      let kind := classifyQmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-den-pool" #[intV x, intV y], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool roundNumeratorPool rng1
      let (y, r3) := pickFromPool roundDenominatorPool r2
      let kind := classifyQmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/round-pool" #[intV x, intV y], r3)
    else if shape = 6 then
      let (y, r2) := pickNonZeroInt rng1
      let kind := classifyQmodr 0 y
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-numerator" #[intV 0, intV y], r2)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/exact/min-div-neg-one" #[intV minInt257, intV (-1)], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-first" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, nonInt], r3)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[nonInt, intV y], r3)
    else if shape = 13 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[xLike, yLike], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/program-y" #[.num x, .nan], r2)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/program-x" #[.nan, .num y], r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (huge, r3) := pickFromPool outOfRangeProgramPool r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-y-before-qmodr"
        #[.num x, .num huge], r3)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (huge, r3) := pickFromPool outOfRangeProgramPool r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-x-before-qmodr"
        #[.num huge, .num y], r3)
    else if shape = 18 then
      let (hugeX, r2) := pickFromPool outOfRangeProgramPool rng1
      let (hugeY, r3) := pickFromPool outOfRangeProgramPool r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-both-before-qmodr"
        #[.num hugeX, .num hugeY], r3)
    else if shape = 19 then
      let kind := classifyQmodr maxInt257 2
      (mkCase s!"fuzz/shape-{shape}/{kind}/max-over-two" #[intV maxInt257, intV 2], rng1)
    else if shape = 20 then
      let kind := classifyQmodr minInt257 2
      (mkCase s!"fuzz/shape-{shape}/{kind}/min-over-two" #[intV minInt257, intV 2], rng1)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmodrId
  unit := #[
    { name := "unit/ok/nearest-sign-and-tie-remainders"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 1),
            (8, 3, -1),
            (-7, 3, -1),
            (-8, 3, 1),
            (7, -3, 1),
            (8, -3, -1),
            (-7, -3, -1),
            (-8, -3, 1),
            (1, 2, -1),
            (-1, 2, -1),
            (1, -2, 1),
            (-1, -2, 1),
            (5, 2, -1),
            (-5, 2, -1),
            (5, -2, 1),
            (-5, -2, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectQmodr s!"{x}%{y}" x y expected }
    ,
    { name := "unit/ok/boundary-and-no-overflow-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, 0),
            (maxInt257, -1, 0),
            (minInt257, 1, 0),
            (minInt257, -1, 0),
            (maxInt257, 2, -1),
            (minInt257, 2, 0),
            (minInt257, -2, 0),
            (minInt257 + 1, 2, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectQmodr s!"{x}%{y}" x y expected }
    ,
    { name := "unit/quiet/divzero-and-nan-funnel"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQmodrDirect #[intV 5, intV 0]) #[.int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQmodrDirect #[intV 0, intV 0]) #[.int .nan]
        expectOkStack "quiet/nan/y-top"
          (runQmodrDirect #[intV 9, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan/x-second"
          (runQmodrDirect #[.int .nan, intV 9]) #[.int .nan]
        expectOkStack "quiet/nan/both"
          (runQmodrDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQmodrDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQmodrDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQmodrDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQmodrDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQmodrDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQmodrDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQmodrDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first"
          (runQmodrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmodrDispatchFallback #[]) #[intV 904] }
  ]
  oracle := #[
    mkCase "ok/sign/pos-pos-inexact-low" #[intV 7, intV 3],
    mkCase "ok/sign/pos-pos-inexact-high" #[intV 8, intV 3],
    mkCase "ok/sign/neg-pos-inexact-low" #[intV (-7), intV 3],
    mkCase "ok/sign/neg-pos-inexact-high" #[intV (-8), intV 3],
    mkCase "ok/sign/pos-neg-inexact-low" #[intV 7, intV (-3)],
    mkCase "ok/sign/pos-neg-inexact-high" #[intV 8, intV (-3)],
    mkCase "ok/sign/neg-neg-inexact-low" #[intV (-7), intV (-3)],
    mkCase "ok/sign/neg-neg-inexact-high" #[intV (-8), intV (-3)],
    mkCase "ok/tie/pos-over-pos-half" #[intV 1, intV 2],
    mkCase "ok/tie/neg-over-pos-half" #[intV (-1), intV 2],
    mkCase "ok/tie/pos-over-neg-half" #[intV 1, intV (-2)],
    mkCase "ok/tie/neg-over-neg-half" #[intV (-1), intV (-2)],
    mkCase "ok/tie/pos-five-over-two" #[intV 5, intV 2],
    mkCase "ok/tie/neg-five-over-two" #[intV (-5), intV 2],
    mkCase "ok/tie/pos-five-over-neg-two" #[intV 5, intV (-2)],
    mkCase "ok/tie/neg-five-over-neg-two" #[intV (-5), intV (-2)],
    mkCase "ok/exact/multiple-pos-pos" #[intV 42, intV 7],
    mkCase "ok/exact/multiple-neg-pos" #[intV (-42), intV 7],
    mkCase "ok/exact/multiple-pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 5],
    mkCase "ok/boundary/max-mod-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-mod-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-mod-one" #[intV minInt257, intV 1],
    mkCase "ok/boundary/min-mod-neg-one-no-overflow" #[intV minInt257, intV (-1)],
    mkCase "ok/boundary/max-mod-two-tie" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/min-mod-two-even" #[intV minInt257, intV 2],
    mkCase "ok/boundary/min-mod-neg-two-even" #[intV minInt257, intV (-2)],
    mkCase "ok/boundary/min-plus-one-mod-two-tie" #[intV (minInt257 + 1), intV 2],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0],
    mkCaseFromIntVals "quiet/nan/program-y" #[IntVal.num 5, IntVal.nan],
    mkCaseFromIntVals "quiet/nan/program-x" #[IntVal.nan, IntVal.num 5],
    mkCaseFromIntVals "quiet/nan/program-both" #[IntVal.nan, IntVal.nan],
    mkCaseFromIntVals "error-order/pushint-range-high-before-qmodr"
      #[IntVal.num (maxInt257 + 1), IntVal.num 7],
    mkCaseFromIntVals "error-order/pushint-range-low-before-qmodr"
      #[IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-range-both-before-qmodr"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257))],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "type/y-cell-top" #[intV 1, .cell Cell.empty],
    mkCase "type/x-cell-second" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qmodrSetGasExact), .tonEnvOp .setGasLimit, qmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 700
      gen := genQmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMODR
