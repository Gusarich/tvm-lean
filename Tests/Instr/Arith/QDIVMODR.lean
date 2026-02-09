import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QDIVMODR

/-
QDIVMODR branch map (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest-mode ties)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (`PUSHINT` overflow/NaN program injections)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp` (`exec_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp` (`mod_div_any`, round_mode=0 ties)

Branch/terminal counts used for this suite:
- Lean `execInstrArithDivMod`: 6 branch sites / 14 terminal outcomes
  (dispatch; add-mode pop split; operand-shape split; divisor-zero split;
   round-mode validation split; `d` switch; non-num `d=3` split).
- C++ `exec_divmod`: 4 branch sites / 10 terminal outcomes
  (add-remap gate; invalid-opcode guard; underflow guard; add/non-add split with `d` switch).

QDIVMODR specialization:
- opcode args4 = `0xd` in quiet `0xb7a90` family;
- fixed params are `d=3`, `roundMode=0` (nearest with ties to +∞),
  `addMode=false`, `quiet=true`.

Key risk areas covered:
- nearest rounding tie behavior and `(q,r)` pairing across sign mixes;
- quiet NaN funnels (div-by-zero / overflow / NaN operand) must not throw `intOv`;
- pop/type error ordering (`y` popped before `x`, underflow before type on short stack);
- NaN and out-of-range operand injection through program (`PUSHNAN`, `PUSHINT_LONG`);
- exact gas threshold around `SETGASLIMIT`.
-/

private def qdivmodrId : InstrId := { name := "QDIVMODR" }

private def qdivmodrInstr : Instr := .divMod 3 0 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qdivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qdivmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[qdivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runQdivmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qdivmodrInstr stack

private def runQdivmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 606)) stack

private def qdivmodrSetGasExact : Int :=
  computeExactGasBudget qdivmodrInstr

private def qdivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qdivmodrInstr

private def expectQdivmodr
    (label : String)
    (x y q r : Int) : IO Unit :=
  expectOkStack label (runQdivmodrDirect #[intV x, intV y]) #[intV q, intV r]

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def roundNumeratorPool : Array Int :=
  #[-11, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 11]

private def roundDenominatorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def tieNumeratorPool : Array Int :=
  #[-11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1, pow2 257, -(pow2 257)]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  pickFromPool outOfRangeProgramPool rng

private def classifyQdivmodr (x y : Int) : String :=
  if y = 0 then
    "divzero"
  else
    let (q, r) := divModRound x y 0
    if !intFitsSigned257 q then
      "overflow"
    else if !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genQdivmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQdivmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-nonzero" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQdivmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-nonzero" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/divzero/random" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickFromPool roundNumeratorPool rng1
      let (y, r3) := pickFromPool roundDenominatorPool r2
      let kind := classifyQdivmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/round-pool" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/overflow/min-div-neg-one" #[intV minInt257, intV (-1)], rng1)
    else if shape = 5 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromPool roundDenominatorPool r2
      let kind := classifyQdivmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-pool" #[intV x, intV y], r3)
    else if shape = 6 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDenominatorPool r2
      let kind := classifyQdivmodr x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/tie-pool" #[intV x, intV y], r3)
    else if shape = 7 then
      let (y, r2) := pickNonZeroInt rng1
      let kind := classifyQdivmodr 0 y
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-numerator" #[intV 0, intV y], r2)
    else if shape = 8 then
      let kind := classifyQdivmodr maxInt257 2
      (mkCase s!"fuzz/shape-{shape}/{kind}/max-over-two" #[intV maxInt257, intV 2], rng1)
    else if shape = 9 then
      let kind := classifyQdivmodr minInt257 2
      (mkCase s!"fuzz/shape-{shape}/{kind}/min-over-two" #[intV minInt257, intV 2], rng1)
    else if shape = 10 then
      let kind := classifyQdivmodr minInt257 (-2)
      (mkCase s!"fuzz/shape-{shape}/{kind}/min-over-neg-two" #[intV minInt257, intV (-2)], rng1)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, .null], r2)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[.null, intV y], r2)
    else if shape = 15 then
      (mkCase s!"fuzz/shape-{shape}/type/both-non-int-y-first" #[.cell Cell.empty, .null], rng1)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-y" #[IntVal.num x, IntVal.nan], r2)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-x" #[IntVal.nan, IntVal.num y], r2)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (huge, r3) := pickOutOfRangeProgramInt r2
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-y"
        #[IntVal.num x, IntVal.num huge], r3)
    else if shape = 19 then
      let (y, r2) := pickSigned257ish rng1
      let (huge, r3) := pickOutOfRangeProgramInt r2
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-x"
        #[IntVal.num huge, IntVal.num y], r3)
    else if shape = 20 then
      let (hugeX, r2) := pickOutOfRangeProgramInt rng1
      let (hugeY, r3) := pickOutOfRangeProgramInt r2
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-both"
        #[IntVal.num hugeX, IntVal.num hugeY], r3)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-fallback" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qdivmodrId
  unit := #[
    { name := "unit/ok/nearest-rounding-sign-and-tie"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 1),
            (-7, 3, -2, -1),
            (7, -3, -2, 1),
            (-7, -3, 2, -1),
            (5, 2, 3, -1),
            (-5, 2, -2, -1),
            (5, -2, -2, 1),
            (-5, -2, 3, 1),
            (1, 2, 1, -1),
            (-1, 2, 0, -1),
            (1, -2, 0, 1),
            (-1, -2, 1, 1),
            (42, 7, 6, 0),
            (-42, -7, 6, 0),
            (0, 5, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectQdivmodr s!"{x}/{y}" x y q r }
    ,
    { name := "unit/ok/quiet-nan-and-overflow-funnels"
      run := do
        expectOkStack "divzero/nonzero-over-zero"
          (runQdivmodrDirect #[intV 5, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "divzero/zero-over-zero"
          (runQdivmodrDirect #[intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "overflow/min-div-neg-one"
          (runQdivmodrDirect #[intV minInt257, intV (-1)]) #[.int .nan, intV 0]
        expectOkStack "nan/y-top"
          (runQdivmodrDirect #[intV 9, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "nan/x-second"
          (runQdivmodrDirect #[.int .nan, intV 9]) #[.int .nan, .int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQdivmodrDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQdivmodrDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQdivmodrDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQdivmodrDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQdivmodrDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-y-first" (runQdivmodrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQdivmodrDispatchFallback #[]) #[intV 606] }
  ]
  oracle := #[
    mkCase "ok/round/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ok/round/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ok/round/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ok/round/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ok/tie/pos-over-pos-two" #[intV 5, intV 2],
    mkCase "ok/tie/neg-over-pos-two" #[intV (-5), intV 2],
    mkCase "ok/tie/pos-over-neg-two" #[intV 5, intV (-2)],
    mkCase "ok/tie/neg-over-neg-two" #[intV (-5), intV (-2)],
    mkCase "ok/tie/neg-one-over-two" #[intV (-1), intV 2],
    mkCase "ok/tie/one-over-neg-two" #[intV 1, intV (-2)],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 5],
    mkCase "ok/boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/boundary/max-div-two-rounds-up" #[intV maxInt257, intV 2],
    mkCase "ok/boundary/min-div-two-exact" #[intV minInt257, intV 2],
    mkCase "ok/boundary/min-div-neg-two-exact" #[intV minInt257, intV (-2)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0],
    mkCase "quiet/overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "type/y-non-int-top" #[intV 1, .null],
    mkCase "type/x-non-int-second" #[.null, intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkInputCase "quiet/nan/program-y" #[IntVal.num 5, IntVal.nan],
    mkInputCase "quiet/nan/program-x" #[IntVal.nan, IntVal.num 5],
    mkInputCase "quiet/out-of-range/program-y-high" #[IntVal.num 5, IntVal.num (maxInt257 + 1)],
    mkInputCase "quiet/out-of-range/program-y-low" #[IntVal.num 5, IntVal.num (minInt257 - 1)],
    mkInputCase "quiet/out-of-range/program-x-high" #[IntVal.num (maxInt257 + 1), IntVal.num 5],
    mkInputCase "quiet/out-of-range/program-x-low" #[IntVal.num (minInt257 - 1), IntVal.num 5],
    mkInputCase "quiet/out-of-range/program-both" #[IntVal.num (pow2 257), IntVal.num (-(pow2 257))],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qdivmodrSetGasExact), .tonEnvOp .setGasLimit, qdivmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qdivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qdivmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020810
      count := 700
      gen := genQdivmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QDIVMODR
