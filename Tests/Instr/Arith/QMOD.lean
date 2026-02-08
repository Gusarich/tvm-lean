import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMOD

/-
QMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, floor mode `-1`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean (`execInstrArithDivMod` generic): 6 branch sites / 14 terminal outcomes
  (dispatch arm; add/non-add pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch; non-num fallback split).
- C++ (`exec_divmod` generic): 4 branch sites / 10 terminal outcomes
  (add-remap gate; invalid-opcode guard; underflow guard; add/non-add split
   with `d` switch push-shape outcomes).

QMOD specialization:
- opcode args4=`0x8` under quiet `0xb7a90` family;
- fixed params: `d=2`, `roundMode=-1` (floor), `addMode=false`, `quiet=true`.

Key risk areas covered:
- floor remainder sign semantics across all sign combinations;
- quiet funnels for divisor-zero and NaN operands (`NaN` result, not throw);
- pop/error order (`stkUnd` before type checks, `y` pops before `x`);
- out-of-range integer handling via `PUSHINT` prelude before QMOD execution;
- deterministic gas cliff (`PUSHINT n; SETGASLIMIT; QMOD`) exact vs exact-minus-one.
-/

private def qmodId : InstrId := { name := "QMOD" }

private def qmodInstr : Instr := .divMod 2 (-1) false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qmodInstr stack

private def runQmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 808)) stack

private def qmodSetGasExact : Int :=
  computeExactGasBudget qmodInstr

private def qmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmodInstr

private def floorNumeratorPool : Array Int :=
  #[-9, -7, -5, -1, 0, 1, 5, 7, 9]

private def floorDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def qmodOutOfRangePool : Array Int :=
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

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def pickOutOfRange (rng : StdGen) : Int × StdGen :=
  pickFromPool qmodOutOfRangePool rng

private def classifyQmod (x y : Int) : String :=
  if y = 0 then
    "divzero"
  else
    let (_, r) := divModRound x y (-1)
    if !intFitsSigned257 r then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQmod x y
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQmod x y
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickFromPool floorNumeratorPool rng1
      let (y, r3) := pickFromPool floorDenominatorPool r2
      let kind := classifyQmod x y
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/small-sign-mix" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/ok/exact/max-mod-one" #[intV maxInt257, intV 1], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/ok/exact/max-mod-neg-one" #[intV maxInt257, intV (-1)], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/ok/inexact/max-mod-two" #[intV maxInt257, intV 2], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/ok/exact/min-mod-one" #[intV minInt257, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/ok/exact/min-mod-neg-one" #[intV minInt257, intV (-1)], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/ok/exact/min-mod-two" #[intV minInt257, intV 2], rng1)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/ok/exact/min-mod-neg-two" #[intV minInt257, intV (-2)], rng1)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow/one-non-int" #[.null], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, yLike], r3)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[xLike, intV y], r3)
    else if shape = 16 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[xLike, yLike], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program" #[.num x, .nan], r2)
    else if shape = 18 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program" #[.nan, .num y], r2)
    else if shape = 19 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program" #[.nan, .nan], rng1)
    else
      let (variant, r2) := randNat rng1 0 2
      if variant = 0 then
        let (x, r3) := pickSigned257ish r2
        let (yo, r4) := pickOutOfRange r3
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-y-before-qmod"
          #[.num x, .num yo], r4)
      else if variant = 1 then
        let (xo, r3) := pickOutOfRange r2
        let (y, r4) := pickNonZeroInt r3
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-qmod"
          #[.num xo, .num y], r4)
      else
        let (xo, r3) := pickOutOfRange r2
        let (yo, r4) := pickOutOfRange r3
        (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-qmod"
          #[.num xo, .num yo], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmodId
  unit := #[
    { name := "unit/ok/floor-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 1),
            (-7, 3, 2),
            (7, -3, -2),
            (-7, -3, -1),
            (-1, 2, 1),
            (1, -2, -1),
            (-5, 2, 1),
            (5, -2, -1),
            (42, 7, 0),
            (-42, 7, 0),
            (42, -7, 0),
            (-42, -7, 0),
            (0, 5, 0),
            (0, -5, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let r := c.2.2
          expectOkStack s!"{x}%{y}" (runQmodDirect #[intV x, intV y]) #[intV r] }
    ,
    { name := "unit/ok/floor-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, 0),
            (maxInt257, -1, 0),
            (maxInt257, 2, 1),
            (minInt257, 1, 0),
            (minInt257, -1, 0),
            (minInt257, 2, 0),
            (minInt257, -2, 0),
            (minInt257 + 1, 2, 1),
            (minInt257 + 1, -2, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let r := c.2.2
          expectOkStack s!"{x}%{y}" (runQmodDirect #[intV x, intV y]) #[intV r] }
    ,
    { name := "unit/quiet/divzero-nan-and-range-funnel"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQmodDirect #[intV 5, intV 0]) #[.int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQmodDirect #[intV 0, intV 0]) #[.int .nan]
        expectOkStack "quiet/nan/y"
          (runQmodDirect #[intV 9, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan/x"
          (runQmodDirect #[.int .nan, intV 9]) #[.int .nan]
        expectOkStack "quiet/nan/both"
          (runQmodDirect #[.int .nan, .int .nan]) #[.int .nan]
        expectOkStack "quiet/range/remainder-overflow-via-huge-x"
          (runQmodDirect #[intV (maxInt257 + 1), intV (pow2 257)]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQmodDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQmodDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQmodDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQmodDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first"
          (runQmodDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmodDispatchFallback #[]) #[intV 808] }
  ]
  oracle := #[
    mkCase "ok/floor/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ok/floor/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ok/floor/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "ok/floor/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "ok/floor/sign/neg-pos-half" #[intV (-5), intV 2],
    mkCase "ok/floor/sign/pos-neg-half" #[intV 5, intV (-2)],
    mkCase "ok/floor/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ok/floor/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ok/floor/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ok/floor/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ok/floor/exact/zero-numerator-pos-divisor" #[intV 0, intV 5],
    mkCase "ok/floor/exact/zero-numerator-neg-divisor" #[intV 0, intV (-5)],
    mkCase "ok/floor/boundary/max-mod-one" #[intV maxInt257, intV 1],
    mkCase "ok/floor/boundary/max-mod-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/floor/boundary/max-mod-two" #[intV maxInt257, intV 2],
    mkCase "ok/floor/boundary/min-mod-one" #[intV minInt257, intV 1],
    mkCase "ok/floor/boundary/min-mod-neg-one" #[intV minInt257, intV (-1)],
    mkCase "ok/floor/boundary/min-mod-two" #[intV minInt257, intV 2],
    mkCase "ok/floor/boundary/min-mod-neg-two" #[intV minInt257, intV (-2)],
    mkCase "ok/floor/boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 2],
    mkCase "ok/floor/boundary/min-plus-one-mod-neg-two" #[intV (minInt257 + 1), intV (-2)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first" #[intV 1, .null],
    mkCase "type/pop-x-second" #[.null, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[.num 5, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 5],
    mkCaseFromIntVals "quiet/nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-overflow-high-x-before-qmod"
      #[.num (maxInt257 + 1), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-low-x-before-qmod"
      #[.num (minInt257 - 1), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-high-y-before-qmod"
      #[.num 5, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-low-y-before-qmod"
      #[.num 5, .num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-both-before-qmod"
      #[.num (pow2 257), .num (-(pow2 257))],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qmodSetGasExact), .tonEnvOp .setGasLimit, qmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmodInstr]
  ]
  fuzz := #[
    { seed := 2026020824
      count := 700
      gen := genQmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMOD
