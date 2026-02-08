import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QDIVMOD

/-
QDIVMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, floor mode `-1`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `register_div_ops`, `dump_divmod`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean generic `.divMod`: 6 branch sites / 14 terminal outcomes
  (dispatch, add/non-add pop path, operand-shape split, divisor-zero split,
   round-mode validity split, `d` switch including `d=3` push shape).
- C++ `exec_divmod`: 4 branch sites / 10 terminal outcomes
  (global-version add-remap gate, invalid-opcode guard, underflow guard,
   add/non-add split with `d` switch push shape).

QDIVMOD specialization:
- opcode args4=`0xc` under `0xb7a90` family;
- fixed params: `d=3`, `roundMode=-1` (floor), `addMode=false`, `quiet=true`.

Key risk areas covered:
- quotient/remainder sign semantics and output order (`q` then `r`) across sign mixes;
- exact and inexact floor division, including zero numerator cases;
- quiet funnels for div-by-zero, NaN operands, and boundary overflow (`minInt257 / -1`);
- underflow-before-type ordering and pop order (`y` first, then `x`);
- deterministic gas cliff (`PUSHINT n; SETGASLIMIT; QDIVMOD`) exact vs exact-minus-one;
- NaN and out-of-range injection via program path (`PUSHINT`) ordering before opcode.
-/

private def qdivmodId : InstrId := { name := "QDIVMOD" }

private def qdivmodInstr : Instr := .divMod 3 (-1) false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qdivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qdivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qdivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQdivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qdivmodInstr stack

private def runQdivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 4242)) stack

private def qdivmodSetGasExact : Int :=
  computeExactGasBudget qdivmodInstr

private def qdivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qdivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def floorNumeratorPool : Array Int :=
  #[-9, -7, -5, -1, 0, 1, 5, 7, 9]

private def floorDenominatorPool : Array Int :=
  #[-3, -2, -1, 1, 2, 3]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1]

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (outOfRangeProgramPool.size - 1)
  (outOfRangeProgramPool[idx]!, rng')

private def classifyQdivmod (x y : Int) : String :=
  if y = 0 then
    "divzero"
  else
    let (q, r) := divModRound x y (-1)
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQdivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQdivmod x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQdivmod x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/divzero/random" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickFromPool floorNumeratorPool rng1
      let (y, r3) := pickFromPool floorDenominatorPool r2
      let kind := classifyQdivmod x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/small-sign-mix" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/min-div-neg-one" #[intV minInt257, intV (-1)], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/exact/max-div-neg-one" #[intV maxInt257, intV (-1)], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/exact/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)], rng1)
    else if shape = 7 then
      let (y, r2) := pickNonZeroInt rng1
      (mkCase s!"fuzz/shape-{shape}/exact/zero-numerator" #[intV 0, intV y], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/one-non-int" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, .null], r2)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[.null, intV y], r2)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first"
        #[.cell Cell.empty, .null], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/y-via-program" #[.num x, .nan], r2)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/x-via-program" #[.nan, .num y], r2)
    else if shape = 16 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/both-via-program" #[.nan, .nan], rng1)
    else if shape = 17 then
      let (y, r2) := pickNonZeroInt rng1
      let (huge, r3) := pickOutOfRangeProgramInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/x-via-program" #[.num huge, .num y], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (huge, r3) := pickOutOfRangeProgramInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/y-via-program" #[.num x, .num huge], r3)
    else if shape = 19 then
      let (hugeX, r2) := pickOutOfRangeProgramInt rng1
      let (hugeY, r3) := pickOutOfRangeProgramInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/both-via-program" #[.num hugeX, .num hugeY], r3)
    else
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromPool floorDenominatorPool r2
      let kind := classifyQdivmod x y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-sign-mix" #[intV x, intV y], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qdivmodId
  unit := #[
    { name := "unit/ok/floor-quotient-remainder-signs-and-zeros"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 1),
            (-7, 3, -3, 2),
            (7, -3, -3, -2),
            (-7, -3, 2, -1),
            (-1, 2, -1, 1),
            (1, -2, -1, -1),
            (-5, 2, -3, 1),
            (5, -2, -3, -1),
            (42, 7, 6, 0),
            (-42, 7, -6, 0),
            (42, -7, -6, 0),
            (-42, -7, 6, 0),
            (0, 5, 0, 0),
            (0, -5, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, q, r) =>
              expectOkStack s!"{x}/{y}" (runQdivmodDirect #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/ok/quiet-divzero-nan-and-overflow-behavior"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQdivmodDirect #[intV 5, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQdivmodDirect #[intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/y"
          (runQdivmodDirect #[intV 5, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/x"
          (runQdivmodDirect #[.int .nan, intV 5]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/both"
          (runQdivmodDirect #[.int .nan, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "quiet/overflow/min-div-neg-one"
          (runQdivmodDirect #[intV minInt257, intV (-1)]) #[.int .nan, intV 0]
        expectOkStack "quiet/exact/max-div-neg-one"
          (runQdivmodDirect #[intV maxInt257, intV (-1)]) #[intV (-maxInt257), intV 0] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQdivmodDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQdivmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQdivmodDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQdivmodDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQdivmodDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first"
          (runQdivmodDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQdivmodDispatchFallback #[]) #[intV 4242] }
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
    mkCase "ok/floor/exact/zero-pos" #[intV 0, intV 5],
    mkCase "ok/floor/exact/zero-neg" #[intV 0, intV (-5)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0],
    mkCase "quiet/overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCase "ok/floor/exact/max-div-one" #[intV maxInt257, intV 1],
    mkCase "ok/floor/exact/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/floor/exact/min-div-one" #[intV minInt257, intV 1],
    mkCase "ok/floor/exact/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "ok/floor/inexact/max-div-two" #[intV maxInt257, intV 2],
    mkCase "ok/floor/exact/min-div-two" #[intV minInt257, intV 2],
    mkCase "ok/floor/exact/min-div-neg-two" #[intV minInt257, intV (-2)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first" #[intV 1, .null],
    mkCase "type/pop-x-second" #[.null, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[.num 5, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 5],
    mkCaseFromIntVals "quiet/nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-overflow-high-x-before-qdivmod"
      #[.num (maxInt257 + 1), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-low-x-before-qdivmod"
      #[.num (minInt257 - 1), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-high-y-before-qdivmod"
      #[.num 5, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-low-y-before-qdivmod"
      #[.num 5, .num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qdivmodSetGasExact), .tonEnvOp .setGasLimit, qdivmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qdivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qdivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 700
      gen := genQdivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QDIVMOD
