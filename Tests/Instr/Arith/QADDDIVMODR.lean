import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADDDIVMODR

/-
QADDDIVMODR branch-map notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `0` nearest/ties-to-+∞)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7a90` quiet family decode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `register_div_ops`, `dump_divmod`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean `execInstrArithDivMod` path: 6 branch sites / 14 terminal outcomes
  (dispatch arm, add-mode arity gate, operand-shape split, divisor-zero split,
   round-mode validity split, `d` switch with dual-push for `d=3`).
- C++ `exec_divmod` path: 4 branch sites / 10 terminal outcomes
  (opcode guard, underflow gate, add-vs-non-add operand flow, result-shape switch).

QADDDIVMODR specialization:
- opcode args4=`0x1` under quiet `0xb7a90` family;
- fixed params: `d=3`, `roundMode=0` (nearest), `addMode=true`, `quiet=true`.

Key risk areas covered:
- nearest rounding ties toward `+∞` across sign combinations;
- quiet funnels for divisor-zero, NaN operands, and 257-bit quotient overflow;
- pop/type error ordering (`y`, then `w`, then `x`) and underflow precedence;
- oracle/fuzz serialization hygiene (NaN/out-of-range only via `PUSHINT` prelude);
- exact gas cliff via `SETGASLIMIT` exact vs exact-minus-one.
-/

private def qadddivmodrId : InstrId := { name := "QADDDIVMODR" }

private def qadddivmodrInstr : Instr := .divMod 3 0 true true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qadddivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qadddivmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[qadddivmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runQAddDivModRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qadddivmodrInstr stack

private def runQAddDivModRDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 4210)) stack

private def qadddivmodrSetGasExact : Int :=
  computeExactGasBudget qadddivmodrInstr

private def qadddivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qadddivmodrInstr

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

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQAddDivModR (x w y : Int) : String :=
  if y = 0 then
    "divzero"
  else
    let (q, r) := divModRound (x + w) y 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genQAddDivModRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 30
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      let kind := classifyQAddDivModR x w y
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-xw" #[intV x, intV w, intV y], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let kind := classifyQAddDivModR x w y
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-all" #[intV x, intV w, intV y], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero-random" #[intV x, intV w, intV 0], r3)
    else if shape = 3 then
      let (x, r2) := pickFromPool roundNumeratorPool rng1
      let (y, r3) := pickFromPool roundDenominatorPool r2
      let kind := classifyQAddDivModR x 0 y
      (mkCase s!"/fuzz/shape-{shape}/{kind}/round-pool-w-zero" #[intV x, intV 0, intV y], r3)
    else if shape = 4 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDenominatorPool r2
      let kind := classifyQAddDivModR (t - 1) 1 y
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-via-addend" #[intV (t - 1), intV 1, intV y], r3)
    else if shape = 5 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-plus-one-over-one"
        #[intV maxInt257, intV 1, intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-minus-one-over-one"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-over-negone"
        #[intV minInt257, intV 0, intV (-1)], rng1)
    else if shape = 8 then
      let kind := classifyQAddDivModR maxInt257 0 2
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-max-over-two" #[intV maxInt257, intV 0, intV 2], rng1)
    else if shape = 9 then
      let kind := classifyQAddDivModR minInt257 0 2
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-min-over-two" #[intV minInt257, intV 0, intV 2], rng1)
    else if shape = 10 then
      let kind := classifyQAddDivModR minInt257 0 (-2)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-min-over-neg-two" #[intV minInt257, intV 0, intV (-2)], rng1)
    else if shape = 11 then
      let (xRaw, r2) := pickSigned257ish rng1
      let x := if xRaw = minInt257 then minInt257 + 1 else xRaw
      let (y, r3) := pickFromPool roundDenominatorPool r2
      let kind := classifyQAddDivModR x (-x) y
      (mkCase s!"/fuzz/shape-{shape}/{kind}/cancel-sum" #[intV x, intV (-x), intV y], r3)
    else if shape = 12 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQAddDivModR 0 w y
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-x" #[intV 0, intV w, intV y], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQAddDivModR x 0 y
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-w" #[intV x, intV 0, intV y], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let kind := classifyQAddDivModR x w 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/y-one" #[intV x, intV w, intV 1], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let kind := classifyQAddDivModR x w (-1)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/y-neg-one" #[intV x, intV w, intV (-1)], r3)
    else if shape = 16 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV w], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-first" #[intV x, intV w, yBad], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (wBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-w-second" #[intV x, wBad, intV y], r4)
    else if shape = 21 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (xBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xBad, intV w, intV y], r4)
    else if shape = 22 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-w"
        #[intV 1, .null, .cell Cell.empty], rng1)
    else if shape = 23 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-x-when-y-int"
        #[.null, .cell Cell.empty, intV 2], rng1)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-y"
        #[IntVal.num x, IntVal.num w, IntVal.nan], r3)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-w"
        #[IntVal.num x, IntVal.nan, IntVal.num y], r3)
    else if shape = 26 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan/program-x"
        #[IntVal.nan, IntVal.num w, IntVal.num y], r3)
    else if shape = 27 then
      let (huge, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-x"
        #[IntVal.num huge, IntVal.num w, IntVal.num y], r4)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (huge, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-w"
        #[IntVal.num x, IntVal.num huge, IntVal.num y], r4)
    else if shape = 29 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (huge, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-y"
        #[IntVal.num x, IntVal.num w, IntVal.num huge], r4)
    else if shape = 30 then
      let (hugeX, r2) := pickInt257OutOfRange rng1
      let (hugeW, r3) := pickInt257OutOfRange r2
      let (hugeY, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/out-of-range/program-all"
        #[IntVal.num hugeX, IntVal.num hugeW, IntVal.num hugeY], r4)
    else
      (mkCase s!"/fuzz/shape-{shape}/underflow/fallback-empty" #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qadddivmodrId
  unit := #[
    { name := "/unit/ok/nearest-rounding-signs-and-ties"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 3, 4, 0),
            (7, 4, 3, 4, -1),
            (7, 0, 3, 2, 1),
            (-7, 0, 3, -2, -1),
            (7, 0, -3, -2, 1),
            (-7, 0, -3, 2, -1),
            (5, 0, 2, 3, -1),
            (-5, 0, 2, -2, -1),
            (5, 0, -2, -2, 1),
            (-5, 0, -2, 3, 1),
            (-1, 0, 2, 0, -1),
            (1, 0, -2, 0, 1),
            (4, 1, 2, 3, -1)
          ]
        for c in checks do
          match c with
          | (x, w, y, q, r) =>
              expectOkStack s!"/unit/ok/({x}+{w})/{y}"
                (runQAddDivModRDirect #[intV x, intV w, intV y])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 1, maxInt257, 0),
            (maxInt257, -1, 1, maxInt257 - 1, 0),
            (minInt257, 1, 1, minInt257 + 1, 0),
            (minInt257 + 1, 0, -1, maxInt257, 0),
            (maxInt257, 0, 2, pow2 255, -1),
            (minInt257, 0, 2, -(pow2 255), 0),
            (minInt257, 0, -2, pow2 255, 0)
          ]
        for c in checks do
          match c with
          | (x, w, y, q, r) =>
              expectOkStack s!"/unit/ok/boundary/({x}+{w})/{y}"
                (runQAddDivModRDirect #[intV x, intV w, intV y])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/quiet-divzero-overflow-and-nan-funnels"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQAddDivModRDirect #[intV 5, intV 7, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQAddDivModRDirect #[intV 0, intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow/max-plus-one-over-one"
          (runQAddDivModRDirect #[intV maxInt257, intV 1, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-minus-one-over-one"
          (runQAddDivModRDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-over-negone"
          (runQAddDivModRDirect #[intV minInt257, intV 0, intV (-1)]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/nan/y-top"
          (runQAddDivModRDirect #[intV 5, intV 7, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan/w-second"
          (runQAddDivModRDirect #[intV 5, .int .nan, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan/x-third"
          (runQAddDivModRDirect #[.int .nan, intV 5, intV 1]) #[.int .nan, .int .nan] }
    ,
    { name := "/unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "/unit/error/underflow/empty" (runQAddDivModRDirect #[]) .stkUnd
        expectErr "/unit/error/underflow/one-arg" (runQAddDivModRDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow/two-args" (runQAddDivModRDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/order/underflow-before-type-with-two-items"
          (runQAddDivModRDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/error/type/pop-y-first"
          (runQAddDivModRDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type/pop-w-second"
          (runQAddDivModRDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type/pop-x-third"
          (runQAddDivModRDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error/order/pop-y-before-w-when-both-non-int"
          (runQAddDivModRDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/order/pop-w-before-x-when-y-int"
          (runQAddDivModRDirect #[.null, .cell Cell.empty, intV 2]) .typeChk }
    ,
    { name := "/unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQAddDivModRDispatchFallback #[]) #[intV 4210] }
  ]
  oracle := #[
    mkCase "/ok/round/exact-pos-pos" #[intV 7, intV 5, intV 3],
    mkCase "/ok/round/inexact-pos-pos" #[intV 7, intV 4, intV 3],
    mkCase "/ok/round/inexact-neg-pos" #[intV (-7), intV 0, intV 3],
    mkCase "/ok/round/inexact-pos-neg" #[intV 7, intV 0, intV (-3)],
    mkCase "/ok/round/inexact-neg-neg" #[intV (-7), intV 0, intV (-3)],
    mkCase "/ok/tie/pos-over-pos-two" #[intV 5, intV 0, intV 2],
    mkCase "/ok/tie/neg-over-pos-two" #[intV (-5), intV 0, intV 2],
    mkCase "/ok/tie/pos-over-neg-two" #[intV 5, intV 0, intV (-2)],
    mkCase "/ok/tie/neg-over-neg-two" #[intV (-5), intV 0, intV (-2)],
    mkCase "/ok/tie/near-zero-neg-pos" #[intV (-1), intV 0, intV 2],
    mkCase "/ok/tie/near-zero-pos-neg" #[intV 1, intV 0, intV (-2)],
    mkCase "/ok/round/addend-shifts-result" #[intV 4, intV 1, intV 2],
    mkCase "/ok/exact/zero-sum" #[intV 42, intV (-42), intV 7],
    mkCase "/ok/exact/zero-x" #[intV 0, intV 21, intV 7],
    mkCase "/ok/exact/zero-w" #[intV 21, intV 0, intV 7],
    mkCase "/ok/boundary/max-plus-negone-over-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "/ok/boundary/min-plus-one-over-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-plus-one-over-negone" #[intV (minInt257 + 1), intV 0, intV (-1)],
    mkCase "/ok/boundary/max-over-two-rounds-up" #[intV maxInt257, intV 0, intV 2],
    mkCase "/ok/boundary/min-over-two-exact" #[intV minInt257, intV 0, intV 2],
    mkCase "/ok/boundary/min-over-neg-two-exact" #[intV minInt257, intV 0, intV (-2)],
    mkCase "/quiet/overflow/max-plus-one-over-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/quiet/overflow/min-minus-one-over-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "/quiet/overflow/min-over-negone" #[intV minInt257, intV 0, intV (-1)],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/type/pop-y-first" #[intV 1, intV 2, .null],
    mkCase "/type/pop-w-second" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "/error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "/error-order/pop-y-before-w-when-both-non-int" #[intV 1, .null, .cell Cell.empty],
    mkCase "/error-order/pop-w-before-x-when-y-int" #[.null, .cell Cell.empty, intV 2],
    mkInputCase "/quiet/nan/program-y" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInputCase "/quiet/nan/program-w" #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkInputCase "/quiet/nan/program-x" #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkInputCase "/error-order/pushint-range/program-x"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 7],
    mkInputCase "/error-order/pushint-range/program-w"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 7],
    mkInputCase "/error-order/pushint-range/program-y"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qadddivmodrSetGasExact), .tonEnvOp .setGasLimit, qadddivmodrInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qadddivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qadddivmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 700
      gen := genQAddDivModRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADDDIVMODR
