import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADDDIVMOD

/-
QADDDIVMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean`
    (`execInstrArithDivMod`, `.divMod d roundMode addMode quiet`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet `0xb7a90` decode to `.divMod` with add-mode remap)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `register_div_ops`, `dump_divmod`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean generic `.divMod`: 6 branch sites / 14 terminal outcomes
  (dispatch arm; add/non-add arity split; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with `d=3` dual-push).
- C++ `exec_divmod`: 4 branch sites / 10 terminal outcomes
  (registration/remap gate; invalid-opcode guard; underflow guard;
   add/non-add pop path with `d` result-shape switch).

QADDDIVMOD specialization under test:
- opcode family `0xb7a90`, args4=`0x0`;
- fixed params: `d=3`, `roundMode=-1` (floor), `addMode=true`, `quiet=true`.

Key risk areas covered:
- add-mode pop order and error order (`y`, then `w`, then `x`);
- floor quotient/remainder invariants and output order (`q` then `r`);
- quiet funnels for divisor-zero, NaN operands, and quotient overflow;
- underflow-before-type precedence for short stacks;
- deterministic gas cliff (`PUSHINT n; SETGASLIMIT; QADDDIVMOD`);
- oracle/fuzz serialization hygiene: NaN and out-of-range operands injected via `PUSHINT`.
-/

private def qadddivmodId : InstrId := { name := "QADDDIVMOD" }

private def qadddivmodInstr : Instr := .divMod 3 (-1) true true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qadddivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qadddivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qadddivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQAddDivModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qadddivmodInstr stack

private def runQAddDivModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 6417)) stack

private def qadddivmodSetGasExact : Int :=
  computeExactGasBudget qadddivmodInstr

private def qadddivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qadddivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  (if tag = 0 then .null else .cell Cell.empty, rng')

private def floorNumeratorPool : Array Int :=
  #[-11, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 11]

private def floorDenominatorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def addendPool : Array Int :=
  #[-8, -5, -3, -1, 0, 1, 3, 5, 8]

private def classifyQAddDivMod (x w y : Int) : String :=
  if y = 0 then
    "divzero"
  else
    let t := x + w
    let (q, r) := divModRound t y (-1)
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQAddDivModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let kind := classifyQAddDivMod x w y
      (mkCase s!"fuzz/shape-{shape}/{kind}/x-boundary" #[intV x, intV w, intV y], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      let kind := classifyQAddDivMod x w y
      (mkCase s!"fuzz/shape-{shape}/{kind}/w-boundary" #[intV x, intV w, intV y], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      let kind := classifyQAddDivMod x w y
      (mkCase s!"fuzz/shape-{shape}/{kind}/xw-boundary" #[intV x, intV w, intV y], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let kind := classifyQAddDivMod x w y
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-random" #[intV x, intV w, intV y], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/divzero/random" #[intV x, intV w, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool floorNumeratorPool rng1
      let (w, r3) := pickFromPool addendPool r2
      let (y, r4) := pickFromPool floorDenominatorPool r3
      let kind := classifyQAddDivMod x w y
      (mkCase s!"fuzz/shape-{shape}/{kind}/small-sign-mix" #[intV x, intV w, intV y], r4)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/min-plus-zero-over-neg-one"
        #[intV minInt257, intV 0, intV (-1)], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/max-plus-one-over-one"
        #[intV maxInt257, intV 1, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/min-minus-one-over-one"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/exact/max-plus-max-over-two"
        #[intV maxInt257, intV maxInt257, intV 2], rng1)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/exact/min-plus-min-over-two"
        #[intV minInt257, intV minInt257, intV 2], rng1)
    else if shape = 11 then
      let (xRaw, r2) := pickSigned257ish rng1
      let x := if xRaw = minInt257 then minInt257 + 1 else xRaw
      let (y, r3) := pickNonZeroInt r2
      let kind := classifyQAddDivMod x (-x) y
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-total" #[intV x, intV (-x), intV y], r3)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-ints" #[intV x, intV w], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yBad, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, intV w, yBad], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (wBad, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-w-second" #[intV x, wBad, intV y], r4)
    else if shape = 17 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (xBad, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-third" #[xBad, intV w, intV y], r4)
    else if shape = 18 then
      (mkCase s!"fuzz/shape-{shape}/error-order/pop-y-before-w-when-both-non-int"
        #[intV 1, .cell Cell.empty, .null], rng1)
    else if shape = 19 then
      (mkCase s!"fuzz/shape-{shape}/error-order/pop-w-before-x-when-y-int"
        #[.null, .cell Cell.empty, intV 1], rng1)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[.num x, .num w, .nan], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-w-via-program"
        #[.num x, .nan, .num y], r3)
    else if shape = 22 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num w, .num y], r3)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/y-via-program"
        #[.num x, .num w, .num yOut], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/w-via-program"
        #[.num x, .num wOut, .num y], r4)
    else if shape = 25 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/x-via-program"
        #[.num xOut, .num w, .num y], r4)
    else if shape = 26 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (yOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/all-via-program"
        #[.num xOut, .num wOut, .num yOut], r4)
    else
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickFromPool addendPool r2
      let (y, r4) := pickFromPool floorDenominatorPool r3
      let kind := classifyQAddDivMod x w y
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-sign-mix" #[intV x, intV w, intV y], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qadddivmodId
  unit := #[
    { name := "/unit/ok/floor-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 1, 3, 2, 2),
            (-7, -1, 3, -3, 1),
            (7, 1, -3, -3, -1),
            (-7, -1, -3, 2, -2),
            (-1, 0, 2, -1, 1),
            (1, 0, -2, -1, -1),
            (5, -7, 3, -1, 1),
            (-5, 7, -3, -1, -1),
            (40, 2, 7, 6, 0),
            (-40, -2, 7, -6, 0),
            (0, 0, 5, 0, 0)
          ]
        for c in checks do
          let (x, w, y, q, r) := c
          expectOkStack s!"/unit/ok/({x}+{w})/{y}"
            (runQAddDivModDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-and-large-numerator-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 1, maxInt257, 0),
            (minInt257, 0, 1, minInt257, 0),
            (minInt257 + 1, 0, -1, maxInt257, 0),
            (maxInt257, -1, 1, maxInt257 - 1, 0),
            (maxInt257, 1, 2, pow2 255, 0),
            (minInt257, -1, 2, (-(pow2 255)) - 1, 1),
            (minInt257, 1, 2, -(pow2 255), 1),
            (maxInt257, -1, 2, (pow2 255) - 1, 0),
            (maxInt257, maxInt257, 2, maxInt257, 0),
            (minInt257, minInt257, 2, minInt257, 0)
          ]
        for c in checks do
          let (x, w, y, q, r) := c
          expectOkStack s!"/unit/ok/boundary/({x}+{w})/{y}"
            (runQAddDivModDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "/unit/quiet/divzero-overflow-and-nan-funnels"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQAddDivModDirect #[intV 5, intV 1, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQAddDivModDirect #[intV 0, intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQAddDivModDirect #[intV 5, intV 1, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-w"
          (runQAddDivModDirect #[intV 5, .int .nan, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQAddDivModDirect #[.int .nan, intV 1, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow/min-plus-zero-over-neg-one"
          (runQAddDivModDirect #[intV minInt257, intV 0, intV (-1)]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/max-plus-one-over-one"
          (runQAddDivModDirect #[intV maxInt257, intV 1, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-minus-one-over-one"
          (runQAddDivModDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/max-plus-max-over-one"
          (runQAddDivModDirect #[intV maxInt257, intV maxInt257, intV 1]) #[.int .nan, intV 0] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow/empty" (runQAddDivModDirect #[]) .stkUnd
        expectErr "/unit/error/underflow/one-item" (runQAddDivModDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow/two-items" (runQAddDivModDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow-before-type-with-two-non-int"
          (runQAddDivModDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/error/type/pop-y-first"
          (runQAddDivModDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type/pop-w-second"
          (runQAddDivModDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type/pop-x-third"
          (runQAddDivModDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error/order-pop-y-before-w-when-both-non-int"
          (runQAddDivModDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error/order-pop-w-before-x-when-y-int"
          (runQAddDivModDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQAddDivModDispatchFallback #[]) #[intV 6417] }
  ]
  oracle := #[
    mkCase "ok/floor/sign/pos-pos-inexact" #[intV 7, intV 1, intV 3],
    mkCase "ok/floor/sign/neg-pos-inexact" #[intV (-7), intV (-1), intV 3],
    mkCase "ok/floor/sign/pos-neg-inexact" #[intV 7, intV 1, intV (-3)],
    mkCase "ok/floor/sign/neg-neg-inexact" #[intV (-7), intV (-1), intV (-3)],
    mkCase "ok/floor/sign/neg-near-zero" #[intV (-1), intV 0, intV 2],
    mkCase "ok/floor/sign/pos-neg-near-zero" #[intV 1, intV 0, intV (-2)],
    mkCase "ok/floor/addend/negative" #[intV 5, intV (-7), intV 3],
    mkCase "ok/floor/addend/positive" #[intV (-5), intV 7, intV (-3)],
    mkCase "ok/floor/exact/pos" #[intV 40, intV 2, intV 7],
    mkCase "ok/floor/exact/neg" #[intV (-40), intV (-2), intV 7],
    mkCase "ok/floor/exact/zero-total" #[intV 5, intV (-5), intV 3],
    mkCase "ok/boundary/max-plus-zero-over-one" #[intV maxInt257, intV 0, intV 1],
    mkCase "ok/boundary/min-plus-zero-over-one" #[intV minInt257, intV 0, intV 1],
    mkCase "ok/boundary/min-plus-one-over-neg-one" #[intV (minInt257 + 1), intV 0, intV (-1)],
    mkCase "ok/boundary/max-minus-one-over-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/boundary/max-plus-one-over-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "ok/boundary/min-minus-one-over-two" #[intV minInt257, intV (-1), intV 2],
    mkCase "ok/boundary/min-plus-one-over-two" #[intV minInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-minus-one-over-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "ok/boundary/max-plus-max-over-two" #[intV maxInt257, intV maxInt257, intV 2],
    mkCase "ok/boundary/min-plus-min-over-two" #[intV minInt257, intV minInt257, intV 2],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 1, intV 0],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0],
    mkCase "quiet/overflow/min-plus-zero-over-neg-one" #[intV minInt257, intV 0, intV (-1)],
    mkCase "quiet/overflow/max-plus-one-over-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "quiet/overflow/min-minus-one-over-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "quiet/overflow/max-plus-max-over-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "quiet/overflow/min-plus-min-over-neg-one" #[intV minInt257, intV minInt257, intV (-1)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-non-int" #[.null, .cell Cell.empty],
    mkCase "type/pop-y-first-null" #[intV 1, intV 2, .null],
    mkCase "type/pop-w-second-null" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-y-before-w-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-x-when-y-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[.num 7, .num 1, .nan],
    mkCaseFromIntVals "quiet/nan/w-via-program" #[.num 7, .nan, .num 3],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 1, .num 3],
    mkCaseFromIntVals "quiet/nan/all-via-program" #[.nan, .nan, .nan],
    mkCaseFromIntVals "error-order/pushint-overflow-x-high-before-op"
      #[.num (maxInt257 + 1), .num 1, .num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-x-low-before-op"
      #[.num (minInt257 - 1), .num 1, .num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-w-high-before-op"
      #[.num 7, .num (maxInt257 + 1), .num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-w-low-before-op"
      #[.num 7, .num (minInt257 - 1), .num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-y-high-before-op"
      #[.num 7, .num 1, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-y-low-before-op"
      #[.num 7, .num 1, .num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-all-before-op"
      #[.num (pow2 257), .num (-(pow2 257)), .num (pow2 257)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 1, intV 3]
      #[.pushInt (.num qadddivmodSetGasExact), .tonEnvOp .setGasLimit, qadddivmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 1, intV 3]
      #[.pushInt (.num qadddivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qadddivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020809
      count := 750
      gen := genQAddDivModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADDDIVMOD
