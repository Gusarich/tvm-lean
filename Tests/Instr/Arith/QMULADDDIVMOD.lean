import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULADDDIVMOD

/-
QMULADDDIVMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
    (`execInstrArithMulDivMod`, `.mulDivMod d roundMode addMode quiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb7a98 + args4` quiet decode family for `QMUL{DIV,MOD,DIVMOD}`).
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `register_div_ops`, `dump_muldivmod`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean generic `.mulDivMod`: 7 branch sites / 16 terminal outcomes
  (dispatch guard; add/non-add underflow depth; add-mode pop path;
   numeric-vs-NaN operand split; divisor-zero split; round-mode validity;
   `d` switch with `d=3` dual-push shape).
- C++ `exec_muldivmod`: 5 branch sites / 11 terminal outcomes
  (quiet opcode gate in registration; invalid-opcode guard; underflow guard;
   add/non-add pop path; `d` switch including dual result).

QMULADDDIVMOD specialization under test:
- fixed params: `d=3`, `roundMode=-1` (floor), `addMode=true`, `quiet=true`;
- stack pop order is `z`, `w`, `y`, `x`; push order is `q`, then `r`.

Key risk areas covered:
- underflow-before-type precedence (`check_underflow(4)` equivalent);
- strict pop ordering (`z → w → y → x`) for type-check/error-order cases;
- quiet funnels for div-by-zero and NaN operands (`NaN, NaN` instead of `intOv`);
- quiet overflow funnel on quotient fit failure (`NaN, 0` in boundary cases);
- floor quotient/remainder invariants across sign combinations and exactness;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QMULADDDIVMOD`.
-/

private def qmulAddDivmodId : InstrId := { name := "QMULADDDIVMOD" }

private def qmulAddDivmodInstr : Instr := .mulDivMod 3 (-1) true true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulAddDivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulAddDivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulAddDivmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def runQMulAddDivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmulAddDivmodInstr stack

private def runQMulAddDivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 2601)) stack

private def qmulAddDivmodSetGasExact : Int :=
  computeExactGasBudget qmulAddDivmodInstr

private def qmulAddDivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulAddDivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def smallFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def smallDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def smallAddendPool : Array Int :=
  #[-8, -5, -3, -1, 0, 1, 3, 5, 8]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def classifyQMulAddDivmod (x y w z : Int) : String :=
  if z = 0 then
    "divzero"
  else
    let tmp := x * y + w
    let (q, r) := divModRound tmp z (-1)
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQMulAddDivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 25
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      let kind := classifyQMulAddDivmod x y w z
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-xy" #[intV x, intV y, intV w, intV z], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickInt257Boundary r3
      let (z, r5) := pickNonZeroInt r4
      let kind := classifyQMulAddDivmod x y w z
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-w" #[intV x, intV y, intV w, intV z], r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      let kind := classifyQMulAddDivmod x y w z
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-random" #[intV x, intV y, intV w, intV z], r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"fuzz/shape-{shape}/divzero/random-total" #[intV x, intV y, intV w, intV 0], r4)
    else if shape = 4 then
      let (x, r2) := pickFromPool smallFactorPool rng1
      let (y, r3) := pickFromPool smallFactorPool r2
      let (w, r4) := pickFromPool smallAddendPool r3
      let (z, r5) := pickFromPool smallDivisorPool r4
      let kind := classifyQMulAddDivmod x y w z
      (mkCase s!"fuzz/shape-{shape}/{kind}/small-sign-mix" #[intV x, intV y, intV w, intV z], r5)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/min-times-one-div-neg-one"
        #[intV minInt257, intV 1, intV 0, intV (-1)], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/max-times-max-div-one"
        #[intV maxInt257, intV maxInt257, intV 0, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/quiet-overflow/min-times-min-div-one"
        #[intV minInt257, intV minInt257, intV 0, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/exact/max-times-one-div-one"
        #[intV maxInt257, intV 1, intV 0, intV 1], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/exact/min-times-one-div-one"
        #[intV minInt257, intV 1, intV 0, intV 1], rng1)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one" #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"fuzz/shape-{shape}/underflow/three" #[intV x, intV y, intV w], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, intV w, .null], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-w-second" #[intV x, intV y, .null, intV z], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-third" #[intV x, .null, intV w, intV z], r4)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-fourth" #[.null, intV y, intV w, intV z], r4)
    else if shape = 17 then
      (mkCase s!"fuzz/shape-{shape}/error-order/z-before-w-when-both-non-int"
        #[intV 1, intV 2, .cell Cell.empty, .null], rng1)
    else if shape = 18 then
      (mkCase s!"fuzz/shape-{shape}/error-order/w-before-y-when-z-int"
        #[intV 1, .null, .cell Cell.empty, intV 2], rng1)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[.num x, .num y, .num w, .nan], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-w-via-program"
        #[.num x, .num y, .nan, .num z], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[.num x, .nan, .num w, .num z], r4)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num y, .num w, .num z], r4)
    else if shape = 23 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/x-via-program"
        #[.num xOut, .num y, .num w, .num z], r5)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/y-via-program"
        #[.num x, .num yOut, .num w, .num z], r5)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wOut, r4) := pickInt257OutOfRange r3
      let (zOut, r5) := pickInt257OutOfRange r4
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/wz-via-program"
        #[.num x, .num y, .num wOut, .num zOut], r5)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      let kind := classifyQMulAddDivmod x y w z
      (mkCase s!"fuzz/shape-{shape}/{kind}/default" #[intV x, intV y, intV w, intV z], r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulAddDivmodId
  unit := #[
    { name := "/unit/ok/floor-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 5, 4, 2),
            (-7, 3, -1, 5, -5, 3),
            (7, -3, 1, 5, -4, 0),
            (7, 3, 1, -5, -5, -3),
            (-7, -3, -1, -5, -4, 0),
            (-1, 2, 0, 3, -1, 1),
            (1, -2, 0, 3, -1, 1),
            (-1, 2, 0, -3, 0, -2),
            (1, -2, 0, -3, 0, -2),
            (40, 2, 2, 7, 11, 5),
            (-40, 2, -2, 7, -12, 2)
          ]
        for c in checks do
          let (x, y, w, z, q, r) := c
          expectOkStack s!"unit/ok/({x}*{y}+{w})/{z}"
            (runQMulAddDivmodDirect #[intV x, intV y, intV w, intV z])
            #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 1, maxInt257, 0),
            (minInt257, 1, 0, 1, minInt257, 0),
            (minInt257 + 1, -1, 0, 1, maxInt257, 0),
            (maxInt257, 1, -1, 2, (pow2 255) - 1, 0),
            (minInt257, 1, 1, 2, -(pow2 255), 1),
            (maxInt257, 0, -1, 1, -1, 0),
            (minInt257, 0, 1, 1, 1, 0),
            (0, maxInt257, 0, 3, 0, 0),
            (0, minInt257, 0, -3, 0, 0)
          ]
        for c in checks do
          let (x, y, w, z, q, r) := c
          expectOkStack s!"unit/ok/boundary/({x}*{y}+{w})/{z}"
            (runQMulAddDivmodDirect #[intV x, intV y, intV w, intV z])
            #[intV q, intV r] }
    ,
    { name := "/unit/quiet/divzero-overflow-and-nan-funnels"
      run := do
        expectOkStack "unit/quiet/divzero/nonzero-over-zero"
          (runQMulAddDivmodDirect #[intV 5, intV 7, intV 1, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/divzero/zero-over-zero"
          (runQMulAddDivmodDirect #[intV 0, intV 0, intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/overflow/min-times-one-div-neg-one"
          (runQMulAddDivmodDirect #[intV minInt257, intV 1, intV 0, intV (-1)]) #[.int .nan, intV 0]
        expectOkStack "unit/quiet/overflow/max-times-max-div-one"
          (runQMulAddDivmodDirect #[intV maxInt257, intV maxInt257, intV 0, intV 1]) #[.int .nan, intV 0]
        expectOkStack "unit/quiet/overflow/min-times-min-div-one"
          (runQMulAddDivmodDirect #[intV minInt257, intV minInt257, intV 0, intV 1]) #[.int .nan, intV 0]
        expectOkStack "unit/quiet/nan-z"
          (runQMulAddDivmodDirect #[intV 7, intV 3, intV 1, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/nan-x"
          (runQMulAddDivmodDirect #[.int .nan, intV 3, intV 1, intV 5]) #[.int .nan, .int .nan] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "unit/error/underflow-empty" (runQMulAddDivmodDirect #[]) .stkUnd
        expectErr "unit/error/underflow-one-non-int" (runQMulAddDivmodDirect #[.null]) .stkUnd
        expectErr "unit/error/underflow-three-top-non-int"
          (runQMulAddDivmodDirect #[intV 1, intV 2, .null]) .stkUnd
        expectErr "unit/error/type/pop-z-first"
          (runQMulAddDivmodDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "unit/error/type/pop-w-second"
          (runQMulAddDivmodDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "unit/error/type/pop-y-third"
          (runQMulAddDivmodDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "unit/error/type/pop-x-fourth"
          (runQMulAddDivmodDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "unit/error/order-z-before-w-when-both-non-int"
          (runQMulAddDivmodDirect #[intV 1, intV 2, .cell Cell.empty, .null]) .typeChk
        expectErr "unit/error/order-w-before-y-when-z-int"
          (runQMulAddDivmodDirect #[intV 1, .null, .cell Cell.empty, intV 2]) .typeChk
        expectErr "unit/error/order-y-before-x-when-z-w-int"
          (runQMulAddDivmodDirect #[.null, .cell Cell.empty, intV 1, intV 2]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "unit/dispatch/fallback" (runQMulAddDivmodDispatchFallback #[]) #[intV 2601] }
  ]
  oracle := #[
    mkCase "ok/floor/sign/pos-pos-inexact" #[intV 7, intV 3, intV 1, intV 5],
    mkCase "ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 3, intV (-1), intV 5],
    mkCase "ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 1, intV 5],
    mkCase "ok/floor/sign/pos-neg-divisor-inexact" #[intV 7, intV 3, intV 1, intV (-5)],
    mkCase "ok/floor/sign/neg-neg-divisor-exact" #[intV (-7), intV (-3), intV (-1), intV (-5)],
    mkCase "ok/floor/near-zero-pos-divisor" #[intV (-1), intV 2, intV 0, intV 3],
    mkCase "ok/floor/near-zero-neg-divisor" #[intV (-1), intV 2, intV 0, intV (-3)],
    mkCase "ok/floor/addend-negative" #[intV 5, intV 4, intV (-7), intV 3],
    mkCase "ok/floor/addend-positive" #[intV (-5), intV 4, intV 7, intV (-3)],
    mkCase "ok/exact/positive-total" #[intV 42, intV 2, intV 0, intV 7],
    mkCase "ok/exact/negative-total" #[intV (-42), intV 2, intV 0, intV 7],
    mkCase "ok/exact/zero-total" #[intV 5, intV 7, intV (-35), intV 3],
    mkCase "ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 0, intV 1],
    mkCase "ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 0, intV 1],
    mkCase "ok/boundary/min-plus-one-negated-div-one"
      #[intV (minInt257 + 1), intV (-1), intV 0, intV 1],
    mkCase "ok/boundary/max-minus-one-div-two"
      #[intV maxInt257, intV 1, intV (-1), intV 2],
    mkCase "ok/boundary/min-plus-one-div-two"
      #[intV minInt257, intV 1, intV 1, intV 2],
    mkCase "quiet/overflow/min-times-one-div-neg-one"
      #[intV minInt257, intV 1, intV 0, intV (-1)],
    mkCase "quiet/overflow/max-times-max-div-one"
      #[intV maxInt257, intV maxInt257, intV 0, intV 1],
    mkCase "quiet/overflow/min-times-min-div-one"
      #[intV minInt257, intV minInt257, intV 0, intV 1],
    mkCase "quiet/overflow/max-times-two-plus-one-div-one"
      #[intV maxInt257, intV 2, intV 1, intV 1],
    mkCase "quiet/divzero/nonzero-total-over-zero"
      #[intV 5, intV 7, intV 1, intV 0],
    mkCase "quiet/divzero/zero-total-over-zero"
      #[intV 0, intV 123, intV 0, intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/three-items-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-z-first-top-non-int"
      #[intV 1, intV 2, intV 3, .null],
    mkCase "type/pop-w-second-non-int"
      #[intV 1, intV 2, .null, intV 3],
    mkCase "type/pop-y-third-non-int"
      #[intV 1, .null, intV 2, intV 3],
    mkCase "type/pop-x-fourth-non-int"
      #[.null, intV 1, intV 2, intV 3],
    mkCase "error-order/pop-z-before-w-when-both-non-int"
      #[intV 1, intV 2, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-y-when-z-int"
      #[intV 1, .null, .cell Cell.empty, intV 2],
    mkCase "error-order/pop-y-before-x-when-z-w-int"
      #[.null, .cell Cell.empty, intV 1, intV 2],
    mkCaseFromIntVals "quiet/nan-z-via-program" #[.num 7, .num 3, .num 1, .nan],
    mkCaseFromIntVals "quiet/nan-w-via-program" #[.num 7, .num 3, .nan, .num 5],
    mkCaseFromIntVals "quiet/nan-y-via-program" #[.num 7, .nan, .num 1, .num 5],
    mkCaseFromIntVals "quiet/nan-x-via-program" #[.nan, .num 3, .num 1, .num 5],
    mkCaseFromIntVals "quiet/nan-all-via-program" #[.nan, .nan, .nan, .nan],
    mkCaseFromIntVals "error-order/pushint-overflow-high-x-before-op"
      #[.num (maxInt257 + 1), .num 7, .num 3, .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-low-x-before-op"
      #[.num (minInt257 - 1), .num 7, .num 3, .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-high-y-before-op"
      #[.num 7, .num (maxInt257 + 1), .num 3, .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-low-y-before-op"
      #[.num 7, .num (minInt257 - 1), .num 3, .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-high-w-before-op"
      #[.num 7, .num 3, .num (maxInt257 + 1), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-low-w-before-op"
      #[.num 7, .num 3, .num (minInt257 - 1), .num 5],
    mkCaseFromIntVals "error-order/pushint-overflow-high-z-before-op"
      #[.num 7, .num 3, .num 1, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-low-z-before-op"
      #[.num 7, .num 3, .num 1, .num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1, intV 5]
      #[.pushInt (.num qmulAddDivmodSetGasExact), .tonEnvOp .setGasLimit, qmulAddDivmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1, intV 5]
      #[.pushInt (.num qmulAddDivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulAddDivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020827
      count := 700
      gen := genQMulAddDivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULADDDIVMOD
