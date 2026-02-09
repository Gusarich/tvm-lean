import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULMOD

/-
QMULMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
    (`execInstrArithMulDivMod`, `.mulDivMod d roundMode addMode quiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode family `0xb7a98 + args4` for `QMUL{DIV,MOD,DIVMOD}`).
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `register_div_ops`, `dump_muldivmod`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean generic `.mulDivMod`: 7 branch sites / 16 terminal outcomes.
- Lean QMULMOD specialization (`d=2`, `roundMode=-1`, `addMode=false`, `quiet=true`):
  8 branch sites / 8 reachable terminal outcomes
  (dispatch fallthrough; underflow; z/y/x type-pop faults; finite success;
   quiet divzero funnel; quiet NaN-input funnel).
- C++ `exec_muldivmod` generic: 5 branch sites / 11 terminal outcomes.

Key risk areas covered:
- floor remainder sign semantics for `x * y mod z` across sign combinations;
- strict pop/error ordering (`stkUnd` before type checks; pop order `z → y → x`);
- quiet funnels for divzero and NaN operands (`NaN` result, no throw);
- NaN/out-of-range oracle/fuzz inputs injected through program prelude only;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QMULMOD`.
-/

private def qmulmodId : InstrId := { name := "QMULMOD" }

private def qmulmodInstr : Instr := .mulDivMod 2 (-1) false true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def runQmulmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmulmodInstr stack

private def runQmulmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 4207)) stack

private def expectAssembleErr
    (label : String)
    (program : List Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

private def qmulmodSetGasExact : Int :=
  computeExactGasBudget qmulmodInstr

private def qmulmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def qmulmodDivisorBoundaryPool : Array Int :=
  #[-3, -2, -1, 1, 2, 3, maxInt257, maxInt257 - 1, minInt257, minInt257 + 1]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickQmulmodDivisorBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool qmulmodDivisorBoundaryPool rng

private def pickQmulmodDivisorMixed (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickQmulmodDivisorBoundary rng1
  else
    pickNonZeroInt rng1

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def classifyQmulmod (x y z : Int) : String :=
  if z = 0 then
    "divzero"
  else
    let (_, r) := divModRound (x * y) z (-1)
    if !intFitsSigned257 r then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQmulmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickQmulmodDivisorBoundary r3
      let kind := classifyQmulmod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-all" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickQmulmodDivisorMixed r3
      let kind := classifyQmulmod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-random" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickQmulmodDivisorMixed r3
      let kind := classifyQmulmod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/x-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickQmulmodDivisorMixed r3
      let kind := classifyQmulmod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/y-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/divzero/random" #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickQmulmodDivisorMixed r2
      (mkCase s!"/fuzz/shape-{shape}/exact/zero-x" #[intV 0, intV y, intV z], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickQmulmodDivisorMixed r2
      (mkCase s!"/fuzz/shape-{shape}/exact/zero-y" #[intV x, intV 0, intV z], r3)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, zLike], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (z, r4) := pickQmulmodDivisorMixed r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second" #[intV x, yLike, intV z], r4)
    else if shape = 12 then
      let (xLike, r2) := pickNonInt rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickQmulmodDivisorMixed r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xLike, intV y, intV z], r4)
    else if shape = 13 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-z-int"
        #[.cell Cell.empty, .null, intV 2], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num z], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num z], r4)
    else if shape = 17 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num z], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num z], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-z-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num zOut], r4)
    else if shape = 20 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        #[IntVal.num xOut, IntVal.num yOut, IntVal.num zOut], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickQmulmodDivisorMixed r3
      let kind := classifyQmulmod x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/fallback" #[intV x, intV y, intV z], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulmodId
  unit := #[
    { name := "/unit/direct/floor-sign-and-product-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 5, 3, 2),
            (-7, 5, 3, 1),
            (7, -5, 3, 1),
            (-7, -5, 3, 2),
            (7, 5, -3, -1),
            (-7, 5, -3, -2),
            (7, -5, -3, -2),
            (-7, -5, -3, -1),
            (0, 123, 7, 0),
            (123, 0, 7, 0),
            (42, 2, 7, 0),
            (-42, 2, 7, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"/unit/ok/({x}*{y})mod{z}"
                (runQmulmodDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, 0),
            (maxInt257, 1, -1, 0),
            (maxInt257, 1, 2, 1),
            (maxInt257, 1, -2, -1),
            (minInt257, 1, 1, 0),
            (minInt257, 1, -1, 0),
            (minInt257, 1, 2, 0),
            (minInt257, 1, -2, 0),
            (minInt257 + 1, 1, 2, 1),
            (minInt257 + 1, 1, -2, -1),
            (maxInt257 - 1, 1, 2, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"/unit/boundary/({x}*{y})mod{z}"
                (runQmulmodDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "/unit/direct/quiet-divzero-nan-and-overflow-funnels"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQmulmodDirect #[intV 5, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQmulmodDirect #[intV 0, intV 0, intV 0]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-z"
          (runQmulmodDirect #[intV 7, intV 5, .int .nan]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQmulmodDirect #[intV 7, .int .nan, intV 5]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQmulmodDirect #[.int .nan, intV 7, intV 5]) #[.int .nan]
        expectOkStack "/unit/quiet/overflow-remainder-out-of-range"
          (runQmulmodDirect #[intV (maxInt257 + 1), intV 1, intV (pow2 257)]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow-empty" (runQmulmodDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-one-arg" (runQmulmodDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-args" (runQmulmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow-single-non-int" (runQmulmodDirect #[.null]) .stkUnd
        expectErr "/unit/error/underflow-two-items-before-z-type" (runQmulmodDirect #[intV 1, .null]) .stkUnd
        expectErr "/unit/error/type/pop-z-first" (runQmulmodDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type/pop-y-second" (runQmulmodDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type/pop-x-third" (runQmulmodDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error/order-pop-y-before-x-when-z-int"
          (runQmulmodDirect #[.cell Cell.empty, .null, intV 2]) .typeChk
        expectErr "/unit/error/order-pop-z-before-y-when-both-non-int"
          (runQmulmodDirect #[intV 1, .cell Cell.empty, .null]) .typeChk }
    ,
    { name := "/unit/direct/pop-order-top-three-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-null"
          (runQmulmodDirect #[.null, intV 7, intV 5, intV 3]) #[.null, intV 2]
        expectOkStack "/unit/pop-order/below-cell-divzero-quiet"
          (runQmulmodDirect #[.cell Cell.empty, intV 7, intV 5, intV 0])
          #[.cell Cell.empty, .int .nan] }
    ,
    { name := "/unit/program-injection/out-of-range-pushint-rangechk"
      run := do
        expectAssembleErr "/unit/pushint/out-of-range-positive"
          [.pushInt (.num (pow2 300)), qmulmodInstr] .rangeChk
        expectAssembleErr "/unit/pushint/out-of-range-negative"
          [.pushInt (.num (-(pow2 300))), qmulmodInstr] .rangeChk }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmulmodDispatchFallback #[]) #[intV 4207] }
  ]
  oracle := #[
    mkCase "/ok/floor/sign/pos-pos-pos-divisor-inexact" #[intV 7, intV 5, intV 3],
    mkCase "/ok/floor/sign/neg-pos-pos-divisor-inexact" #[intV (-7), intV 5, intV 3],
    mkCase "/ok/floor/sign/pos-neg-pos-divisor-inexact" #[intV 7, intV (-5), intV 3],
    mkCase "/ok/floor/sign/neg-neg-pos-divisor-inexact" #[intV (-7), intV (-5), intV 3],
    mkCase "/ok/floor/sign/pos-pos-neg-divisor-inexact" #[intV 7, intV 5, intV (-3)],
    mkCase "/ok/floor/sign/neg-pos-neg-divisor-inexact" #[intV (-7), intV 5, intV (-3)],
    mkCase "/ok/floor/sign/pos-neg-neg-divisor-inexact" #[intV 7, intV (-5), intV (-3)],
    mkCase "/ok/floor/sign/neg-neg-neg-divisor-inexact" #[intV (-7), intV (-5), intV (-3)],
    mkCase "/ok/exact/zero-x" #[intV 0, intV 123, intV 7],
    mkCase "/ok/exact/zero-y" #[intV 123, intV 0, intV 7],
    mkCase "/ok/exact/zero-times-zero" #[intV 0, intV 0, intV 7],
    mkCase "/ok/boundary/max-times-one-mod-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-one-mod-neg-one" #[intV maxInt257, intV 1, intV (-1)],
    mkCase "/ok/boundary/max-times-one-mod-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "/ok/boundary/max-times-one-mod-neg-two" #[intV maxInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/min-times-one-mod-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-times-one-mod-neg-one" #[intV minInt257, intV 1, intV (-1)],
    mkCase "/ok/boundary/min-times-one-mod-two" #[intV minInt257, intV 1, intV 2],
    mkCase "/ok/boundary/min-times-one-mod-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 1, intV 2],
    mkCase "/ok/boundary/min-plus-one-mod-neg-two" #[intV (minInt257 + 1), intV 1, intV (-2)],
    mkCase "/ok/boundary/max-minus-one-mod-two" #[intV (maxInt257 - 1), intV 1, intV 2],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/error-order/single-non-int-underflow-first" #[.null],
    mkCase "/error-order/two-items-underflow-before-z-type" #[intV 1, .null],
    mkCase "/type/pop-z-first" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-y-before-x-when-z-int" #[.cell Cell.empty, .null, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCaseFromIntVals "/quiet/nan/z-via-program" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "/quiet/nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkCaseFromIntVals "/quiet/nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkCaseFromIntVals "/quiet/nan/all-via-program" #[IntVal.nan, IntVal.nan, IntVal.nan],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-before-qmulmod"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 7],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-before-qmulmod"
      #[IntVal.num (minInt257 - 1), IntVal.num 5, IntVal.num 7],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-before-qmulmod"
      #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 7],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-low-before-qmulmod"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 7],
    mkCaseFromIntVals "/error-order/pushint-overflow-z-high-before-qmulmod"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-z-low-before-qmulmod"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-all-before-qmulmod"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodSetGasExact), .tonEnvOp .setGasLimit, qmulmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulmodInstr]
  ]
  fuzz := #[
    { seed := 2026020858
      count := 700
      gen := genQmulmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULMOD
