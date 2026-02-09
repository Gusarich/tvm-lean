import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ISNAN

/-
ISNAN branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.isnan`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushSmallInt`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_is_nan`, opcode wiring in `register_int_cmp_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_int`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.hpp` (`check_underflow`)

Branch counts used for this suite:
- Lean: 5 branch points / 6 terminal outcomes
  (dispatch to `.contExt`; dispatch to `.isnan`; `popInt` underflow/type/success;
   validity split to `0` vs `-1`).
- C++: 4 branch points / 6 aligned terminal outcomes
  (`ISNAN` opcode registration; underflow guard; `pop_int` type check;
   `is_valid()` split to `0` vs `-1`).

Key risk areas:
- validity classification for NaN and out-of-range integers injected via `PUSHINT`;
- unary top-of-stack behavior (top consumed, lower stack preserved);
- error ordering (`stkUnd` on empty stack before any type check);
- deterministic gas cliffs for `PUSHINT n; SETGASLIMIT; ISNAN`.
-/

private def isnanId : InstrId := { name := "ISNAN" }

private def isnanInstr : Instr := .contExt .isnan

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[isnanInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := isnanId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (progPrefix.push isnanInstr)

private def runIsNanDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt isnanInstr stack

private def runIsNanDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 31337)) stack

private def isnanSetGasExact : Int :=
  computeExactGasBudget isnanInstr

private def isnanSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne isnanInstr

private def isnanOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickIsNanOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (isnanOutOfRangePool.size - 1)
  (isnanOutOfRangePool[idx]!, rng')

private def pickIsNanNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genIsNanFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, rng3) := pickInt257Boundary rng2
    (mkInputCase s!"fuzz/ok/boundary-{tag}" (.num x), rng3)
  else if shape = 1 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/random-{tag}" (.num x), rng3)
  else if shape = 2 then
    let (x, rng3) := pickIsNanOutOfRange rng2
    (mkInputCase s!"fuzz/range/out-of-range-via-program-{tag}" (.num x), rng3)
  else if shape = 3 then
    let (below, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/nan/pushnan-over-int-{tag}" .nan #[intV below], rng3)
  else if shape = 4 then
    (mkCase s!"fuzz/underflow/empty-{tag}" #[], rng2)
  else if shape = 5 then
    let (below, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/type/top-null-{tag}" #[intV below, .null], rng3)
  else if shape = 6 then
    let (below, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/type/top-cell-{tag}" #[intV below, .cell Cell.empty], rng3)
  else if shape = 7 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/error-order/top-int-below-non-int-{tag}" (.num x) #[.null], rng3)
  else if shape = 8 then
    let (v, rng3) := pickIsNanNonInt rng2
    (mkCase s!"fuzz/error-order/non-empty-type-check-{tag}" #[v], rng3)
  else
    let (x, rng3) := pickSigned257ish rng2
    let (v, rng4) := pickIsNanNonInt rng3
    (mkInputCase s!"fuzz/ok/top-int-below-non-int-{tag}" (.num x) #[v], rng4)

def suite : InstrSuite where
  id := isnanId
  unit := #[
    { name := "unit/ok/finite-values-map-to-zero"
      run := do
        let checks : Array Int :=
          #[
            0,
            1,
            -1,
            17,
            -17,
            pow2 200,
            -(pow2 200),
            minInt257,
            maxInt257
          ]
        for x in checks do
          expectOkStack s!"isnan({x})" (runIsNanDirect #[intV x]) #[intV 0] }
    ,
    { name := "unit/error-order/underflow-before-type"
      run := do
        expectErr "empty-underflow" (runIsNanDirect #[]) .stkUnd
        expectErr "top-null" (runIsNanDirect #[.null]) .typeChk
        expectErr "top-cell" (runIsNanDirect #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-with-below-int" (runIsNanDirect #[intV 9, .null]) .typeChk }
    ,
    { name := "unit/ok/top-only-consumed-below-preserved"
      run := do
        expectOkStack "below-null" (runIsNanDirect #[.null, intV 9]) #[.null, intV 0]
        expectOkStack "below-cell" (runIsNanDirect #[.cell Cell.empty, intV (-9)]) #[.cell Cell.empty, intV 0] }
    ,
    { name := "unit/dispatch/non-isnan-falls-through"
      run := do
        expectOkStack "fallback/non-contExt" (runIsNanDispatchFallback .add #[]) #[intV 31337]
        expectOkStack "fallback/other-contExt" (runIsNanDispatchFallback (.contExt .condSel) #[]) #[intV 31337] }
  ]
  oracle := #[
    mkInputCase "ok/finite/zero" (.num 0),
    mkInputCase "ok/finite/positive" (.num 17),
    mkInputCase "ok/finite/negative" (.num (-17)),
    mkInputCase "ok/boundary/min-int257" (.num minInt257),
    mkInputCase "ok/boundary/max-int257" (.num maxInt257),
    mkInputCase "ok/stack/top-int-below-null" (.num 7) #[.null],
    mkInputCase "ok/stack/top-int-below-cell" (.num (-7)) #[.cell Cell.empty],
    mkInputCase "range/out-of-range-via-program/positive" (.num (maxInt257 + 1)),
    mkInputCase "range/out-of-range-via-program/negative" (.num (minInt257 - 1)),
    mkInputCase "range/out-of-range-via-program/pow2-257" (.num (pow2 257)),
    mkInputCase "nan/pushnan-empty" .nan,
    mkInputCase "nan/pushnan-over-int" .nan #[intV 42],
    mkInputCase "nan/pushnan-over-null" .nan #[.null],
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "type/top-null-with-below-int" #[intV 1, .null],
    mkCase "error-order/empty-underflow-before-type" #[],
    mkCase "error-order/non-empty-type-check" #[.cell Cell.empty],
    mkCase "gas/exact-cost-succeeds" #[intV 5]
      #[.pushInt (.num isnanSetGasExact), .tonEnvOp .setGasLimit, isnanInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 5]
      #[.pushInt (.num isnanSetGasExactMinusOne), .tonEnvOp .setGasLimit, isnanInstr]
  ]
  fuzz := #[
    { seed := 2026020806
      count := 500
      gen := genIsNanFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ISNAN
