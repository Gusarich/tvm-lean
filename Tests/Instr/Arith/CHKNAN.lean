import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.CHKNAN

/-
CHKNAN branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.chknan` arm)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (program-side NaN / range handling)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_chk_nan`, opcode wiring in `register_int_cmp_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::pop_int`, `Stack::push_int`)

Branch map used by this suite:
- Lean: 4 branch points / 6 terminal outcomes
  (instruction dispatch; `.contExt` op dispatch; `popInt` underflow/type/success;
   non-quiet checked push path: success vs `intOv` on NaN/out-of-range).
- C++: 4 branch points / 6 aligned terminal outcomes
  (opcode registration to `exec_chk_nan`; `check_underflow(1)` pass/fail;
   `pop_int` type check; `push_int` signed-257 check).

Key risk areas:
- CHKNAN must throw `intOv` for NaN (not pass NaN through).
- Unary error ordering: underflow precedes type-check.
- Top-of-stack only behavior (lower stack values, including NaN, remain untouched).
- Out-of-range integers must be injected via program; `PUSHINT` should fail before CHKNAN.
- Exact gas boundary for `PUSHINT n; SETGASLIMIT; CHKNAN`.
-/

private def chknanId : InstrId := { name := "CHKNAN" }

private def chknanInstr : Instr := .contExt .chknan

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[chknanInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := chknanId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runChknanDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt chknanInstr stack

private def runChknanDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt .add (VM.push (intV 777)) stack

private def chknanSetGasExact : Int :=
  computeExactGasBudget chknanInstr

private def chknanSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne chknanInstr

private def genChknanFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/ok/signed-{tag}" #[intV x], rng3)
  else if shape = 1 then
    let (x, rng3) := pickInt257Boundary rng2
    (mkCase s!"fuzz/ok/boundary-{tag}" #[intV x], rng3)
  else if shape = 2 then
    let (which, rng3) := randNat rng2 0 3
    let x : Int :=
      if which = 0 then maxInt257
      else if which = 1 then maxInt257 - 1
      else if which = 2 then minInt257
      else minInt257 + 1
    (mkCase s!"fuzz/ok/near-boundary-{tag}" #[intV x], rng3)
  else if shape = 3 then
    (mkCase s!"fuzz/overflow/nan-top-via-program-{tag}" #[] #[.pushInt .nan, chknanInstr], rng2)
  else if shape = 4 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/ok/top-only-nan-below-{tag}" #[intV x] #[.pushInt .nan, .xchg0 1, chknanInstr], rng3)
  else if shape = 5 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/type/top-null-{tag}" #[intV x, .null], rng3)
  else if shape = 6 then
    (mkCase s!"fuzz/underflow/empty-{tag}" #[], rng2)
  else if shape = 7 then
    (mkCase s!"fuzz/error-order/type-before-nan-below-{tag}" #[.null]
      #[.pushInt .nan, .xchg0 1, chknanInstr], rng2)
  else
    (mkCase s!"fuzz/error-order/pushint-overflow-before-op-{tag}" #[]
      #[.pushInt (.num (maxInt257 + 1)), chknanInstr], rng2)

def suite : InstrSuite where
  id := chknanId
  unit := #[
    { name := "unit/direct/pass-through-finite-and-boundary"
      run := do
        let checks : Array Int :=
          #[
            0, 1, -1, pow2 200, -(pow2 200),
            minInt257, minInt257 + 1, maxInt257 - 1, maxInt257
          ]
        for x in checks do
          expectOkStack s!"chknan({x})" (runChknanDirect #[intV x]) #[intV x]
        expectOkStack "top-only-with-tail" (runChknanDirect #[intV 7, intV (-3)]) #[intV 7, intV (-3)] }
    ,
    { name := "unit/direct/nan-throws-intov"
      run := do
        expectErr "chknan(nan)" (runChknanDirect #[.int .nan]) .intOv }
    ,
    { name := "unit/direct/underflow-type-and-error-ordering"
      run := do
        expectErr "empty-underflow" (runChknanDirect #[]) .stkUnd
        expectErr "top-null-type" (runChknanDirect #[.null]) .typeChk
        expectErr "top-cell-type" (runChknanDirect #[.cell Cell.empty]) .typeChk
        expectErr "type-before-nan-below" (runChknanDirect #[.int .nan, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-contExt-falls-through"
      run := do
        expectOkStack "fallback-next" (runChknanDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/positive-small" #[intV 37],
    mkCase "ok/negative-small" #[intV (-37)],
    mkCase "ok/top-only-with-tail" #[intV 7, intV (-3)],
    mkCase "ok/top-only-nan-below" #[intV 5] #[.pushInt .nan, .xchg0 1, chknanInstr],
    mkCase "boundary/min" #[intV minInt257],
    mkCase "boundary/min-plus-one" #[intV (minInt257 + 1)],
    mkCase "boundary/max-minus-one" #[intV (maxInt257 - 1)],
    mkCase "boundary/max" #[intV maxInt257],
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/type-before-intov-nan-below" #[.null]
      #[.pushInt .nan, .xchg0 1, chknanInstr],
    mkCase "overflow/nan-via-program-intov" #[] #[.pushInt .nan, chknanInstr],
    mkCase "error-order/pushint-overflow-before-chknan" #[]
      #[.pushInt (.num (maxInt257 + 1)), chknanInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num chknanSetGasExact), .tonEnvOp .setGasLimit, chknanInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num chknanSetGasExactMinusOne), .tonEnvOp .setGasLimit, chknanInstr]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 600
      gen := genChknanFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.CHKNAN
