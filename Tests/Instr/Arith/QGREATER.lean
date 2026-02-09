import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QGREATER

/-
QGREATER branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qgreater` arm in `execInstrArithContExt`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.checkUnderflow`, `VM.popInt`, `VM.pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7bc -> .contExt .qgreater`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp`, `register_int_cmp_ops` wiring for `QGREATER` mode `0x788`, quiet=true)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Lean-vs-C++ terminal mapping used for this suite:
- Lean: 9 terminal outcomes
  (non-`contExt` fallback; non-`qgreater` fallback; `stkUnd`;
   `typeChk` on `y`; `typeChk` on `x`; quiet-NaN success;
   finite `x > y` success; finite `x ≤ y` success; out-of-gas).
- C++: 9 aligned outcomes
  (`QGREATER` opcode registration to `exec_cmp(..., mode=0x788, quiet=true)`;
   explicit `check_underflow(2)`; two `pop_int` type checks;
   invalid-int quiet propagation; compare result-class mapping by mode).

Key risk areas covered:
- underflow must be checked before any pop (`#[.null]` must be `stkUnd`);
- pop order is `y` first then `x`, so type-check ordering must follow;
- quiet NaN propagation must return NaN (not `intOv`);
- comparator mapping must be TVM-boolean (`-1` for true, `0` for false);
- exact gas threshold for `PUSHINT n; SETGASLIMIT; QGREATER`.
-/

private def qgreaterId : InstrId := { name := "QGREATER" }

private def qgreaterInstr : Instr := .contExt .qgreater

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qgreaterInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qgreaterId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qgreaterInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programSuffix) gasLimits fuel

private def runQgreaterDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qgreaterInstr stack

private def runQgreaterDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 27182)) stack

private def runQgreaterRaw
    (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithContExt qgreaterInstr (pure ())).run st0
  (res, st1.stack)

private def qgreaterSetGasExact : Int :=
  computeExactGasBudget qgreaterInstr

private def qgreaterSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qgreaterInstr

private def genQgreaterFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-random" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-equal" #[intV x, intV x], r2)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (dir, r3) := randNat r2 0 1
      let y :=
        if x = minInt257 then minInt257 + 1
        else if x = maxInt257 then maxInt257 - 1
        else if dir = 0 then x - 1 else x + 1
      (mkCase s!"fuzz/shape-{shape}/ok-neighbor" #[intV x, intV y], r3)
    else if shape = 4 then
      let (flip, r2) := randBool rng1
      let x := if flip then maxInt257 else minInt257
      let y := if flip then minInt257 else maxInt257
      (mkCase s!"fuzz/shape-{shape}/ok-minmax-cross" #[intV x, intV y], r2)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/error-order-one-non-int-underflow-first" #[.null], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-first" #[intV x, .null], r2)
    else if shape = 9 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-second" #[.null, intV y], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-right-via-program" #[.num x, .nan], r2)
    else
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-left-via-program" #[.nan, .num y], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qgreaterId
  unit := #[
    { name := "unit/direct/finite-ordering-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (2, 1, -1),
            (1, 2, 0),
            (-7, -7, 0),
            (-7, -8, -1),
            (-8, -7, 0),
            (1, -1, -1),
            (-1, 1, 0),
            (minInt257, minInt257, 0),
            (maxInt257, maxInt257, 0),
            (minInt257, maxInt257, 0),
            (maxInt257, minInt257, -1),
            (maxInt257 - 1, maxInt257, 0),
            (minInt257 + 1, minInt257, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>{y}" (runQgreaterDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-propagates"
      run := do
        expectOkStack "nan/x" (runQgreaterDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y" (runQgreaterDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "nan/both" (runQgreaterDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQgreaterDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQgreaterDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQgreaterDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQgreaterDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQgreaterDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQgreaterDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQgreaterDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQgreaterDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/regression/underflow-singleton-does-not-pop"
      run := do
        let (r1, s1) := runQgreaterRaw #[intV 9]
        match r1 with
        | .error .stkUnd =>
            if s1 == #[intV 9] then
              pure ()
            else
              throw (IO.userError s!"singleton-int stack mutated on underflow: got {reprStr s1}")
        | .error e =>
            throw (IO.userError s!"singleton-int expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "singleton-int expected stkUnd, got success")
        let (r2, s2) := runQgreaterRaw #[.null]
        match r2 with
        | .error .stkUnd =>
            if s2 == #[.null] then
              pure ()
            else
              throw (IO.userError s!"singleton-non-int stack mutated on underflow: got {reprStr s2}")
        | .error e =>
            throw (IO.userError s!"singleton-non-int expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "singleton-non-int expected stkUnd, got success") }
    ,
    { name := "unit/dispatch/non-qgreater-falls-through"
      run := do
        expectOkStack "dispatch/non-contExt" (runQgreaterDispatchFallback .add #[]) #[intV 27182]
        expectOkStack "dispatch/other-contExt" (runQgreaterDispatchFallback (.contExt .condSel) #[]) #[intV 27182] }
  ]
  oracle := #[
    mkCase "ok/order/zero-eq-zero" #[intV 0, intV 0],
    mkCase "ok/order/pos-gt-pos" #[intV 2, intV 1],
    mkCase "ok/order/pos-lt-pos" #[intV 1, intV 2],
    mkCase "ok/order/neg-eq-neg" #[intV (-7), intV (-7)],
    mkCase "ok/order/neg-gt-neg" #[intV (-7), intV (-8)],
    mkCase "ok/order/neg-lt-neg" #[intV (-8), intV (-7)],
    mkCase "ok/order/pos-gt-neg" #[intV 1, intV (-1)],
    mkCase "ok/order/neg-lt-pos" #[intV (-1), intV 1],
    mkCase "ok/edge/min-eq-min" #[intV minInt257, intV minInt257],
    mkCase "ok/edge/max-eq-max" #[intV maxInt257, intV maxInt257],
    mkCase "ok/edge/min-lt-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/edge/max-gt-min" #[intV maxInt257, intV minInt257],
    mkCase "ok/edge/max-minus-one-lt-max" #[intV (maxInt257 - 1), intV maxInt257],
    mkCase "ok/edge/min-plus-one-gt-min" #[intV (minInt257 + 1), intV minInt257],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-before-type" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "nan/right-via-program" #[.num 42, .nan],
    mkCaseFromIntVals "nan/left-via-program" #[.nan, .num 42],
    mkCaseFromIntVals "nan/both-via-program" #[.nan, .nan],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qgreaterSetGasExact), .tonEnvOp .setGasLimit, qgreaterInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qgreaterSetGasExactMinusOne), .tonEnvOp .setGasLimit, qgreaterInstr]
  ]
  fuzz := #[
    { seed := 2026020821
      count := 600
      gen := genQgreaterFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QGREATER
