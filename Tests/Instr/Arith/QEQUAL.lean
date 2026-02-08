import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QEQUAL

/-
QEQUAL branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qequal` in `execInstrArithContExt`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7ba -> .contExt .qequal`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp`, `register_int_cmp_ops` wiring for `QEQUAL`, mode `0x878`, quiet=true)

Branch map used for this suite:
- Lean: 8 branch points / 10 terminal outcomes
  (dispatch to `.contExt`; dispatch to `.qequal`; explicit underflow check;
   `popInt` type checks at `y` then `x`; NaN-vs-finite split; finite `a=b` true/false;
   quiet push path including NaN and out-of-range encoded inputs).
- C++: 7 branch points / 10 aligned outcomes
  (`QEQUAL` registration to `exec_cmp(..., 0x878, true)`; `check_underflow(2)`;
   `pop_int` type checks (`y` then `x`); invalid-int path returns quiet NaN;
   compare class `{<,=,>}` mapped to `{0,-1,0}`).

Key risk areas covered:
- quiet NaN propagation for QEQUAL (must succeed with NaN, never throw `intOv`);
- underflow-before-type ordering on short stacks (especially singleton non-int);
- operand pop order (`y` first, then `x`) and corresponding type-check site;
- equality truth table for mode `0x878` (`-1` iff equal, else `0`);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QEQUAL`.
-/

private def qequalId : InstrId := { name := "QEQUAL" }

private def qequalInstr : Instr := .contExt .qequal

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qequalInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qequalId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qequalInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (programPrefix ++ programSuffix) gasLimits fuel

private def runQequalDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qequalInstr stack

private def runQequalDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 606)) stack

private def runQequalRaw
    (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithContExt qequalInstr (pure ())).run st0
  (res, st1.stack)

private def qequalSetGasExact : Int :=
  computeExactGasBudget qequalInstr

private def qequalSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qequalInstr

private def qequalOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQequalOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qequalOutOfRangePool.size - 1)
  (qequalOutOfRangePool[idx]!, rng')

private def genQequalFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-random" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-boundary" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-random" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-boundary" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-forced-equality" #[intV x, intV x], r2)
    else if shape = 5 then
      let (base, r2) := pickInt257Boundary rng1
      let (dir, r3) := randNat r2 0 1
      let y :=
        if base = minInt257 then minInt257 + 1
        else if base = maxInt257 then maxInt257 - 1
        else if dir = 0 then base - 1 else base + 1
      (mkCase s!"fuzz/shape-{shape}/ok-near-boundary-ne" #[intV base, intV y], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow-one-non-int" #[.null], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-first-null" #[intV x, .null], r2)
    else if shape = 10 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-second-null" #[.null, intV y], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-first-cell" #[intV x, .cell Cell.empty], r2)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-second-cell" #[.cell Cell.empty, intV y], r2)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/error-order-both-non-int-pop-y-first" #[.cell Cell.empty, .null], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-right-via-program" #[.num x, .nan], r2)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-left-via-program" #[.nan, .num y], r2)
    else if shape = 16 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-both-via-program" #[.nan, .nan], rng1)
    else if shape = 17 then
      let (x, r2) := pickQequalOutOfRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-high-before-qequal" #[.num x, .num 7], r2)
    else
      let (x, r2) := pickQequalOutOfRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-low-before-qequal" #[.num x, .num (-7)], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qequalId
  unit := #[
    { name := "unit/direct/finite-equality-sign-and-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, -1),
            (1, 1, -1),
            (1, 2, 0),
            (-7, -7, -1),
            (-7, -8, 0),
            (-1, 1, 0),
            (1, -1, 0),
            (minInt257, minInt257, -1),
            (maxInt257, maxInt257, -1),
            (minInt257, maxInt257, 0),
            (maxInt257, minInt257, 0),
            (maxInt257 - 1, maxInt257, 0),
            (minInt257 + 1, minInt257, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} qequal {y}" (runQequalDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQequalDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQequalDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQequalDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQequalDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQequalDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQequalDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQequalDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQequalDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/regression/singleton-underflow-does-not-pop"
      run := do
        let (rInt, sInt) := runQequalRaw #[intV 9]
        match rInt with
        | .error .stkUnd =>
            if sInt == #[intV 9] then
              pure ()
            else
              throw (IO.userError s!"singleton-int stack mutated on underflow: got {reprStr sInt}")
        | .error e =>
            throw (IO.userError s!"singleton-int expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "singleton-int expected stkUnd, got success")

        let (rNonInt, sNonInt) := runQequalRaw #[.null]
        match rNonInt with
        | .error .stkUnd =>
            if sNonInt == #[.null] then
              pure ()
            else
              throw (IO.userError s!"singleton-non-int stack mutated on underflow: got {reprStr sNonInt}")
        | .error e =>
            throw (IO.userError s!"singleton-non-int expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "singleton-non-int expected stkUnd, got success") }
    ,
    { name := "unit/dispatch/non-qequal-falls-through"
      run := do
        expectOkStack "dispatch/non-contExt" (runQequalDispatchFallback .add #[]) #[intV 606]
        expectOkStack "dispatch/other-contExt" (runQequalDispatchFallback (.contExt .condSel) #[]) #[intV 606] }
  ]
  oracle := #[
    mkCase "ok/equal/zero-eq-zero" #[intV 0, intV 0],
    mkCase "ok/equal/pos-eq-pos" #[intV 17, intV 17],
    mkCase "ok/equal/neg-eq-neg" #[intV (-17), intV (-17)],
    mkCase "ok/not-equal/pos-ne-pos" #[intV 17, intV 25],
    mkCase "ok/not-equal/neg-ne-neg" #[intV (-17), intV (-25)],
    mkCase "ok/not-equal/neg-ne-pos" #[intV (-1), intV 1],
    mkCase "ok/not-equal/pos-ne-neg" #[intV 1, intV (-1)],
    mkCase "ok/edge/min-eq-min" #[intV minInt257, intV minInt257],
    mkCase "ok/edge/max-eq-max" #[intV maxInt257, intV maxInt257],
    mkCase "ok/edge/min-ne-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/edge/max-ne-min" #[intV maxInt257, intV minInt257],
    mkCase "ok/edge/max-minus-one-ne-max" #[intV (maxInt257 - 1), intV maxInt257],
    mkCase "ok/edge/min-plus-one-ne-min" #[intV (minInt257 + 1), intV minInt257],
    mkCase "underflow/empty" #[],
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
    mkCaseFromIntVals "error-order/pushint-range-high-before-qequal" #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-low-before-qequal" #[.num (minInt257 - 1), .num 7],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qequalSetGasExact), .tonEnvOp .setGasLimit, qequalInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qequalSetGasExactMinusOne), .tonEnvOp .setGasLimit, qequalInstr]
  ]
  fuzz := #[
    { seed := 2026020819
      count := 600
      gen := genQequalFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QEQUAL
