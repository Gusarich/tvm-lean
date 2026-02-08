import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QCMP

/-
QCMP branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Cmp.lean` (`execInstrArithCmp`, `.qcmp`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp`, `register_int_cmp_ops` mapping `QCMP -> mode 0x987, quiet=true`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch map used for this suite:
- Lean: 8 branch points / 10 terminal outcomes
  (instruction dispatch; `checkUnderflow 2`; two `popInt` checks; quiet NaN path;
   finite compare split `{<,=,>}` mapped to `{-1,0,1}`).
- C++: 6 branch points / 10 aligned terminal outcomes
  (`QCMP` opcode registration to `exec_cmp(..., quiet=true)`; underflow guard;
   two `pop_int` checks; invalid-int quiet NaN propagation; compare-class mapping).

Key risk areas covered:
- quiet NaN propagation must succeed with top `NaN` (never throw `intOv`);
- underflow must win over type checks for arity < 2;
- pop order (`y` then `x`) governs error ordering;
- signed ordering at `[-2^256, 2^256-1]` boundaries;
- deterministic gas threshold for `PUSHINT n; SETGASLIMIT; QCMP`;
- oracle safety: NaN/out-of-range int inputs are encoded via program, not `initStack`.
-/

private def qcmpId : InstrId := { name := "QCMP" }

private def qcmpInstr : Instr := .qcmp

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qcmpInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qcmpId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qcmpInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (programPrefix ++ programSuffix) gasLimits fuel

private def runQcmpDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithCmp qcmpInstr stack

private def runQcmpDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithCmp .add (VM.push (intV 987)) stack

private def runQcmpRaw (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithCmp qcmpInstr (pure ())).run st0
  (res, st1.stack)

private def qcmpSetGasExact : Int :=
  computeExactGasBudget qcmpInstr

private def qcmpSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qcmpInstr

private def qcmpOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQcmpOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qcmpOutOfRangePool.size - 1)
  (qcmpOutOfRangePool[idx]!, rng')

private def genQcmpFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-boundary" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/signed-signed" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-signed" #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/signed-boundary" #[intV x, intV y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/equal" #[intV x, intV x], r2)
    else if shape = 5 then
      let (base, r2) := pickInt257Boundary rng1
      let y :=
        if base = maxInt257 then maxInt257
        else base + 1
      (mkCase s!"fuzz/shape-{shape}/ok/neighbor-lt" #[intV base, intV y], r2)
    else if shape = 6 then
      let (base, r2) := pickInt257Boundary rng1
      let y :=
        if base = minInt257 then minInt257
        else base - 1
      (mkCase s!"fuzz/shape-{shape}/ok/neighbor-gt" #[intV base, intV y], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/right-zero" #[intV x, intV 0], r2)
    else if shape = 8 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok/left-zero" #[intV 0, intV y], r2)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-first" #[.null], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, .null], r2)
    else if shape = 13 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[.null, intV y], r2)
    else if shape = 14 then
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null], rng1)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/right-via-program" #[.num x, .nan], r2)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/left-via-program" #[.nan, .num y], r2)
    else if shape = 17 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/both-via-program" #[.nan, .nan], rng1)
    else if shape = 18 then
      let (x, r2) := pickQcmpOutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/high-before-qcmp" #[.num x, .num y], r3)
    else
      let (x, r2) := pickQcmpOutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/low-before-qcmp" #[.num y, .num x], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qcmpId
  unit := #[
    { name := "unit/direct/finite-ordering-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (1, 2, -1),
            (2, 1, 1),
            (-7, -7, 0),
            (-8, -7, -1),
            (-7, -8, 1),
            (-1, 1, -1),
            (1, -1, 1),
            (minInt257, minInt257, 0),
            (maxInt257, maxInt257, 0),
            (minInt257, maxInt257, -1),
            (maxInt257, minInt257, 1),
            (maxInt257 - 1, maxInt257, -1),
            (minInt257 + 1, minInt257, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"qcmp/{x}/{y}" (runQcmpDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-propagates"
      run := do
        expectOkStack "nan/x" (runQcmpDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y" (runQcmpDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "nan/both" (runQcmpDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQcmpDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQcmpDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-first" (runQcmpDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQcmpDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQcmpDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQcmpDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQcmpDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQcmpDirect #[.cell Cell.empty, .null]) .typeChk
        expectOkStack "error-order/top-two-only-lower-preserved"
          (runQcmpDirect #[.null, intV (-8), intV 7]) #[.null, intV (-1)] }
    ,
    { name := "unit/regression/singleton-underflow-does-not-pop"
      run := do
        let (r1, s1) := runQcmpRaw #[intV 9]
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
        let (r2, s2) := runQcmpRaw #[.null]
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
    { name := "unit/dispatch/non-qcmp-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQcmpDispatchFallback #[]) #[intV 987] }
  ]
  oracle := #[
    mkCase "ok/order/zero-eq-zero" #[intV 0, intV 0],
    mkCase "ok/order/pos-lt-pos" #[intV 1, intV 2],
    mkCase "ok/order/pos-gt-pos" #[intV 2, intV 1],
    mkCase "ok/order/neg-eq-neg" #[intV (-7), intV (-7)],
    mkCase "ok/order/neg-lt-neg" #[intV (-8), intV (-7)],
    mkCase "ok/order/neg-gt-neg" #[intV (-7), intV (-8)],
    mkCase "ok/order/neg-lt-pos" #[intV (-1), intV 1],
    mkCase "ok/order/pos-gt-neg" #[intV 1, intV (-1)],
    mkCase "ok/edge/min-eq-min" #[intV minInt257, intV minInt257],
    mkCase "ok/edge/max-eq-max" #[intV maxInt257, intV maxInt257],
    mkCase "ok/edge/min-lt-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/edge/max-gt-min" #[intV maxInt257, intV minInt257],
    mkCase "ok/edge/max-minus-one-lt-max" #[intV (maxInt257 - 1), intV maxInt257],
    mkCase "ok/edge/min-plus-one-gt-min" #[intV (minInt257 + 1), intV minInt257],
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCaseFromIntVals "nan/right-via-program" #[.num 42, .nan],
    mkCaseFromIntVals "nan/left-via-program" #[.nan, .num 42],
    mkCaseFromIntVals "nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "range/high-via-program-before-qcmp" #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "range/low-via-program-before-qcmp" #[.num (minInt257 - 1), .num 7],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qcmpSetGasExact), .tonEnvOp .setGasLimit, qcmpInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qcmpSetGasExactMinusOne), .tonEnvOp .setGasLimit, qcmpInstr]
  ]
  fuzz := #[
    { seed := 2026020827
      count := 600
      gen := genQcmpFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QCMP
