import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLESS

/-
QLESS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.qless`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp`, `register_int_cmp_ops`, mode `0x887`, `quiet=true`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 8 branch points / 9 terminal outcomes
  (instruction/opcode dispatch gates; two-arg underflow guard; two `popInt` checks;
   quiet NaN propagation split; finite `<` mapping split).
- C++: 6 branch points / 9 aligned terminal outcomes
  (`QLESS` wiring to `exec_cmp(..., mode=0x887, quiet=true)`; underflow guard;
   two `pop_int` sites; invalid-int quiet NaN path; `<` vs `≥` finite mapping).

Key risk areas covered:
- underflow must be checked before any pop/type work (`check_underflow(2)` parity);
- error ordering from pop order (`y` then `x`);
- quiet NaN propagation must return NaN (never `intOv`);
- truth-table mapping for mode `0x887` (`< -> -1`, `=|> -> 0`);
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QLESS` (exact vs exact-minus-one);
- oracle serialization safety: NaN/out-of-range inputs are injected via program, not `initStack`.
-/

private def qlessId : InstrId := { name := "QLESS" }

private def qlessInstr : Instr := .contExt .qless

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlessInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlessId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x y : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name (below ++ stackOrEmpty) (programPrefix ++ #[qlessInstr])

private def runQlessDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qlessInstr stack

private def runQlessDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 31415)) stack

private def runQlessRaw
    (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithContExt qlessInstr (pure ())).run st0
  (res, st1.stack)

private def qlessSetGasExact : Int :=
  computeExactGasBudget qlessInstr

private def qlessSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlessInstr

private def qlessOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQlessOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qlessOutOfRangePool.size - 1)
  (qlessOutOfRangePool[idx]!, rng')

private def genQlessFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/boundary-boundary" (.num x) (.num y), r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/signed-signed" (.num x) (.num y), r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/boundary-signed" (.num x) (.num y), r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/signed-boundary" (.num x) (.num y), r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/equal" (.num x) (.num x), r2)
    else if shape = 5 then
      let (base, r2) := pickInt257Boundary rng1
      let y0 :=
        if base = maxInt257 then maxInt257
        else base + 1
      (mkInputCase s!"fuzz/shape-{shape}/ok/neighbor-lt" (.num base) (.num y0), r2)
    else if shape = 6 then
      let (base, r2) := pickInt257Boundary rng1
      let y0 :=
        if base = minInt257 then minInt257
        else base - 1
      (mkInputCase s!"fuzz/shape-{shape}/ok/neighbor-geq" (.num base) (.num y0), r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/right-zero" (.num x) (.num 0), r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/error-order/one-non-int-underflow-first" #[.null], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, .null], r2)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[.null, intV y], r2)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/nan/right-via-program" (.num x) .nan, r2)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/nan/left-via-program" .nan (.num y), r2)
    else if shape = 16 then
      (mkInputCase s!"fuzz/shape-{shape}/nan/both-via-program" .nan .nan, rng1)
    else
      let (x, r2) := pickQlessOutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"fuzz/shape-{shape}/range/pushint-before-qless" (.num x) (.num y), r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlessId
  unit := #[
    { name := "unit/direct/finite-ordering-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (1, 2, -1),
            (2, 1, 0),
            (-7, -7, 0),
            (-8, -7, -1),
            (-7, -8, 0),
            (-1, 1, -1),
            (1, -1, 0),
            (minInt257, minInt257, 0),
            (maxInt257, maxInt257, 0),
            (minInt257, maxInt257, -1),
            (maxInt257, minInt257, 0),
            (maxInt257 - 1, maxInt257, -1),
            (minInt257 + 1, minInt257, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"ok/{x}/{y}" (runQlessDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-propagates"
      run := do
        expectOkStack "nan/x" (runQlessDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y" (runQlessDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "nan/both" (runQlessDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQlessDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQlessDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-first" (runQlessDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQlessDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQlessDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQlessDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQlessDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQlessDirect #[.cell Cell.empty, .null]) .typeChk
        expectOkStack "error-order/top-two-only-lower-preserved"
          (runQlessDirect #[.null, intV (-8), intV 7]) #[.null, intV (-1)] }
    ,
    { name := "unit/regression/singleton-underflow-does-not-pop"
      run := do
        let (r1, s1) := runQlessRaw #[intV 9]
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
        let (r2, s2) := runQlessRaw #[.null]
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
    { name := "unit/dispatch/non-qless-falls-through"
      run := do
        expectOkStack "dispatch/non-contExt" (runQlessDispatchFallback .add #[]) #[intV 31415]
        expectOkStack "dispatch/other-contExt"
          (runQlessDispatchFallback (.contExt .condSel) #[]) #[intV 31415] }
  ]
  oracle := #[
    mkInputCase "ok/order/zero-eq-zero" (.num 0) (.num 0),
    mkInputCase "ok/order/pos-lt-pos" (.num 1) (.num 2),
    mkInputCase "ok/order/pos-gt-pos" (.num 2) (.num 1),
    mkInputCase "ok/order/neg-eq-neg" (.num (-7)) (.num (-7)),
    mkInputCase "ok/order/neg-lt-neg" (.num (-8)) (.num (-7)),
    mkInputCase "ok/order/neg-gt-neg" (.num (-7)) (.num (-8)),
    mkInputCase "ok/order/neg-lt-pos" (.num (-1)) (.num 1),
    mkInputCase "ok/order/pos-gt-neg" (.num 1) (.num (-1)),
    mkInputCase "ok/edge/min-eq-min" (.num minInt257) (.num minInt257),
    mkInputCase "ok/edge/max-eq-max" (.num maxInt257) (.num maxInt257),
    mkInputCase "ok/edge/min-lt-max" (.num minInt257) (.num maxInt257),
    mkInputCase "ok/edge/max-gt-min" (.num maxInt257) (.num minInt257),
    mkInputCase "ok/edge/max-minus-one-lt-max" (.num (maxInt257 - 1)) (.num maxInt257),
    mkInputCase "ok/edge/min-plus-one-gt-min" (.num (minInt257 + 1)) (.num minInt257),
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkInputCase "nan/right-via-program" (.num 42) .nan,
    mkInputCase "nan/left-via-program" .nan (.num 42),
    mkInputCase "nan/both-via-program" .nan .nan,
    mkInputCase "range/high-via-program-before-qless" (.num (maxInt257 + 1)) (.num 7),
    mkInputCase "range/low-via-program-before-qless" (.num (minInt257 - 1)) (.num 7),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qlessSetGasExact), .tonEnvOp .setGasLimit, qlessInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qlessSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlessInstr]
  ]
  fuzz := #[
    { seed := 2026020823
      count := 600
      gen := genQlessFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLESS
