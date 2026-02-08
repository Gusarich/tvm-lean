import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QAND

/-
QAND branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qand` arm in `execInstrArithContExt`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7b0 -> .contExt .qand`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_and`, `register_shift_logic_ops` wiring for `QAND`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Lean-vs-C++ terminal mapping used for this suite:
- Lean: 8 terminal outcomes
  (non-`contExt` fallback; non-`qand` fallback; `stkUnd`; `typeChk` on `y`;
   `typeChk` on `x`; quiet-NaN success; finite success; out-of-range direct-int guard path).
- C++: 8 aligned outcomes
  (`QAND` opcode registration to `exec_and(..., quiet=true)`; underflow guard;
   two `pop_int` type-check sites; invalid->NaN quiet path; finite path;
   `push_int_quiet` quiet handling for non-finite/out-of-range representations).

Key risk areas covered:
- regression fixed here: underflow must be checked before any pop (singleton `.null` => `stkUnd`);
- pop order (`y` then `x`) controls type-check ordering;
- quiet NaN propagation must succeed and keep NaN;
- 257-bit two's-complement behavior near `minInt257`/`maxInt257` and high-bit patterns;
- gas boundary precision for `PUSHINT n; SETGASLIMIT; QAND` (exact vs exact-minus-one).
-/

private def qandId : InstrId := { name := "QAND" }

private def qandInstr : Instr := .contExt .qand

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qandInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qandId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qandInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programSuffix) gasLimits fuel

private def runQandDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qandInstr stack

private def runQandDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 27182)) stack

private def runQandRaw
    (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithContExt qandInstr (pure ())).run st0
  (res, st1.stack)

private def qandSetGasExact : Int :=
  computeExactGasBudget qandInstr

private def qandSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qandInstr

private def qandOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQandOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qandOutOfRangePool.size - 1)
  (qandOutOfRangePool[idx]!, rng')

private def genQandFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
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
      (mkCase s!"fuzz/shape-{shape}/ok-right-zero" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-right-neg-one" #[intV x, intV (-1)], r2)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-high-bit-mask" #[intV x, intV (pow2 255)], r2)
    else if shape = 5 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-min-mask" #[intV x, intV minInt257], r2)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/error-order-one-non-int-underflow-first" #[.null], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-first" #[intV x, .null], r2)
    else if shape = 10 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-second" #[.null, intV y], r2)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/error-order-both-non-int-pop-y-first" #[.cell Cell.empty, .null], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-right-via-program" #[.num x, .nan], r2)
    else if shape = 13 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-left-via-program" #[.nan, .num y], r2)
    else if shape = 14 then
      let (x, r2) := pickQandOutOfRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-high-before-qand" #[.num x, .num 1], r2)
    else
      let (x, r2) := pickQandOutOfRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-low-before-qand" #[.num x, .num (-1)], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qandId
  unit := #[
    { name := "unit/direct/finite-identities-and-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 0, 0),
            (0, 7, 0),
            (7, -1, 7),
            (-7, -1, -7),
            (-5, 3, 3),
            (-7, -3, -7),
            (maxInt257, -1, maxInt257),
            (minInt257, -1, minInt257),
            (minInt257, maxInt257, 0),
            (pow2 255, pow2 254, 0),
            (maxInt257, pow2 255, pow2 255),
            (minInt257, pow2 255, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} qand {y}" (runQandDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-propagates"
      run := do
        expectOkStack "nan/x" (runQandDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y" (runQandDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "nan/both" (runQandDirect #[.int .nan, .int .nan]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQandDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQandDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-non-int-underflow-before-type" (runQandDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQandDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQandDirect #[.null, intV 1]) .typeChk
        expectErr "type/pop-y-first-cell" (runQandDirect #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-cell" (runQandDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first" (runQandDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/regression/underflow-singleton-does-not-pop"
      run := do
        let (r1, s1) := runQandRaw #[intV 9]
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
        let (r2, s2) := runQandRaw #[.null]
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
    { name := "unit/dispatch/non-qand-falls-through"
      run := do
        expectOkStack "dispatch/non-contExt" (runQandDispatchFallback .add #[]) #[intV 27182]
        expectOkStack "dispatch/other-contExt" (runQandDispatchFallback (.contExt .condSel) #[]) #[intV 27182] }
  ]
  oracle := #[
    mkCase "ok/zero/zero-zero" #[intV 0, intV 0],
    mkCase "ok/identity/left-and-zero" #[intV 222, intV 0],
    mkCase "ok/identity/right-and-zero" #[intV 0, intV 222],
    mkCase "ok/identity/and-neg-one-positive" #[intV 123, intV (-1)],
    mkCase "ok/identity/and-neg-one-negative" #[intV (-123), intV (-1)],
    mkCase "ok/sign/mixed-sign" #[intV (-5), intV 3],
    mkCase "ok/sign/both-negative" #[intV (-7), intV (-3)],
    mkCase "ok/boundary/max-and-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "ok/boundary/min-and-neg-one" #[intV minInt257, intV (-1)],
    mkCase "ok/boundary/min-and-max" #[intV minInt257, intV maxInt257],
    mkCase "ok/pattern/high-bit-pair" #[intV (pow2 255), intV (pow2 254)],
    mkCase "ok/pattern/max-and-high-bit" #[intV maxInt257, intV (pow2 255)],
    mkCase "ok/pattern/min-and-high-bit" #[intV minInt257, intV (pow2 255)],
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
    mkCaseFromIntVals "error-order/pushint-range-high-before-qand" #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-low-before-qand" #[.num (minInt257 - 1), .num 7],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qandSetGasExact), .tonEnvOp .setGasLimit, qandInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qandSetGasExactMinusOne), .tonEnvOp .setGasLimit, qandInstr]
  ]
  fuzz := #[
    { seed := 2026020817
      count := 600
      gen := genQandFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QAND
