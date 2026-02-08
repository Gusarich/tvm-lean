import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QSGN

/-
QSGN branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.qsgn`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`, `VM.pushSmallInt`)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (program-side `PUSHINT` NaN/range ordering)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_sgn`, `register_int_cmp_ops` wiring `QSGN -> mode 0x987, quiet=true`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`, `Stack::push_smallint`)

Branch map used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (dispatch to `.contExt`; dispatch to `.qsgn`; unary pop underflow/type/success;
   NaN-vs-num split; numeric sign split `<0`, `=0`, `>0`).
- C++: 5 branch points / 8 aligned terminal outcomes for QSGN path
  (opcode registration to `exec_sgn(..., mode=0x987, quiet=true)`; underflow guard;
   `pop_int` type check; invalid-vs-valid split; `td::sgn` class split `{-1,0,1}`).

Key risk areas covered:
- mode-table mapping (`0x987`) must stay exactly `-1/0/1`;
- quiet NaN propagation must return NaN (not throw `intOv`);
- unary error ordering (`stkUnd` before type checks; top-of-stack selected first);
- signed-257 boundary behavior at `minInt257`, `maxInt257`, and neighbors;
- program ordering where out-of-range `PUSHINT` fails before QSGN executes;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QSGN`.
-/

private def qsgnId : InstrId := { name := "QSGN" }

private def qsgnInstr : Instr := .contExt .qsgn

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qsgnInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qsgnId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (progPrefix.push qsgnInstr)

private def mkInputProgramCase
    (name : String)
    (x : IntVal)
    (programSuffix : Array Instr)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (progPrefix ++ programSuffix)

private def runQsgnDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qsgnInstr stack

private def runQsgnDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 1919)) stack

private def qsgnSetGasExact : Int :=
  computeExactGasBudget qsgnInstr

private def qsgnSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qsgnInstr

private def qsgnOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQsgnOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qsgnOutOfRangePool.size - 1)
  (qsgnOutOfRangePool[idx]!, rng')

private def pickQsgnNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genQsgnFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok-boundary" (.num x), r2)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok-random" (.num x), r2)
    else if shape = 2 then
      (mkInputCase s!"fuzz/shape-{shape}/ok-zero" (.num 0), rng1)
    else if shape = 3 then
      (mkInputCase s!"fuzz/shape-{shape}/ok-positive-one" (.num 1), rng1)
    else if shape = 4 then
      (mkInputCase s!"fuzz/shape-{shape}/ok-negative-one" (.num (-1)), rng1)
    else if shape = 5 then
      let (which, r2) := randNat rng1 0 3
      let x : Int :=
        if which = 0 then minInt257
        else if which = 1 then minInt257 + 1
        else if which = 2 then maxInt257 - 1
        else maxInt257
      (mkInputCase s!"fuzz/shape-{shape}/ok-bounds-near" (.num x), r2)
    else if shape = 6 then
      (mkInputCase s!"fuzz/shape-{shape}/nan-via-program" .nan, rng1)
    else if shape = 7 then
      let (x, r2) := pickQsgnOutOfRange rng1
      (mkInputCase s!"fuzz/shape-{shape}/range-via-program" (.num x), r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 9 then
      let (top, r2) := pickQsgnNonInt rng1
      (mkCase s!"fuzz/shape-{shape}/type-single-non-int" #[top], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (top, r3) := pickQsgnNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type-top-non-int-before-below-int" #[intV x, top], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (below, r3) := pickQsgnNonInt r2
      (mkInputCase s!"fuzz/shape-{shape}/ok-top-int-below-non-int" (.num x) #[below], r3)
    else if shape = 12 then
      let (below, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/nan-via-program-with-tail" .nan #[intV below], r2)
    else
      let (x, r2) := pickSigned257ish rng1
      (mkInputProgramCase s!"fuzz/shape-{shape}/ok-double-qsgn" (.num x) #[qsgnInstr, qsgnInstr], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qsgnId
  unit := #[
    { name := "unit/ok/finite-sign-zero-and-boundaries"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (minInt257, -1),
            (minInt257 + 1, -1),
            (-17, -1),
            (-1, -1),
            (0, 0),
            (1, 1),
            (17, 1),
            (maxInt257 - 1, 1),
            (maxInt257, 1)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"qsgn({x})" (runQsgnDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/ok/quiet-nan-propagates"
      run := do
        expectOkStack "nan/single" (runQsgnDirect #[.int .nan]) #[.int .nan]
        expectOkStack "nan/top-over-int" (runQsgnDirect #[intV 42, .int .nan]) #[intV 42, .int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-top-selection"
      run := do
        expectErr "underflow/empty" (runQsgnDirect #[]) .stkUnd
        expectErr "type/top-null" (runQsgnDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runQsgnDirect #[.cell Cell.empty]) .typeChk
        expectErr "type/top-non-int-before-below-int" (runQsgnDirect #[intV 7, .null]) .typeChk
        expectOkStack "ok/top-int-below-null-untouched"
          (runQsgnDirect #[.null, intV (-8)]) #[.null, intV (-1)] }
    ,
    { name := "unit/dispatch/non-qsgn-falls-through"
      run := do
        expectOkStack "fallback/non-contExt"
          (runQsgnDispatchFallback .add #[]) #[intV 1919]
        expectOkStack "fallback/other-contExt"
          (runQsgnDispatchFallback (.contExt .qnot) #[]) #[intV 1919] }
  ]
  oracle := #[
    mkInputCase "ok/zero" (.num 0),
    mkInputCase "ok/positive-small" (.num 17),
    mkInputCase "ok/negative-small" (.num (-17)),
    mkInputCase "ok/top-int-below-null" (.num (-7)) #[.null],
    mkInputCase "ok/top-int-below-cell" (.num 7) #[.cell Cell.empty],
    mkInputCase "boundary/min" (.num minInt257),
    mkInputCase "boundary/min-plus-one" (.num (minInt257 + 1)),
    mkInputCase "boundary/max-minus-one" (.num (maxInt257 - 1)),
    mkInputCase "boundary/max" (.num maxInt257),
    mkInputProgramCase "ok/double-qsgn" (.num 123456789) #[qsgnInstr, qsgnInstr],
    mkInputCase "nan/pushnan-via-program" .nan,
    mkInputCase "nan/pushnan-via-program-with-tail" .nan #[intV 42],
    mkInputCase "range/out-of-range-high-via-program" (.num (maxInt257 + 1)),
    mkInputCase "range/out-of-range-low-via-program" (.num (minInt257 - 1)),
    mkInputCase "range/out-of-range-pow2-257-via-program" (.num (pow2 257)),
    mkInputCase "range/out-of-range-neg-pow2-257-via-program" (.num (-(pow2 257))),
    mkCase "underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "type/top-non-int-before-below-int" #[intV 7, .null],
    mkInputCase "ok/top-int-below-non-int-untouched" (.num (-8)) #[.null],
    mkCase "gas/exact-cost-succeeds" #[intV (-7)]
      #[.pushInt (.num qsgnSetGasExact), .tonEnvOp .setGasLimit, qsgnInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV (-7)]
      #[.pushInt (.num qsgnSetGasExactMinusOne), .tonEnvOp .setGasLimit, qsgnInstr]
  ]
  fuzz := #[
    { seed := 2026020825
      count := 600
      gen := genQsgnFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QSGN
