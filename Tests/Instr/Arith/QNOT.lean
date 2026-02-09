import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QNOT

/-
QNOT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qnot`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_not`, opcode wiring in `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 5 branch points / 6 terminal outcomes
  (dispatch to `.contExt`; dispatch to `.qnot`; `popInt` underflow/type/success;
   NaN-vs-num operand split; quiet push path finite-vs-out-of-range→NaN).
- C++: 4 branch points / 6 aligned terminal outcomes
  (`QNOT` registration to `exec_not(..., quiet=true)`; underflow guard;
   `pop_int` type check; `push_int_quiet` fit/NaN handling).

Key risk areas:
- quiet NaN behavior for QNOT itself, and ordering where out-of-range `PUSHINT` fails before QNOT;
- two's-complement identity `~x = -x-1` at `minInt257`/`maxInt257`;
- unary error ordering (`stkUnd` before type checks; top-of-stack selected first);
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QNOT` exact vs exact-minus-one.
-/

private def qnotId : InstrId := { name := "QNOT" }

private def qnotInstr : Instr := .contExt .qnot

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qnotInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qnotId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (progPrefix.push qnotInstr)

private def mkInputProgramCase
    (name : String)
    (x : IntVal)
    (programSuffix : Array Instr)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (progPrefix ++ programSuffix)

private def runQNotDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qnotInstr stack

private def runQNotDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 4242)) stack

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def runQNotVm
    (program : Array Instr)
    (initStack : Array Value := #[])
    (gasLimit : Int := 1_000_000)
    (gasMax : Int := 1_000_000)
    (fuel : Nat := 200_000) : IO StepResult := do
  let code ←
    match assembleCp0 program.toList with
    | .ok c => pure c
    | .error e => failUnit s!"assemble QNOT failed: {e}"
  let st0 := { (VmState.initial code gasLimit gasMax 0) with stack := initStack }
  pure (VmState.run nativeHost fuel st0)

private def expectExit (label : String) (expected : Int) (res : StepResult) : IO VmState := do
  match res with
  | .halt exitCode st =>
      if exitCode = expected then
        pure st
      else
        failUnit s!"{label}: expected exit={expected}, got {exitCode}"
  | .continue _ =>
      failUnit s!"{label}: execution did not halt"

private def expectTopIntVal (label : String) (expected : IntVal) (st : VmState) : IO Unit := do
  match st.stack.back? with
  | some (.int got) =>
      if got = expected then
        pure ()
      else
        failUnit s!"{label}: expected top int {reprStr expected}, got {reprStr got}"
  | some v =>
      failUnit s!"{label}: expected top int, got {reprStr v}"
  | none =>
      failUnit s!"{label}: expected non-empty stack"

private def qnotSetGasExact : Int :=
  computeExactGasBudget qnotInstr

private def qnotSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qnotInstr

private def not257 (value : Int) : Int :=
  -value - 1

private def qnotOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQNotOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qnotOutOfRangePool.size - 1)
  (qnotOutOfRangePool[idx]!, rng')

private def pickQNotNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genQNotFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, rng3) := pickInt257Boundary rng2
    (mkInputCase s!"fuzz/ok/boundary-{tag}" (.num x), rng3)
  else if shape = 1 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/random-{tag}" (.num x), rng3)
  else if shape = 2 then
    let (x, rng3) := pickQNotOutOfRange rng2
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
    (mkCase s!"fuzz/error-order/top-non-int-before-lower-int-{tag}" #[intV x, .null], rng3)
  else if shape = 8 then
    let (x, rng3) := pickSigned257ish rng2
    let (nonInt, rng4) := pickQNotNonInt rng3
    (mkInputCase s!"fuzz/ok/top-int-below-non-int-{tag}" (.num x) #[nonInt], rng4)
  else
    let (x, rng3) := pickSigned257ish rng2
    (mkInputProgramCase s!"fuzz/ok/involution-double-qnot-{tag}" (.num x) #[qnotInstr, qnotInstr], rng3)

def suite : InstrSuite where
  id := qnotId
  unit := #[
    { name := "unit/ok/twos-complement-known-values"
      run := do
        let checks : Array Int :=
          #[
            minInt257,
            minInt257 + 1,
            minInt257 + 2,
            -(pow2 255),
            -7,
            -1,
            0,
            1,
            7,
            (pow2 255) - 1,
            maxInt257 - 1,
            maxInt257
          ]
        for x in checks do
          expectOkStack s!"qnot({x})" (runQNotDirect #[intV x]) #[intV (not257 x)] }
    ,
    { name := "unit/error-order/underflow-before-type-and-top-selection"
      run := do
        expectErr "underflow/empty" (runQNotDirect #[]) .stkUnd
        expectErr "type/top-null" (runQNotDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runQNotDirect #[.cell Cell.empty]) .typeChk
        expectErr "error-order/top-non-int-before-lower-int"
          (runQNotDirect #[intV 9, .null]) .typeChk
        expectOkStack "error-order/top-int-lower-non-int-untouched"
          (runQNotDirect #[.null, intV 9]) #[.null, intV (not257 9)] }
    ,
    { name := "unit/quiet/program-injected-nan-and-pushint-range-ordering"
      run := do
        let nanRes ← runQNotVm #[.pushInt .nan, qnotInstr]
        let nanSt ← expectExit "unit/quiet/pushnan" (~~~ 0) nanRes
        expectTopIntVal "unit/quiet/pushnan" .nan nanSt

        let rangeHiRes ← runQNotVm #[.pushInt (.num (maxInt257 + 1)), qnotInstr]
        let _ ← expectExit "unit/quiet/range-high" (~~~ Excno.intOv.toInt) rangeHiRes

        let rangeLoRes ← runQNotVm #[.pushInt (.num (minInt257 - 1)), qnotInstr]
        let _ ← expectExit "unit/quiet/range-low" (~~~ Excno.intOv.toInt) rangeLoRes
        pure () }
    ,
    { name := "unit/dispatch/non-qnot-falls-through"
      run := do
        expectOkStack "fallback/non-contExt" (runQNotDispatchFallback .add #[]) #[intV 4242]
        expectOkStack "fallback/other-contExt" (runQNotDispatchFallback (.contExt .condSel) #[]) #[intV 4242] }
  ]
  oracle := #[
    mkInputCase "ok/finite/zero" (.num 0),
    mkInputCase "ok/finite/positive" (.num 23),
    mkInputCase "ok/finite/negative" (.num (-23)),
    mkInputCase "ok/boundary/min-int257" (.num minInt257),
    mkInputCase "ok/boundary/min-plus-one" (.num (minInt257 + 1)),
    mkInputCase "ok/boundary/max-int257" (.num maxInt257),
    mkInputCase "ok/boundary/max-minus-one" (.num (maxInt257 - 1)),
    mkInputProgramCase "ok/involution-double-qnot" (.num 123456789) #[qnotInstr, qnotInstr],
    mkInputCase "ok/stack/top-int-below-null" (.num 9) #[.null],
    mkInputCase "ok/stack/top-int-below-cell" (.num (-9)) #[.cell Cell.empty],
    mkInputCase "nan/pushnan-empty" .nan,
    mkInputCase "nan/pushnan-over-int" .nan #[intV 42],
    mkInputCase "nan/pushnan-over-null" .nan #[.null],
    mkInputCase "range/out-of-range-via-program/positive" (.num (maxInt257 + 1)),
    mkInputCase "range/out-of-range-via-program/negative" (.num (minInt257 - 1)),
    mkInputCase "range/out-of-range-via-program/pow2-257" (.num (pow2 257)),
    mkInputCase "range/out-of-range-via-program/neg-pow2-257" (.num (-(pow2 257))),
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "type/top-null-with-below-int" #[intV 1, .null],
    mkCase "error-order/empty-underflow-before-type" #[],
    mkCase "error-order/non-empty-type-check" #[.cell Cell.empty],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num qnotSetGasExact), .tonEnvOp .setGasLimit, qnotInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num qnotSetGasExactMinusOne), .tonEnvOp .setGasLimit, qnotInstr]
  ]
  fuzz := #[
    { seed := 2026020814
      count := 500
      gen := genQNotFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QNOT
