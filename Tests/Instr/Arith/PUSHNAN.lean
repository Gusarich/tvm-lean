import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHNAN

/-
PUSHNAN branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (`execInstrStackPushInt`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.pushIntQuiet`, prelude PUSHINT overflow path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`encodeCp0`, `PUSHNAN` opcode emit)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0x8300..0x83ff` split to `PUSHPOW2` vs `PUSHNAN`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_push_nan`, opcode wiring in `register_int_const_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::push_int`, prelude overflow path)

Branch counts used for this suite:
- Lean: 5 branch points / 8 terminal outcomes
  (dispatch to `.pushInt`; `.nan` vs `.num`; numeric signed-257 fit check in prelude `PUSHINT`;
   cp0 decode split at `0x83ff`; cp0 encode split for `.pushInt .nan` vs numeric encodings).
- C++: 3 branch points / 5 aligned terminal outcomes
  (registration maps `0x83ff` to `exec_push_nan`; `exec_push_nan` success path;
   `Stack::push_int` signed-257 fit check hit by prelude `PUSHINT` before `PUSHNAN`).

Key risk areas:
- Opcode-boundary aliasing: `0x83ff` must decode/encode as `PUSHNAN`, not `PUSHPOW2 256`.
- `PUSHNAN` must push NaN directly (never routed through non-quiet overflow checks).
- Out-of-range immediates in prelude `PUSHINT` must fail before `PUSHNAN` executes.
- Stack preservation (no pops): lower ints/non-ints remain untouched.
- Deterministic gas cliffs for `PUSHINT n; SETGASLIMIT; PUSHNAN` exact vs exact-minus-one.
-/

private def pushnanId : InstrId := { name := "PUSHNAN" }

private def pushnanInstr : Instr := .pushInt .nan

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pushnanInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pushnanId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stackOrEmpty) (progPrefix.push pushnanInstr)

private def runPushnanDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushInt pushnanInstr stack

private def runPushnanDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushInt .add (VM.push (intV 777)) stack

private def pushnanSetGasExact : Int :=
  computeExactGasBudget pushnanInstr

private def pushnanSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pushnanInstr

private def genPushnanFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    (mkCase s!"/fuzz/ok/empty-{tag}" #[], rng2)
  else if shape = 1 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"/fuzz/ok/int-tail-{tag}" #[intV x], rng3)
  else if shape = 2 then
    let (x, rng3) := pickInt257Boundary rng2
    (mkCase s!"/fuzz/ok/null-and-boundary-tail-{tag}" #[.null, intV x], rng3)
  else if shape = 3 then
    let (x, rng3) := pickSigned257ish rng2
    let (y, rng4) := pickSigned257ish rng3
    (mkCase s!"/fuzz/ok/two-int-tail-{tag}" #[intV x, intV y], rng4)
  else if shape = 4 then
    (mkCase s!"/fuzz/ok/cell-tail-{tag}" #[.cell Cell.empty], rng2)
  else if shape = 5 then
    let (x, rng3) := pickInt257OutOfRange rng2
    (mkCase s!"/fuzz/error-order/pushint-overflow-before-pushnan-{tag}" #[]
      #[.pushInt (.num x), pushnanInstr], rng3)
  else if shape = 6 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"/fuzz/input/pushnan-prelude-over-int-{tag}" #[.nan] #[intV x], rng3)
  else if shape = 7 then
    let (x, rng3) := pickInt257OutOfRange rng2
    (mkInputCase s!"/fuzz/input/pushint-overflow-prelude-{tag}" #[.num x], rng3)
  else if shape = 8 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"/fuzz/gas/exact-cost-{tag}" #[intV x]
      #[.pushInt (.num pushnanSetGasExact), .tonEnvOp .setGasLimit, pushnanInstr], rng3)
  else
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"/fuzz/gas/exact-minus-one-{tag}" #[intV x]
      #[.pushInt (.num pushnanSetGasExactMinusOne), .tonEnvOp .setGasLimit, pushnanInstr], rng3)

def suite : InstrSuite where
  id := pushnanId
  unit := #[
    { name := "/unit/direct/pushes-nan-and-preserves-lower-stack"
      run := do
        expectOkStack "empty" (runPushnanDirect #[]) #[.int .nan]
        expectOkStack "int-tail" (runPushnanDirect #[intV 17]) #[intV 17, .int .nan]
        expectOkStack "null-tail" (runPushnanDirect #[.null]) #[.null, .int .nan]
        expectOkStack "cell-tail" (runPushnanDirect #[.cell Cell.empty]) #[.cell Cell.empty, .int .nan]
        expectOkStack "mixed-tail" (runPushnanDirect #[.null, intV (-3)]) #[.null, intV (-3), .int .nan] }
    ,
    { name := "/unit/dispatch/non-pushint-falls-through"
      run := do
        expectOkStack "fallback-next" (runPushnanDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "/ok/empty-stack" #[],
    mkCase "/ok/finite-tail/positive" #[intV 17],
    mkCase "/ok/finite-tail/negative" #[intV (-17)],
    mkCase "/ok/finite-tail/boundary-max" #[intV maxInt257],
    mkCase "/ok/finite-tail/boundary-min" #[intV minInt257],
    mkCase "/ok/nonint-tail/null" #[.null],
    mkCase "/ok/nonint-tail/cell" #[.cell Cell.empty],
    mkCase "/ok/mixed-tail/null-then-int" #[.null, intV 5],
    mkCase "/ok/mixed-tail/cell-then-int" #[.cell Cell.empty, intV (-5)],
    mkCase "/ok/opcode-boundary/pushpow2-255-then-pushnan" #[] #[.pushPow2 255, pushnanInstr],
    mkInputCase "/ok/prelude/pushnan-over-int" #[.nan] #[intV 42],
    mkInputCase "/ok/prelude/finite-then-pushnan-over-null" #[.num 7, .nan] #[.null],
    mkInputCase "/error-order/prelude-pushint-overflow-high-before-pushnan" #[.num (maxInt257 + 1)],
    mkInputCase "/error-order/prelude-pushint-overflow-low-before-pushnan" #[.num (minInt257 - 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num pushnanSetGasExact), .tonEnvOp .setGasLimit, pushnanInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num pushnanSetGasExactMinusOne), .tonEnvOp .setGasLimit, pushnanInstr]
  ]
  fuzz := #[
    { seed := 2026020807
      count := 600
      gen := genPushnanFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHNAN
