import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IF

/-!
IF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/If.lean` (`execInstrFlowIf`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xde` decodes to `.if_`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.if_` encodes as canonical `0xde`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_if`, registration `OpcodeInstr::mksimple(0xde, 8, "IF", exec_if)`).

Branch map used for this suite:
- dispatch: `.if_` handled vs non-`.if_` fallback to `next`;
- handled path:
  1. `checkUnderflow(2)` success/failure (`stkUnd`);
  2. `popCont` success/type failure (`typeChk`);
  3. `popBool` success vs type/finite-int failures (`typeChk` / `intOv`);
  4. condition true: call continuation (`VM.call`, matching C++ `st->call(cont)`);
  5. condition false: no call, only pops are applied.

Key risk areas:
- pop order is continuation first, then boolean condition;
- true-path must use call semantics (not a simple `cc := cont` update),
  because prebound-`c0` continuations and captured-stack continuations are special in C++;
- deep-stack/noise values must be preserved when IF does not rewrite argument stacks;
- deterministic gas cliff through `PUSHINT n; SETGASLIMIT; IF`.
-/

private def ifId : InstrId := { name := "IF" }

private def ifInstr : Instr := .if_

private def dispatchSentinel : Int := 4109

private def oracleCont : Value := .cont (.quit 0)

private def refCellA : Cell := Cell.ofUInt 8 0xa5

private def fullSliceA : Slice := Slice.ofCell refCellA

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[intV (-1), .null, intV 0, .cell Cell.empty, .builder Builder.empty]

private def withIfArgs
    (below : Array Value)
    (cond : IntVal)
    (top : Value := oracleCont) : Array Value :=
  below ++ #[.int cond, top]

private def withIfRawArgs
    (below : Array Value)
    (cond : Value)
    (top : Value := oracleCont) : Array Value :=
  below ++ #[cond, top]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runIfDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIf ifInstr stack

private def runIfDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIf instr (VM.push (intV dispatchSentinel)) stack

private def runIfState (stack : Array Value) : Except Excno VmState := do
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrFlowIf ifInstr (pure ())).run st0
  match res with
  | .ok _ => pure st1
  | .error e => throw e

private def expectStateOk (label : String) (res : Except Excno VmState) : IO VmState := do
  match res with
  | .ok st => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def ifSetGasExact : Int :=
  computeExactGasBudget ifInstr

private def ifSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifInstr

private def ifOracleFamilies : Array String :=
  #[
    "ok/true/",
    "ok/false/",
    "err/underflow/",
    "err/type/",
    "err/intov/",
    "gas/"
  ]

private def ifFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := ifOracleFamilies
    -- Bias toward stack-shape perturbations while still exercising all mutation modes.
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def preboundC0Cont : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 23) }
    OrdCdata.empty

private def capturedStackCont : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty
    { stack := #[intV 91, .null], nargs := 0 }

def suite : InstrSuite where
  id := ifId
  unit := #[
    { name := "unit/state/true-branch-calls-continuation"
      run := do
        let st ← expectStateOk "state/true-branch"
          (runIfState #[intV 13, intV 1, .cont (.quit 7)])
        if st.stack != #[intV 13] then
          throw (IO.userError s!"state/true-branch: unexpected stack {reprStr st.stack}")
        if st.cc != .quit 7 then
          throw (IO.userError s!"state/true-branch: expected cc=quit7, got {reprStr st.cc}")
        match st.regs.c0 with
        | .ordinary _ _ _ _ => pure ()
        | _ =>
            throw (IO.userError
              s!"state/true-branch: expected c0 return continuation, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/false-branch-skips-call"
      run := do
        let st ← expectStateOk "state/false-branch"
          (runIfState #[intV 13, intV 0, .cont (.quit 7)])
        let initial := VmState.initial Cell.empty
        if st.stack != #[intV 13] then
          throw (IO.userError s!"state/false-branch: unexpected stack {reprStr st.stack}")
        if st.cc != initial.cc then
          throw (IO.userError
            s!"state/false-branch: cc changed unexpectedly to {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"state/false-branch: expected c0=quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/true-prebound-c0-reduces-to-jump"
      run := do
        let st ← expectStateOk "state/prebound-c0"
          (runIfState #[intV 1, .cont preboundC0Cont])
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"state/prebound-c0: expected unchanged c0=quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/true-captured-stack-is-applied"
      run := do
        let st ← expectStateOk "state/captured-stack"
          (runIfState #[.null, intV 44, intV 1, .cont capturedStackCont])
        if st.stack != #[intV 91, .null] then
          throw (IO.userError
            s!"state/captured-stack: expected stack #[91,null], got {reprStr st.stack}") }
    ,
    { name := "unit/direct/deep-stack-preserved-on-false"
      run := do
        let below : Array Value := #[.null, intV (-9), .cell refCellA, .builder Builder.empty, .tuple #[]]
        expectOkStack "direct/deep-false"
          (runIfDirect (withIfArgs below (.num 0)))
          below }
    ,
    { name := "unit/direct/deep-stack-preserved-on-true-quit"
      run := do
        let below : Array Value := #[.null, intV (-9), .cell refCellA, .builder Builder.empty, .tuple #[]]
        expectOkStack "direct/deep-true-quit"
          (runIfDirect (withIfArgs below (.num 8)))
          below }
    ,
    { name := "unit/dispatch/if-vs-fallback"
      run := do
        expectOkStack "dispatch/matched-if"
          (runIfDispatchFallback ifInstr (withIfArgs #[] (.num 1)))
          #[]
        expectOkStack "dispatch/non-if-fallback"
          (runIfDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel] }
    ,
    { name := "unit/errors/underflow-type-intov-and-order"
      run := do
        expectErr "underflow/empty" (runIfDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runIfDirect #[intV 0]) .stkUnd
        expectErr "underflow/one-cont" (runIfDirect #[oracleCont]) .stkUnd
        expectErr "type/cont-top-int" (runIfDirect (withIfArgs #[] (.num 1) (intV 7))) .typeChk
        expectErr "type/bool-null" (runIfDirect (withIfRawArgs #[] (.null : Value))) .typeChk
        expectErr "intov/bool-nan" (runIfDirect (withIfArgs #[] .nan)) .intOv
        expectErr "type/pop-order-top-first"
          (runIfDirect #[.null, .cell refCellA]) .typeChk }
  ]
  oracle := #[
    -- True condition branch (`VM.call cont`) with oracle-encodable continuation K=quit(0).
    mkCase "ok/true/one" (withIfArgs #[] (.num 1)),
    mkCase "ok/true/neg-one" (withIfArgs #[] (.num (-1))),
    mkCase "ok/true/two" (withIfArgs #[] (.num 2)),
    mkCase "ok/true/neg-two" (withIfArgs #[] (.num (-2))),
    mkCase "ok/true/max-int257" (withIfArgs #[] (.num maxInt257)),
    mkCase "ok/true/min-int257" (withIfArgs #[] (.num minInt257)),
    mkCase "ok/true/deep-noise-a" (withIfArgs noiseA (.num 3)),
    mkCase "ok/true/deep-noise-b" (withIfArgs noiseB (.num 5)),
    mkCase "ok/true/deep-noise-c" (withIfArgs noiseC (.num 9)),

    -- False condition branch (no call; only argument pops).
    mkCase "ok/false/zero" (withIfArgs #[] (.num 0)),
    mkCase "ok/false/deep-noise-a" (withIfArgs noiseA (.num 0)),
    mkCase "ok/false/deep-noise-b" (withIfArgs noiseB (.num 0)),
    mkCase "ok/false/deep-noise-c" (withIfArgs noiseC (.num 0)),
    mkCase "ok/false/preserve-max-noise" (withIfArgs #[intV maxInt257] (.num 0)),
    mkCase "ok/false/preserve-min-noise" (withIfArgs #[intV minInt257] (.num 0)),
    mkCase "ok/false/slice-builder-noise"
      (withIfArgs #[.slice fullSliceA, .builder Builder.empty] (.num 0)),
    mkCase "ok/false/tuple-cell-noise"
      (withIfArgs #[.tuple #[], .cell refCellA] (.num 0)),

    -- Underflow checks (`checkUnderflow(2)`).
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/one-int" #[intV 1],
    mkCase "err/underflow/one-cont" #[oracleCont],

    -- `popCont` type-check failures (top is not a continuation).
    mkCase "err/type/cont-top-int" (withIfArgs #[] (.num 1) (intV 7)),
    mkCase "err/type/cont-top-null" (withIfArgs #[] (.num 1) (.null : Value)),
    mkCase "err/type/cont-top-cell" (withIfArgs #[] (.num 1) (.cell refCellA)),
    mkCase "err/type/cont-top-slice" (withIfArgs #[] (.num 1) (.slice fullSliceA)),
    mkCase "err/type/cont-top-builder" (withIfArgs #[] (.num 1) (.builder Builder.empty)),
    mkCase "err/type/cont-top-tuple" (withIfArgs #[] (.num 1) (.tuple #[])),
    mkCase "err/type/pop-order-top-first" #[.null, .cell refCellA],

    -- `popBool` failures after successful `popCont`.
    mkCase "err/type/bool-null" (withIfRawArgs #[] (.null : Value)),
    mkCase "err/type/bool-cell" (withIfRawArgs #[] (.cell refCellA)),
    mkCase "err/type/bool-slice" (withIfRawArgs #[] (.slice fullSliceA)),
    mkCase "err/type/bool-builder" (withIfRawArgs #[] (.builder Builder.empty)),
    mkCase "err/type/bool-tuple" (withIfRawArgs #[] (.tuple #[])),

    -- Deterministic gas cliff.
    mkCase "gas/exact-false-succeeds" (withIfArgs #[] (.num 0))
      #[.pushInt (.num ifSetGasExact), .tonEnvOp .setGasLimit, ifInstr],
    mkCase "gas/exact-minus-one-false-out-of-gas" (withIfArgs #[] (.num 0))
      #[.pushInt (.num ifSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifInstr],
    mkCase "gas/exact-true-succeeds" (withIfArgs #[] (.num 1))
      #[.pushInt (.num ifSetGasExact), .tonEnvOp .setGasLimit, ifInstr]
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile ifId ifFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.IF
