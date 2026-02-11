import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFNOTJMP

/-
IFNOTJMP branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Flow/Ifnotjmp.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
  (`exec_ifnot_jmp`, opcode `0xe1` in `register_continuation_cond_loop_ops`).

Branch map and ordering used by this suite:
- explicit `checkUnderflow 2` / `check_underflow(2)` happens first;
- pop order is `cont` first, then `bool` (`popBool` / `pop_bool`);
- branch predicate is inverted (`jump` iff popped bool is false / zero);
- `.ifnotjmp` updates `cc` via jump (not call), non-matching opcode falls through to `next`.

Key risk areas:
- branch inversion bugs (`if` vs `ifnot`);
- pop-order regressions (`popBool` before `popCont`);
- underflow-vs-type/intov ordering;
- deep-stack/noise preservation below the two consumed operands.
-/

private def ifnotjmpId : InstrId := { name := "IFNOTJMP" }

private def ifnotjmpInstr : Instr := .ifnotjmp

private def quitContV (n : Int) : Value :=
  .cont (.quit n)

private def q0 : Value :=
  quitContV 0

private def emptySlice : Slice :=
  Slice.ofCell Cell.empty

private def tailMarker : Int := 777

private def branchObservableProgram : Array Instr :=
  #[ifnotjmpInstr, .pushInt (.num tailMarker)]

private def boolNanProgram : Array Instr :=
  #[.pushInt .nan, .xchg0 1, ifnotjmpInstr]

private def popContBeforeBoolNanProgram : Array Instr :=
  #[.pushInt .nan, ifnotjmpInstr]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifnotjmpInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnotjmpId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runIfnotjmpDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfnotjmp ifnotjmpInstr stack

private def runIfnotjmpDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfnotjmp .add (VM.push (intV 901)) stack

private def runIfnotjmpState
    (stack : Array Value)
    (cc : Continuation := .quit 71) : Except Excno VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc }
  let (res, st1) := (execInstrFlowIfnotjmp ifnotjmpInstr (pure ())).run st0
  match res with
  | .ok _ => .ok st1
  | .error e => .error e

private def expectStateQuitAndStack
    (label : String)
    (res : Except Excno VmState)
    (expectedQuit : Int)
    (expectedStack : Array Value) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.stack != expectedStack then
        throw (IO.userError s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st.stack}")
      else
        match st.cc with
        | .quit n =>
            if n = expectedQuit then
              pure ()
            else
              throw (IO.userError s!"{label}: expected cc quit({expectedQuit}), got quit({n})")
        | _ =>
            throw (IO.userError s!"{label}: expected cc quit({expectedQuit}), got {reprStr st.cc}")

private def ifnotjmpSetGasExact : Int :=
  computeExactGasBudget ifnotjmpInstr

private def ifnotjmpSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifnotjmpInstr

private def noisePool : Array Value :=
  #[.null, intV 42, .cell Cell.empty, .builder Builder.empty, .tuple #[]]

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (idx, rng') := randNat rng 0 (noisePool.size - 1)
  (noisePool[idx]!, rng')

private def ensureNonZero (x : Int) : Int :=
  if x = 0 then 1 else x

private def genIfnotjmpFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    (mkCase s!"fuzz/branch/jump/{tag}" #[intV 0, q0] branchObservableProgram, rng2)
  else if shape = 1 then
    let (raw, rng3) := pickSigned257ish rng2
    let cond := ensureNonZero raw
    (mkCase s!"fuzz/branch/nojump/{tag}" #[intV cond, q0] branchObservableProgram, rng3)
  else if shape = 2 then
    let (n0, rng3) := pickNoise rng2
    let (n1, rng4) := pickNoise rng3
    (mkCase s!"fuzz/deep/jump/{tag}" #[n0, n1, intV 0, q0] branchObservableProgram, rng4)
  else if shape = 3 then
    let (n0, rng3) := pickNoise rng2
    let (n1, rng4) := pickNoise rng3
    let (raw, rng5) := pickSigned257ish rng4
    let cond := ensureNonZero raw
    (mkCase s!"fuzz/deep/nojump/{tag}" #[n0, n1, intV cond, q0] branchObservableProgram, rng5)
  else if shape = 4 then
    (mkCase s!"fuzz/underflow/empty/{tag}" #[], rng2)
  else if shape = 5 then
    let (pick, rng3) := randNat rng2 0 2
    let one : Value := if pick = 0 then intV 1 else if pick = 1 then q0 else .null
    (mkCase s!"fuzz/underflow/one/{pick}/{tag}" #[one], rng3)
  else if shape = 6 then
    let (pick, rng3) := randNat rng2 0 4
    let top : Value :=
      if pick = 0 then intV 1
      else if pick = 1 then .null
      else if pick = 2 then .cell Cell.empty
      else if pick = 3 then .builder Builder.empty
      else .slice emptySlice
    (mkCase s!"fuzz/type/popcont/{pick}/{tag}" #[intV 0, top], rng3)
  else if shape = 7 then
    let (pick, rng3) := randNat rng2 0 3
    let badBool : Value :=
      if pick = 0 then .null
      else if pick = 1 then .cell Cell.empty
      else if pick = 2 then .builder Builder.empty
      else .slice emptySlice
    (mkCase s!"fuzz/type/popbool/{pick}/{tag}" #[badBool, q0], rng3)
  else if shape = 8 then
    (mkCase s!"fuzz/intov/popbool-nan/{tag}" #[q0] boolNanProgram, rng2)
  else
    (mkCase s!"fuzz/error-order/popcont-before-bool-nan/{tag}" #[intV 1] popContBeforeBoolNanProgram, rng2)

def suite : InstrSuite where
  id := ifnotjmpId
  unit := #[
    { name := "unit/branch-inversion-and-cc-target"
      run := do
        expectStateQuitAndStack "jump/zero"
          (runIfnotjmpState #[intV 0, quitContV 13] (.quit 71))
          13
          #[]
        expectStateQuitAndStack "nojump/one"
          (runIfnotjmpState #[intV 1, quitContV 13] (.quit 71))
          71
          #[]
        expectStateQuitAndStack "nojump/minus-nine"
          (runIfnotjmpState #[intV (-9), quitContV 13] (.quit 71))
          71
          #[]
        expectStateQuitAndStack "jump/deep-stack"
          (runIfnotjmpState #[.null, intV 7, intV 0, quitContV 13] (.quit 71))
          13
          #[.null, intV 7]
        expectStateQuitAndStack "nojump/deep-stack"
          (runIfnotjmpState #[.null, intV 7, intV 5, quitContV 13] (.quit 71))
          71
          #[.null, intV 7] }
    ,
    { name := "unit/underflow-happens-before-any-type-check"
      run := do
        expectErr "underflow/empty" (runIfnotjmpDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runIfnotjmpDirect #[intV 0]) .stkUnd
        expectErr "underflow/one-cont" (runIfnotjmpDirect #[q0]) .stkUnd
        expectErr "underflow/one-null" (runIfnotjmpDirect #[.null]) .stkUnd }
    ,
    { name := "unit/type-errors-at-cont-pop-site"
      run := do
        expectErr "popcont/top-int" (runIfnotjmpDirect #[intV 0, intV 1]) .typeChk
        expectErr "popcont/top-null" (runIfnotjmpDirect #[intV 0, .null]) .typeChk
        expectErr "popcont/top-cell" (runIfnotjmpDirect #[intV 0, .cell Cell.empty]) .typeChk
        expectErr "popcont/top-builder" (runIfnotjmpDirect #[intV 0, .builder Builder.empty]) .typeChk
        expectErr "popcont/top-slice" (runIfnotjmpDirect #[intV 0, .slice emptySlice]) .typeChk
        expectErr "error-order/popcont-before-popbool-nan-below"
          (runIfnotjmpDirect #[.int .nan, intV 1]) .typeChk }
    ,
    { name := "unit/type-and-intov-at-bool-pop-site"
      run := do
        expectErr "popbool/null" (runIfnotjmpDirect #[.null, q0]) .typeChk
        expectErr "popbool/cell" (runIfnotjmpDirect #[.cell Cell.empty, q0]) .typeChk
        expectErr "popbool/builder" (runIfnotjmpDirect #[.builder Builder.empty, q0]) .typeChk
        expectErr "popbool/slice" (runIfnotjmpDirect #[.slice emptySlice, q0]) .typeChk
        expectErr "popbool/nan-intov" (runIfnotjmpDirect #[.int .nan, q0]) .intOv
        expectOkStack "popbool/zero-valid" (runIfnotjmpDirect #[intV 0, q0]) #[]
        expectOkStack "popbool/nonzero-valid" (runIfnotjmpDirect #[intV 2, q0]) #[] }
    ,
    { name := "unit/deep-stack-noise-preserved"
      run := do
        expectOkStack "jump/preserve-below"
          (runIfnotjmpDirect #[.null, .tuple #[], intV 0, q0])
          #[.null, .tuple #[]]
        expectOkStack "nojump/preserve-below"
          (runIfnotjmpDirect #[.null, .tuple #[], intV (-1), q0])
          #[.null, .tuple #[]] }
    ,
    { name := "unit/dispatch-non-ifnotjmp-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runIfnotjmpDispatchFallback #[intV 5])
          #[intV 5, intV 901] }
  ]
  oracle := #[
    mkCase "branch/observable/jump-when-zero" #[intV 0, q0] branchObservableProgram,
    mkCase "branch/observable/nojump-when-one" #[intV 1, q0] branchObservableProgram,
    mkCase "branch/observable/nojump-when-minus-one" #[intV (-1), q0] branchObservableProgram,
    mkCase "branch/observable/nojump-when-two" #[intV 2, q0] branchObservableProgram,
    mkCase "branch/observable/nojump-when-minus-two" #[intV (-2), q0] branchObservableProgram,
    mkCase "branch/observable/nojump-when-big-pos" #[intV (pow2 200), q0] branchObservableProgram,
    mkCase "branch/observable/nojump-when-big-neg" #[intV (-(pow2 200)), q0] branchObservableProgram,
    mkCase "branch/observable/deep-jump-zero" #[.null, intV 9, intV 0, q0] branchObservableProgram,
    mkCase "branch/observable/deep-nojump-one" #[.null, intV 9, intV 1, q0] branchObservableProgram,
    mkCase "branch/observable/deep-nojump-minus-seven" #[.null, intV 9, intV (-7), q0] branchObservableProgram,

    mkCase "ok/no-tail/zero" #[intV 0, q0],
    mkCase "ok/no-tail/one" #[intV 1, q0],
    mkCase "ok/no-tail/minus-one" #[intV (-1), q0],
    mkCase "ok/no-tail/deep-zero" #[.null, .cell Cell.empty, intV 0, q0],
    mkCase "ok/no-tail/deep-nonzero" #[.null, .cell Cell.empty, intV 17, q0],

    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 0],
    mkCase "underflow/one-cont" #[q0],
    mkCase "underflow/one-null-underflow-first" #[.null],
    mkCase "underflow/one-cell-underflow-first" #[.cell Cell.empty],

    mkCase "type/popcont/top-int" #[intV 0, intV 1],
    mkCase "type/popcont/top-null" #[intV 0, .null],
    mkCase "type/popcont/top-cell" #[intV 0, .cell Cell.empty],
    mkCase "type/popcont/top-builder" #[intV 0, .builder Builder.empty],
    mkCase "type/popcont/top-slice" #[intV 0, .slice emptySlice],
    mkCase "error-order/popcont-before-popbool-type" #[.null, intV 1],
    mkCase "error-order/popcont-before-popbool-intov" #[intV 1] popContBeforeBoolNanProgram,

    mkCase "type/popbool/null-after-cont" #[.null, q0],
    mkCase "type/popbool/cell-after-cont" #[.cell Cell.empty, q0],
    mkCase "type/popbool/builder-after-cont" #[.builder Builder.empty, q0],
    mkCase "type/popbool/slice-after-cont" #[.slice emptySlice, q0],
    mkCase "intov/popbool/nan-after-cont" #[q0] boolNanProgram,

    mkCase "deep/noise/jump-builder-tuple" #[.builder Builder.empty, .tuple #[], intV 0, q0] branchObservableProgram,
    mkCase "deep/noise/nojump-builder-tuple" #[.builder Builder.empty, .tuple #[], intV 5, q0] branchObservableProgram,

    mkCase "gas/exact-cost-succeeds" #[intV 1, q0]
      #[.pushInt (.num ifnotjmpSetGasExact), .tonEnvOp .setGasLimit, ifnotjmpInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 1, q0]
      #[.pushInt (.num ifnotjmpSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotjmpInstr]
  ]
  fuzz := #[
    { seed := 2026021104
      count := 500
      gen := genIfnotjmpFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.IFNOTJMP
