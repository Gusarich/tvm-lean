import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFJMP

/-
IFJMP branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Ifjmp.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popCont`, `popBool`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.jump`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_if_jmp`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_cont`, `pop_bool`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::jump`, `adjust_jump_cont`)

Branch map covered by this suite:
- dispatch: `.ifjmp` handled vs fallback to `next`;
- pre-pop guard: `check_underflow(2)` before any pop;
- pop order: top is continuation (`pop_cont`) first, then boolean integer (`pop_bool`);
- boolean split: `false` => no jump, `true` => jump;
- jump path semantics: taken branch must use full jump semantics (`VmState::jump`),
  including closure `nargs` underflow checks and captured-stack application.

Mismatch found and fixed:
- C++ `exec_if_jmp` calls `st->jump(std::move(cont))`.
- Lean previously called `jumpTo` directly in IFJMP, bypassing jump-time closure checks.
- This suite includes regression tests that fail without `VM.jump`.
-/

private def ifjmpId : InstrId := { name := "IFJMP" }

private def ifjmpInstr : Instr := .ifjmp

private def dispatchSentinel : Int := 31003

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice := Slice.ofCell refCellA

private def fullSliceB : Slice := Slice.ofCell refCellB

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def mkIfjmpStack
    (below : Array Value)
    (flag : Int)
    (cont : Continuation := .quit 0) : Array Value :=
  below ++ #[intV flag, .cont cont]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifjmpInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifjmpId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRetAltProbeCase
    (name : String)
    (flag : Int)
    (below : Array Value := #[]) : OracleCase :=
  mkCase name (mkIfjmpStack below flag) #[ifjmpInstr, .retAlt]

private def mkPushProbeCase
    (name : String)
    (flag : Int)
    (pushN : Int)
    (below : Array Value := #[]) : OracleCase :=
  mkCase name (mkIfjmpStack below flag) #[ifjmpInstr, .pushInt (.num pushN)]

private def runIfjmpDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfjmp ifjmpInstr stack

private def runIfjmpDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfjmp instr (VM.push (intV dispatchSentinel)) stack

private def runIfjmpRaw
    (stack : Array Value)
    (cc : Continuation := .quit 0) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc }
  (execInstrFlowIfjmp ifjmpInstr (pure ())).run st0

private def ifjmpSetGasExact : Int :=
  computeExactGasBudget ifjmpInstr

private def ifjmpSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifjmpInstr

private def belowPool : Array Value :=
  #[.null, intV 0, intV 7, intV (-9), .cell refCellB, .builder Builder.empty, .tuple #[], .slice fullSliceB]

private def topNonContPool : Array Value :=
  #[.null, intV 4, .cell refCellA, .builder Builder.empty, .tuple #[], .slice fullSliceA]

private def boolNonIntPool : Array Value :=
  #[.null, .cell refCellA, .builder Builder.empty, .tuple #[], .slice fullSliceA]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genIfjmpFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (belowV, rng2) := pickFromPool belowPool rng1
  let (topV, rng3) := pickFromPool topNonContPool rng2
  let (boolBad, rng4) := pickFromPool boolNonIntPool rng3
  let case0 :=
    if shape = 0 then
      mkCase s!"fuzz/shape-{shape}/taken-default" (mkIfjmpStack #[belowV] 1)
    else if shape = 1 then
      mkCase s!"fuzz/shape-{shape}/not-taken-default" (mkIfjmpStack #[belowV] 0)
    else if shape = 2 then
      mkRetAltProbeCase s!"fuzz/shape-{shape}/taken-retalt-skipped" 9 #[belowV]
    else if shape = 3 then
      mkRetAltProbeCase s!"fuzz/shape-{shape}/not-taken-retalt-exec" 0 #[belowV]
    else if shape = 4 then
      mkCase s!"fuzz/shape-{shape}/underflow-empty" #[]
    else if shape = 5 then
      mkCase s!"fuzz/shape-{shape}/underflow-one-item" #[belowV]
    else if shape = 6 then
      mkCase s!"fuzz/shape-{shape}/type-top-not-cont" #[intV 1, topV]
    else if shape = 7 then
      mkCase s!"fuzz/shape-{shape}/type-bool-not-int" #[boolBad, .cont (.quit 0)]
    else if shape = 8 then
      mkCase s!"fuzz/shape-{shape}/nan-bool-via-program"
        #[.cont (.quit 0)]
        #[.pushInt .nan, .xchg0 1, ifjmpInstr]
    else if shape = 9 then
      mkCase s!"fuzz/shape-{shape}/nan-bool-with-below-via-program"
        #[belowV, .cont (.quit 0)]
        #[.pushInt .nan, .xchg0 1, ifjmpInstr]
    else if shape = 10 then
      mkCase s!"fuzz/shape-{shape}/not-taken-trailing-add"
        (mkIfjmpStack #[intV 2, intV 3] 0)
        #[ifjmpInstr, .add]
    else
      mkCase s!"fuzz/shape-{shape}/taken-trailing-push-skipped"
        (mkIfjmpStack #[belowV] (-5))
        #[ifjmpInstr, .pushInt (.num 999)]
  let (tag, rng5) := randNat rng4 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

def suite : InstrSuite where
  id := ifjmpId
  unit := #[
    { name := "unit/direct/taken-and-not-taken-pop-contract"
      run := do
        let below : Array Value := #[.null, intV 9]
        expectOkStack "taken/pop-two-preserve-below"
          (runIfjmpDirect (mkIfjmpStack below 1 (.quit 7)))
          below
        expectOkStack "not-taken/pop-two-preserve-below"
          (runIfjmpDirect (mkIfjmpStack below 0 (.quit 7)))
          below }
    ,
    { name := "unit/raw/cc-transition-taken-vs-not-taken"
      run := do
        let ccInit : Continuation := .quit 111
        let takenCont : Continuation := .quit 7
        let (resTaken, stTaken) := runIfjmpRaw (mkIfjmpStack #[intV 3] 1 takenCont) ccInit
        match resTaken with
        | .error e =>
            throw (IO.userError s!"raw/taken: expected success, got {e}")
        | .ok _ =>
            if stTaken.stack != #[intV 3] then
              throw (IO.userError s!"raw/taken: stack mismatch {reprStr stTaken.stack}")
            else if stTaken.cc != takenCont then
              throw (IO.userError s!"raw/taken: expected cc={reprStr takenCont}, got {reprStr stTaken.cc}")
            else
              pure ()
        let (resNotTaken, stNotTaken) := runIfjmpRaw (mkIfjmpStack #[intV 4] 0 (.quit 7)) ccInit
        match resNotTaken with
        | .error e =>
            throw (IO.userError s!"raw/not-taken: expected success, got {e}")
        | .ok _ =>
            if stNotTaken.stack != #[intV 4] then
              throw (IO.userError s!"raw/not-taken: stack mismatch {reprStr stNotTaken.stack}")
            else if stNotTaken.cc != ccInit then
              throw (IO.userError s!"raw/not-taken: expected cc unchanged, got {reprStr stNotTaken.cc}")
            else
              pure () }
    ,
    { name := "unit/error/underflow-before-any-pop"
      run := do
        expectErr "underflow/empty" (runIfjmpDirect #[]) .stkUnd
        expectErr "underflow/one-cont" (runIfjmpDirect #[.cont (.quit 0)]) .stkUnd
        let singleton : Array Value := #[.null]
        let (res, st) := runIfjmpRaw singleton (.quit 9)
        match res with
        | .error .stkUnd =>
            if st.stack == singleton then
              pure ()
            else
              throw (IO.userError s!"underflow/singleton-mutated: got {reprStr st.stack}")
        | .error e =>
            throw (IO.userError s!"underflow/singleton: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "underflow/singleton: expected stkUnd, got success") }
    ,
    { name := "unit/error/type-at-pop-cont"
      run := do
        expectErr "type/top-null" (runIfjmpDirect #[intV 1, .null]) .typeChk
        expectErr "type/top-int" (runIfjmpDirect #[intV 1, intV 2]) .typeChk
        expectErr "type/top-cell" (runIfjmpDirect #[intV 1, .cell refCellA]) .typeChk
        expectErr "type/top-builder" (runIfjmpDirect #[intV 1, .builder Builder.empty]) .typeChk
        expectErr "type/top-slice" (runIfjmpDirect #[intV 1, .slice fullSliceA]) .typeChk
        expectErr "type/top-tuple" (runIfjmpDirect #[intV 1, .tuple #[]]) .typeChk }
    ,
    { name := "unit/error/pop-bool-after-pop-cont"
      run := do
        let (rType, sType) := runIfjmpRaw #[intV 77, .null, .cont (.quit 0)] (.quit 10)
        match rType with
        | .error .typeChk =>
            if sType.stack == #[intV 77] then
              pure ()
            else
              throw (IO.userError s!"type/pop-bool: stack mismatch {reprStr sType.stack}")
        | .error e =>
            throw (IO.userError s!"type/pop-bool: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "type/pop-bool: expected typeChk, got success")
        let (rNan, sNan) := runIfjmpRaw #[intV 88, .int .nan, .cont (.quit 0)] (.quit 10)
        match rNan with
        | .error .intOv =>
            if sNan.stack == #[intV 88] then
              pure ()
            else
              throw (IO.userError s!"nan/pop-bool: stack mismatch {reprStr sNan.stack}")
        | .error e =>
            throw (IO.userError s!"nan/pop-bool: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "nan/pop-bool: expected intOv, got success") }
    ,
    { name := "unit/regression/taken-jump-enforces-nargs-underflow"
      run := do
        let ccInit : Continuation := .quit 123
        let contNeed2 : Continuation := mkOrdCont 2 #[]
        let (res, st) := runIfjmpRaw (mkIfjmpStack #[intV 5] 1 contNeed2) ccInit
        match res with
        | .error .stkUnd =>
            if st.stack != #[intV 5] then
              throw (IO.userError s!"nargs-underflow: stack mismatch {reprStr st.stack}")
            else if st.cc != ccInit then
              throw (IO.userError s!"nargs-underflow: cc should remain unchanged, got {reprStr st.cc}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"nargs-underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "nargs-underflow: expected stkUnd, got success") }
    ,
    { name := "unit/regression/taken-jump-applies-captured-stack"
      run := do
        let contCaptured : Continuation := mkOrdCont 1 #[intV 42]
        let (res, st) := runIfjmpRaw (mkIfjmpStack #[.null, intV 99] 1 contCaptured) (.quit 55)
        match res with
        | .error e =>
            throw (IO.userError s!"captured-stack: expected success, got {e}")
        | .ok _ =>
            if st.stack != #[intV 42, intV 99] then
              throw (IO.userError s!"captured-stack: expected [42,99], got {reprStr st.stack}")
            else if st.cc != contCaptured then
              throw (IO.userError s!"captured-stack: expected cc=contCaptured, got {reprStr st.cc}")
            else
              pure () }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfjmpDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/match-ifjmp"
          (runIfjmpDispatchFallback ifjmpInstr (mkIfjmpStack #[] 0 (.quit 0)))
          #[] }
  ]
  oracle := #[
    mkRetAltProbeCase "taken/flag-1/retalt-skipped" 1,
    mkRetAltProbeCase "taken/flag-neg1/retalt-skipped" (-1),
    mkRetAltProbeCase "taken/flag-42/retalt-skipped" 42,
    mkRetAltProbeCase "taken/flag-min257/retalt-skipped" minInt257,
    mkCase "taken/deep/default-preserve-null-int"
      (mkIfjmpStack #[.null, intV 9] 1),
    mkPushProbeCase "taken/deep/push-skipped" 1 777 #[intV (-7)],
    mkCase "taken/below-cell-preserved"
      (mkIfjmpStack #[.cell refCellA] 5),
    mkCase "taken/below-builder-preserved"
      (mkIfjmpStack #[.builder Builder.empty] 5),
    mkCase "taken/below-tuple-preserved"
      (mkIfjmpStack #[.tuple #[]] 5),
    mkCase "taken/below-slice-preserved"
      (mkIfjmpStack #[.slice fullSliceA] 5),
    mkCase "taken/two-trailing-ops-skipped"
      (mkIfjmpStack #[intV 3] 1)
      #[ifjmpInstr, .pushInt (.num 12), .retAlt],
    mkCase "taken/large-flag-still-true"
      (mkIfjmpStack #[] (pow2 255)),

    mkRetAltProbeCase "not-taken/flag-0/retalt-exec" 0,
    mkPushProbeCase "not-taken/flag-0/push-exec" 0 777,
    mkCase "not-taken/default-pop-two"
      (mkIfjmpStack #[] 0),
    mkCase "not-taken/deep/default-preserve"
      (mkIfjmpStack #[.null, intV 9] 0),
    mkPushProbeCase "not-taken/deep/push-exec" 0 333 #[.null, intV 9],
    mkCase "not-taken/below-cell-preserved"
      (mkIfjmpStack #[.cell refCellB] 0),
    mkCase "not-taken/below-builder-preserved"
      (mkIfjmpStack #[.builder Builder.empty] 0),
    mkCase "not-taken/below-tuple-preserved"
      (mkIfjmpStack #[.tuple #[]] 0),
    mkCase "not-taken/below-slice-preserved"
      (mkIfjmpStack #[.slice fullSliceB] 0),
    mkCase "not-taken/below-maxint-preserved"
      (mkIfjmpStack #[intV maxInt257] 0),
    mkCase "not-taken/below-minplus1-preserved"
      (mkIfjmpStack #[intV (minInt257 + 1)] 0),
    mkCase "not-taken/trailing-add-exec"
      (mkIfjmpStack #[intV 2, intV 3] 0)
      #[ifjmpInstr, .add],

    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "underflow/one-cont" #[.cont (.quit 0)],
    mkCase "type/top-null-not-cont" #[intV 1, .null],
    mkCase "type/top-int-not-cont" #[intV 1, intV 2],
    mkCase "type/top-cell-not-cont" #[intV 1, .cell refCellA],
    mkCase "type/top-builder-not-cont" #[intV 1, .builder Builder.empty],
    mkCase "type/top-slice-not-cont" #[intV 1, .slice fullSliceA],
    mkCase "type/top-tuple-not-cont" #[intV 1, .tuple #[]],

    mkCase "type/bool-null-under-cont" #[.null, .cont (.quit 0)],
    mkCase "type/bool-cell-under-cont" #[.cell refCellA, .cont (.quit 0)],
    mkCase "type/bool-builder-under-cont" #[.builder Builder.empty, .cont (.quit 0)],
    mkCase "type/bool-slice-under-cont" #[.slice fullSliceA, .cont (.quit 0)],
    mkCase "type/bool-tuple-under-cont" #[.tuple #[], .cont (.quit 0)],
    mkCase "intov/bool-nan-via-program"
      #[.cont (.quit 0)]
      #[.pushInt .nan, .xchg0 1, ifjmpInstr],
    mkCase "intov/bool-nan-with-below-via-program"
      #[intV 9, .cont (.quit 0)]
      #[.pushInt .nan, .xchg0 1, ifjmpInstr],

    mkCase "gas/exact-cost-succeeds"
      (mkIfjmpStack #[] 1)
      #[.pushInt (.num ifjmpSetGasExact), .tonEnvOp .setGasLimit, ifjmpInstr],
    mkCase "gas/exact-minus-one-out-of-gas"
      (mkIfjmpStack #[] 1)
      #[.pushInt (.num ifjmpSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifjmpInstr]
  ]
  fuzz := #[
    { seed := 2026021103
      count := 320
      gen := genIfjmpFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.IFJMP
