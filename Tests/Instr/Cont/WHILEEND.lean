import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.WHILEEND

/-!
WHILEEND / WHILEENDBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.whileEnd brk`)
  - `TvmLean/Semantics/Step/Step.lean` (`.whileCond` / `.whileBody` runtime behavior)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (child VM runtime parity)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_while_end`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::loop_while`, `WhileCont::jump[_w]`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `c1_envelope_if`)

Branch map covered:
1. Dispatch branch (`.contExt (.whileEnd brk)` handled vs fallback to `next`).
2. Entry pop branch (`pop_cont` underflow/type/pop-order).
3. Body capture branch (`exec_while_end` uses `extract_cc(0)`, so current `cc` must be ordinary).
4. Loop install branch (`VmState::loop_while`): install `.whileCond` into `c0` only when `cond.hasC0 = false`.
5. BRK after-cont branch (`c1_envelope_if(brk, get_c0())`).
6. Runtime continuation branches (`WhileCont`):
   - `whileCond`: bool true/false, plus `body.hasC0` split;
   - `whileBody`: `cond.hasC0` split.
-/

private def whileEndId : InstrId := { name := "WHILEEND" }

private def whileEndInstr : Instr := .contExt (.whileEnd false)

private def whileEndBrkInstr : Instr := .contExt (.whileEnd true)

private def q0 : Value := .cont (.quit 0)

private def dispatchSentinel : Int := 59241

private def tailMarker : Int := 991

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def cellB : Cell := Cell.mkOrdinary (natToBits 0x3c 8) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA

private def sliceB : Slice := Slice.ofCell cellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, intV (-3)]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell cellA, .slice sliceB, .builder Builder.empty, .tuple #[]]

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def defaultCc : Continuation :=
  mkOrdCont

private def cregsEmpty (cregs : OrdCregs) : Bool :=
  cregs.c0.isNone &&
  cregs.c1.isNone &&
  cregs.c2.isNone &&
  cregs.c3.isNone &&
  cregs.c4.isNone &&
  cregs.c5.isNone &&
  cregs.c7.isNone

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

private def condHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 777) }
    OrdCdata.empty

private def bodyHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 31337) }
    OrdCdata.empty

private def whileEndTailProgram : Array Instr :=
  #[whileEndInstr, .pushInt (.num tailMarker)]

private def whileEndBrkTailProgram : Array Instr :=
  #[whileEndBrkInstr, .pushInt (.num tailMarker)]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[whileEndInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := whileEndId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def progCondCtr0 (loopInstr : Instr) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, loopInstr] ++ tail

private def progCondCtr1 (loopInstr : Instr) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, loopInstr] ++ tail

private def progCondHasC0 (loopInstr : Instr) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushCtr 0, .setContCtr 0, loopInstr] ++ tail

private def runWhileEndDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt whileEndInstr stack

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runWhileEndRaw
    (instr : Instr)
    (stack : Array Value)
    (cc : Continuation := defaultCc)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowLoopExt instr (pure ())).run st0

private def runStepWith
    (stack : Array Value)
    (cc : Continuation)
    (c0 : Continuation := .quit 0) : StepResult :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := cc }
  VmState.step stubHost st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (res, st) := out
  match res with
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def expectContinue (label : String) (res : StepResult) : IO VmState := do
  match res with
  | .continue st => pure st
  | .halt code st =>
      throw (IO.userError s!"{label}: expected continue, got halt({code}) with state {reprStr st}")

private def whileEndGasExact : Int :=
  computeExactGasBudget whileEndInstr

private def whileEndGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne whileEndInstr

private def whileEndBrkGasExact : Int :=
  computeExactGasBudget whileEndBrkInstr

private def whileEndBrkGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne whileEndBrkInstr

private def whileEndOracleFamilies : Array String :=
  #[
    "ok/nonbrk/",
    "ok/brk/",
    "err/nonbrk/",
    "err/brk/",
    "gas/"
  ]

private def whileEndFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := whileEndOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := whileEndId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-whileend"
          (runLoopExtFallback whileEndInstr #[q0])
          #[]
        expectOkStack "dispatch/matched-whileendbrk"
          (runLoopExtFallback whileEndBrkInstr #[q0])
          #[] }
    ,
    { name := "unit/direct/errors-and-pop-order"
      run := do
        expectErr "underflow/empty" (runWhileEndDirect #[]) .stkUnd
        expectErr "type/top-int" (runWhileEndDirect #[intV 1]) .typeChk
        expectErr "type/top-null" (runWhileEndDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runWhileEndDirect #[.cell cellA]) .typeChk
        expectErr "type/top-slice" (runWhileEndDirect #[.slice sliceA]) .typeChk
        expectErr "type/top-builder" (runWhileEndDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runWhileEndDirect #[.tuple #[]]) .typeChk

        let stPop ← expectRawErr "pop-order/top-first"
          (runWhileEndRaw whileEndInstr #[q0, intV 9]) .typeChk
        if stPop.stack != #[q0] then
          throw (IO.userError s!"pop-order/top-first: expected stack #[q0], got {reprStr stPop.stack}")

        let stPopNonOrdCc ← expectRawErr "pop-order/nonordinary-cc-not-reached"
          (runWhileEndRaw whileEndInstr #[q0, intV 11] (.quit 7)) .typeChk
        if stPopNonOrdCc.stack != #[q0] then
          throw (IO.userError
            s!"pop-order/nonordinary-cc-not-reached: expected stack #[q0], got {reprStr stPopNonOrdCc.stack}") }
    ,
    { name := "unit/state/cond-without-c0-installs-whilecond"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let st ← expectRawOk "state/cond-no-c0"
          (runWhileEndRaw whileEndInstr #[q0] (mkOrdCont bodySlice) (.quit 44))

        if st.stack != #[] then
          throw (IO.userError s!"state/cond-no-c0: expected empty stack, got {reprStr st.stack}")
        else if st.cc != .quit 0 then
          throw (IO.userError s!"state/cond-no-c0: expected cc=quit0, got {reprStr st.cc}")
        else
          match st.regs.c0 with
          | .whileCond cond body after =>
              if cond != .quit 0 then
                throw (IO.userError s!"state/cond-no-c0: expected cond=quit0, got {reprStr cond}")
              else if after != .quit 44 then
                throw (IO.userError s!"state/cond-no-c0: expected after=quit44, got {reprStr after}")
              else
                match body with
                | .ordinary code saved cregs cdata =>
                    if code != bodySlice then
                      throw (IO.userError s!"state/cond-no-c0: body.code mismatch {reprStr code}")
                    else if saved != .quit 0 then
                      throw (IO.userError s!"state/cond-no-c0: body.saved mismatch {reprStr saved}")
                    else if !(cregsEmpty cregs) then
                      throw (IO.userError s!"state/cond-no-c0: expected empty cregs, got {reprStr cregs}")
                    else if !(cdataEmpty cdata) then
                      throw (IO.userError s!"state/cond-no-c0: expected empty cdata, got {reprStr cdata}")
                    else
                      pure ()
                | other =>
                    throw (IO.userError s!"state/cond-no-c0: expected ordinary body, got {reprStr other}")
          | other =>
              throw (IO.userError s!"state/cond-no-c0: expected c0=whileCond, got {reprStr other}") }
    ,
    { name := "unit/state/cond-with-c0-keeps-c0"
      run := do
        let marker : Continuation := .quit 42
        let st ← expectRawOk "state/cond-has-c0"
          (runWhileEndRaw whileEndInstr #[.cont condHasC0] defaultCc marker)
        if st.stack != #[] then
          throw (IO.userError s!"state/cond-has-c0: expected empty stack, got {reprStr st.stack}")
        else if st.cc != condHasC0 then
          throw (IO.userError s!"state/cond-has-c0: expected cc=condHasC0, got {reprStr st.cc}")
        else if st.regs.c0 != marker then
          throw (IO.userError s!"state/cond-has-c0: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/regression/whileend-uses-extract-cc0"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let weirdCc : Continuation :=
          .ordinary bodySlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66) }
            { stack := #[intV 3], nargs := 2 }

        let st ← expectRawOk "extract-cc0/regression"
          (runWhileEndRaw whileEndInstr #[q0] weirdCc (.quit 5))

        match st.regs.c0 with
        | .whileCond cond body after =>
            if cond != .quit 0 then
              throw (IO.userError s!"extract-cc0/regression: expected cond=quit0, got {reprStr cond}")
            else if after != .quit 5 then
              throw (IO.userError s!"extract-cc0/regression: expected after=quit5, got {reprStr after}")
            else
              match body with
              | .ordinary code saved cregs cdata =>
                  if code != bodySlice then
                    throw (IO.userError s!"extract-cc0/regression: body.code mismatch {reprStr code}")
                  else if saved != .quit 0 then
                    throw (IO.userError
                      s!"extract-cc0/regression: expected saved=quit0, got {reprStr saved}")
                  else if !(cregsEmpty cregs) then
                    throw (IO.userError
                      s!"extract-cc0/regression: expected empty cregs, got {reprStr cregs}")
                  else if !(cdataEmpty cdata) then
                    throw (IO.userError
                      s!"extract-cc0/regression: expected empty cdata, got {reprStr cdata}")
                  else
                    pure ()
              | other =>
                  throw (IO.userError
                    s!"extract-cc0/regression: expected ordinary body, got {reprStr other}")
        | other =>
            throw (IO.userError s!"extract-cc0/regression: expected c0=whileCond, got {reprStr other}") }
    ,
    { name := "unit/state/extractcc-requires-ordinary-current-cc"
      run := do
        let st ← expectRawErr "state/non-ordinary-cc"
          (runWhileEndRaw whileEndInstr #[q0] (.quit 13))
          .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError s!"state/non-ordinary-cc: expected empty stack after cond pop, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/brk/after-envelope-cond-without-c0"
      run := do
        let st ← expectRawOk "brk/cond-no-c0"
          (runWhileEndRaw whileEndBrkInstr #[q0] defaultCc (.quit 5) (.quit 6))
        if st.cc != .quit 0 then
          throw (IO.userError s!"brk/cond-no-c0: expected cc=quit0, got {reprStr st.cc}")
        else
          match st.regs.c0 with
          | .whileCond cond _ after =>
              if cond != .quit 0 then
                throw (IO.userError s!"brk/cond-no-c0: cond mismatch {reprStr cond}")
              else if st.regs.c1 != after then
                throw (IO.userError "brk/cond-no-c0: expected c1 to equal after continuation")
              else
                match after with
                | .envelope ext cregs cdata =>
                    if ext != .quit 5 then
                      throw (IO.userError s!"brk/cond-no-c0: envelope ext mismatch {reprStr ext}")
                    else if cregs.c0 != some (.quit 5) then
                      throw (IO.userError s!"brk/cond-no-c0: expected captured c0=quit5, got {reprStr cregs.c0}")
                    else if cregs.c1 != some (.quit 6) then
                      throw (IO.userError s!"brk/cond-no-c0: expected captured c1=quit6, got {reprStr cregs.c1}")
                    else if !(cdataEmpty cdata) then
                      throw (IO.userError s!"brk/cond-no-c0: expected empty cdata, got {reprStr cdata}")
                    else
                      pure ()
                | other =>
                    throw (IO.userError s!"brk/cond-no-c0: expected envelope after, got {reprStr other}")
          | other =>
              throw (IO.userError s!"brk/cond-no-c0: expected c0=whileCond, got {reprStr other}") }
    ,
    { name := "unit/brk/cond-with-c0-keeps-c0-and-updates-c1"
      run := do
        let marker0 : Continuation := .quit 501
        let marker1 : Continuation := .quit 601
        let st ← expectRawOk "brk/cond-has-c0"
          (runWhileEndRaw whileEndBrkInstr #[.cont condHasC0] defaultCc marker0 marker1)
        if st.cc != condHasC0 then
          throw (IO.userError s!"brk/cond-has-c0: cc mismatch {reprStr st.cc}")
        else if st.regs.c0 != marker0 then
          throw (IO.userError s!"brk/cond-has-c0: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          match st.regs.c1 with
          | .envelope ext cregs cdata =>
              if ext != marker0 then
                throw (IO.userError s!"brk/cond-has-c0: envelope ext mismatch {reprStr ext}")
              else if cregs.c0 != some marker0 then
                throw (IO.userError s!"brk/cond-has-c0: expected captured c0 marker, got {reprStr cregs.c0}")
              else if cregs.c1 != some marker1 then
                throw (IO.userError s!"brk/cond-has-c0: expected captured c1 marker, got {reprStr cregs.c1}")
              else if !(cdataEmpty cdata) then
                throw (IO.userError s!"brk/cond-has-c0: expected empty cdata, got {reprStr cdata}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"brk/cond-has-c0: expected envelope in c1, got {reprStr other}") }
    ,
    { name := "unit/step/whilecond-true-body-no-c0-installs-whilebody"
      run := do
        let cond : Continuation := .quit 9
        let body : Continuation := .quit 5
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 61
        let st ← expectContinue "step/true/no-c0"
          (runStepWith #[intV 1] (.whileCond cond body after) marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/true/no-c0: expected empty stack, got {reprStr st.stack}")
        else if st.cc != body then
          throw (IO.userError s!"step/true/no-c0: expected cc=body, got {reprStr st.cc}")
        else if st.regs.c0 != .whileBody cond body after then
          throw (IO.userError s!"step/true/no-c0: expected c0=whileBody, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/step/whilecond-true-body-has-c0-keeps-c0"
      run := do
        let cond : Continuation := .quit 9
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 62
        let st ← expectContinue "step/true/has-c0"
          (runStepWith #[intV 1] (.whileCond cond bodyHasC0 after) marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/true/has-c0: expected empty stack, got {reprStr st.stack}")
        else if st.cc != bodyHasC0 then
          throw (IO.userError s!"step/true/has-c0: expected cc=bodyHasC0, got {reprStr st.cc}")
        else if st.regs.c0 != marker then
          throw (IO.userError s!"step/true/has-c0: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/step/whilecond-false-jumps-to-after-and-restores-saved-c0"
      run := do
        let after : Continuation := .ordinary (Slice.ofCell Cell.empty) (.quit 77) OrdCregs.empty OrdCdata.empty
        let st ← expectContinue "step/false/ordinary-after"
          (runStepWith #[intV 0] (.whileCond (.quit 9) (.quit 5) after) (.quit 88))
        let expectedCc : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        if st.stack != #[] then
          throw (IO.userError s!"step/false/ordinary-after: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c0 != .quit 77 then
          throw (IO.userError s!"step/false/ordinary-after: expected c0=quit77, got {reprStr st.regs.c0}")
        else if st.cc != expectedCc then
          throw (IO.userError s!"step/false/ordinary-after: expected cc={reprStr expectedCc}, got {reprStr st.cc}")
        else
          pure () }
    ,
    { name := "unit/step/whilecond-false-nonordinary-after-keeps-c0"
      run := do
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 88
        let st ← expectContinue "step/false/nonordinary-after"
          (runStepWith #[intV 0] (.whileCond (.quit 9) (.quit 5) after) marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/false/nonordinary-after: expected empty stack, got {reprStr st.stack}")
        else if st.cc != after then
          throw (IO.userError s!"step/false/nonordinary-after: expected cc=after, got {reprStr st.cc}")
        else if st.regs.c0 != marker then
          throw (IO.userError s!"step/false/nonordinary-after: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/step/whilebody-cond-no-c0-installs-whilecond"
      run := do
        let cond : Continuation := .quit 3
        let body : Continuation := .quit 4
        let after : Continuation := .quit 5
        let st ← expectContinue "step/whilebody/no-c0"
          (runStepWith #[] (.whileBody cond body after) (.quit 99))
        if st.cc != cond then
          throw (IO.userError s!"step/whilebody/no-c0: expected cc=cond, got {reprStr st.cc}")
        else if st.regs.c0 != .whileCond cond body after then
          throw (IO.userError s!"step/whilebody/no-c0: expected c0=whileCond, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/step/whilebody-cond-has-c0-keeps-c0"
      run := do
        let marker : Continuation := .quit 123
        let st ← expectContinue "step/whilebody/has-c0"
          (runStepWith #[] (.whileBody condHasC0 (.quit 4) (.quit 5)) marker)
        if st.cc != condHasC0 then
          throw (IO.userError s!"step/whilebody/has-c0: expected cc=condHasC0, got {reprStr st.cc}")
        else if st.regs.c0 != marker then
          throw (IO.userError s!"step/whilebody/has-c0: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          pure () }
  ]
  oracle := #[
    -- WHILEEND direct success (`cond = quit0`): body/tail is not executed.
    mkCase "ok/nonbrk/direct/no-tail/empty" #[q0],
    mkCase "ok/nonbrk/direct/tail-skipped" #[q0] whileEndTailProgram,
    mkCase "ok/nonbrk/direct/no-tail/int-prefix" #[intV 7, q0],
    mkCase "ok/nonbrk/direct/no-tail/null-prefix" #[.null, q0],
    mkCase "ok/nonbrk/direct/no-tail/cell-prefix" #[.cell cellA, q0],
    mkCase "ok/nonbrk/direct/no-tail/slice-prefix" #[.slice sliceA, q0],
    mkCase "ok/nonbrk/direct/no-tail/builder-prefix" #[.builder Builder.empty, q0],
    mkCase "ok/nonbrk/direct/no-tail/tuple-prefix" #[.tuple #[], q0],
    mkCase "ok/nonbrk/direct/no-tail/noise-a" (noiseA ++ #[q0]),
    mkCase "ok/nonbrk/direct/no-tail/noise-b" (noiseB ++ #[q0]),
    mkCase "ok/nonbrk/direct/no-tail/noise-long" (noiseLong ++ #[q0]),
    mkCase "ok/nonbrk/direct/no-tail/two-conts-top-first" #[q0, q0],

    -- Build condition from control registers.
    mkCase "ok/nonbrk/ctr0/default" #[] (progCondCtr0 whileEndInstr),
    mkCase "ok/nonbrk/ctr0/tail-skipped" #[] (progCondCtr0 whileEndInstr #[.pushInt (.num 5)]),
    mkCase "ok/nonbrk/ctr1/default" #[] (progCondCtr1 whileEndInstr),
    mkCase "ok/nonbrk/ctr1/tail-skipped" #[] (progCondCtr1 whileEndInstr #[.pushInt (.num 6)]),

    -- Build condition with embedded c0 (`cond.hasC0 = true`).
    mkCase "ok/nonbrk/cond-has-c0/default" #[] (progCondHasC0 whileEndInstr),
    mkCase "ok/nonbrk/cond-has-c0/tail-skipped" #[] (progCondHasC0 whileEndInstr #[.pushInt (.num 8)]),
    mkCase "ok/nonbrk/cond-has-c0/prefix-null-int" #[.null, intV 3] (progCondHasC0 whileEndInstr),
    mkCase "ok/nonbrk/cond-has-c0/prefix-cell-slice" #[.cell cellA, .slice sliceB] (progCondHasC0 whileEndInstr),

    -- Non-BRK pop/type errors.
    mkCase "err/nonbrk/underflow-empty" #[],
    mkCase "err/nonbrk/type-top-int" #[intV 1],
    mkCase "err/nonbrk/type-top-null" #[.null],
    mkCase "err/nonbrk/type-top-cell" #[.cell cellA],
    mkCase "err/nonbrk/type-top-slice" #[.slice sliceA],
    mkCase "err/nonbrk/type-top-builder" #[.builder Builder.empty],
    mkCase "err/nonbrk/type-top-tuple" #[.tuple #[]],
    mkCase "err/nonbrk/pop-order-top-first" #[q0, intV 9],

    -- WHILEENDBRK success variants.
    mkCase "ok/brk/direct/no-tail/empty" #[q0] #[whileEndBrkInstr],
    mkCase "ok/brk/direct/tail-skipped" #[q0] whileEndBrkTailProgram,
    mkCase "ok/brk/direct/no-tail/noise-a" (noiseA ++ #[q0]) #[whileEndBrkInstr],
    mkCase "ok/brk/direct/no-tail/noise-b" (noiseB ++ #[q0]) #[whileEndBrkInstr],
    mkCase "ok/brk/ctr0/default" #[] (progCondCtr0 whileEndBrkInstr),
    mkCase "ok/brk/ctr1/default" #[] (progCondCtr1 whileEndBrkInstr),
    mkCase "ok/brk/cond-has-c0/default" #[] (progCondHasC0 whileEndBrkInstr),
    mkCase "ok/brk/cond-has-c0/prefix-null-int" #[.null, intV (-5)] (progCondHasC0 whileEndBrkInstr),

    -- BRK pop/type errors.
    mkCase "err/brk/underflow-empty" #[] #[whileEndBrkInstr],
    mkCase "err/brk/type-top-int" #[intV 2] #[whileEndBrkInstr],
    mkCase "err/brk/type-top-null" #[.null] #[whileEndBrkInstr],
    mkCase "err/brk/pop-order-top-first" #[q0, .cell cellA] #[whileEndBrkInstr],

    -- Deterministic gas boundaries.
    mkCase "gas/nonbrk/exact-succeeds" #[q0] #[whileEndInstr]
      (oracleGasLimitsExact whileEndGasExact),
    mkCase "gas/nonbrk/exact-minus-one-out-of-gas" #[q0] #[whileEndInstr]
      (oracleGasLimitsExact whileEndGasExactMinusOne),
    mkCase "gas/brk/exact-succeeds" #[q0] #[whileEndBrkInstr]
      (oracleGasLimitsExact whileEndBrkGasExact),
    mkCase "gas/brk/exact-minus-one-out-of-gas" #[q0] #[whileEndBrkInstr]
      (oracleGasLimitsExact whileEndBrkGasExactMinusOne)
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile whileEndId whileEndFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.WHILEEND
