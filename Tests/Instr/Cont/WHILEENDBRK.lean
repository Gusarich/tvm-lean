import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.WHILEENDBRK

/-!
WHILEENDBRK branch map (Lean + C++ reference):
- Lean:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.whileEnd true`)
  - `TvmLean/Semantics/Step/Step.lean` (`.whileCond` / `.whileBody`)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (child runtime parity)
- C++:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_while_end(..., brk=true)`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::loop_while`, `WhileCont::jump[_w]`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `c1_envelope_if`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_cont`, `pop_bool`)

Covered branches:
1. Dispatch branch (`.contExt (.whileEnd true)` vs fallback `next`).
2. Entry pop branch (`pop_cont` underflow/type/pop-order).
3. Ordering branch (`pop_cont` happens before `extract_cc(0)` ordinary-cc requirement).
4. BRK envelope branch (`after := c1_envelope_if(true, get_c0())`).
5. `loop_while` install branch (`cond.hasC0` gates c0 while-cont install).
6. Runtime while branches (`whileCond` true/false + `body.hasC0`; `whileBody` + `cond.hasC0`).
-/

private def whileEndBrkId : InstrId := { name := "WHILEENDBRK" }

private def whileEndBrkInstr : Instr := .contExt (.whileEnd true)

private def dispatchSentinel : Int := 60491

private def tailMarker : Int := 977

private def q0 : Value := .cont (.quit 0)

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

private def whileEndBrkTailProgram : Array Instr :=
  #[whileEndBrkInstr, .pushInt (.num tailMarker)]

private def progCondCtr0 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, whileEndBrkInstr] ++ tail

private def progCondCtr1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, whileEndBrkInstr] ++ tail

private def progCondHasC0 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushCtr 0, .setContCtr 0, whileEndBrkInstr] ++ tail

private def runWhileEndBrkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt whileEndBrkInstr stack

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runWhileEndBrkRaw
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
  (execInstrFlowLoopExt whileEndBrkInstr (pure ())).run st0

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

private def whileEndBrkGasExact : Int :=
  computeExactGasBudget whileEndBrkInstr

private def whileEndBrkGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne whileEndBrkInstr

private def whileEndBrkOracleFamilies : Array String :=
  #[
    "ok/direct/no-tail/",
    "ok/direct/tail-skipped/",
    "ok/ctr",
    "ok/cond-has-c0/",
    "err/underflow-",
    "err/type-",
    "err/pop-order-",
    "gas/"
  ]

private def whileEndBrkFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := whileEndBrkOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[whileEndBrkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := whileEndBrkId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

def suite : InstrSuite where
  id := whileEndBrkId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-whileendbrk"
          (runLoopExtFallback whileEndBrkInstr #[q0])
          #[] }
    ,
    { name := "unit/direct/errors-and-pop-order"
      run := do
        expectErr "underflow/empty" (runWhileEndBrkDirect #[]) .stkUnd
        expectErr "type/top-int" (runWhileEndBrkDirect #[intV 1]) .typeChk
        expectErr "type/top-null" (runWhileEndBrkDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runWhileEndBrkDirect #[.cell cellA]) .typeChk
        expectErr "type/top-slice" (runWhileEndBrkDirect #[.slice sliceA]) .typeChk
        expectErr "type/top-builder" (runWhileEndBrkDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runWhileEndBrkDirect #[.tuple #[]]) .typeChk

        let stPop ← expectRawErr "pop-order/top-first"
          (runWhileEndBrkRaw #[q0, intV 9]) .typeChk
        if stPop.stack != #[q0] then
          throw (IO.userError s!"pop-order/top-first: expected stack #[q0], got {reprStr stPop.stack}")

        let stPopNonOrdCc ← expectRawErr "pop-order/nonordinary-cc-not-reached"
          (runWhileEndBrkRaw #[q0, intV 11] (.quit 7)) .typeChk
        if stPopNonOrdCc.stack != #[q0] then
          throw (IO.userError
            s!"pop-order/nonordinary-cc-not-reached: expected stack #[q0], got {reprStr stPopNonOrdCc.stack}") }
    ,
    { name := "unit/state/extractcc-requires-ordinary-current-cc"
      run := do
        let st ← expectRawErr "state/non-ordinary-cc"
          (runWhileEndBrkRaw #[q0] (.quit 13))
          .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError s!"state/non-ordinary-cc: expected empty stack after cond pop, got {reprStr st.stack}") }
    ,
    { name := "unit/state/cond-without-c0-installs-whilecond-and-brk-envelope"
      run := do
        let st ← expectRawOk "state/cond-no-c0"
          (runWhileEndBrkRaw #[q0] defaultCc (.quit 5) (.quit 6))
        if st.stack != #[] then
          throw (IO.userError s!"state/cond-no-c0: expected empty stack, got {reprStr st.stack}")
        else
          match st.regs.c0 with
          | .whileCond cond body after =>
              if cond != .quit 0 then
                throw (IO.userError s!"state/cond-no-c0: cond mismatch {reprStr cond}")
              else if st.cc != .quit 0 then
                throw (IO.userError s!"state/cond-no-c0: expected cc=quit0, got {reprStr st.cc}")
              else
                match body with
                | .ordinary _ saved cregs cdata =>
                    if saved != .quit 0 then
                      throw (IO.userError s!"state/cond-no-c0: body.saved mismatch {reprStr saved}")
                    else if !(cregsEmpty cregs) then
                      throw (IO.userError s!"state/cond-no-c0: expected empty body cregs, got {reprStr cregs}")
                    else if !(cdataEmpty cdata) then
                      throw (IO.userError s!"state/cond-no-c0: expected empty body cdata, got {reprStr cdata}")
                    else
                      match after, st.regs.c1 with
                      | .envelope extA cregsA cdataA, .envelope extB cregsB cdataB =>
                          if extA != .quit 5 then
                            throw (IO.userError s!"state/cond-no-c0: envelope ext mismatch {reprStr extA}")
                          else if extB != extA then
                            throw (IO.userError s!"state/cond-no-c0: c1 ext mismatch {reprStr extB}")
                          else if cregsA.c0 != some (.quit 5) then
                            throw (IO.userError s!"state/cond-no-c0: after.c0 mismatch {reprStr cregsA.c0}")
                          else if cregsA.c1 != some (.quit 6) then
                            throw (IO.userError s!"state/cond-no-c0: after.c1 mismatch {reprStr cregsA.c1}")
                          else if cregsB.c0 != cregsA.c0 || cregsB.c1 != cregsA.c1 then
                            throw (IO.userError s!"state/cond-no-c0: c1 envelope mismatch {reprStr cregsB}")
                          else if !(cdataEmpty cdataA) || !(cdataEmpty cdataB) then
                            throw (IO.userError "state/cond-no-c0: expected empty envelope cdata")
                      | _, _ =>
                          throw (IO.userError
                            s!"state/cond-no-c0: expected envelope after/c1, got after={reprStr after} c1={reprStr st.regs.c1}")
                | other =>
                    throw (IO.userError s!"state/cond-no-c0: expected ordinary body, got {reprStr other}")
          | other =>
              throw (IO.userError s!"state/cond-no-c0: expected c0=whileCond, got {reprStr other}") }
    ,
    { name := "unit/state/cond-with-c0-keeps-c0-and-updates-c1"
      run := do
        let marker0 : Continuation := .quit 501
        let marker1 : Continuation := .quit 601
        let st ← expectRawOk "state/cond-has-c0"
          (runWhileEndBrkRaw #[.cont condHasC0] defaultCc marker0 marker1)
        if st.stack != #[] then
          throw (IO.userError s!"state/cond-has-c0: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c0 != marker0 then
          throw (IO.userError s!"state/cond-has-c0: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          match st.cc with
          | .ordinary _ _ cregs _ =>
              if cregs.c0 != some (.quit 777) then
                throw (IO.userError s!"state/cond-has-c0: expected cond.cc to retain embedded c0, got {reprStr cregs.c0}")
              else
                match st.regs.c1 with
                | .envelope ext cregs1 cdata =>
                    if ext != marker0 then
                      throw (IO.userError s!"state/cond-has-c0: envelope ext mismatch {reprStr ext}")
                    else if cregs1.c0 != some marker0 then
                      throw (IO.userError s!"state/cond-has-c0: expected captured c0 marker, got {reprStr cregs1.c0}")
                    else if cregs1.c1 != some marker1 then
                      throw (IO.userError s!"state/cond-has-c0: expected captured c1 marker, got {reprStr cregs1.c1}")
                    else if !(cdataEmpty cdata) then
                      throw (IO.userError s!"state/cond-has-c0: expected empty cdata, got {reprStr cdata}")
                | other =>
                    throw (IO.userError s!"state/cond-has-c0: expected envelope in c1, got {reprStr other}")
          | other =>
              throw (IO.userError s!"state/cond-has-c0: expected ordinary cond in cc, got {reprStr other}") }
    ,
    { name := "unit/state/extractcc0-body-shape-regression"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let weirdCc : Continuation :=
          .ordinary bodySlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66) }
            { stack := #[intV 3], nargs := 2 }
        let st ← expectRawOk "state/extract-cc0-shape"
          (runWhileEndBrkRaw #[q0] weirdCc (.quit 5) (.quit 6))
        match st.regs.c0 with
        | .whileCond _ body _ =>
            match body with
            | .ordinary code saved cregs cdata =>
                if code != bodySlice then
                  throw (IO.userError s!"state/extract-cc0-shape: code mismatch {reprStr code}")
                else if saved != .quit 0 then
                  throw (IO.userError s!"state/extract-cc0-shape: saved mismatch {reprStr saved}")
                else if !(cregsEmpty cregs) then
                  throw (IO.userError s!"state/extract-cc0-shape: expected empty cregs, got {reprStr cregs}")
                else if !(cdataEmpty cdata) then
                  throw (IO.userError s!"state/extract-cc0-shape: expected empty cdata, got {reprStr cdata}")
            | other =>
                throw (IO.userError s!"state/extract-cc0-shape: expected ordinary body, got {reprStr other}")
        | other =>
            throw (IO.userError s!"state/extract-cc0-shape: expected c0=whileCond, got {reprStr other}") }
    ,
    { name := "unit/state/brk-envelope-define-only-does-not-overwrite-existing-c0-c1"
      run := do
        let afterRaw : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0)
            { OrdCregs.empty with c0 := some (.quit 123), c1 := some (.quit 124) }
            OrdCdata.empty
        let st ← expectRawOk "state/brk-define-only"
          (runWhileEndBrkRaw #[.cont condHasC0] defaultCc afterRaw (.quit 999))
        if st.regs.c0 != afterRaw then
          throw (IO.userError s!"state/brk-define-only: expected c0 unchanged, got {reprStr st.regs.c0}")
        match st.regs.c1 with
        | .ordinary _ _ cregs _ =>
            if cregs.c0 != some (.quit 123) then
              throw (IO.userError s!"state/brk-define-only: c1.c0 overwritten unexpectedly {reprStr cregs.c0}")
            else if cregs.c1 != some (.quit 124) then
              throw (IO.userError s!"state/brk-define-only: c1.c1 overwritten unexpectedly {reprStr cregs.c1}")
            else
              pure ()
        | other =>
            throw (IO.userError s!"state/brk-define-only: expected ordinary c1, got {reprStr other}") }
    ,
    { name := "unit/step/whilecond-true-body-no-c0-installs-whilebody"
      run := do
        let cond : Continuation := .quit 9
        let body : Continuation := .quit 5
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 61
        let st ← expectContinue "step/whilecond-true/no-c0"
          (runStepWith #[intV 1] (.whileCond cond body after) marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-true/no-c0: expected empty stack, got {reprStr st.stack}")
        else if st.cc != body then
          throw (IO.userError s!"step/whilecond-true/no-c0: expected cc=body, got {reprStr st.cc}")
        else if st.regs.c0 != .whileBody cond body after then
          throw (IO.userError s!"step/whilecond-true/no-c0: expected c0=whileBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/whilecond-true-body-has-c0-keeps-c0"
      run := do
        let cond : Continuation := .quit 9
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 62
        let st ← expectContinue "step/whilecond-true/has-c0"
          (runStepWith #[intV 1] (.whileCond cond bodyHasC0 after) marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-true/has-c0: expected empty stack, got {reprStr st.stack}")
        else if st.cc != bodyHasC0 then
          throw (IO.userError s!"step/whilecond-true/has-c0: expected cc=bodyHasC0, got {reprStr st.cc}")
        else if st.regs.c0 != marker then
          throw (IO.userError s!"step/whilecond-true/has-c0: expected c0 unchanged, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/whilecond-false-envelope-after-keeps-c0"
      run := do
        let after : Continuation :=
          .envelope (.quit 17) { OrdCregs.empty with c0 := some (.quit 21), c1 := some (.quit 22) } OrdCdata.empty
        let marker : Continuation := .quit 88
        let st ← expectContinue "step/whilecond-false/envelope"
          (runStepWith #[intV 0] (.whileCond (.quit 9) (.quit 5) after) marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/whilecond-false/envelope: expected empty stack, got {reprStr st.stack}")
        else if st.cc != after then
          throw (IO.userError s!"step/whilecond-false/envelope: expected cc=after, got {reprStr st.cc}")
        else if st.regs.c0 != marker then
          throw (IO.userError s!"step/whilecond-false/envelope: expected c0 unchanged, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/whilecond-false-after-nargs-underflow-throws-stkund"
      run := do
        let after : Continuation :=
          .envelope (.quit 17) OrdCregs.empty { stack := #[], nargs := 2 }
        let st ← expectContinue "step/whilecond-false/nargs-underflow"
          (runStepWith #[intV 0] (.whileCond (.quit 9) (.quit 5) after) (.quit 88))
        if st.cc != .excQuit then
          throw (IO.userError s!"step/whilecond-false/nargs-underflow: expected cc=excQuit, got {reprStr st.cc}")
        else if st.stack != #[intV 0, intV Excno.stkUnd.toInt] then
          throw (IO.userError
            s!"step/whilecond-false/nargs-underflow: expected exception stack #[0,{Excno.stkUnd.toInt}], got {reprStr st.stack}") }
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
          throw (IO.userError s!"step/whilebody/no-c0: expected c0=whileCond, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/whilebody-cond-has-c0-keeps-c0"
      run := do
        let marker : Continuation := .quit 123
        let st ← expectContinue "step/whilebody/has-c0"
          (runStepWith #[] (.whileBody condHasC0 (.quit 4) (.quit 5)) marker)
        if st.cc != condHasC0 then
          throw (IO.userError s!"step/whilebody/has-c0: expected cc=condHasC0, got {reprStr st.cc}")
        else if st.regs.c0 != marker then
          throw (IO.userError s!"step/whilebody/has-c0: expected c0 unchanged, got {reprStr st.regs.c0}") }
  ]
  oracle := #[
    -- Direct WHILEENDBRK success variants.
    mkCase "ok/direct/no-tail/basic" #[q0],
    mkCase "ok/direct/no-tail/int-prefix" #[intV 7, q0],
    mkCase "ok/direct/no-tail/null-prefix" #[.null, q0],
    mkCase "ok/direct/no-tail/cell-prefix" #[.cell cellA, q0],
    mkCase "ok/direct/no-tail/slice-prefix" #[.slice sliceA, q0],
    mkCase "ok/direct/no-tail/builder-prefix" #[.builder Builder.empty, q0],
    mkCase "ok/direct/no-tail/tuple-prefix" #[.tuple #[], q0],
    mkCase "ok/direct/no-tail/max-int257-prefix" #[intV maxInt257, q0],
    mkCase "ok/direct/no-tail/min-int257-prefix" #[intV minInt257, q0],
    mkCase "ok/direct/no-tail/noise-a" (noiseA ++ #[q0]),
    mkCase "ok/direct/no-tail/noise-b" (noiseB ++ #[q0]),
    mkCase "ok/direct/no-tail/noise-long" (noiseLong ++ #[q0]),
    mkCase "ok/direct/no-tail/two-conts-top-first" #[q0, q0],
    mkCase "ok/direct/tail-skipped/basic" #[q0] whileEndBrkTailProgram,
    mkCase "ok/direct/tail-skipped/noise-a" (noiseA ++ #[q0]) whileEndBrkTailProgram,
    mkCase "ok/direct/tail-skipped/noise-b" (noiseB ++ #[q0]) whileEndBrkTailProgram,

    -- Build condition from control registers.
    mkCase "ok/ctr0/default" #[] (progCondCtr0),
    mkCase "ok/ctr0/tail-skipped" #[] (progCondCtr0 #[.pushInt (.num 5)]),
    mkCase "ok/ctr1/default" #[] (progCondCtr1),
    mkCase "ok/ctr1/tail-skipped" #[] (progCondCtr1 #[.pushInt (.num 6)]),

    -- Build condition with embedded c0 (`cond.hasC0 = true`).
    mkCase "ok/cond-has-c0/default" #[] (progCondHasC0),
    mkCase "ok/cond-has-c0/tail-skipped" #[] (progCondHasC0 #[.pushInt (.num 8)]),
    mkCase "ok/cond-has-c0/prefix-null-int" #[.null, intV 3] (progCondHasC0),
    mkCase "ok/cond-has-c0/prefix-cell-slice" #[.cell cellA, .slice sliceB] (progCondHasC0),
    mkCase "ok/cond-has-c0/noise-long" noiseLong (progCondHasC0),

    -- Pop/type errors and pop-order error.
    mkCase "err/underflow-empty" #[],
    mkCase "err/type-top-int" #[intV 1],
    mkCase "err/type-top-null" #[.null],
    mkCase "err/type-top-cell" #[.cell cellA],
    mkCase "err/type-top-slice" #[.slice sliceA],
    mkCase "err/type-top-builder" #[.builder Builder.empty],
    mkCase "err/type-top-tuple" #[.tuple #[]],
    mkCase "err/pop-order-top-first-int" #[q0, intV 9],
    mkCase "err/pop-order-top-first-null" #[q0, .null],
    mkCase "err/pop-order-top-first-cell" #[q0, .cell cellA],
    mkCase "err/pop-order-top-first-tuple" #[q0, .tuple #[]],

    -- Deterministic gas boundaries.
    mkCase "gas/exact-succeeds" #[q0] #[whileEndBrkInstr]
      (oracleGasLimitsExact whileEndBrkGasExact),
    mkCase "gas/exact-minus-one-out-of-gas" #[q0] #[whileEndBrkInstr]
      (oracleGasLimitsExact whileEndBrkGasExactMinusOne)
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile whileEndBrkId whileEndBrkFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.WHILEENDBRK
