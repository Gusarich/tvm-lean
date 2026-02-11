import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.UNTILENDBRK

/-!
UNTILENDBRK branch map (Lean + C++ reference):
- Lean audited files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.untilEnd true`)
  - `TvmLean/Semantics/Step/Step.lean` (`.untilBody` runtime branches)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (`childStep` `.untilBody` mirror)
- C++ audited files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_until_end` with `brk=true`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::until`, `UntilCont::jump/_w`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `c1_envelope_if`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_bool`)

Handler branches (`.contExt (.untilEnd true)`):
1. dispatch vs fallback to `next`
2. capture path: `body := extract_cc(0)` from current continuation tail
3. BRK capture path: `after := c1_envelope_if(true, get_c0())` and `c1` update
4. install path:
   - `body.hasC0` => jump body directly
   - otherwise => install `.untilBody body after` in `c0`, jump body

Runtime continuation branches (`.untilBody` / `UntilCont`):
- bool decode: underflow / type / intov / false / true
- false path: body has/no `c0` split
- true path: jump to `after` plus jump-time `nargs` underflow checks
- deterministic error order: bool decode errors precede jump-time arg checks
-/

private def untilEndBrkId : InstrId := { name := "UNTILENDBRK" }

private def untilEndBrkInstr : Instr := .contExt (.untilEnd true)

private def dispatchSentinel : Int := 64231

private def markerA : Int := 47

private def markerB : Int := -19

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def cellB : Cell := Cell.mkOrdinary (natToBits 0x3c 8) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA

private def sliceB : Slice := Slice.ofCell cellB

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def defaultCc : Continuation :=
  mkOrdCont

private def bodyHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 31337) }
    OrdCdata.empty

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

private def runUntilEndBrkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt untilEndBrkInstr stack

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runUntilEndBrkRaw
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
  (execInstrFlowLoopExt untilEndBrkInstr (pure ())).run st0

private def runUntilBodyStep
    (stack : Array Value)
    (body after : Continuation)
    (c0 : Continuation := .quit 0) : StepResult :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := .untilBody body after }
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

private def expectExcContinue (label : String) (res : StepResult) (expected : Excno) : IO Unit := do
  let st ← expectContinue label res
  if st.cc != st.regs.c2 then
    throw (IO.userError s!"{label}: expected cc to jump to c2, got {reprStr st.cc}")
  let expectedStack : Array Value := #[intV 0, intV expected.toInt]
  if st.stack != expectedStack then
    throw (IO.userError
      s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st.stack}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[untilEndBrkInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := untilEndBrkId
    program := program
    initStack := stack
    fuel := fuel }

private def progBodyPush (b : Int) : Array Instr :=
  #[untilEndBrkInstr, .pushInt (.num b)]

private def progBodyPushPair (x b : Int) : Array Instr :=
  #[untilEndBrkInstr, .pushInt (.num x), .pushInt (.num b)]

private def progBodyNull : Array Instr :=
  #[untilEndBrkInstr, .pushNull]

private def progBodyNaN : Array Instr :=
  #[untilEndBrkInstr, .pushInt .nan]

private def progBodyRetAlt : Array Instr :=
  #[untilEndBrkInstr, .retAlt]

private def progBodyRet : Array Instr :=
  #[untilEndBrkInstr, .ret]

private def progSetC0Quit1 (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, untilEndBrkInstr] ++ body

private def progSetC0Nargs (n : Int) (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, untilEndBrkInstr] ++ body

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, intV (-3)]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell cellA, .slice sliceB, .builder Builder.empty, .tuple #[]]

def suite : InstrSuite where
  id := untilEndBrkId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-untilendbrk"
          (runLoopExtFallback untilEndBrkInstr #[])
          #[] }
    ,
    { name := "unit/state/extract-cc0-and-brk-envelope"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let weirdCc : Continuation :=
          .ordinary bodySlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66) }
            { stack := #[intV 3], nargs := 2 }

        let st ← expectRawOk "extract-cc0/brk"
          (runUntilEndBrkRaw #[] weirdCc (.quit 5) (.quit 6))

        match st.regs.c0 with
        | .untilBody body after =>
            if st.cc != body then
              throw (IO.userError s!"extract-cc0/brk: expected cc=body, got {reprStr st.cc}")
            else
              match body with
              | .ordinary code saved cregs cdata =>
                  if code != bodySlice then
                    throw (IO.userError s!"extract-cc0/brk: body.code mismatch {reprStr code}")
                  else if saved != .quit 0 then
                    throw (IO.userError
                      s!"extract-cc0/brk: expected body.saved=quit0, got {reprStr saved}")
                  else if !(cregsEmpty cregs) then
                    throw (IO.userError
                      s!"extract-cc0/brk: expected empty body cregs, got {reprStr cregs}")
                  else if !(cdataEmpty cdata) then
                    throw (IO.userError "extract-cc0/brk: expected empty body cdata")
                  else
                    match after, st.regs.c1 with
                    | .envelope extA cregsA cdataA, .envelope extB cregsB cdataB =>
                        if extA != .quit 5 then
                          throw (IO.userError s!"extract-cc0/brk: after ext mismatch {reprStr extA}")
                        else if extB != extA then
                          throw (IO.userError s!"extract-cc0/brk: c1 ext mismatch {reprStr extB}")
                        else if cregsA.c0 != some (.quit 5) then
                          throw (IO.userError
                            s!"extract-cc0/brk: after c0 capture mismatch {reprStr cregsA.c0}")
                        else if cregsA.c1 != some (.quit 6) then
                          throw (IO.userError
                            s!"extract-cc0/brk: after c1 capture mismatch {reprStr cregsA.c1}")
                        else if cregsB.c0 != cregsA.c0 ||
                            cregsB.c1 != cregsA.c1 ||
                            cregsB.c2 != cregsA.c2 ||
                            cregsB.c3 != cregsA.c3 ||
                            cregsB.c4 != cregsA.c4 ||
                            cregsB.c5 != cregsA.c5 ||
                            cregsB.c7 != cregsA.c7 then
                          throw (IO.userError "extract-cc0/brk: expected c1 to equal installed after envelope")
                        else if !(cdataEmpty cdataA) || !(cdataEmpty cdataB) then
                          throw (IO.userError "extract-cc0/brk: expected empty cdata in envelope")
                        else
                          pure ()
                    | _, _ =>
                        throw (IO.userError
                          s!"extract-cc0/brk: expected envelope after/c1, got after={reprStr after}, c1={reprStr st.regs.c1}")
              | _ =>
                  throw (IO.userError s!"extract-cc0/brk: expected ordinary body, got {reprStr body}")
        | _ =>
            throw (IO.userError s!"extract-cc0/brk: expected c0=untilBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/brk-define-only-preserves-existing-after-c0-c1"
      run := do
        let afterRaw : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0)
            { OrdCregs.empty with c0 := some (.quit 123), c1 := some (.quit 124) }
            OrdCdata.empty

        let st ← expectRawOk "brk/define-only"
          (runUntilEndBrkRaw #[] defaultCc afterRaw (.quit 6))

        match st.regs.c0 with
        | .untilBody _ after =>
            match after, st.regs.c1 with
            | .ordinary _ _ cregsA _, .ordinary _ _ cregsB _ =>
                if cregsA.c0 != some (.quit 123) then
                  throw (IO.userError s!"brk/define-only: after c0 changed to {reprStr cregsA.c0}")
                else if cregsA.c1 != some (.quit 124) then
                  throw (IO.userError s!"brk/define-only: after c1 changed to {reprStr cregsA.c1}")
                else if cregsB.c0 != cregsA.c0 || cregsB.c1 != cregsA.c1 then
                  throw (IO.userError "brk/define-only: c1 continuation does not preserve saved c0/c1")
                else
                  pure ()
            | _, _ =>
                throw (IO.userError
                  s!"brk/define-only: expected ordinary after/c1, got after={reprStr after}, c1={reprStr st.regs.c1}")
        | _ =>
            throw (IO.userError s!"brk/define-only: expected c0=untilBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/errors/non-ordinary-cc-ordering"
      run := do
        let st ← expectRawErr "non-ordinary-cc/type-before-envelope"
          (runUntilEndBrkRaw #[intV 9, .null] (.quit 7) (.quit 5) (.quit 6)) .typeChk
        if st.stack != #[intV 9, .null] then
          throw (IO.userError s!"non-ordinary-cc/type-before-envelope: stack changed to {reprStr st.stack}")
        if st.regs.c0 != .quit 5 then
          throw (IO.userError s!"non-ordinary-cc/type-before-envelope: c0 changed to {reprStr st.regs.c0}")
        if st.regs.c1 != .quit 6 then
          throw (IO.userError s!"non-ordinary-cc/type-before-envelope: c1 changed to {reprStr st.regs.c1}") }
    ,
    { name := "unit/step/untilbody-false-reinstalls-loop-when-body-has-no-c0"
      run := do
        let body : Continuation := .quit 5
        let after : Continuation := .quit 17
        let marker : Continuation := .quit 61
        let st ← expectContinue "step/false/no-c0" (runUntilBodyStep #[intV 0] body after marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/false/no-c0: expected empty stack, got {reprStr st.stack}")
        if st.cc != body then
          throw (IO.userError s!"step/false/no-c0: expected cc=body, got {reprStr st.cc}")
        if st.regs.c0 != .untilBody body after then
          throw (IO.userError
            s!"step/false/no-c0: expected c0 reinstalled untilBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/untilbody-false-keeps-c0-when-body-has-c0"
      run := do
        let marker : Continuation := .quit 62
        let after : Continuation := .quit 17
        let st ← expectContinue "step/false/has-c0" (runUntilBodyStep #[intV 0] bodyHasC0 after marker)
        if st.stack != #[] then
          throw (IO.userError s!"step/false/has-c0: expected empty stack, got {reprStr st.stack}")
        if st.cc != bodyHasC0 then
          throw (IO.userError s!"step/false/has-c0: expected cc=bodyHasC0, got {reprStr st.cc}")
        if st.regs.c0 != marker then
          throw (IO.userError
            s!"step/false/has-c0: expected c0 unchanged={reprStr marker}, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/step/untilbody-true-jumps-to-after-and-restores-saved-c0"
      run := do
        let after : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 77) OrdCregs.empty OrdCdata.empty
        let st ← expectContinue "step/true" (runUntilBodyStep #[intV 1] (.quit 9) after (.quit 88))
        let expectedCc : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        if st.stack != #[] then
          throw (IO.userError s!"step/true: expected empty stack, got {reprStr st.stack}")
        if st.regs.c0 != .quit 77 then
          throw (IO.userError s!"step/true: expected c0=quit77, got {reprStr st.regs.c0}")
        if st.cc != expectedCc then
          throw (IO.userError s!"step/true: expected cc={reprStr expectedCc}, got {reprStr st.cc}") }
    ,
    { name := "unit/step/pop-bool-errors-and-after-nargs-underflow"
      run := do
        expectExcContinue "step/pop-bool/underflow"
          (runUntilBodyStep #[] (.quit 9) (.quit 17))
          .stkUnd
        expectExcContinue "step/pop-bool/type"
          (runUntilBodyStep #[.null] (.quit 9) (.quit 17))
          .typeChk
        expectExcContinue "step/pop-bool/intov"
          (runUntilBodyStep #[.int .nan] (.quit 9) (.quit 17))
          .intOv

        let afterNeedArg : Continuation :=
          .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := 1 }
        expectExcContinue "step/after-nargs/underflow"
          (runUntilBodyStep #[intV 1] (.quit 9) afterNeedArg)
          .stkUnd }
    ,
    { name := "unit/order/bool-decode-errors-before-after-nargs-check"
      run := do
        let afterNeedArg : Continuation :=
          .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := 1 }

        expectExcContinue "order/bool-type-before-nargs"
          (runUntilBodyStep #[.null] (.quit 9) afterNeedArg)
          .typeChk
        expectExcContinue "order/bool-intov-before-nargs"
          (runUntilBodyStep #[.int .nan] (.quit 9) afterNeedArg)
          .intOv }
  ]
  oracle := #[
    -- Baseline terminating body: push bool true.
    mkCase "ok/basic/empty" #[] (progBodyPush 1),
    mkCase "ok/basic/int-noise" #[intV 7] (progBodyPush 1),
    mkCase "ok/basic/null-noise" #[.null] (progBodyPush 1),
    mkCase "ok/basic/cell-noise" #[.cell cellA] (progBodyPush 1),
    mkCase "ok/basic/slice-noise" #[.slice sliceA] (progBodyPush 1),
    mkCase "ok/basic/builder-noise" #[.builder Builder.empty] (progBodyPush 1),
    mkCase "ok/basic/tuple-empty-noise" #[.tuple #[]] (progBodyPush 1),
    mkCase "ok/basic/mixed-a" (noiseA ++ #[intV 9]) (progBodyPush 1),
    mkCase "ok/basic/mixed-b" (noiseB ++ #[.null]) (progBodyPush 1),
    mkCase "ok/basic/max-int257" #[intV maxInt257] (progBodyPush 1),
    mkCase "ok/basic/min-int257" #[intV minInt257] (progBodyPush 1),
    mkCase "ok/basic/deep-long" noiseLong (progBodyPush 1),
    mkCase "ok/basic/deep-long-plus" (noiseLong ++ #[intV 42]) (progBodyPush 1),

    -- Body can leave data below the consumed terminating bool.
    mkCase "ok/body/push-marker-then-true" #[] (progBodyPushPair markerA 1),
    mkCase "ok/body/push-neg-marker-then-true" #[.null] (progBodyPushPair markerB 1),
    mkCase "ok/body/push-two-markers-then-true" #[]
      #[untilEndBrkInstr, .pushInt (.num 4), .pushInt (.num (-2)), .pushInt (.num 1)],
    mkCase "ok/body/push-null-then-true" #[.cell cellA]
      #[untilEndBrkInstr, .pushNull, .pushInt (.num 1)],

    -- Body explicit returns / break behavior.
    mkCase "ok/body/retalt" #[] progBodyRetAlt,
    mkCase "ok/body/retalt-with-noise" #[intV 5, .null] progBodyRetAlt,
    mkCase "ok/body/ret-with-preseeded-true" #[intV 1] progBodyRet,
    mkCase "ok/body/ret-with-preseeded-negtrue" #[intV (-1)] progBodyRet,
    mkCase "ok/body/ret-with-preseeded-large" #[intV 123456789] progBodyRet,
    mkCase "err/body/ret-with-preseeded-null" #[.null] progBodyRet,
    mkCase "err/body/ret-with-preseeded-cell" #[.cell cellA] progBodyRet,
    mkCase "err/body/ret-with-preseeded-slice" #[.slice sliceA] progBodyRet,
    mkCase "err/body/ret-with-preseeded-builder" #[.builder Builder.empty] progBodyRet,
    mkCase "err/body/ret-with-preseeded-tuple" #[.tuple #[]] progBodyRet,
    mkCase "err/body/ret-with-preseeded-cont" #[.cont (.quit 0)] progBodyRet,

    -- After-continuation shaping through c0 before UNTILENDBRK.
    mkCase "ok/after/c0-quit1" #[] (progSetC0Quit1 #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-quit1-with-noise" #[intV 17] (progSetC0Quit1 #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-nargs0" #[] (progSetC0Nargs 0 #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-nargs1-success" #[intV 44] (progSetC0Nargs 1 #[.pushInt (.num 1)]),
    mkCase "err/after/c0-nargs1-underflow" #[] (progSetC0Nargs 1 #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-nargs2-success" #[intV 11, intV 22] (progSetC0Nargs 2 #[.pushInt (.num 1)]),
    mkCase "err/after/c0-nargs2-underflow" #[intV 11] (progSetC0Nargs 2 #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-nargs3-success" #[intV 1, intV 2, intV 3] (progSetC0Nargs 3 #[.pushInt (.num 1)]),
    mkCase "err/after/c0-nargs3-underflow" #[intV 1, intV 2] (progSetC0Nargs 3 #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-nargs1-success-with-noise" #[.null, intV 73] (progSetC0Nargs 1 #[.pushInt (.num 1)]),
    mkCase "err/after/c0-nargs2-underflow-with-noise" #[.null] (progSetC0Nargs 2 #[.pushInt (.num 1)]),

    -- pop_bool and runtime-decode errors in until-body.
    mkCase "err/body-empty-underflow" #[] #[untilEndBrkInstr],
    mkCase "err/body-empty-underflow-with-noise" #[.null] #[untilEndBrkInstr],
    mkCase "err/body-null-type" #[] progBodyNull,
    mkCase "err/body-null-type-with-noise" #[intV 3, .cell cellA] progBodyNull,
    mkCase "err/body-nan-intov" #[] progBodyNaN,
    mkCase "err/body-nan-intov-with-noise" #[.slice sliceA] progBodyNaN
  ]
  fuzz := #[ mkReplayOracleFuzzSpec untilEndBrkId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.UNTILENDBRK
