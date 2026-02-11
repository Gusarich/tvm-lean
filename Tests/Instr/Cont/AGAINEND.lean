import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.AGAINEND

/-!
AGAINEND / AGAINENDBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.againEnd brk`)
  - `TvmLean/Semantics/Exec/Common.lean` (`extractCc`)
  - `TvmLean/Semantics/Step/Step.lean` (`.againBody` runtime behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_again_end`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`c1_save_set`, `extract_cc`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::again`, `AgainCont::jump[_w]`)

Branch map:
1. Dispatch: `.contExt (.againEnd brk)` handled vs fallback to `next`.
2. AGAINEND setup split:
   - `brk = false`: directly `extract_cc(0)` then `again(body)`.
   - `brk = true`: `c1_save_set()` first, then `extract_cc(0)`, then `again(body)`.
3. `extract_cc(0)` effect:
   - requires ordinary current continuation in Lean handler-level tests;
   - normalizes extracted body to ordinary continuation with `saved = quit(0)` and empty save-list/cdata.
4. Runtime `AgainCont` / `.againBody` split:
   - `body.has_c0 = true`  -> jump body; keep current `c0`.
   - `body.has_c0 = false` -> install `againBody(body)` into `c0`, then jump body.

Mismatch found and fixed:
- C++ executes `again(extract_cc(0))` for AGAINEND/AGAINENDBRK.
- Lean previously wrapped raw `st.cc` directly (`cc := .againBody st.cc`), skipping `extractCc 0`.
- Patched Lean `.againEnd` to:
  - run `c1SaveSet` first when `brk`;
  - run `VM.extractCc 0`;
  - set `cc := .againBody body`.
-/

private def againEndId : InstrId := { name := "AGAINEND" }

private def againEndInstr : Instr := .contExt (.againEnd false)

private def againEndBrkInstr : Instr := .contExt (.againEnd true)

private def dispatchSentinel : Int := 61733

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def fullSliceB : Slice := Slice.ofCell cellB

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

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

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runAgainEndRaw
    (instr : Instr)
    (stack : Array Value)
    (cc : Continuation := mkOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowLoopExt instr (pure ())).run st0

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

private def runAgainBodyStep
    (stack : Array Value)
    (body : Continuation)
    (c0 : Continuation := .quit 0) : StepResult :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := .againBody body }
  VmState.step stubHost st0

private def expectContinue (label : String) (res : StepResult) : IO VmState := do
  match res with
  | .continue st => pure st
  | .halt code st =>
      throw (IO.userError s!"{label}: expected continue, got halt({code}) with state {reprStr st}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[againEndInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := againEndId
    program := program
    initStack := stack
    fuel := fuel }

private def progRetAlt (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .retAlt]

private def progPushRetAlt (loopInstr : Instr) (n : Int) : Array Instr :=
  #[loopInstr, .pushInt (.num n), .retAlt]

private def progAddRetAlt (loopInstr : Instr) (a b : Int) : Array Instr :=
  #[loopInstr, .pushInt (.num a), .pushInt (.num b), .add, .retAlt]

private def progAddOnly (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .add]

private def progPopCtr0 (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .popCtr 0]

private def progSetC0FromC1ImplicitRet (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .pushCtr 1, .popCtr 0]

private def progSetC0FromC1Ret (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .pushCtr 1, .popCtr 0, .ret]

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice fullSliceB, .builder Builder.empty, .tuple #[]]

def suite : InstrSuite where
  id := againEndId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-againend"
          (runLoopExtFallback againEndInstr #[.null, intV 7])
          #[.null, intV 7] }
    ,
    { name := "unit/regression/extract-cc0-normalizes-body"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let weirdCc : Continuation :=
          .ordinary bodySlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66), c1 := some (.quit 88) }
            { stack := #[intV 3], nargs := 2 }

        let st ← expectRawOk "extract-cc0/nonbrk"
          (runAgainEndRaw againEndInstr #[intV 42] weirdCc (.quit 5) (.quit 6))

        if st.stack != #[intV 42] then
          throw (IO.userError s!"extract-cc0/nonbrk: stack mismatch {reprStr st.stack}")
        else if st.regs.c0 != .quit 5 then
          throw (IO.userError s!"extract-cc0/nonbrk: c0 changed unexpectedly to {reprStr st.regs.c0}")
        else if st.regs.c1 != .quit 6 then
          throw (IO.userError s!"extract-cc0/nonbrk: c1 changed unexpectedly to {reprStr st.regs.c1}")
        else
          match st.cc with
          | .againBody body =>
              match body with
              | .ordinary code saved cregs cdata =>
                  if code != bodySlice then
                    throw (IO.userError
                      s!"extract-cc0/nonbrk: code mismatch {reprStr code}")
                  else if saved != .quit 0 then
                    throw (IO.userError
                      s!"extract-cc0/nonbrk: expected saved=quit0, got {reprStr saved}")
                  else if !(cregsEmpty cregs) then
                    throw (IO.userError s!"extract-cc0/nonbrk: expected empty cregs, got {reprStr cregs}")
                  else if !(cdataEmpty cdata) then
                    throw (IO.userError s!"extract-cc0/nonbrk: expected empty cdata, got {reprStr cdata}")
                  else
                    pure ()
              | other =>
                  throw (IO.userError
                    s!"extract-cc0/nonbrk: expected ordinary extracted body, got {reprStr other}")
          | other =>
              throw (IO.userError s!"extract-cc0/nonbrk: expected againBody, got {reprStr other}") }
    ,
    { name := "unit/error/nonordinary-cc-no-brk-no-reg-mutation"
      run := do
        let st ← expectRawErr "nonordinary/no-brk"
          (runAgainEndRaw againEndInstr #[intV 11] (.quit 7) (.quit 5) (.quit 6))
          .typeChk
        if st.stack != #[intV 11] then
          throw (IO.userError s!"nonordinary/no-brk: stack mismatch {reprStr st.stack}")
        else if st.regs.c0 != .quit 5 then
          throw (IO.userError s!"nonordinary/no-brk: c0 changed unexpectedly {reprStr st.regs.c0}")
        else if st.regs.c1 != .quit 6 then
          throw (IO.userError s!"nonordinary/no-brk: c1 changed unexpectedly {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/error/brk-saves-c1-before-extract-typechk"
      run := do
        let st ← expectRawErr "nonordinary/brk"
          (runAgainEndRaw againEndBrkInstr #[intV 11] (.quit 7) (.quit 5) (.quit 6))
          .typeChk
        if st.stack != #[intV 11] then
          throw (IO.userError s!"nonordinary/brk: stack mismatch {reprStr st.stack}")
        else if st.regs.c1 != st.regs.c0 then
          throw (IO.userError "nonordinary/brk: expected c1 == c0 after c1SaveSet")
        else
          match st.regs.c0 with
          | .envelope ext cregs cdata =>
              if ext != .quit 5 then
                throw (IO.userError s!"nonordinary/brk: envelope ext mismatch {reprStr ext}")
              else if cregs.c1 != some (.quit 6) then
                throw (IO.userError
                  s!"nonordinary/brk: expected captured c1=quit6, got {reprStr cregs.c1}")
              else if cregs.c0.isSome then
                throw (IO.userError
                  s!"nonordinary/brk: expected no captured c0 in save-list, got {reprStr cregs.c0}")
              else if !(cdataEmpty cdata) then
                throw (IO.userError s!"nonordinary/brk: expected empty cdata, got {reprStr cdata}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"nonordinary/brk: expected envelope c0, got {reprStr other}") }
    ,
    { name := "unit/brk/success-c1-save-shape-and-extracted-body"
      run := do
        let st ← expectRawOk "brk/success"
          (runAgainEndRaw againEndBrkInstr #[.null] (mkOrdCont) (.quit 5) (.quit 6))
        if st.stack != #[.null] then
          throw (IO.userError s!"brk/success: stack mismatch {reprStr st.stack}")
        else if st.regs.c1 != st.regs.c0 then
          throw (IO.userError "brk/success: expected c1 == c0 after c1SaveSet")
        else
          match st.regs.c0 with
          | .envelope ext cregs _ =>
              if ext != .quit 5 then
                throw (IO.userError s!"brk/success: envelope ext mismatch {reprStr ext}")
              else if cregs.c1 != some (.quit 6) then
                throw (IO.userError s!"brk/success: expected captured c1=quit6, got {reprStr cregs.c1}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"brk/success: expected envelope c0, got {reprStr other}")
        match st.cc with
        | .againBody body =>
            match body with
            | .ordinary _ saved cregs cdata =>
                if saved != .quit 0 then
                  throw (IO.userError s!"brk/success: expected extracted saved=quit0, got {reprStr saved}")
                else if !(cregsEmpty cregs) then
                  throw (IO.userError s!"brk/success: expected empty body cregs, got {reprStr cregs}")
                else if !(cdataEmpty cdata) then
                  throw (IO.userError s!"brk/success: expected empty body cdata, got {reprStr cdata}")
                else
                  pure ()
            | other =>
                throw (IO.userError s!"brk/success: expected ordinary extracted body, got {reprStr other}")
        | other =>
            throw (IO.userError s!"brk/success: expected againBody cc, got {reprStr other}") }
    ,
    { name := "unit/runtime/againbody-no-c0-installs-self"
      run := do
        let body : Continuation := .quit 9
        let marker : Continuation := .quit 44
        let st ← expectContinue "runtime/no-c0"
          (runAgainBodyStep #[intV 7] body marker)
        if st.stack != #[intV 7] then
          throw (IO.userError s!"runtime/no-c0: stack mismatch {reprStr st.stack}")
        else if st.cc != body then
          throw (IO.userError s!"runtime/no-c0: expected cc=body, got {reprStr st.cc}")
        else if st.regs.c0 != .againBody body then
          throw (IO.userError
            s!"runtime/no-c0: expected c0=againBody(body), got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/runtime/againbody-has-c0-keeps-c0"
      run := do
        let marker : Continuation := .quit 45
        let st ← expectContinue "runtime/has-c0"
          (runAgainBodyStep #[intV 8] bodyHasC0 marker)
        if st.stack != #[intV 8] then
          throw (IO.userError s!"runtime/has-c0: stack mismatch {reprStr st.stack}")
        else if st.regs.c0 != marker then
          throw (IO.userError
            s!"runtime/has-c0: expected c0 unchanged={reprStr marker}, got {reprStr st.regs.c0}")
        else
          match st.cc with
          | .ordinary _ _ cregs _ =>
              if cregs.c0 != some (.quit 31337) then
                throw (IO.userError
                  s!"runtime/has-c0: expected body c0 marker 31337, got {reprStr cregs.c0}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"runtime/has-c0: expected ordinary body cc, got {reprStr other}") }
  ]
  oracle := #[
    -- AGAINEND (non-BRK): successful terminating bodies.
    mkCase "ok/nonbrk/retalt/empty" #[] (progRetAlt againEndInstr),
    mkCase "ok/nonbrk/retalt/noise-a" noiseA (progRetAlt againEndInstr),
    mkCase "ok/nonbrk/retalt/noise-b" noiseB (progRetAlt againEndInstr),
    mkCase "ok/nonbrk/push-retalt/pos" #[] (progPushRetAlt againEndInstr 7),
    mkCase "ok/nonbrk/push-retalt/neg" #[intV 3] (progPushRetAlt againEndInstr (-9)),
    mkCase "ok/nonbrk/push-retalt/deep" #[.builder Builder.empty, intV 4]
      (progPushRetAlt againEndInstr 11),
    mkCase "ok/nonbrk/add-retalt/basic" #[] (progAddRetAlt againEndInstr 2 3),
    mkCase "ok/nonbrk/add-retalt/mixed-sign" #[.null, intV 10]
      (progAddRetAlt againEndInstr (-2) 9),
    mkCase "ok/nonbrk/add-retalt/deep-cell" #[.cell cellB, intV 1]
      (progAddRetAlt againEndInstr 5 (-8)),
    mkCase "ok/nonbrk/setc0fromc1-implicitret/empty" #[]
      (progSetC0FromC1ImplicitRet againEndInstr),
    mkCase "ok/nonbrk/setc0fromc1-implicitret/deep" #[.cell cellA, intV 7]
      (progSetC0FromC1ImplicitRet againEndInstr),
    mkCase "ok/nonbrk/setc0fromc1-ret/empty" #[]
      (progSetC0FromC1Ret againEndInstr),
    mkCase "ok/nonbrk/setc0fromc1-ret/deep" #[.slice fullSliceB, .tuple #[]]
      (progSetC0FromC1Ret againEndInstr),
    mkCase "ok/nonbrk/retalt/trailing-skipped" #[]
      #[againEndInstr, .retAlt, .pushInt (.num 777)],
    mkCase "ok/nonbrk/push-retalt/trailing-skipped" #[]
      #[againEndInstr, .pushInt (.num 4), .retAlt, .pushInt (.num 8)],

    -- AGAINEND (non-BRK): deterministic body errors.
    mkCase "err/nonbrk/body-add-underflow-empty" #[] (progAddOnly againEndInstr),
    mkCase "err/nonbrk/body-add-underflow-one" #[intV 1] (progAddOnly againEndInstr),
    mkCase "err/nonbrk/body-add-type" #[.null, intV 1] (progAddOnly againEndInstr),
    mkCase "err/nonbrk/body-popctr-underflow" #[] (progPopCtr0 againEndInstr),
    mkCase "err/nonbrk/body-popctr-type" #[.null] (progPopCtr0 againEndInstr),

    -- AGAINENDBRK-related branch behavior from the same opcode family.
    mkCase "ok/brk/retalt/empty" #[] (progRetAlt againEndBrkInstr),
    mkCase "ok/brk/retalt/noise-a" noiseA (progRetAlt againEndBrkInstr),
    mkCase "ok/brk/retalt/noise-b" noiseB (progRetAlt againEndBrkInstr),
    mkCase "ok/brk/push-retalt/pos" #[] (progPushRetAlt againEndBrkInstr 6),
    mkCase "ok/brk/push-retalt/neg" #[intV 3] (progPushRetAlt againEndBrkInstr (-4)),
    mkCase "ok/brk/push-retalt/deep" #[.builder Builder.empty, intV 5]
      (progPushRetAlt againEndBrkInstr 13),
    mkCase "ok/brk/add-retalt/basic" #[] (progAddRetAlt againEndBrkInstr 1 2),
    mkCase "ok/brk/add-retalt/mixed-sign" #[.null, intV 10]
      (progAddRetAlt againEndBrkInstr (-2) 9),
    mkCase "ok/brk/add-retalt/deep-cell" #[.cell cellB, intV 1]
      (progAddRetAlt againEndBrkInstr 5 (-8)),
    mkCase "ok/brk/setc0fromc1-implicitret/empty" #[]
      (progSetC0FromC1ImplicitRet againEndBrkInstr),
    mkCase "ok/brk/setc0fromc1-implicitret/deep" #[.cell cellA, intV 7]
      (progSetC0FromC1ImplicitRet againEndBrkInstr),
    mkCase "ok/brk/setc0fromc1-ret/empty" #[]
      (progSetC0FromC1Ret againEndBrkInstr),
    mkCase "ok/brk/setc0fromc1-ret/deep" #[.slice fullSliceB, .tuple #[]]
      (progSetC0FromC1Ret againEndBrkInstr),
    mkCase "ok/brk/retalt/trailing-skipped" #[]
      #[againEndBrkInstr, .retAlt, .pushInt (.num 777)],
    mkCase "ok/brk/push-retalt/trailing-skipped" #[]
      #[againEndBrkInstr, .pushInt (.num 4), .retAlt, .pushInt (.num 8)],
    mkCase "err/brk/body-add-underflow-empty" #[] (progAddOnly againEndBrkInstr),
    mkCase "err/brk/body-add-underflow-one" #[intV 1] (progAddOnly againEndBrkInstr),
    mkCase "err/brk/body-add-type-deep" #[.cell cellA, .null, intV 1] (progAddOnly againEndBrkInstr),
    mkCase "err/brk/body-popctr-underflow" #[] (progPopCtr0 againEndBrkInstr),
    mkCase "err/brk/body-popctr-type" #[.null] (progPopCtr0 againEndBrkInstr)
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.AGAINEND
