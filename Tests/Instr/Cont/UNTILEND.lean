import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.UNTILEND

/-!
UNTILEND / UNTILENDBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.untilEnd brk`)
  - `TvmLean/Semantics/Step/Step.lean` (`.untilBody` runtime behavior)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (`.untilBody` child-vm mirror)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_until_end`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::until`, `UntilCont::jump[_w]`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `c1_envelope_if`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_bool`)

Branch map:
1. Dispatch: `.contExt (.untilEnd brk)` handled vs fallback to `next`.
2. Body capture: `extract_cc(0)` must build loop body from current continuation tail.
3. `brk` split: `after = get_c0()` vs `c1_envelope_if(true, get_c0())` (with `c1` update).
4. `VmState::until` split:
   - `body.has_c0` => jump body without installing loop continuation;
   - no `c0` => install `untilBody(body, after)` into `c0`, jump body.
5. Runtime `UntilCont` / `.untilBody` split:
   - pop bool `true` => jump `after`;
   - pop bool `false`, body has/no `c0` => jump body, optionally reinstall loop cont;
   - pop_bool errors => `stkUnd` / `typeChk` / `intOv`.
6. Runtime jump parity:
   - when `after` requires fixed nargs greater than current stack depth,
     C++ `adjust_jump_cont` throws `stk_und` before jumping.

Mismatch found and fixed:
- Lean `.untilBody` true-termination path did not enforce the C++
  `adjust_jump_cont` underflow check for `after.cdata.nargs > stack.depth`.
- Fixed in `Step.step` + `Runvm.childStep` mirror by throwing `.stkUnd`
  before switching to `after` when this predicate holds.
-/

private def untilEndId : InstrId := { name := "UNTILEND" }

private def untilEndInstr : Instr := .contExt (.untilEnd false)

private def untilEndBrkInstr : Instr := .contExt (.untilEnd true)

private def dispatchSentinel : Int := 65117

private def markerA : Int := 47

private def markerB : Int := -19

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def sliceA : Slice := Slice.ofCell cellA

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

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

private def runUntilEndRaw
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
    (program : Array Instr := #[untilEndInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := untilEndId
    program := program
    initStack := stack
    fuel := fuel }

private def progBodyPush (loopInstr : Instr) (b : Int) : Array Instr :=
  #[loopInstr, .pushInt (.num b)]

private def progBodyPushPair (loopInstr : Instr) (x b : Int) : Array Instr :=
  #[loopInstr, .pushInt (.num x), .pushInt (.num b)]

private def progBodyNull (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .pushNull]

private def progBodyNaN (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .pushInt .nan]

private def progBodyRetAlt (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .retAlt]

private def progBodyRet (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .ret]

private def progSetC0Quit1 (loopInstr : Instr) (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, loopInstr] ++ body

private def progSetC0Nargs (n : Int) (loopInstr : Instr) (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, loopInstr] ++ body

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, intV (-3)]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell cellA, .slice sliceA, .builder Builder.empty, .tuple #[]]

private def untilEndOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/body/",
    "ok/after/",
    "err/body-",
    "err/after/",
    "brk/ok/",
    "brk/err/"
  ]

private def untilEndSetGasExact : Int :=
  computeExactGasBudget untilEndInstr

private def untilEndSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne untilEndInstr

private def pickNoise (rng0 : StdGen) : Array Value × StdGen :=
  let (choice, rng1) := randNat rng0 0 2
  match choice with
  | 0 => (#[], rng1)
  | 1 => (noiseA, rng1)
  | _ => (noiseB, rng1)

private def pickProgramOk (rng0 : StdGen) (loopInstr : Instr) : Array Instr × StdGen :=
  let (choice, rng1) := randNat rng0 0 3
  match choice with
  | 0 =>
      let (x, rng2) := pickSigned257ish rng1
      (progBodyPush loopInstr x, rng2)
  | 1 =>
      let (x, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      (progBodyPushPair loopInstr x b, rng3)
  | 2 => (progBodyRetAlt loopInstr, rng1)
  | _ => (progBodyRet loopInstr, rng1)

private def genUntilEndFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  match shape with
  | 0 =>
      let (noise, rng2) := pickNoise rng1
      let (program, rng3) := pickProgramOk rng2 untilEndInstr
      (mkCase "fuzz/ok/basic" noise program, rng3)
  | 1 =>
      let (noise, rng2) := pickNoise rng1
      let (program, rng3) := pickProgramOk rng2 untilEndBrkInstr
      (mkCase "fuzz/ok/brk" noise program, rng3)
  | 2 =>
      (mkCase "fuzz/err/body-underflow" #[] #[untilEndInstr], rng1)
  | 3 =>
      (mkCase "fuzz/err/body-type" #[] (progBodyNull untilEndInstr), rng1)
  | 4 =>
      let (useExact, rng2) := randBool rng1
      let gas := if useExact then untilEndSetGasExact else untilEndSetGasExactMinusOne
      let name := if useExact then "fuzz/gas/exact" else "fuzz/gas/minus-one"
      let program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, untilEndInstr]
      (mkCase name #[] program, rng2)
  | 5 =>
      let (program, rng2) := pickProgramOk rng1 untilEndInstr
      (mkCase "fuzz/ok/body" #[] program, rng2)
  | _ =>
      let (program, rng2) := pickProgramOk rng1 untilEndBrkInstr
      (mkCase "fuzz/ok/body-brk" #[] program, rng2)

def suite : InstrSuite where
  id := untilEndId
  unit := #[
    { name := "unit/dispatch/untilend-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[.null, intV 5])
          #[.null, intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-untilend"
          (runLoopExtFallback untilEndInstr #[])
          #[] }
    ,
    { name := "unit/state/positive-branch-uses-extract-cc0"
      run := do
        let codeCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let codeSlice : Slice := Slice.ofCell codeCell
        let weirdCc : Continuation :=
          .ordinary codeSlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66) }
            { stack := #[intV 3], nargs := 2 }

        let st ← expectRawOk "extract-cc0/regression"
          (runUntilEndRaw untilEndInstr #[] weirdCc (.quit 5))

        match st.regs.c0 with
        | .untilBody body after =>
            if after != .quit 5 then
              throw (IO.userError s!"extract-cc0/regression: after mismatch {reprStr after}")
            else if st.cc != body then
              throw (IO.userError s!"extract-cc0/regression: cc != body ({reprStr st.cc})")
            else
              match body with
              | .ordinary code saved cregs cdata =>
                  if code != codeSlice then
                    throw (IO.userError s!"extract-cc0/regression: code mismatch {reprStr code}")
                  else if saved != .quit 0 then
                    throw (IO.userError
                      s!"extract-cc0/regression: expected saved=quit0, got {reprStr saved}")
                  else if !(cregsEmpty cregs) then
                    throw (IO.userError s!"extract-cc0/regression: expected empty cregs, got {reprStr cregs}")
                  else if !(cdataEmpty cdata) then
                    throw (IO.userError s!"extract-cc0/regression: expected empty cdata, got {reprStr cdata}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError
                    s!"extract-cc0/regression: expected ordinary body, got {reprStr body}")
        | other =>
            throw (IO.userError s!"extract-cc0/regression: expected c0=untilBody, got {reprStr other}") }
    ,
    { name := "unit/state/brk-c1-envelope-captures-c0-c1"
      run := do
        let st ← expectRawOk "brk/envelope"
          (runUntilEndRaw untilEndBrkInstr #[] defaultCc (.quit 5) (.quit 6))
        match st.regs.c0 with
        | .untilBody _ after =>
            if st.regs.c1 != after then
              throw (IO.userError "brk/envelope: expected c1 to equal after continuation")
            else
              match after with
              | .envelope ext cregs cdata =>
                  if ext != .quit 5 then
                    throw (IO.userError s!"brk/envelope: ext mismatch {reprStr ext}")
                  else if cregs.c0 != some (.quit 5) then
                    throw (IO.userError
                      s!"brk/envelope: expected captured c0=quit5, got {reprStr cregs.c0}")
                  else if cregs.c1 != some (.quit 6) then
                    throw (IO.userError
                      s!"brk/envelope: expected captured c1=quit6, got {reprStr cregs.c1}")
                  else if !(cdataEmpty cdata) then
                    throw (IO.userError "brk/envelope: expected empty cdata")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"brk/envelope: expected envelope after, got {reprStr after}")
        | _ =>
            throw (IO.userError s!"brk/envelope: expected c0=untilBody, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/errors/non-ordinary-cc-and-ordering"
      run := do
        let st0 ← expectRawErr "non-ordinary/type"
          (runUntilEndRaw untilEndInstr #[] (.quit 7) (.quit 9) (.quit 6)) .typeChk
        if st0.regs.c1 != .quit 6 then
          throw (IO.userError s!"non-ordinary/type: unexpected c1 mutation {reprStr st0.regs.c1}")

        let st1 ← expectRawErr "non-ordinary-brk/type-before-envelope"
          (runUntilEndRaw untilEndBrkInstr #[] (.quit 7) (.quit 9) (.quit 6)) .typeChk
        if st1.regs.c1 != .quit 6 then
          throw (IO.userError s!"non-ordinary-brk/type: c1 changed unexpectedly {reprStr st1.regs.c1}") }
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
  ]
  oracle := #[
    -- Base UNTILEND success: body pushes a terminating bool (non-zero).
    mkCase "ok/basic/empty" #[] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/int-noise" #[intV 7] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/null-noise" #[.null] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/cell-noise" #[.cell cellA] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/slice-noise" #[.slice sliceA] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/builder-noise" #[.builder Builder.empty] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/tuple-empty-noise" #[.tuple #[]] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/mixed-a" (noiseA ++ #[intV 9]) (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/mixed-b" (noiseB ++ #[.null]) (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/max-int257" #[intV maxInt257] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/min-int257" #[intV minInt257] (progBodyPush untilEndInstr 1),
    mkCase "ok/basic/deep-long" noiseLong (progBodyPush untilEndInstr 1),

    -- Body can leave additional stack data below the consumed bool.
    mkCase "ok/body/push-marker-then-true" #[] (progBodyPushPair untilEndInstr markerA 1),
    mkCase "ok/body/push-neg-marker-then-true" #[.null] (progBodyPushPair untilEndInstr markerB 1),

    -- Body explicit returns.
    mkCase "ok/body/retalt" #[] (progBodyRetAlt untilEndInstr),
    mkCase "ok/body/retalt-with-noise" #[intV 5, .null] (progBodyRetAlt untilEndInstr),
    mkCase "ok/body/ret-with-preseeded-true" #[intV 1] (progBodyRet untilEndInstr),
    mkCase "err/body/ret-with-preseeded-null" #[.null] (progBodyRet untilEndInstr),

    -- After-continuation shaping through c0.
    mkCase "ok/after/c0-quit1" #[] (progSetC0Quit1 untilEndInstr #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-nargs1-success" #[intV 44] (progSetC0Nargs 1 untilEndInstr #[.pushInt (.num 1)]),
    mkCase "err/after/c0-nargs1-underflow" #[] (progSetC0Nargs 1 untilEndInstr #[.pushInt (.num 1)]),
    mkCase "ok/after/c0-nargs2-success" #[intV 11, intV 22] (progSetC0Nargs 2 untilEndInstr #[.pushInt (.num 1)]),
    mkCase "err/after/c0-nargs2-underflow" #[intV 11] (progSetC0Nargs 2 untilEndInstr #[.pushInt (.num 1)]),

    -- pop_bool errors in until runtime.
    mkCase "err/body-empty-underflow" #[] #[untilEndInstr],
    mkCase "err/body-null-type" #[] (progBodyNull untilEndInstr),
    mkCase "err/body-nan-intov" #[] (progBodyNaN untilEndInstr),
    mkCase "err/body-null-type-with-noise" #[intV 3, .cell cellA] (progBodyNull untilEndInstr),

    -- UNTILENDBRK branch matrix.
    mkCase "brk/ok/basic" #[] (progBodyPush untilEndBrkInstr 1),
    mkCase "brk/ok/noise" (noiseA ++ #[.null]) (progBodyPush untilEndBrkInstr 1),
    mkCase "brk/ok/max-int257" #[intV maxInt257] (progBodyPush untilEndBrkInstr 1),
    mkCase "brk/ok/min-int257" #[intV minInt257] (progBodyPush untilEndBrkInstr 1),
    mkCase "brk/ok/body-marker" #[] (progBodyPushPair untilEndBrkInstr 99 1),
    mkCase "brk/ok/body-retalt" #[] (progBodyRetAlt untilEndBrkInstr),

    mkCase "brk/ok/after-c0-quit1" #[] (progSetC0Quit1 untilEndBrkInstr #[.pushInt (.num 1)]),
    mkCase "brk/ok/after-c0-nargs1-success" #[intV 73] (progSetC0Nargs 1 untilEndBrkInstr #[.pushInt (.num 1)]),
    mkCase "brk/err/after-c0-nargs1-underflow" #[] (progSetC0Nargs 1 untilEndBrkInstr #[.pushInt (.num 1)]),

    mkCase "brk/err/body-empty-underflow" #[] #[untilEndBrkInstr],
    mkCase "brk/err/body-null-type" #[] (progBodyNull untilEndBrkInstr),
    mkCase "brk/err/body-nan-intov" #[] (progBodyNaN untilEndBrkInstr)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr untilEndId
      count := 500
      gen := genUntilEndFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.UNTILEND
