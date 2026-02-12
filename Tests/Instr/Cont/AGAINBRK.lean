import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.AGAINBRK

/-!
AGAINBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.again true` setup path)
  - `TvmLean/Semantics/Step/Step.lean` (`.againBody` runtime continuation)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (`.againBody` child-vm path)
  - `TvmLean/Semantics/Exec/Common.lean` (`extractCc`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_again(..., brk=true)`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`AgainCont::jump/_w`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `jump_to`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_cont`)

Covered ordering and branches:
1. Dispatch: `.contExt (.again true)` handled vs fallback to `next`.
2. Setup (`exec_again(..., brk=true)` parity):
   - `extract_cc(3)` runs before any `pop_cont` check;
   - extracted continuation captures old `{c0,c1}` and resets `c0`;
   - then `pop_cont` underflow/type checks run.
3. Runtime `.againBody` parity with `AgainCont::jump/_w` + `jump_to`:
   - `body.hasC0` true: keep current `c0`, jump body;
   - `body.hasC0` false: install `c0 := againBody(body)` first, then jump body;
   - jump-time `nargs` underflow (`adjust_jump_cont`) throws `stkUnd`.
-/

private def againBrkId : InstrId := { name := "AGAINBRK" }

private def againBrkInstr : Instr := .contExt (.again true)

private def dispatchSentinel : Int := 88241

private def tailMarker : Int := 1701

private def kCont : Value := .cont (.quit 0)

private def refCellA : Cell := Cell.ofUInt 8 0xa5

private def refCellB : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def sliceA : Slice := Slice.ofCell refCellA

private def sliceB : Slice := Slice.ofCell refCellB

private def defaultOrdCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def bodyNoC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def bodyHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 31) }
    OrdCdata.empty

private def bodyNeedsTwoArgs : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := #[], nargs := 2 }

private def bodyNeedsTwoArgsHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 77) }
    { stack := #[], nargs := 2 }

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, .tuple #[]]

private def noiseLong : Array Value :=
  #[intV 1, .null, intV (-1), .cell refCellB, .slice sliceB, .builder Builder.empty, .tuple #[]]

private def againBrkTailPushProgram : Array Instr :=
  #[againBrkInstr, .pushInt (.num tailMarker)]

private def againBrkTailAddProgram : Array Instr :=
  #[againBrkInstr, .add]

private def againBrkTailRetAltProgram : Array Instr :=
  #[againBrkInstr, .retAlt]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[againBrkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := againBrkId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAgainBrkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt againBrkInstr stack

private def runAgainBrkDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runAgainBrkRaw
    (stack : Array Value)
    (cc : Continuation := defaultOrdCc)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowLoopExt againBrkInstr (pure ())).run st0

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

private def stepOnce (st : VmState) : StepResult :=
  VmState.step stubHost st

private def expectExtractCc3Shape
    (label : String)
    (captured : Continuation)
    (oldC0 oldC1 : Continuation)
    (expectedCode : Slice) : IO Unit := do
  match captured with
  | .ordinary code saved cregs cdata =>
      if code != expectedCode then
        throw (IO.userError s!"{label}: expected code {reprStr expectedCode}, got {reprStr code}")
      else if saved != .quit 0 then
        throw (IO.userError s!"{label}: expected saved=quit0, got {reprStr saved}")
      else if cregs.c0 != some oldC0 then
        throw (IO.userError s!"{label}: expected cregs.c0={reprStr oldC0}, got {reprStr cregs.c0}")
      else if cregs.c1 != some oldC1 then
        throw (IO.userError s!"{label}: expected cregs.c1={reprStr oldC1}, got {reprStr cregs.c1}")
      else if !cdata.stack.isEmpty ∨ cdata.nargs != -1 then
        throw (IO.userError s!"{label}: expected empty cdata stack and nargs=-1, got {reprStr cdata}")
      else
        pure ()
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary extract_cc(3) continuation, got {reprStr captured}")

private def againBrkSetGasExact : Int :=
  computeExactGasBudget againBrkInstr

private def againBrkSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne againBrkInstr

private def againBrkFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/no-tail/",
      "ok/tail-push-skipped/",
      "ok/tail-add-skipped/",
      "ok/tail-retalt-skipped/",
      "err/underflow/",
      "err/type/",
      "gas/"
    ]
    -- Bias toward branch/underflow/order stress while still including all mutation modes.
    mutationModes := #[0, 0, 0, 2, 2, 2, 3, 3, 1, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := againBrkId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runAgainBrkDispatchFallback .add #[intV 1])
          #[intV 1, intV dispatchSentinel]
        expectOkStack "dispatch/matched-againbrk"
          (runAgainBrkDispatchFallback againBrkInstr #[kCont])
          #[] }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runAgainBrkDirect #[]) .stkUnd
        expectErr "type/top-int" (runAgainBrkDirect #[intV 1]) .typeChk
        expectErr "type/top-null" (runAgainBrkDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runAgainBrkDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice" (runAgainBrkDirect #[.slice sliceA]) .typeChk
        expectErr "type/top-builder" (runAgainBrkDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty" (runAgainBrkDirect #[.tuple #[]]) .typeChk
        expectErr "order/top-before-below-cont" (runAgainBrkDirect #[kCont, intV 9]) .typeChk

        let oldC0 : Continuation := .quit 71
        let oldC1 : Continuation := .quit 72
        let stType ← expectRawErr "order/top-pop-before-type"
          (runAgainBrkRaw #[intV 77, .null] defaultOrdCc oldC0 oldC1) .typeChk
        if stType.stack != #[intV 77] then
          throw (IO.userError s!"order/top-pop-before-type: expected stack #[77], got {reprStr stType.stack}")
        else if stType.regs.c0 != .quit 0 then
          throw (IO.userError s!"order/top-pop-before-type: expected c0 reset to quit0, got {reprStr stType.regs.c0}")
        else
          expectExtractCc3Shape "order/top-pop-before-type/c1" stType.regs.c1 oldC0 oldC1 (Slice.ofCell Cell.empty) }
    ,
    { name := "unit/state/success-extractcc3-before-popcont"
      run := do
        let oldC0 : Continuation := .quit 61
        let oldC1 : Continuation := .quit 62
        let codeCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let code : Slice := Slice.ofCell codeCell
        let cc0 : Continuation := .ordinary code (.quit 17) OrdCregs.empty OrdCdata.empty
        let st ← expectRawOk "brk/success"
          (runAgainBrkRaw #[intV 5, .cont bodyNoC0] cc0 oldC0 oldC1)
        if st.stack != #[intV 5] then
          throw (IO.userError s!"brk/success: stack mismatch {reprStr st.stack}")
        else if st.cc != .againBody bodyNoC0 then
          throw (IO.userError s!"brk/success: expected cc=againBody(body), got {reprStr st.cc}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"brk/success: expected c0 reset to quit0, got {reprStr st.regs.c0}")
        else
          expectExtractCc3Shape "brk/success/c1-shape" st.regs.c1 oldC0 oldC1 code }
    ,
    { name := "unit/order/nonordinary-cc-before-popcont"
      run := do
        let oldC0 : Continuation := .quit 81
        let oldC1 : Continuation := .quit 82
        let st ← expectRawErr "brk/nonordinary-cc"
          (runAgainBrkRaw #[intV 11, .null] (.quit 7) oldC0 oldC1) .typeChk
        if st.stack != #[intV 11, .null] then
          throw (IO.userError s!"brk/nonordinary-cc: expected stack unchanged, got {reprStr st.stack}")
        else if st.regs.c0 != oldC0 then
          throw (IO.userError s!"brk/nonordinary-cc: expected c0 unchanged, got {reprStr st.regs.c0}")
        else if st.regs.c1 != oldC1 then
          throw (IO.userError s!"brk/nonordinary-cc: expected c1 unchanged, got {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/order/extract-before-popcont-errors"
      run := do
        let oldC0 : Continuation := .quit 91
        let oldC1 : Continuation := .quit 92
        let codeCell : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[]
        let code : Slice := Slice.ofCell codeCell
        let cc0 : Continuation := .ordinary code (.quit 19) OrdCregs.empty OrdCdata.empty

        let stType ← expectRawErr "brk/order/type-after-extract"
          (runAgainBrkRaw #[intV 13, .null] cc0 oldC0 oldC1) .typeChk
        if stType.stack != #[intV 13] then
          throw (IO.userError s!"brk/order/type-after-extract: expected stack #[13], got {reprStr stType.stack}")
        else if stType.regs.c0 != .quit 0 then
          throw (IO.userError s!"brk/order/type-after-extract: expected c0 reset, got {reprStr stType.regs.c0}")
        else
          expectExtractCc3Shape "brk/order/type-after-extract/c1" stType.regs.c1 oldC0 oldC1 code

        let stUnd ← expectRawErr "brk/order/underflow-after-extract"
          (runAgainBrkRaw #[] cc0 oldC0 oldC1) .stkUnd
        if stUnd.stack != #[] then
          throw (IO.userError s!"brk/order/underflow-after-extract: expected empty stack, got {reprStr stUnd.stack}")
        else if stUnd.regs.c0 != .quit 0 then
          throw (IO.userError s!"brk/order/underflow-after-extract: expected c0 reset, got {reprStr stUnd.regs.c0}")
        else
          expectExtractCc3Shape "brk/order/underflow-after-extract/c1" stUnd.regs.c1 oldC0 oldC1 code }
    ,
    { name := "unit/runtime/againBody-branches"
      run := do
        let base := VmState.initial Cell.empty

        let stNoC00 : VmState :=
          { base with
            regs := { base.regs with c0 := .quit 101 }
            cc := .againBody bodyNoC0 }
        let stNoC0 ← expectContinue "runtime/no-c0" (stepOnce stNoC00)
        if stNoC0.cc != bodyNoC0 then
          throw (IO.userError s!"runtime/no-c0: expected cc=bodyNoC0, got {reprStr stNoC0.cc}")
        else if stNoC0.regs.c0 != .againBody bodyNoC0 then
          throw (IO.userError s!"runtime/no-c0: expected c0=againBody(body), got {reprStr stNoC0.regs.c0}")
        else
          pure ()

        let stHasC00 : VmState :=
          { base with
            regs := { base.regs with c0 := .quit 102 }
            cc := .againBody bodyHasC0 }
        let stHasC0 ← expectContinue "runtime/has-c0" (stepOnce stHasC00)
        if stHasC0.cc != bodyHasC0 then
          throw (IO.userError s!"runtime/has-c0: expected cc=bodyHasC0, got {reprStr stHasC0.cc}")
        else if stHasC0.regs.c0 != .quit 102 then
          throw (IO.userError s!"runtime/has-c0: expected c0 unchanged, got {reprStr stHasC0.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/runtime/againBody-underflow-noC0-installs-loop-c0-first"
      run := do
        let st0 : VmState :=
          { (VmState.initial Cell.empty) with
            stack := #[intV 1]
            regs := { (VmState.initial Cell.empty).regs with c0 := .quit 111 }
            cc := .againBody bodyNeedsTwoArgs }
        let st ← expectContinue "runtime/nargs-underflow/no-c0" (stepOnce st0)
        if st.cc != st0.regs.c2 then
          throw (IO.userError s!"runtime/nargs-underflow/no-c0: expected cc=c2, got {reprStr st.cc}")
        else if st.stack != #[intV 0, intV Excno.stkUnd.toInt] then
          throw (IO.userError
            s!"runtime/nargs-underflow/no-c0: expected stack #[0,{Excno.stkUnd.toInt}], got {reprStr st.stack}")
        else if st.regs.c0 != .againBody bodyNeedsTwoArgs then
          throw (IO.userError
            s!"runtime/nargs-underflow/no-c0: expected c0=againBody(body) before exception, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/runtime/againBody-underflow-hasC0-keeps-c0"
      run := do
        let st0 : VmState :=
          { (VmState.initial Cell.empty) with
            stack := #[intV 1]
            regs := { (VmState.initial Cell.empty).regs with c0 := .quit 112 }
            cc := .againBody bodyNeedsTwoArgsHasC0 }
        let st ← expectContinue "runtime/nargs-underflow/has-c0" (stepOnce st0)
        if st.cc != st0.regs.c2 then
          throw (IO.userError s!"runtime/nargs-underflow/has-c0: expected cc=c2, got {reprStr st.cc}")
        else if st.stack != #[intV 0, intV Excno.stkUnd.toInt] then
          throw (IO.userError
            s!"runtime/nargs-underflow/has-c0: expected stack #[0,{Excno.stkUnd.toInt}], got {reprStr st.stack}")
        else if st.regs.c0 != .quit 112 then
          throw (IO.userError
            s!"runtime/nargs-underflow/has-c0: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/runtime/againBody-nargs-ok"
      run := do
        let bodyNeedsOneArgNoC0 : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := #[], nargs := 1 }
        let bodyNeedsOneArgHasC0 : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0)
            { OrdCregs.empty with c0 := some (.quit 55) }
            { stack := #[], nargs := 1 }

        let stNoC00 : VmState :=
          { (VmState.initial Cell.empty) with
            stack := #[intV 9]
            regs := { (VmState.initial Cell.empty).regs with c0 := .quit 121 }
            cc := .againBody bodyNeedsOneArgNoC0 }
        let stNoC0 ← expectContinue "runtime/nargs-ok/no-c0" (stepOnce stNoC00)
        if stNoC0.cc != bodyNeedsOneArgNoC0 then
          throw (IO.userError s!"runtime/nargs-ok/no-c0: cc mismatch {reprStr stNoC0.cc}")
        else if stNoC0.regs.c0 != .againBody bodyNeedsOneArgNoC0 then
          throw (IO.userError s!"runtime/nargs-ok/no-c0: expected loop c0, got {reprStr stNoC0.regs.c0}")
        else
          pure ()

        let stHasC00 : VmState :=
          { (VmState.initial Cell.empty) with
            stack := #[intV 10]
            regs := { (VmState.initial Cell.empty).regs with c0 := .quit 122 }
            cc := .againBody bodyNeedsOneArgHasC0 }
        let stHasC0 ← expectContinue "runtime/nargs-ok/has-c0" (stepOnce stHasC00)
        if stHasC0.cc != bodyNeedsOneArgHasC0 then
          throw (IO.userError s!"runtime/nargs-ok/has-c0: cc mismatch {reprStr stHasC0.cc}")
        else if stHasC0.regs.c0 != .quit 122 then
          throw (IO.userError s!"runtime/nargs-ok/has-c0: expected c0 unchanged, got {reprStr stHasC0.regs.c0}")
        else
          pure () }
  ]
  oracle := #[
    -- Direct AGAINBRK with oracle-encodable continuation token K=quit(0).
    mkCase "ok/no-tail/empty-prefix" #[kCont],
    mkCase "ok/no-tail/int-prefix" #[intV 7, kCont],
    mkCase "ok/no-tail/null-prefix" #[.null, kCont],
    mkCase "ok/no-tail/cell-prefix" #[.cell refCellA, kCont],
    mkCase "ok/no-tail/slice-prefix" #[.slice sliceA, kCont],
    mkCase "ok/no-tail/builder-prefix" #[.builder Builder.empty, kCont],
    mkCase "ok/no-tail/tuple-empty-prefix" #[.tuple #[], kCont],
    mkCase "ok/no-tail/mixed-a" (noiseA ++ #[kCont]),
    mkCase "ok/no-tail/mixed-b" (noiseB ++ #[kCont]),
    mkCase "ok/no-tail/max-int257" #[intV maxInt257, kCont],
    mkCase "ok/no-tail/min-int257" #[intV minInt257, kCont],
    mkCase "ok/no-tail/deep-long" (noiseLong ++ #[kCont]),
    mkCase "ok/no-tail/int-pair" #[intV 0, intV 1, kCont],
    mkCase "ok/no-tail/cell-slice-builder" #[.cell refCellB, .slice sliceB, .builder Builder.empty, kCont],
    mkCase "ok/no-tail/all-basic-tokens" #[.null, .tuple #[], .builder Builder.empty, intV (-5), .cell refCellA, kCont],

    -- Tail instructions should be skipped after AGAINBRK transfers control.
    mkCase "ok/tail-push-skipped/basic" #[kCont] againBrkTailPushProgram,
    mkCase "ok/tail-push-skipped/int-prefix" #[intV 4, kCont] againBrkTailPushProgram,
    mkCase "ok/tail-push-skipped/mixed-prefix" #[.null, .cell refCellB, kCont] againBrkTailPushProgram,
    mkCase "ok/tail-push-skipped/max-int257" #[intV maxInt257, kCont] againBrkTailPushProgram,
    mkCase "ok/tail-push-skipped/deep-long" (noiseLong ++ #[kCont]) againBrkTailPushProgram,
    mkCase "ok/tail-add-skipped/two-ints" #[intV 2, intV 3, kCont] againBrkTailAddProgram,
    mkCase "ok/tail-add-skipped/with-noise" #[.null, intV 10, intV (-6), .cell refCellA, kCont] againBrkTailAddProgram,
    mkCase "ok/tail-add-skipped/min-max" #[intV minInt257, intV maxInt257, kCont] againBrkTailAddProgram,
    mkCase "ok/tail-retalt-skipped/basic" #[kCont] againBrkTailRetAltProgram,
    mkCase "ok/tail-retalt-skipped/deep" #[.builder Builder.empty, .tuple #[], intV 7, kCont] againBrkTailRetAltProgram,
    mkCase "ok/tail-retalt-skipped/mixed" #[.slice sliceA, .null, intV 15, kCont] againBrkTailRetAltProgram,
    mkCase "ok/tail-push-skipped/noise-a" (noiseA ++ #[kCont]) againBrkTailPushProgram,
    mkCase "ok/tail-push-skipped/noise-b" (noiseB ++ #[kCont]) againBrkTailPushProgram,
    mkCase "ok/tail-add-skipped/noise-long" (noiseLong ++ #[intV 8, intV 9, kCont]) againBrkTailAddProgram,
    mkCase "ok/tail-retalt-skipped/noise-a" (noiseA ++ #[kCont]) againBrkTailRetAltProgram,

    -- pop_cont underflow/type behavior (extract_cc side effects are covered in unit tests).
    mkCase "err/underflow/empty" #[],
    mkCase "err/type/top-int" #[intV 1],
    mkCase "err/type/top-null" #[.null],
    mkCase "err/type/top-cell" #[.cell refCellA],
    mkCase "err/type/top-slice" #[.slice sliceA],
    mkCase "err/type/top-builder" #[.builder Builder.empty],
    mkCase "err/type/top-tuple-empty" #[.tuple #[]],
    mkCase "err/type/top-int-with-below-cont" #[kCont, intV 5],
    mkCase "err/type/top-null-with-below-int" #[intV 7, .null],
    mkCase "err/type/top-cell-with-deep-noise" #[.null, intV 7, .cell refCellA],

    -- Deterministic gas cliff.
    mkCase "gas/exact-succeeds" #[kCont]
      #[.pushInt (.num againBrkSetGasExact), .tonEnvOp .setGasLimit, againBrkInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[kCont]
      #[.pushInt (.num againBrkSetGasExactMinusOne), .tonEnvOp .setGasLimit, againBrkInstr]
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile againBrkId againBrkFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.AGAINBRK
