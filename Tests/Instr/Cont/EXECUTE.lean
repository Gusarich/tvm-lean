import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.EXECUTE

/-
EXECUTE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Execute.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popCont`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.call`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd8 -> .execute`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.execute -> 0xd8`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_execute`, cp0 registration `0xd8`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::call`)

Branch map covered by this suite:
- decode: canonical `0xd8` success vs truncated-prefix `invOpcode`;
- handler dispatch: `.execute` handled vs non-`.execute` fallthrough to `next`;
- stack/type: empty stack (`stkUnd`) and top-not-cont (`typeChk`) paths;
- control-flow: successful `VM.call` transfer (tail opcodes skipped), with `quit(0/1/11)` targets;
- call semantics: unit-only checks for return-cont install, prebound-c0 jump reduction,
  captured-stack application, and callee `nargs` underflow;
- gas-relevant branch: deterministic `SETGASLIMIT` exact vs exact-minus-one around `EXECUTE`.

Oracle harness note:
- Oracle stack tokens can encode only continuation `K = quit(0)`, so non-`quit(0)` targets are
  exercised by program-side `PUSHCTR` setup and richer continuation-shape checks stay in unit tests.
-/

private def executeId : InstrId := { name := "EXECUTE" }

private def executeInstr : Instr := .execute

private def executeOpcode : Nat := 0xd8

private def dispatchSentinel : Int := 43043

private def tailMarker : Int := 7201

private def q0 : Value := .cont (.quit 0)

private def refCellA : Cell := Cell.ofUInt 8 0xa5

private def refCellB : Cell := Cell.mkOrdinary (natToBits 0x15 5) #[refCellA]

private def sliceA : Slice := Slice.ofCell refCellA

private def noiseA : Array Value := #[.null, intV 7]

private def noiseB : Array Value := #[.cell refCellA, .builder Builder.empty]

private def noiseC : Array Value := #[.slice sliceA, .tuple #[]]

private def noiseD : Array Value := #[intV maxInt257, intV minInt257]

private def withQ0 (below : Array Value) : Array Value :=
  below ++ #[q0]

private def assembleOrPanic (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c => c
  | .error e => panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def executeCode : Cell :=
  Cell.mkOrdinary (natToBits executeOpcode 8) #[]

private def executeWithRefCode : Cell :=
  Cell.mkOrdinary (natToBits executeOpcode 8) #[refCellA]

private def truncated7Code : Cell :=
  -- First seven bits of 0xd8 (`1101100`).
  Cell.mkOrdinary (natToBits 0x6c 7) #[]

private def truncated7WithRefCode : Cell :=
  Cell.mkOrdinary (natToBits 0x6c 7) #[refCellA]

private def executeThenTruncatedCode : Cell :=
  Cell.mkOrdinary (natToBits executeOpcode 8 ++ natToBits 0x6c 7) #[]

private def truncatedThenExecuteCode : Cell :=
  Cell.mkOrdinary (natToBits 0x6c 7 ++ natToBits executeOpcode 8) #[]

private def twoExecuteCode : Cell :=
  Cell.mkOrdinary (natToBits executeOpcode 8 ++ natToBits executeOpcode 8) #[]

private def preboundC0Cont : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 23) }
    OrdCdata.empty

private def capturedStackCont : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty
    { stack := #[intV 91, .null], nargs := 1 }

private def needTwoArgsCont : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty
    { stack := #[], nargs := 2 }

private def runExecuteDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowExecute executeInstr stack

private def runExecuteDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowExecute instr (VM.push (intV dispatchSentinel)) stack

private def runExecuteRaw
    (stack : Array Value)
    (cc : Continuation := .quit 0) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc }
  (execInstrFlowExecute executeInstr (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  match res with
  | (.ok _, st) => pure st
  | (.error e, _) =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  match res with
  | (.error e, st) =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | (.ok _, st) =>
      throw (IO.userError
        s!"{label}: expected error {expected}, got success with state {reprStr st}")

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      if instr != expectedInstr then
        throw (IO.userError
          s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, _) =>
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got success {reprStr instr}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[executeInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := executeId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := executeId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def executeSetGasExact : Int :=
  computeExactGasBudget executeInstr

private def executeSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne executeInstr

private def gasProgExact : Array Instr :=
  #[.pushInt (.num executeSetGasExact), .tonEnvOp .setGasLimit, executeInstr]

private def gasProgExactMinusOne : Array Instr :=
  #[.pushInt (.num executeSetGasExactMinusOne), .tonEnvOp .setGasLimit, executeInstr]

private def oracleCases : Array OracleCase :=
  #[
    -- Success and control-flow transfer (`VM.call cont`) with oracle-encodable K=quit(0).
    mkCase "ok/control/direct/basic" (withQ0 #[]),
    mkCase "ok/control/direct/noise-a" (withQ0 noiseA),
    mkCase "ok/control/direct/noise-b" (withQ0 noiseB),
    mkCase "ok/control/direct/noise-c" (withQ0 noiseC),
    mkCase "ok/control/direct/noise-d" (withQ0 noiseD),
    mkCase "ok/control/direct/max-min-tail" (withQ0 #[intV maxInt257, intV (minInt257 + 1)]),
    mkCase "ok/control/skip-tail/retalt" (withQ0 #[]) #[executeInstr, .retAlt],
    mkCase "ok/control/skip-tail/pushint" (withQ0 #[]) #[executeInstr, .pushInt (.num tailMarker)],
    mkCase "ok/control/skip-tail/add-underflow-avoided" (withQ0 #[]) #[executeInstr, .add],

    -- Program-side non-K continuations through PUSHCTR.
    mkCase "ok/control/pushctr0/empty-stack" #[] #[.pushCtr 0, executeInstr],
    mkCase "ok/control/pushctr1/empty-stack" #[] #[.pushCtr 1, executeInstr],
    mkCase "ok/control/pushctr3/empty-stack" #[] #[.pushCtr 3, executeInstr],
    mkCase "ok/control/pushctr1/tail-skipped" #[] #[.pushCtr 1, executeInstr, .pushInt (.num tailMarker)],
    mkCase "ok/control/pushctr3/tail-skipped" #[] #[.pushCtr 3, executeInstr, .pushInt (.num tailMarker)],
    mkCase "ok/control/pushctr1/preserve-below" noiseA #[.pushCtr 1, executeInstr],
    mkCase "ok/control/pushctr3/preserve-below" noiseB #[.pushCtr 3, executeInstr],

    -- Multi-opcode code cells proving post-EXECUTE decode is skipped.
    mkCodeCase "ok/control/two-exec/second-skipped" #[q0, q0] twoExecuteCode,
    mkCodeCase "ok/control/execute-then-truncated/skipped-tail-decode" (withQ0 #[]) executeThenTruncatedCode,
    mkCodeCase "ok/decode/execute-with-spare-ref/basic" (withQ0 #[]) executeWithRefCode,
    mkCodeCase "ok/decode/execute-with-spare-ref/deep" (withQ0 noiseB) executeWithRefCode,

    -- Underflow (`popCont`/`pop` empty-stack guard).
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/empty-tail-retalt" #[] #[executeInstr, .retAlt],
    mkCase "err/underflow/empty-tail-add" #[] #[executeInstr, .add],
    mkCodeCase "err/underflow/empty-with-spare-ref-code" #[] executeWithRefCode,

    -- Type checks (`popCont` after successful pop of non-cont top).
    mkCase "err/type/top-int" #[intV 1],
    mkCase "err/type/top-null" #[.null],
    mkCase "err/type/top-cell" #[.cell refCellA],
    mkCase "err/type/top-slice" #[.slice sliceA],
    mkCase "err/type/top-builder" #[.builder Builder.empty],
    mkCase "err/type/top-tuple-empty" #[.tuple #[]],
    mkCase "err/type/top-first-over-below-int" #[intV 77, .null],
    mkCase "err/type/top-first-over-below-cont" #[q0, .null],
    mkCase "err/type/top-first-over-deep-a" #[intV 5, .cell refCellA, .builder Builder.empty],
    mkCase "err/type/top-first-over-deep-b" #[.tuple #[], intV (-3), .slice sliceA],

    -- Decode failures (must fail before touching stack/execution path).
    mkCodeCase "err/decode/truncated7/empty" #[] truncated7Code,
    mkCodeCase "err/decode/truncated7/with-int" #[intV 0] truncated7Code,
    mkCodeCase "err/decode/truncated7/with-cont" #[q0] truncated7Code,
    mkCodeCase "err/decode/truncated7-with-ref/empty" #[] truncated7WithRefCode,
    mkCodeCase "err/decode/truncated7-with-ref/deep" noiseA truncated7WithRefCode,
    mkCodeCase "err/decode/truncated-then-execute/empty" #[] truncatedThenExecuteCode,
    mkCodeCase "err/decode/truncated-then-execute/with-cont" #[q0] truncatedThenExecuteCode,
    mkCodeCase "err/decode/truncated-then-execute/deep" (withQ0 noiseC) truncatedThenExecuteCode,

    -- Deterministic gas cliffs via runtime SETGASLIMIT program setup.
    mkCase "gas/exact-succeeds" (withQ0 #[]) gasProgExact,
    mkCase "gas/exact-minus-one/out-of-gas" (withQ0 #[]) gasProgExactMinusOne,
    mkCase "gas/exact/underflow-stkund" #[] gasProgExact,
    mkCase "gas/exact-minus-one/type-path-oog-first" #[intV 1] gasProgExactMinusOne
  ]

def suite : InstrSuite where
  id := executeId
  unit := #[
    { name := "unit/decode/canonical-and-truncated"
      run := do
        let assembled := assembleOrPanic "unit/decode/assemble" #[executeInstr]
        if assembled.bits != executeCode.bits || assembled.refs != executeCode.refs then
          throw (IO.userError
            s!"decode/assemble: expected 0xd8 code cell, got bits={assembled.bits.size}, refs={assembled.refs.size}")
        expectDecodeOk "decode/execute" executeCode executeInstr 8
        expectDecodeOk "decode/execute-with-spare-ref" executeWithRefCode executeInstr 8
        expectDecodeErr "decode/truncated7" truncated7Code .invOpcode
        expectDecodeErr "decode/truncated7-with-ref" truncated7WithRefCode .invOpcode }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runExecuteDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/matched-execute"
          (runExecuteDispatchFallback executeInstr (withQ0 #[]))
          #[] }
    ,
    { name := "unit/raw/quit-target-reduces-to-jump"
      run := do
        let st ← expectRawOk "raw/call-retcont"
          (runExecuteRaw #[intV 13, q0] (.quit 111))
        if st.stack != #[intV 13] then
          throw (IO.userError s!"raw/call-retcont: unexpected stack {reprStr st.stack}")
        if st.cc != .quit 0 then
          throw (IO.userError s!"raw/call-retcont: expected cc=quit0, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"raw/call-retcont: expected unchanged c0=quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/prebound-c0-reduces-to-jump"
      run := do
        let st ← expectRawOk "raw/prebound-c0"
          (runExecuteRaw #[intV 5, .cont preboundC0Cont] (.quit 44))
        if st.stack != #[intV 5] then
          throw (IO.userError s!"raw/prebound-c0: unexpected stack {reprStr st.stack}")
        if st.cc != preboundC0Cont then
          throw (IO.userError
            s!"raw/prebound-c0: expected jump to continuation, got cc={reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"raw/prebound-c0: expected unchanged c0=quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/captured-stack-applied"
      run := do
        let st ← expectRawOk "raw/captured-stack"
          (runExecuteRaw #[.null, intV 44, .cont capturedStackCont] (.quit 55))
        if st.stack != #[intV 91, .null, intV 44] then
          throw (IO.userError
            s!"raw/captured-stack: expected #[91,null,44], got {reprStr st.stack}")
        match st.cc with
        | .ordinary _ _ _ cdata =>
            if !cdata.stack.isEmpty || cdata.nargs != -1 then
              throw (IO.userError
                s!"raw/captured-stack: expected consumed cdata, got {reprStr cdata}")
        | other =>
            throw (IO.userError
              s!"raw/captured-stack: expected ordinary continuation, got {reprStr other}") }
    ,
    { name := "unit/raw/callee-nargs-underflow"
      run := do
        let st ← expectRawErr "raw/nargs-underflow"
          (runExecuteRaw #[intV 5, .cont needTwoArgsCont] (.quit 123))
          .stkUnd
        if st.stack != #[intV 5] then
          throw (IO.userError s!"raw/nargs-underflow: expected stack #[5], got {reprStr st.stack}")
        if st.cc != .quit 123 then
          throw (IO.userError
            s!"raw/nargs-underflow: expected unchanged cc=quit123, got {reprStr st.cc}") }
    ,
    { name := "unit/errors/underflow-type-and-pop-order"
      run := do
        let stUnd ← expectRawErr "err/underflow-empty" (runExecuteRaw #[] (.quit 9)) .stkUnd
        if !stUnd.stack.isEmpty then
          throw (IO.userError s!"err/underflow-empty: stack mutated to {reprStr stUnd.stack}")

        let stType ← expectRawErr "err/type-top-null"
          (runExecuteRaw #[intV 7, .null] (.quit 9)) .typeChk
        if stType.stack != #[intV 7] then
          throw (IO.userError
            s!"err/type-top-null: expected top-pop ordering, got stack {reprStr stType.stack}")

        let stTypeDeep ← expectRawErr "err/type-top-cell-over-cont"
          (runExecuteRaw #[q0, .cell refCellB] (.quit 9)) .typeChk
        if stTypeDeep.stack != #[q0] then
          throw (IO.userError
            s!"err/type-top-cell-over-cont: expected remaining #[K], got {reprStr stTypeDeep.stack}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec executeId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.EXECUTE
