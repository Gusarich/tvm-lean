import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.ATEXITALT

/-
ATEXITALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cont/AtExit.lean` (`.contExt .atexitAlt` branch)
  - `TvmLean/Model/Cont/Continuation.lean` (`forceCdata`, `defineC1`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_atexit_alt`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`force_cregs`)

Mapped behavior covered by this suite:
1. Dispatch branch:
  - `.contExt .atexitAlt` handled;
  - non-matching instructions fall through to `next`.
2. Pop/type ordering:
  - underflow (`stkUnd`) before type checks;
  - non-cont top yields `typeChk` after popping the top value.
3. Core ATEXITALT rewrite:
  - pop continuation `k`;
  - `define_c1` semantics: define only if missing (no overwrite);
  - set VM `c1 := k`.
4. `force_cregs` parity:
  - when `k` has no cdata (e.g. `quit`), ATEXITALT wraps into envelope-like continuation
    before storing `c1`.
5. Tricky control-register observability:
  - nested RETALT-chain programs distinguish "define current c1" vs "existing c1 preserved".
-/

private def atExitAltId : InstrId := { name := "ATEXITALT" }

private def atExitAltInstr : Instr := .contExt .atexitAlt

private def dispatchSentinel : Int := 8114

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q9 : Continuation := .quit 9

private def q0V : Value := .cont q0

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def fullSliceA : Slice := Slice.ofCell cellA

private def noiseA : Array Value :=
  #[intV 5, .null]

private def noiseB : Array Value :=
  #[.cell cellA, intV 8]

private def retAltCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0xdb31 16) #[]

private def retAltCodeSlice : Slice := Slice.ofCell retAltCodeCell

private def atExitAltRawCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf4 16) #[]

private def atExitAltTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def atExitAltTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf4 >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[atExitAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := atExitAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := atExitAltId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runAtExitAltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContAtExit atExitAltInstr stack

private def runAtExitAltDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContAtExit instr (VM.push (intV dispatchSentinel)) stack

private def runAtExitAltRaw
    (stack : Array Value)
    (c0 : Continuation := q0)
    (c1 : Continuation := q1)
    (instr : Instr := atExitAltInstr)
    (next : VM Unit := pure ()) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrContAtExit instr next).run st0

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

private def assertCdataEmpty (label : String) (cdata : OrdCdata) : IO Unit := do
  if cdata.nargs != -1 then
    throw (IO.userError s!"{label}: expected cdata.nargs = -1, got {cdata.nargs}")
  else if !cdata.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty cdata.stack, got {reprStr cdata.stack}")
  else
    pure ()

private def expectC1Field (label : String) (cregs : OrdCregs) (expected : Continuation) : IO Unit := do
  match cregs.c1 with
  | none =>
      throw (IO.userError s!"{label}: expected defined c1 in continuation cregs")
  | some got =>
      if got == expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected cregs.c1={reprStr expected}, got {reprStr got}")

private def expectEnvelopeWithC1
    (label : String)
    (k : Continuation)
    (expectedExt : Continuation)
    (expectedC1 : Continuation) : IO Unit := do
  match k with
  | .envelope ext cregs cdata =>
      if ext != expectedExt then
        throw (IO.userError s!"{label}: expected envelope ext={reprStr expectedExt}, got {reprStr ext}")
      else
        expectC1Field label cregs expectedC1
        assertCdataEmpty label cdata
  | _ =>
      throw (IO.userError s!"{label}: expected envelope continuation, got {reprStr k}")

private def expectOrdinaryWithC1
    (label : String)
    (k : Continuation)
    (expectedCode : Slice)
    (expectedSaved : Continuation)
    (expectedC1 : Continuation) : IO Unit := do
  match k with
  | .ordinary code saved cregs cdata =>
      if code != expectedCode then
        throw (IO.userError s!"{label}: expected ordinary code {reprStr expectedCode}, got {reprStr code}")
      else if saved != expectedSaved then
        throw (IO.userError s!"{label}: expected saved={reprStr expectedSaved}, got {reprStr saved}")
      else
        expectC1Field label cregs expectedC1
        assertCdataEmpty label cdata
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr k}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectDecodeAtExitAlt
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != atExitAltInstr then
        throw (IO.userError s!"{label}: expected {reprStr atExitAltInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def progAtExitAltThenPushC1 (tail : Array Instr := #[]) : Array Instr :=
  #[atExitAltInstr, .pushCtr 1] ++ tail

private def progDefineFromC0RetAlt : Array Instr :=
  #[.pushCtr 0, .popCtr 1, .pushRefCont retAltCodeCell, atExitAltInstr, .retAlt]

private def progNoOverwriteRetAlt : Array Instr :=
  #[.pushCtr 0, .pushRefCont retAltCodeCell, .setContCtr 1, atExitAltInstr, .retAlt]

private def progExistingQuit1RetAlt : Array Instr :=
  #[.pushCtr 1, .pushRefCont retAltCodeCell, .setContCtr 1, atExitAltInstr, .retAlt]

private def progObserveFromOrdinary : Array Instr :=
  #[.pushRefCont retAltCodeCell, atExitAltInstr, .pushCtr 1]

private def progObserveFromExistingC1 : Array Instr :=
  #[.pushCtr 0, .pushRefCont retAltCodeCell, .setContCtr 1, atExitAltInstr, .pushCtr 1]

private def atExitAltGasExact : Int :=
  computeExactGasBudget atExitAltInstr

private def atExitAltGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne atExitAltInstr

private def oracleCases : Array OracleCase := #[
  mkCase "ok/basic/q0-only" #[q0V],
  mkCase "ok/basic/q0-over-int" #[intV 1, q0V],
  mkCase "ok/basic/q0-over-null" #[.null, q0V],
  mkCase "ok/basic/q0-over-cell" #[.cell cellA, q0V],
  mkCase "ok/basic/q0-over-slice" #[.slice fullSliceA, q0V],
  mkCase "ok/basic/q0-over-builder" #[.builder Builder.empty, q0V],
  mkCase "ok/basic/q0-over-empty-tuple" #[.tuple #[], q0V],
  mkCase "ok/basic/q0-over-cont" #[q0V, q0V],
  mkCase "ok/basic/q0-over-mixed-two" #[intV 7, .cell cellA, q0V],
  mkCase "ok/basic/q0-over-mixed-three" #[.null, .builder Builder.empty, .tuple #[], q0V],

  mkCase "ok/observe-c1/envelope-from-quit0" #[q0V] (progAtExitAltThenPushC1),
  mkCase "ok/observe-c1/envelope-from-quit0-noise" #[intV 3, q0V] (progAtExitAltThenPushC1),
  mkCase "ok/observe-c1/envelope-from-quit0-mixed" #[.null, .cell cellA, q0V] (progAtExitAltThenPushC1),

  mkCase "ok/control/tail-runs-after-atexitalt" #[q0V] #[atExitAltInstr, .pushInt (.num 7)],
  mkCase "ok/control/tail-runs-add" #[q0V] #[atExitAltInstr, .pushInt (.num 2), .pushInt (.num 3), .add],
  mkCase "err/control/tail-underflow-after-atexitalt" #[q0V] #[atExitAltInstr, .add],

  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/second-atexitalt" #[q0V] #[atExitAltInstr, atExitAltInstr],
  mkCase "err/underflow/third-atexitalt-chain" #[q0V, q0V] #[atExitAltInstr, atExitAltInstr, atExitAltInstr],

  mkCase "err/type/top-int" #[intV 0],
  mkCase "err/type/top-null" #[.null],
  mkCase "err/type/top-cell" #[.cell cellA],
  mkCase "err/type/top-slice" #[.slice fullSliceA],
  mkCase "err/type/top-builder-empty" #[.builder Builder.empty],
  mkCase "err/type/top-empty-tuple" #[.tuple #[]],
  mkCase "err/type/top-nan-via-program" #[] #[.pushInt .nan, atExitAltInstr],
  mkCase "err/order/type-before-below-cont" #[q0V, .null],
  mkCase "err/order/type-before-below-cont-via-program" #[q0V] #[.pushInt (.num 42), atExitAltInstr],
  mkCase "err/order/type-before-below-cont-via-program-nan" #[q0V] #[.pushInt .nan, atExitAltInstr],

  mkCaseCode "ok/decode/raw-opcode-edf4" #[q0V] atExitAltRawCode,
  mkCaseCode "err/decode/truncated-8" #[] atExitAltTruncated8Code,
  mkCaseCode "err/decode/truncated-15" #[q0V] atExitAltTruncated15Code,

  mkCase "gas/exact-cost-succeeds"
    #[q0V]
    #[.pushInt (.num atExitAltGasExact), .tonEnvOp .setGasLimit, atExitAltInstr],
  mkCase "gas/exact-minus-one-out-of-gas"
    #[q0V]
    #[.pushInt (.num atExitAltGasExactMinusOne), .tonEnvOp .setGasLimit, atExitAltInstr]
]

def suite : InstrSuite where
  id := atExitAltId
  unit := #[
    { name := "unit/dispatch/atexitalt-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runAtExitAltDispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-atexitalt"
          (runAtExitAltDispatchFallback atExitAltInstr #[q0V])
          #[] }
    ,
    { name := "unit/errors/underflow-and-top-pop-order"
      run := do
        expectErr "underflow/empty"
          (runAtExitAltDirect #[]) .stkUnd
        expectErr "type/top-int"
          (runAtExitAltDirect #[intV 0]) .typeChk

        let st ← expectRawErr "order/top-popped-before-type-error"
          (runAtExitAltRaw #[q0V, .null]) .typeChk
        if st.stack != #[q0V] then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected stack #[q0], got {reprStr st.stack}")
        else if st.regs.c1 != q1 then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected c1 unchanged (quit1), got {reprStr st.regs.c1}")
        else if st.regs.c0 != q0 then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected c0 unchanged (quit0), got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/raw/force-cdata-wraps-quit-and-captures-current-c1"
      run := do
        let st ← expectRawOk "raw/force-cdata-wraps-quit"
          (runAtExitAltRaw #[q0V] q1 q9)
        if !st.stack.isEmpty then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c0 != q1 then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          expectEnvelopeWithC1 "raw/force-cdata-wraps-quit" st.regs.c1 q0 q9 }
    ,
    { name := "unit/raw/ordinary-cont-define-c1-and-no-overwrite"
      run := do
        let ordNoC1 : Continuation := .ordinary retAltCodeSlice q0 OrdCregs.empty OrdCdata.empty
        let stDefined ← expectRawOk "raw/ordinary-define-c1"
          (runAtExitAltRaw #[.cont ordNoC1] q0 q1)
        expectOrdinaryWithC1 "raw/ordinary-define-c1" stDefined.regs.c1 retAltCodeSlice q0 q1

        let ordWithC1 : Continuation :=
          .ordinary retAltCodeSlice q0 ({ OrdCregs.empty with c1 := some q1 }) OrdCdata.empty
        let stNoOverwrite ← expectRawOk "raw/no-overwrite-existing-c1"
          (runAtExitAltRaw #[.cont ordWithC1] q0 q9)
        expectOrdinaryWithC1 "raw/no-overwrite-existing-c1" stNoOverwrite.regs.c1 retAltCodeSlice q0 q1 }
    ,
    { name := "unit/decode/atexitalt-and-truncated-prefix"
      run := do
        expectDecodeAtExitAlt "decode/atexitalt" atExitAltRawCode
        expectDecodeErr "decode/truncated-8" atExitAltTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" atExitAltTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec atExitAltId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.ATEXITALT
