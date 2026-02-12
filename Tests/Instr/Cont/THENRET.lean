import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.THENRET

/-
THENRET branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cont/AtExit.lean` (`.contExt .thenret` branch)
  - `TvmLean/Model/Cont/Continuation.lean` (`forceCdata`, `defineC0`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_thenret`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`force_cregs`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.h` (`ControlRegs::define_c0`)

Mapped behavior covered by this suite:
1. Dispatch branch:
  - `.contExt .thenret` handled;
  - non-matching instructions fall through to `next`.
2. Pop/type ordering:
  - underflow (`stkUnd`) first on empty stack;
  - non-cont top yields `typeChk` after top is popped.
3. Core THENRET rewrite:
  - pop continuation `k`;
  - `define_c0` semantics: define only if missing (no overwrite);
  - push resulting continuation back to stack;
  - VM control registers remain unchanged.
4. `force_cregs` parity:
  - when `k` has no cdata (e.g. `quit`), THENRET wraps into envelope-like continuation
    before storing `c0`.
-/

private def thenRetId : InstrId := { name := "THENRET" }

private def thenRetInstr : Instr := .contExt .thenret

private def dispatchSentinel : Int := 88421

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q9 : Continuation := .quit 9
private def q17 : Continuation := .quit 17

private def q0V : Value := .cont q0

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def fullSliceA : Slice := Slice.ofCell cellA

private def retCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0xdb30 16) #[]

private def retCodeSlice : Slice := Slice.ofCell retCodeCell

private def thenRetRawCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf6 16) #[]

private def thenRetTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def thenRetTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf6 >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[thenRetInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := thenRetId
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
    instr := thenRetId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runThenRetDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContAtExit thenRetInstr stack

private def runThenRetDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContAtExit instr (VM.push (intV dispatchSentinel)) stack

private def runThenRetRaw
    (stack : Array Value)
    (c0 : Continuation := q0)
    (c1 : Continuation := q1)
    (instr : Instr := thenRetInstr)
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

private def expectC0Field (label : String) (cregs : OrdCregs) (expected : Continuation) : IO Unit := do
  match cregs.c0 with
  | none =>
      throw (IO.userError s!"{label}: expected defined c0 in continuation cregs")
  | some got =>
      if got == expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected cregs.c0={reprStr expected}, got {reprStr got}")

private def expectEnvelopeWithC0
    (label : String)
    (k : Continuation)
    (expectedExt : Continuation)
    (expectedC0 : Continuation) : IO Unit := do
  match k with
  | .envelope ext cregs cdata =>
      if ext != expectedExt then
        throw (IO.userError s!"{label}: expected envelope ext={reprStr expectedExt}, got {reprStr ext}")
      else
        expectC0Field label cregs expectedC0
        assertCdataEmpty label cdata
  | _ =>
      throw (IO.userError s!"{label}: expected envelope continuation, got {reprStr k}")

private def expectOrdinaryWithC0
    (label : String)
    (k : Continuation)
    (expectedCode : Slice)
    (expectedSaved : Continuation)
    (expectedC0 : Continuation) : IO Unit := do
  match k with
  | .ordinary code saved cregs cdata =>
      if code != expectedCode then
        throw (IO.userError s!"{label}: expected ordinary code {reprStr expectedCode}, got {reprStr code}")
      else if saved != expectedSaved then
        throw (IO.userError s!"{label}: expected saved={reprStr expectedSaved}, got {reprStr saved}")
      else
        expectC0Field label cregs expectedC0
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

private def expectDecodeThenRet
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != thenRetInstr then
        throw (IO.userError s!"{label}: expected {reprStr thenRetInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def progThenRetThenPushC0 (tail : Array Instr := #[]) : Array Instr :=
  #[thenRetInstr, .pushCtr 0] ++ tail

private def thenRetGasExact : Int :=
  computeExactGasBudget thenRetInstr

private def thenRetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne thenRetInstr

private def thenRetOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/control/",
    "err/control/",
    "err/underflow/",
    "err/type/",
    "err/order/",
    "ok/decode/",
    "err/decode/",
    "gas/"
  ]

private def thenRetFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := thenRetOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

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
  mkCase "ok/basic/q0-over-mixed-four" #[intV (-7), .builder Builder.empty, .cell cellA, q0V],
  mkCase "ok/basic/q0-over-slice-and-tuple" #[.slice fullSliceA, .tuple #[], q0V],

  mkCase "ok/control/tail-runs-after-thenret" #[q0V] #[thenRetInstr, .pushInt (.num 7)],
  mkCase "ok/control/tail-runs-add" #[q0V] #[thenRetInstr, .pushInt (.num 2), .pushInt (.num 3), .add],
  mkCase "ok/control/thenret-twice" #[q0V] #[thenRetInstr, thenRetInstr],
  mkCase "ok/control/thenret-drop" #[q0V] #[thenRetInstr, .pop 0],
  mkCase "ok/control/observe-c0-after-thenret" #[q0V] (progThenRetThenPushC0),
  mkCase "ok/control/observe-c0-after-thenret-noise" #[intV 3, q0V] (progThenRetThenPushC0),
  mkCase "ok/control/observe-c0-after-thenret-mixed" #[.null, .cell cellA, q0V] (progThenRetThenPushC0),
  mkCase "ok/control/observe-c0-after-thenret-drop-tail" #[q0V] (progThenRetThenPushC0 #[.pop 0]),
  mkCase "err/control/drop-thenret-underflow" #[q0V] #[.pop 0, thenRetInstr],
  mkCase "err/control/thenret-drop-thenret-underflow" #[q0V] #[thenRetInstr, .pop 0, thenRetInstr],

  mkCase "err/underflow/empty" #[],

  mkCase "err/type/top-int" #[intV 0],
  mkCase "err/type/top-null" #[.null],
  mkCase "err/type/top-cell" #[.cell cellA],
  mkCase "err/type/top-slice" #[.slice fullSliceA],
  mkCase "err/type/top-builder-empty" #[.builder Builder.empty],
  mkCase "err/type/top-empty-tuple" #[.tuple #[]],
  mkCase "err/type/top-nan-via-program" #[] #[.pushInt .nan, thenRetInstr],
  mkCase "err/order/type-before-below-cont" #[q0V, .null],
  mkCase "err/order/type-before-below-cont-via-program" #[q0V] #[.pushInt (.num 42), thenRetInstr],
  mkCase "err/order/type-before-below-cont-via-program-nan" #[q0V] #[.pushInt .nan, thenRetInstr],

  mkCaseCode "ok/decode/raw-opcode-edf6" #[q0V] thenRetRawCode,
  mkCaseCode "err/decode/truncated-8" #[] thenRetTruncated8Code,
  mkCaseCode "err/decode/truncated-15" #[q0V] thenRetTruncated15Code,

  mkCase "gas/exact-cost-succeeds"
    #[q0V]
    #[.pushInt (.num thenRetGasExact), .tonEnvOp .setGasLimit, thenRetInstr],
  mkCase "gas/exact-minus-one-out-of-gas"
    #[q0V]
    #[.pushInt (.num thenRetGasExactMinusOne), .tonEnvOp .setGasLimit, thenRetInstr]
]

def suite : InstrSuite where
  id := thenRetId
  unit := #[
    { name := "unit/dispatch/thenret-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runThenRetDispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]

        let st ← expectRawOk "dispatch/matched-thenret-no-next"
          (runThenRetRaw #[q0V] q1 q9 thenRetInstr (VM.push (intV dispatchSentinel)))
        if st.stack.size != 1 then
          throw (IO.userError
            s!"dispatch/matched-thenret-no-next: expected stack size 1, got {st.stack.size}")
        else
          match st.stack.back? with
          | some (.cont _) =>
              pure ()
          | some v =>
              throw (IO.userError
                s!"dispatch/matched-thenret-no-next: expected top continuation, got {reprStr v}")
          | none =>
              throw (IO.userError "dispatch/matched-thenret-no-next: expected non-empty stack") }
    ,
    { name := "unit/errors/underflow-and-top-pop-order"
      run := do
        expectErr "underflow/empty"
          (runThenRetDirect #[]) .stkUnd
        expectErr "type/top-int"
          (runThenRetDirect #[intV 0]) .typeChk

        let st ← expectRawErr "order/top-popped-before-type-error"
          (runThenRetRaw #[q0V, .null] q1 q9) .typeChk
        if st.stack != #[q0V] then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected stack #[q0], got {reprStr st.stack}")
        else if st.regs.c0 != q1 then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected c0 unchanged (quit1), got {reprStr st.regs.c0}")
        else if st.regs.c1 != q9 then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected c1 unchanged (quit9), got {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/raw/force-cdata-wraps-quit-and-defines-from-c0"
      run := do
        let st ← expectRawOk "raw/force-cdata-wraps-quit"
          (runThenRetRaw #[q0V] q1 q9)
        if st.regs.c0 != q1 then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected c0 unchanged, got {reprStr st.regs.c0}")
        else if st.regs.c1 != q9 then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected c1 unchanged, got {reprStr st.regs.c1}")
        else
          match st.stack.back? with
          | some (.cont k) =>
              expectEnvelopeWithC0 "raw/force-cdata-wraps-quit" k q0 q1
          | some v =>
              throw (IO.userError s!"raw/force-cdata-wraps-quit: expected top cont, got {reprStr v}")
          | none =>
              throw (IO.userError "raw/force-cdata-wraps-quit: expected non-empty stack") }
    ,
    { name := "unit/raw/ordinary-cont-define-c0-and-no-overwrite"
      run := do
        let ordNoC0 : Continuation := .ordinary retCodeSlice q0 OrdCregs.empty OrdCdata.empty
        let stDefined ← expectRawOk "raw/ordinary-define-c0"
          (runThenRetRaw #[.cont ordNoC0] q1)
        if stDefined.regs.c0 != q1 then
          throw (IO.userError s!"raw/ordinary-define-c0: expected c0 unchanged, got {reprStr stDefined.regs.c0}")
        else
          match stDefined.stack.back? with
          | some (.cont k) =>
              expectOrdinaryWithC0 "raw/ordinary-define-c0" k retCodeSlice q0 q1
          | some v =>
              throw (IO.userError s!"raw/ordinary-define-c0: expected top cont, got {reprStr v}")
          | none =>
              throw (IO.userError "raw/ordinary-define-c0: expected non-empty stack")

        let ordWithC0 : Continuation :=
          .ordinary retCodeSlice q0 ({ OrdCregs.empty with c0 := some q1 }) OrdCdata.empty
        let stNoOverwrite ← expectRawOk "raw/no-overwrite-existing-c0"
          (runThenRetRaw #[.cont ordWithC0] q9)
        if stNoOverwrite.regs.c0 != q9 then
          throw (IO.userError
            s!"raw/no-overwrite-existing-c0: expected c0 unchanged (quit9), got {reprStr stNoOverwrite.regs.c0}")
        else
          match stNoOverwrite.stack.back? with
          | some (.cont k) =>
              expectOrdinaryWithC0 "raw/no-overwrite-existing-c0" k retCodeSlice q0 q1
          | some v =>
              throw (IO.userError s!"raw/no-overwrite-existing-c0: expected top cont, got {reprStr v}")
          | none =>
              throw (IO.userError "raw/no-overwrite-existing-c0: expected non-empty stack") }
    ,
    { name := "unit/raw/below-stack-preserved-and-regs-unchanged"
      run := do
        let below : Array Value := #[intV 7, .null, .cell cellA]
        let st ← expectRawOk "raw/below-stack-preserved"
          (runThenRetRaw (below ++ #[q0V]) q17 q9)
        if st.regs.c0 != q17 then
          throw (IO.userError s!"raw/below-stack-preserved: expected c0 unchanged, got {reprStr st.regs.c0}")
        else if st.regs.c1 != q9 then
          throw (IO.userError s!"raw/below-stack-preserved: expected c1 unchanged, got {reprStr st.regs.c1}")
        else if st.stack.take below.size != below then
          throw (IO.userError
            s!"raw/below-stack-preserved: expected prefix {reprStr below}, got {reprStr (st.stack.take below.size)}")
        else
          match st.stack.back? with
          | some (.cont k) =>
              expectEnvelopeWithC0 "raw/below-stack-preserved" k q0 q17
          | some v =>
              throw (IO.userError s!"raw/below-stack-preserved: expected top cont, got {reprStr v}")
          | none =>
              throw (IO.userError "raw/below-stack-preserved: expected non-empty stack") }
    ,
    { name := "unit/decode/thenret-and-truncated-prefix"
      run := do
        expectDecodeThenRet "decode/thenret" thenRetRawCode
        expectDecodeErr "decode/truncated-8" thenRetTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" thenRetTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile thenRetId thenRetFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.THENRET
