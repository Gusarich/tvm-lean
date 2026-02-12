import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.ATEXIT

/-
ATEXIT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cont/AtExit.lean` (`.contExt .atexit` branch)
  - `TvmLean/Model/Cont/Continuation.lean` (`forceCdata`, `defineC0`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_atexit`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`force_cregs`)

Mapped behavior covered by this suite:
1. Dispatch branch:
  - `.contExt .atexit` handled;
  - non-matching instructions fall through to `next`.
2. Pop/type ordering:
  - underflow (`stkUnd`) before type checks;
  - non-cont top yields `typeChk` after popping the top value.
3. Core ATEXIT rewrite:
  - pop continuation `k`;
  - `define_c0` semantics: define only if missing (no overwrite);
  - set VM `c0 := k`.
4. `force_cregs` parity:
  - when `k` has no cdata (e.g. `quit`), ATEXIT wraps into envelope-like continuation
    before storing `c0`.
5. Tricky control-register observability:
  - nested return-chain programs distinguish "define current c0" vs "existing c0 preserved".
-/

private def atExitId : InstrId := { name := "ATEXIT" }

private def atExitInstr : Instr := .contExt .atexit

private def dispatchSentinel : Int := 8107

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

private def retCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0xdb30 16) #[]

private def retCodeSlice : Slice := Slice.ofCell retCodeCell

private def atExitRawCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf3 16) #[]

private def atExitTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def atExitTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf3 >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[atExitInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := atExitId
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
    instr := atExitId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runAtExitDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContAtExit atExitInstr stack

private def runAtExitDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContAtExit instr (VM.push (intV dispatchSentinel)) stack

private def runAtExitRaw
    (stack : Array Value)
    (c0 : Continuation := q0)
    (c1 : Continuation := q1)
    (instr : Instr := atExitInstr)
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

private def expectDecodeAtExit
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != atExitInstr then
        throw (IO.userError s!"{label}: expected {reprStr atExitInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def progAtExitThenPushC0 (tail : Array Instr := #[]) : Array Instr :=
  #[atExitInstr, .pushCtr 0] ++ tail

private def progDefineFromC1Ret : Array Instr :=
  #[.pushCtr 1, .popCtr 0, .pushRefCont retCodeCell, atExitInstr, .ret]

private def progNoOverwriteRet : Array Instr :=
  #[.pushCtr 1, .pushRefCont retCodeCell, .setContCtr 0, atExitInstr, .ret]

private def progExistingQuit0Ret : Array Instr :=
  #[.pushCtr 0, .pushRefCont retCodeCell, .setContCtr 0, atExitInstr, .ret]

private def progObserveFromOrdinary : Array Instr :=
  #[.pushRefCont retCodeCell, atExitInstr, .pushCtr 0]

private def progObserveFromExistingC0 : Array Instr :=
  #[.pushCtr 1, .pushRefCont retCodeCell, .setContCtr 0, atExitInstr, .pushCtr 0]

private def atExitGasExact : Int :=
  computeExactGasBudget atExitInstr

private def atExitGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne atExitInstr

private def atExitFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/basic/",
      "ok/observe-c0/",
      "ok/control/",
      "err/control/",
      "err/underflow/",
      "err/type/",
      "err/order/",
      "ok/decode/",
      "err/decode/",
      "gas/"
    ]
    -- Bias toward continuation-composition perturbations around the popped top item.
    mutationModes := #[
      0, 0, 0,
      1, 1, 1, 1,
      2, 2, 2, 2,
      3, 3,
      4
    ]
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

  mkCase "ok/observe-c0/envelope-from-quit0" #[q0V] (progAtExitThenPushC0),
  mkCase "ok/observe-c0/envelope-from-quit0-noise" #[intV 3, q0V] (progAtExitThenPushC0),
  mkCase "ok/observe-c0/envelope-from-quit0-mixed" #[.null, .cell cellA, q0V] (progAtExitThenPushC0),

  mkCase "ok/control/tail-runs-after-atexit" #[q0V] #[atExitInstr, .pushInt (.num 7)],
  mkCase "ok/control/tail-runs-add" #[q0V] #[atExitInstr, .pushInt (.num 2), .pushInt (.num 3), .add],
  mkCase "err/control/tail-underflow-after-atexit" #[q0V] #[atExitInstr, .add],

  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/second-atexit" #[q0V] #[atExitInstr, atExitInstr],
  mkCase "err/underflow/third-atexit-chain" #[q0V, q0V] #[atExitInstr, atExitInstr, atExitInstr],

  mkCase "err/type/top-int" #[intV 0],
  mkCase "err/type/top-null" #[.null],
  mkCase "err/type/top-cell" #[.cell cellA],
  mkCase "err/type/top-slice" #[.slice fullSliceA],
  mkCase "err/type/top-builder-empty" #[.builder Builder.empty],
  mkCase "err/type/top-empty-tuple" #[.tuple #[]],
  mkCase "err/type/top-nan-via-program" #[] #[.pushInt .nan, atExitInstr],
  mkCase "err/order/type-before-below-cont" #[q0V, .null],
  mkCase "err/order/type-before-below-cont-via-program" #[q0V] #[.pushInt (.num 42), atExitInstr],
  mkCase "err/order/type-before-below-cont-via-program-nan" #[q0V] #[.pushInt .nan, atExitInstr],

  mkCaseCode "ok/decode/raw-opcode-edf3" #[q0V] atExitRawCode,
  mkCaseCode "err/decode/truncated-8" #[] atExitTruncated8Code,
  mkCaseCode "err/decode/truncated-15" #[q0V] atExitTruncated15Code,

  mkCase "gas/exact-cost-succeeds"
    #[q0V]
    #[.pushInt (.num atExitGasExact), .tonEnvOp .setGasLimit, atExitInstr],
  mkCase "gas/exact-minus-one-out-of-gas"
    #[q0V]
    #[.pushInt (.num atExitGasExactMinusOne), .tonEnvOp .setGasLimit, atExitInstr]
]

def suite : InstrSuite where
  id := atExitId
  unit := #[
    { name := "unit/dispatch/atexit-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runAtExitDispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-atexit"
          (runAtExitDispatchFallback atExitInstr #[q0V])
          #[] }
    ,
    { name := "unit/errors/underflow-and-top-pop-order"
      run := do
        expectErr "underflow/empty"
          (runAtExitDirect #[]) .stkUnd
        expectErr "type/top-int"
          (runAtExitDirect #[intV 0]) .typeChk

        let st ← expectRawErr "order/top-popped-before-type-error"
          (runAtExitRaw #[q0V, .null]) .typeChk
        if st.stack != #[q0V] then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected stack #[q0], got {reprStr st.stack}")
        else if st.regs.c0 != q0 then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected c0 unchanged (quit0), got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/raw/force-cdata-wraps-quit-and-captures-current-c0"
      run := do
        let st ← expectRawOk "raw/force-cdata-wraps-quit"
          (runAtExitRaw #[q0V] q1 q9)
        if !st.stack.isEmpty then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c1 != q9 then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected c1 unchanged, got {reprStr st.regs.c1}")
        else
          expectEnvelopeWithC0 "raw/force-cdata-wraps-quit" st.regs.c0 q0 q1 }
    ,
    { name := "unit/raw/ordinary-cont-define-c0-and-no-overwrite"
      run := do
        let ordNoC0 : Continuation := .ordinary retCodeSlice q0 OrdCregs.empty OrdCdata.empty
        let stDefined ← expectRawOk "raw/ordinary-define-c0"
          (runAtExitRaw #[.cont ordNoC0] q1)
        expectOrdinaryWithC0 "raw/ordinary-define-c0" stDefined.regs.c0 retCodeSlice q0 q1

        let ordWithC0 : Continuation :=
          .ordinary retCodeSlice q0 ({ OrdCregs.empty with c0 := some q1 }) OrdCdata.empty
        let stNoOverwrite ← expectRawOk "raw/no-overwrite-existing-c0"
          (runAtExitRaw #[.cont ordWithC0] q9)
        expectOrdinaryWithC0 "raw/no-overwrite-existing-c0" stNoOverwrite.regs.c0 retCodeSlice q0 q1 }
    ,
    { name := "unit/decode/atexit-and-truncated-prefix"
      run := do
        expectDecodeAtExit "decode/atexit" atExitRawCode
        expectDecodeErr "decode/truncated-8" atExitTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" atExitTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile atExitId atExitFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.ATEXIT
