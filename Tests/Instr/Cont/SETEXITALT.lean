import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETEXITALT

/-!
SETEXITALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cont/ChangeExt.lean` (`.contExt .setExitAlt`)
  - `TvmLean/Model/Cont/Continuation.lean` (`forceCdata`, `defineC0`, `defineC1`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_setexit_alt`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`force_cregs`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.h` (`ControlRegs::define_c0`, `define_c1`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)

Mapped behavior covered by this suite:
1. Dispatch:
  - `.contExt .setExitAlt` handled vs fallback to `next`.
2. Pop/type ordering:
  - underflow before type checks;
  - non-cont top yields `typeChk` after popping the top value.
3. Core SETEXITALT rewrite:
  - pop continuation `k`;
  - `force_cregs(k)`/`forceCdata`: wrap non-cdata continuation into envelope;
  - define `k.c0` from current `c0` iff missing;
  - define `k.c1` from current `c1` iff missing;
  - set VM `c1 := k`.
4. Ordering-sensitive register effect:
  - captured `c1` inside the new continuation must be old VM `c1`
    (writeback to `c1` happens after `define_c1`).
-/

private def setExitAltId : InstrId := { name := "SETEXITALT" }

private def setExitAltInstr : Instr := .contExt .setExitAlt

private def dispatchSentinel : Int := 53791

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q5 : Continuation := .quit 5
private def q6 : Continuation := .quit 6
private def q7 : Continuation := .quit 7
private def q9 : Continuation := .quit 9
private def q70 : Continuation := .quit 70
private def q71 : Continuation := .quit 71

private def q0V : Value := .cont q0

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x5a 8) #[cellA]

private def fullSliceA : Slice := Slice.ofCell cellA

private def refContCell : Cell :=
  Cell.mkOrdinary (natToBits 0xdb30 16) #[]

private def setExitAltCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf5 16) #[]

private def setExitAltTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def setExitAltTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf5 >>> 1) 15) #[]

private def noiseA : Array Value :=
  #[intV 5, .null]

private def noiseB : Array Value :=
  #[.cell cellA, intV 8]

private def preCode : Slice := Slice.ofCell refContCell

private def preCdata : OrdCdata :=
  { stack := #[intV 42], nargs := 1 }

private def preCont : Continuation :=
  .ordinary preCode q9
    { OrdCregs.empty with c0 := some q70, c1 := some q71 }
    preCdata

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.nargs = -1 && cdata.stack.isEmpty

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[setExitAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setExitAltId
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
    instr := setExitAltId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runSetExitAltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt setExitAltInstr stack

private def runSetExitAltFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSetExitAltRaw
    (stack : Array Value)
    (c0 : Continuation := q0)
    (c1 : Continuation := q1)
    (instr : Instr := setExitAltInstr)
    (next : VM Unit := pure ()) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrContChangeExt instr next).run st0

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

private def expectEnvelopeCaptured
    (label : String)
    (k : Continuation)
    (expectedExt : Continuation)
    (expectedC0 : Continuation)
    (expectedC1 : Continuation) : IO Unit := do
  match k with
  | .envelope ext cregs cdata =>
      if ext != expectedExt then
        throw (IO.userError s!"{label}: expected envelope ext={reprStr expectedExt}, got {reprStr ext}")
      else if cregs.c0 != some expectedC0 then
        throw (IO.userError s!"{label}: expected cregs.c0={reprStr expectedC0}, got {reprStr cregs.c0}")
      else if cregs.c1 != some expectedC1 then
        throw (IO.userError s!"{label}: expected cregs.c1={reprStr expectedC1}, got {reprStr cregs.c1}")
      else if !cdataEmpty cdata then
        throw (IO.userError s!"{label}: expected empty cdata, got {reprStr cdata}")
      else
        pure ()
  | _ =>
      throw (IO.userError s!"{label}: expected envelope continuation, got {reprStr k}")

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

private def expectDecodeSetExitAlt
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != setExitAltInstr then
        throw (IO.userError s!"{label}: expected {reprStr setExitAltInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def progSetThenPushC1 : Array Instr :=
  #[setExitAltInstr, .pushCtr 1]

private def progSetThenPushC0 : Array Instr :=
  #[setExitAltInstr, .pushCtr 0]

private def progSetThenAdd (n : Int) : Array Instr :=
  #[setExitAltInstr, .pushInt (.num n), .add]

private def progSetThenRetAlt : Array Instr :=
  #[setExitAltInstr, .retAlt]

private def progSetThenRetAltTail : Array Instr :=
  #[setExitAltInstr, .retAlt, .pushInt (.num 777)]

private def progPushRefSet : Array Instr :=
  #[.pushRefCont refContCell, setExitAltInstr]

private def progPushRefSetPushC1 : Array Instr :=
  #[.pushRefCont refContCell, setExitAltInstr, .pushCtr 1]

private def progPushCtr1Set : Array Instr :=
  #[.pushCtr 1, setExitAltInstr]

private def progPushCtr0Set : Array Instr :=
  #[.pushCtr 0, setExitAltInstr]

private def progDefineC1ThenSet : Array Instr :=
  #[.pushCtr 1, .pushRefCont refContCell, .setContCtr 1, setExitAltInstr, .pushCtr 1]

private def progDefineC0ThenSet : Array Instr :=
  #[.pushCtr 0, .pushRefCont refContCell, .setContCtr 0, setExitAltInstr, .pushCtr 1]

private def progDefineC0ThenSetRetAlt : Array Instr :=
  #[.pushCtr 0, .pushRefCont refContCell, .setContCtr 0, setExitAltInstr, .retAlt]

private def setExitAltOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/order/",
    "ok/gas/",
    "err/gas/",
    "err/underflow/",
    "err/type/",
    "err/decode/"
  ]

private def setExitAltFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := setExitAltOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Basic direct SETEXITALT coverage.
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

  -- Ordering: SETEXITALT does not jump; tail instructions continue.
  mkCase "ok/order/tail-runs-push-c1/empty" #[q0V] progSetThenPushC1,
  mkCase "ok/order/tail-runs-push-c1/noise-a" (noiseA ++ #[q0V]) progSetThenPushC1,
  mkCase "ok/order/tail-runs-push-c0/empty" #[q0V] progSetThenPushC0,
  mkCase "ok/order/tail-runs-add/basic" #[intV 3, q0V] (progSetThenAdd 2),
  mkCase "ok/order/tail-runs-add/noise" #[.null, intV 4, q0V] (progSetThenAdd (-1)),
  mkCase "ok/order/set-then-retalt" #[q0V] progSetThenRetAlt,
  mkCase "ok/order/set-then-retalt-tail-skipped" #[q0V] progSetThenRetAltTail,

  -- Gas fenceposts.
  mkCase "ok/gas/exact-budget" #[q0V] #[setExitAltInstr]
    (oracleGasLimitsExact (computeExactGasBudget setExitAltInstr)),
  mkCase "err/gas/exact-minus-one" #[q0V] #[setExitAltInstr]
    (oracleGasLimitsExactMinusOne (computeExactGasBudget setExitAltInstr)),

  -- Error branches: underflow/type ordering.
  mkCase "err/underflow/empty" #[],
  mkCase "err/type/top-int" #[intV 1],
  mkCase "err/type/top-null" #[.null],
  mkCase "err/type/top-cell" #[.cell cellA],
  mkCase "err/type/top-slice" #[.slice fullSliceA],
  mkCase "err/type/top-builder" #[.builder Builder.empty],
  mkCase "err/type/top-empty-tuple" #[.tuple #[]],
  mkCase "err/type/program-pushint" #[] #[.pushInt (.num 7), setExitAltInstr],
  mkCase "err/type/program-add-result" #[intV 3, intV 4] #[.add, setExitAltInstr],
  mkCase "err/underflow/program-drop-before-set" #[q0V] #[.pop 0, setExitAltInstr],

  -- Decode boundaries for the 16-bit opcode width.
  mkCaseCode "err/decode/truncated-8-prefix" #[] setExitAltTruncated8Code,
  mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] setExitAltTruncated15Code
]

def suite : InstrSuite where
  id := setExitAltId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSetExitAltFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-setexitalt"
          (runSetExitAltFallback setExitAltInstr #[q0V])
          #[] }
    ,
    { name := "unit/error/underflow-and-type-ordering"
      run := do
        expectErr "underflow/empty" (runSetExitAltDirect #[]) .stkUnd
        expectErr "type/top-int" (runSetExitAltDirect #[intV 1]) .typeChk
        let st ← expectRawErr "type/pop-before-check"
          (runSetExitAltRaw #[intV 77, .null] q5 q6)
          .typeChk
        if st.stack != #[intV 77] then
          throw (IO.userError s!"type/pop-before-check: expected stack #[77], got {reprStr st.stack}")
        else if st.regs.c0 != q5 then
          throw (IO.userError s!"type/pop-before-check: expected c0 unchanged={reprStr q5}, got {reprStr st.regs.c0}")
        else if st.regs.c1 != q6 then
          throw (IO.userError s!"type/pop-before-check: expected c1 unchanged={reprStr q6}, got {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/cregs/quit-wraps-and-captures-old-c0-c1"
      run := do
        let st ← expectRawOk "cregs/quit-wrap"
          (runSetExitAltRaw #[intV 3, q0V] q5 q6)
        if st.stack != #[intV 3] then
          throw (IO.userError s!"cregs/quit-wrap: stack mismatch {reprStr st.stack}")
        else if st.regs.c0 != q5 then
          throw (IO.userError s!"cregs/quit-wrap: expected c0 unchanged={reprStr q5}, got {reprStr st.regs.c0}")
        else
          expectEnvelopeCaptured "cregs/quit-wrap" st.regs.c1 q0 q5 q6 }
    ,
    { name := "unit/order/writeback-after-define-c1"
      run := do
        let st ← expectRawOk "order/writeback-after-define-c1"
          (runSetExitAltRaw #[q0V] q7 q9)
        if st.regs.c0 != q7 then
          throw (IO.userError
            s!"order/writeback-after-define-c1: expected c0 unchanged={reprStr q7}, got {reprStr st.regs.c0}")
        else
          expectEnvelopeCaptured "order/writeback-after-define-c1" st.regs.c1 q0 q7 q9 }
    ,
    { name := "unit/cregs/preexisting-fields-are-not-overwritten"
      run := do
        let st ← expectRawOk "cregs/preexisting-keep"
          (runSetExitAltRaw #[.cont preCont] q5 q6)
        if !st.stack.isEmpty then
          throw (IO.userError s!"cregs/preexisting-keep: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c0 != q5 then
          throw (IO.userError
            s!"cregs/preexisting-keep: expected c0 unchanged={reprStr q5}, got {reprStr st.regs.c0}")
        else
          match st.regs.c1 with
          | .ordinary code saved cregs cdata =>
              if code != preCode then
                throw (IO.userError
                  s!"cregs/preexisting-keep: expected code {reprStr preCode}, got {reprStr code}")
              else if saved != q9 then
                throw (IO.userError
                  s!"cregs/preexisting-keep: expected saved={reprStr q9}, got {reprStr saved}")
              else if cregs.c0 != some q70 then
                throw (IO.userError
                  s!"cregs/preexisting-keep: expected cregs.c0={reprStr q70}, got {reprStr cregs.c0}")
              else if cregs.c1 != some q71 then
                throw (IO.userError
                  s!"cregs/preexisting-keep: expected cregs.c1={reprStr q71}, got {reprStr cregs.c1}")
              else if cdata.nargs != preCdata.nargs then
                throw (IO.userError
                  s!"cregs/preexisting-keep: expected cdata.nargs={preCdata.nargs}, got {cdata.nargs}")
              else if cdata.stack != preCdata.stack then
                throw (IO.userError
                  s!"cregs/preexisting-keep: expected cdata.stack={reprStr preCdata.stack}, got {reprStr cdata.stack}")
              else
                pure ()
          | other =>
              throw (IO.userError
                s!"cregs/preexisting-keep: expected ordinary continuation, got {reprStr other}") }
    ,
    { name := "unit/decode/setexitalt-and-truncated-prefix"
      run := do
        expectDecodeSetExitAlt "decode/setexitalt" setExitAltCode
        expectDecodeErr "decode/truncated-8" setExitAltTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" setExitAltTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile setExitAltId setExitAltFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SETEXITALT
