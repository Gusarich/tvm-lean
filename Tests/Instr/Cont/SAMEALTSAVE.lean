import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SAMEALTSAVE

/-
SAMEALTSAVE branch map (Lean + C++):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cont/SameAltSave.lean`
  - `TvmLean/Model/Cont/Continuation.lean` (`forceCdata`, `defineC1`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont` parity baseline)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_samealt(save=true)`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`force_cregs`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.h` (`ControlRegs::define_c1`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont` parity baseline)

Mapped behavior covered below:
1. Dispatch:
  - `.sameAltSave` handled; other instructions fall through to `next`.
2. Core mutation order:
  - read `c0`; define missing `c1` in that continuation from current VM `c1`;
  - write back `c0`; then set VM `c1 := c0`.
3. define semantics:
  - `define_c1` only defines when absent (no overwrite);
  - `force_cregs`/`forceCdata` wraps non-cdata continuations into envelope form.
4. Control flow:
  - SAMEALTSAVE itself does not pop stack and does not jump/call; execution continues.
5. Observability:
  - RETALT-chain and continuation-shaping programs expose define/no-overwrite behavior,
    envelope wrapping, and post-instruction fallthrough.
-/

private def sameAltSaveId : InstrId := { name := "SAMEALTSAVE" }

private def sameAltSaveInstr : Instr := .sameAltSave

private def retAltInstr : Instr := .retAlt

private def dispatchSentinel : Int := 62107

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q5 : Continuation := .quit 5
private def q7 : Continuation := .quit 7
private def q9 : Continuation := .quit 9
private def q11 : Continuation := .quit 11

private def q0V : Value := .cont q0

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def fullSliceA : Slice :=
  Slice.ofCell cellA

private def fullSliceB : Slice :=
  Slice.ofCell cellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[q0V, .null, intV (-4), .cell cellB]

private def retAltCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0xdb31 16) #[]

private def retAltCodeSlice : Slice :=
  Slice.ofCell retAltCodeCell

private def sameAltSaveRawCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedfb 16) #[]

private def sameAltSaveTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def sameAltSaveTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedfb >>> 1) 15) #[]

private def sameAltSaveGasExact : Int :=
  computeExactGasBudget sameAltSaveInstr

private def sameAltSaveGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sameAltSaveInstr

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sameAltSaveInstr, retAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sameAltSaveId
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
    instr := sameAltSaveId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runSameAltSaveFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContSameAltSave instr (VM.push (intV dispatchSentinel)) stack

private def runSameAltSaveRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc)
    (instr : Instr := sameAltSaveInstr)
    (next : VM Unit := pure ()) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrContSameAltSave instr next).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

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

private def expectDecodeSameAltSave
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != sameAltSaveInstr then
        throw (IO.userError s!"{label}: expected .sameAltSave, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def progSetC0FromC1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, sameAltSaveInstr, retAltInstr] ++ tail

private def progSetC0Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, sameAltSaveInstr, retAltInstr] ++ tail

private def progSetC0Captured (capture : Int) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 0,
    sameAltSaveInstr, retAltInstr] ++ tail

private def progSetC0RetAltWithC1FromC0 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushRefCont retAltCodeCell, .setContCtr 1, .popCtr 0, sameAltSaveInstr, retAltInstr] ++ tail

private def oracleCases : Array OracleCase := #[
  -- Basic SAMEALTSAVE + RETALT observations on default control registers.
  mkCase "ok/basic/empty" #[],
  mkCase "ok/basic/int" #[intV 5],
  mkCase "ok/basic/null-int" #[.null, intV 9],
  mkCase "ok/basic/cell" #[.cell cellA],
  mkCase "ok/basic/slice" #[.slice fullSliceB],
  mkCase "ok/basic/builder" #[.builder Builder.empty],
  mkCase "ok/basic/tuple-empty" #[.tuple #[]],
  mkCase "ok/basic/cont-quit0" #[q0V],
  mkCase "ok/basic/noise-a" noiseA,
  mkCase "ok/basic/noise-b" noiseB,
  mkCase "ok/basic/noise-c" noiseC,
  mkCase "ok/basic/trailing-push-skipped" #[intV 3] #[sameAltSaveInstr, retAltInstr, .pushInt (.num 777)],
  mkCase "ok/basic/trailing-add-skipped" #[intV 6, intV 2] #[sameAltSaveInstr, retAltInstr, .add],

  -- Prepare c0 from c1 before SAMEALTSAVE.
  mkCase "ok/c0-from-c1/empty" #[] (progSetC0FromC1),
  mkCase "ok/c0-from-c1/int" #[intV 12] (progSetC0FromC1),
  mkCase "ok/c0-from-c1/noise-a" noiseA (progSetC0FromC1),
  mkCase "ok/c0-from-c1/noise-b" noiseB (progSetC0FromC1),
  mkCase "ok/c0-from-c1/trailing-push-skipped" #[intV 4] (progSetC0FromC1 #[.pushInt (.num 111)]),
  mkCase "ok/c0-from-c1/trailing-add-skipped"
    #[intV 1, intV 2] (progSetC0FromC1 #[.add]),

  -- c0 nargs coverage via SETNUMVARARGS, then SAMEALTSAVE + RETALT.
  mkCase "ok/nargs0/empty" #[] (progSetC0Nargs 0),
  mkCase "ok/nargs0/noise-a" noiseA (progSetC0Nargs 0),
  mkCase "err/nargs1/empty-underflow" #[] (progSetC0Nargs 1),
  mkCase "ok/nargs1/one-int" #[intV 33] (progSetC0Nargs 1),
  mkCase "ok/nargs1/one-null" #[.null] (progSetC0Nargs 1),
  mkCase "err/nargs2/empty-underflow" #[] (progSetC0Nargs 2),
  mkCase "err/nargs2/one-underflow" #[intV 44] (progSetC0Nargs 2),
  mkCase "ok/nargs2/two-int" #[intV 4, intV 5] (progSetC0Nargs 2),
  mkCase "ok/nargs2/two-noise" #[.null, intV 5] (progSetC0Nargs 2),
  mkCase "err/nargs3/two-underflow" #[intV 2, intV 3] (progSetC0Nargs 3),
  mkCase "ok/nargs3/three-int" #[intV 1, intV 2, intV 3] (progSetC0Nargs 3),
  mkCase "ok/nargs1/trailing-skipped" #[intV 7] (progSetC0Nargs 1 #[.pushInt (.num 999)]),

  -- c0 captured-stack merge coverage via SETCONTVARARGS(copy=1), then SAMEALTSAVE + RETALT.
  mkCase "ok/captured/more-minus1/empty-init" #[] (progSetC0Captured 70 (-1)),
  mkCase "ok/captured/more-minus1/one-init" #[intV 9] (progSetC0Captured 71 (-1)),
  mkCase "ok/captured/more0/empty-init" #[] (progSetC0Captured 72 0),
  mkCase "err/captured/more1/empty-underflow" #[] (progSetC0Captured 73 1),
  mkCase "ok/captured/more1/one-init" #[intV 9] (progSetC0Captured 74 1),
  mkCase "err/captured/more2/one-underflow" #[intV 9] (progSetC0Captured 75 2),
  mkCase "ok/captured/more2/two-init" #[intV 1, intV 2] (progSetC0Captured 76 2),
  mkCase "ok/captured/more0/noise-init" noiseA (progSetC0Captured 77 0),
  mkCase "ok/captured/more0/trailing-skipped" #[intV 4]
    (progSetC0Captured 78 0 #[.pushInt (.num 1234)]),
  mkCase "ok/captured/more1/two-init" #[intV 8, intV 9] (progSetC0Captured 79 1),

  -- Control-flow continuation and instruction-local failure fences.
  mkCase "ok/control/tail-runs-after-samealtsave" #[intV 2] #[sameAltSaveInstr, .pushInt (.num 5), .add],
  mkCase "err/control/tail-underflow-after-samealtsave" #[] #[sameAltSaveInstr, .add],

  -- Decode and gas boundaries.
  mkCaseCode "ok/decode/raw-opcode-edfb" #[q0V] sameAltSaveRawCode,
  mkCaseCode "err/decode/truncated-8" #[] sameAltSaveTruncated8Code,
  mkCaseCode "err/decode/truncated-15" #[intV 1] sameAltSaveTruncated15Code,
  mkCase "gas/exact-cost-succeeds"
    #[q0V]
    #[.pushInt (.num sameAltSaveGasExact), .tonEnvOp .setGasLimit, sameAltSaveInstr],
  mkCase "gas/exact-minus-one-out-of-gas"
    #[q0V]
    #[.pushInt (.num sameAltSaveGasExactMinusOne), .tonEnvOp .setGasLimit, sameAltSaveInstr]
]

def suite : InstrSuite where
  id := sameAltSaveId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSameAltSaveFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]

        expectOkStack "dispatch/matched-samealtsave-does-not-run-next"
          (runSameAltSaveFallback sameAltSaveInstr #[intV 9])
          #[intV 9] }
    ,
    { name := "unit/raw/force-cdata-wraps-and-captures-old-c1"
      run := do
        let regs : Regs := { Regs.initial with c0 := q7, c1 := q9 }
        let st ← expectRawOk "raw/force-cdata-wraps"
          (runSameAltSaveRaw noiseA regs q11)
        if st.stack != noiseA then
          throw (IO.userError s!"raw/force-cdata-wraps: expected stack unchanged, got {reprStr st.stack}")
        else if st.cc != q11 then
          throw (IO.userError s!"raw/force-cdata-wraps: expected cc unchanged, got {reprStr st.cc}")
        else if st.regs.c0 != st.regs.c1 then
          throw (IO.userError s!"raw/force-cdata-wraps: expected c0 == c1, got {reprStr st.regs}")
        else
          expectEnvelopeWithC1 "raw/force-cdata-wraps" st.regs.c0 q7 q9 }
    ,
    { name := "unit/raw/ordinary-define-c1-and-no-overwrite"
      run := do
        let ordNoC1 : Continuation := .ordinary retAltCodeSlice q0 OrdCregs.empty OrdCdata.empty
        let stDefined ← expectRawOk "raw/ordinary-define-c1"
          (runSameAltSaveRaw noiseB { Regs.initial with c0 := ordNoC1, c1 := q9 } q11)
        if stDefined.regs.c0 != stDefined.regs.c1 then
          throw (IO.userError s!"raw/ordinary-define-c1: expected c0 == c1, got {reprStr stDefined.regs}")
        else
          expectOrdinaryWithC1 "raw/ordinary-define-c1" stDefined.regs.c0 retAltCodeSlice q0 q9

        let ordWithC1 : Continuation :=
          .ordinary retAltCodeSlice q0 ({ OrdCregs.empty with c1 := some q1 }) OrdCdata.empty
        let stNoOverwrite ← expectRawOk "raw/no-overwrite-existing-c1"
          (runSameAltSaveRaw noiseC { Regs.initial with c0 := ordWithC1, c1 := q9 } q11)
        if stNoOverwrite.regs.c0 != stNoOverwrite.regs.c1 then
          throw (IO.userError s!"raw/no-overwrite-existing-c1: expected c0 == c1, got {reprStr stNoOverwrite.regs}")
        else
          expectOrdinaryWithC1 "raw/no-overwrite-existing-c1" stNoOverwrite.regs.c0 retAltCodeSlice q0 q1 }
    ,
    { name := "unit/raw/ordering-define-before-writeback"
      run := do
        let ordNoC1 : Continuation := .ordinary retAltCodeSlice q0 OrdCregs.empty OrdCdata.empty
        let st ← expectRawOk "raw/ordering-define-before-writeback"
          (runSameAltSaveRaw #[] { Regs.initial with c0 := ordNoC1, c1 := q5 } q11)
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"raw/ordering-define-before-writeback: expected empty stack, got {reprStr st.stack}")
        else
          expectOrdinaryWithC1 "raw/ordering-define-before-writeback" st.regs.c0 retAltCodeSlice q0 q5 }
    ,
    { name := "unit/raw/no-stack-access"
      run := do
        let stEmpty ← expectRawOk "raw/no-stack-access/empty"
          (runSameAltSaveRaw #[] { Regs.initial with c0 := q5, c1 := q1 } q11)
        if stEmpty.stack != #[] then
          throw (IO.userError s!"raw/no-stack-access/empty: expected empty stack, got {reprStr stEmpty.stack}")

        let stDeep ← expectRawOk "raw/no-stack-access/deep"
          (runSameAltSaveRaw noiseC { Regs.initial with c0 := q7, c1 := q5 } q11)
        if stDeep.stack != noiseC then
          throw (IO.userError s!"raw/no-stack-access/deep: expected stack unchanged, got {reprStr stDeep.stack}") }
    ,
    { name := "unit/opcode/decode-and-truncated-prefix"
      run := do
        let assembled ←
          match assembleCp0 [sameAltSaveInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/samealtsave failed: {reprStr e}")
        if assembled.bits = natToBits 0xedfb 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/samealtsave: expected 0xedfb, got {reprStr assembled.bits}")

        expectDecodeSameAltSave "decode/samealtsave" sameAltSaveRawCode
        expectDecodeErr "decode/truncated-8" sameAltSaveTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" sameAltSaveTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SAMEALTSAVE
