import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.THENRETALT

/-
THENRETALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cont/AtExit.lean` (`.contExt .thenretAlt` branch)
  - `TvmLean/Model/Cont/Continuation.lean` (`forceCdata`, `defineC0`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_thenret_alt`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`force_cregs`)

Mapped behavior covered by this suite:
1. Dispatch branch:
  - `.contExt .thenretAlt` handled;
  - non-matching instructions fall through to `next`.
2. Pop/type ordering:
  - underflow (`stkUnd`) before type checks;
  - non-cont top yields `typeChk` after popping the top value.
3. Core THENRETALT rewrite:
  - pop continuation `k`;
  - compute `compose0(k, c1)` as `k.defineC0(c1)` (define-only, no overwrite);
  - push rewritten continuation back to stack.
4. `force_cregs` parity:
  - when `k` has no cdata (e.g. `quit`), operation wraps it into an envelope-like continuation
    before defining `c0`.
5. Register non-mutation:
  - `c0` and `c1` registers remain unchanged by THENRETALT itself.
-/

private def thenRetAltId : InstrId := { name := "THENRETALT" }

private def thenRetAltInstr : Instr := .contExt .thenretAlt

private def dispatchSentinel : Int := 8147

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q9 : Continuation := .quit 9

private def q0V : Value := .cont q0

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def fullSliceA : Slice := Slice.ofCell cellA

private def retCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0xdb30 16) #[]

private def retCodeSlice : Slice := Slice.ofCell retCodeCell

private def thenRetAltRawCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf7 16) #[]

private def thenRetAltTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def thenRetAltTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf7 >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[thenRetAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := thenRetAltId
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
    instr := thenRetAltId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runThenRetAltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContAtExit thenRetAltInstr stack

private def runThenRetAltDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContAtExit instr (VM.push (intV dispatchSentinel)) stack

private def runThenRetAltRaw
    (stack : Array Value)
    (c0 : Continuation := q0)
    (c1 : Continuation := q1)
    (instr : Instr := thenRetAltInstr)
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

private def expectTopEnvelopeWithC0
    (label : String)
    (stack : Array Value)
    (expectedExt : Continuation)
    (expectedC0 : Continuation) : IO Unit := do
  match stack.back? with
  | some (.cont k) => expectEnvelopeWithC0 label k expectedExt expectedC0
  | some v => throw (IO.userError s!"{label}: expected top continuation, got {reprStr v}")
  | none => throw (IO.userError s!"{label}: expected non-empty stack")

private def expectTopOrdinaryWithC0
    (label : String)
    (stack : Array Value)
    (expectedCode : Slice)
    (expectedSaved : Continuation)
    (expectedC0 : Continuation) : IO Unit := do
  match stack.back? with
  | some (.cont k) => expectOrdinaryWithC0 label k expectedCode expectedSaved expectedC0
  | some v => throw (IO.userError s!"{label}: expected top continuation, got {reprStr v}")
  | none => throw (IO.userError s!"{label}: expected non-empty stack")

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

private def expectDecodeThenRetAlt
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != thenRetAltInstr then
        throw (IO.userError s!"{label}: expected {reprStr thenRetAltInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def thenRetAltGasExact : Int :=
  computeExactGasBudget thenRetAltInstr

private def thenRetAltGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne thenRetAltInstr

private def thenRetAltOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/program/",
    "ok/control/",
    "err/underflow/",
    "err/type/",
    "err/order/",
    "ok/decode/",
    "err/decode/",
    "gas/"
  ]

private def thenRetAltFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := thenRetAltOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def thenRetAltNoisePool : Array (Array Value) :=
  #[
    #[q0V],
    #[intV 1, q0V],
    #[.null, q0V],
    #[.cell cellA, q0V],
    #[.slice fullSliceA, q0V],
    #[.builder Builder.empty, q0V],
    #[.tuple #[], q0V]
  ]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genThenRetAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (noise, rng2) := pickFromPool thenRetAltNoisePool rng1
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/basic" noise
    else if shape = 1 then
      mkCase "fuzz/ok/program-pushctr0" #[q0V] #[thenRetAltInstr, .pushCtr 0]
    else if shape = 2 then
      mkCase "fuzz/err/underflow-empty" #[]
    else if shape = 3 then
      mkCase "fuzz/err/type-top-int" #[intV 0]
    else if shape = 4 then
      mkCase "fuzz/err/order-type-before-below-cont" #[q0V, .null]
    else if shape = 5 then
      mkCaseCode "fuzz/ok/decode-raw-opcode" #[q0V] thenRetAltRawCode
    else if shape = 6 then
      mkCaseCode "fuzz/err/decode-truncated-8" #[] thenRetAltTruncated8Code
    else if shape = 7 then
      mkCaseCode "fuzz/err/decode-truncated-15" #[q0V] thenRetAltTruncated15Code
    else if shape = 8 then
      mkCase "fuzz/gas/exact-cost-succeeds"
        #[q0V]
        #[.pushInt (.num thenRetAltGasExact), .tonEnvOp .setGasLimit, thenRetAltInstr]
    else if shape = 9 then
      mkCase "fuzz/gas/exact-minus-one-out-of-gas"
        #[q0V]
        #[.pushInt (.num thenRetAltGasExactMinusOne), .tonEnvOp .setGasLimit, thenRetAltInstr]
    else
      mkCase "fuzz/ok/control-tail" #[q0V] #[thenRetAltInstr, .pushInt (.num 7)]
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

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

  mkCase "ok/program/thenretalt-then-pushctr0" #[q0V] #[thenRetAltInstr, .pushCtr 0],
  mkCase "ok/program/thenretalt-then-pushctr1" #[q0V] #[thenRetAltInstr, .pushCtr 1],

  mkCase "ok/control/tail-runs-after-thenretalt" #[q0V] #[thenRetAltInstr, .pushInt (.num 7)],
  mkCase "ok/control/tail-runs-add" #[q0V] #[thenRetAltInstr, .pushInt (.num 2), .pushInt (.num 3), .add],

  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/second-thenretalt" #[q0V] #[thenRetAltInstr, thenRetAltInstr],
  mkCase "err/underflow/third-thenretalt-chain" #[q0V, q0V] #[thenRetAltInstr, thenRetAltInstr, thenRetAltInstr],

  mkCase "err/type/top-int" #[intV 0],
  mkCase "err/type/top-null" #[.null],
  mkCase "err/type/top-cell" #[.cell cellA],
  mkCase "err/type/top-slice" #[.slice fullSliceA],
  mkCase "err/type/top-builder-empty" #[.builder Builder.empty],
  mkCase "err/type/top-empty-tuple" #[.tuple #[]],
  mkCase "err/type/top-nan-via-program" #[] #[.pushInt .nan, thenRetAltInstr],
  mkCase "err/order/type-before-below-cont" #[q0V, .null],
  mkCase "err/order/type-before-below-cont-via-program" #[q0V] #[.pushInt (.num 42), thenRetAltInstr],
  mkCase "err/order/type-before-below-cont-via-program-nan" #[q0V] #[.pushInt .nan, thenRetAltInstr],

  mkCaseCode "ok/decode/raw-opcode-edf7" #[q0V] thenRetAltRawCode,
  mkCaseCode "err/decode/truncated-8" #[] thenRetAltTruncated8Code,
  mkCaseCode "err/decode/truncated-15" #[q0V] thenRetAltTruncated15Code,

  mkCase "gas/exact-cost-succeeds"
    #[q0V]
    #[.pushInt (.num thenRetAltGasExact), .tonEnvOp .setGasLimit, thenRetAltInstr],
  mkCase "gas/exact-minus-one-out-of-gas"
    #[q0V]
    #[.pushInt (.num thenRetAltGasExactMinusOne), .tonEnvOp .setGasLimit, thenRetAltInstr]
]

def suite : InstrSuite where
  id := thenRetAltId
  unit := #[
    { name := "unit/dispatch/thenretalt-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runThenRetAltDispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-thenretalt"
          (runThenRetAltDirect #[q0V])
          #[.cont (q0.defineC0 q1)] }
    ,
    { name := "unit/errors/underflow-and-top-pop-order"
      run := do
        expectErr "underflow/empty"
          (runThenRetAltDirect #[]) .stkUnd
        expectErr "type/top-int"
          (runThenRetAltDirect #[intV 0]) .typeChk

        let st ← expectRawErr "order/top-popped-before-type-error"
          (runThenRetAltRaw #[q0V, .null]) .typeChk
        if st.stack != #[q0V] then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected stack #[q0], got {reprStr st.stack}")
        else if st.regs.c0 != q0 then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected c0 unchanged (quit0), got {reprStr st.regs.c0}")
        else if st.regs.c1 != q1 then
          throw (IO.userError
            s!"order/top-popped-before-type-error: expected c1 unchanged (quit1), got {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/raw/force-cdata-wraps-quit-and-captures-current-c1"
      run := do
        let st ← expectRawOk "raw/force-cdata-wraps-quit"
          (runThenRetAltRaw #[q0V] q9 q1)
        if st.regs.c0 != q9 then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected c0 unchanged, got {reprStr st.regs.c0}")
        else if st.regs.c1 != q1 then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected c1 unchanged, got {reprStr st.regs.c1}")
        else if st.stack.size != 1 then
          throw (IO.userError s!"raw/force-cdata-wraps-quit: expected stack size=1, got {st.stack.size}")
        else
          expectTopEnvelopeWithC0 "raw/force-cdata-wraps-quit" st.stack q0 q1 }
    ,
    { name := "unit/raw/ordinary-cont-define-c0-and-no-overwrite"
      run := do
        let ordNoC0 : Continuation := .ordinary retCodeSlice q0 OrdCregs.empty OrdCdata.empty
        let stDefined ← expectRawOk "raw/ordinary-define-c0"
          (runThenRetAltRaw #[.cont ordNoC0] q0 q9)
        expectTopOrdinaryWithC0 "raw/ordinary-define-c0" stDefined.stack retCodeSlice q0 q9

        let ordWithC0 : Continuation :=
          .ordinary retCodeSlice q0 ({ OrdCregs.empty with c0 := some q1 }) OrdCdata.empty
        let stNoOverwrite ← expectRawOk "raw/no-overwrite-existing-c0"
          (runThenRetAltRaw #[.cont ordWithC0] q0 q9)
        expectTopOrdinaryWithC0 "raw/no-overwrite-existing-c0" stNoOverwrite.stack retCodeSlice q0 q1 }
    ,
    { name := "unit/raw/stack-shape-and-lower-values-preserved"
      run := do
        let st ← expectRawOk "raw/stack-shape-preserved"
          (runThenRetAltRaw #[intV 5, .null, q0V])
        if st.stack.size != 3 then
          throw (IO.userError s!"raw/stack-shape-preserved: expected stack size=3, got {st.stack.size}")
        else if st.stack[0]! != intV 5 then
          throw (IO.userError
            s!"raw/stack-shape-preserved: expected bottom int 5, got {reprStr (st.stack[0]!)}")
        else if st.stack[1]! != .null then
          throw (IO.userError
            s!"raw/stack-shape-preserved: expected middle null, got {reprStr (st.stack[1]!)}")
        else
          expectTopEnvelopeWithC0 "raw/stack-shape-preserved" st.stack q0 q1 }
    ,
    { name := "unit/decode/thenretalt-and-truncated-prefix"
      run := do
        expectDecodeThenRetAlt "decode/thenretalt" thenRetAltRawCode
        expectDecodeErr "decode/truncated-8" thenRetAltTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" thenRetAltTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr thenRetAltId
      count := 500
      gen := genThenRetAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.THENRETALT
