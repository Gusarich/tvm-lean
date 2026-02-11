import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.JMPDICT

/-!
JMPDICT branch map (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.contExt (.jmpDict idx)`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.jump` / jump-time stack shaping)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`pushSmallInt`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`JMPDICT` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`JMPDICT` encode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_jmpdict`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::jump`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::push_smallint`)

Behavior under test:
1. Dispatch: only `.contExt (.jmpDict _)` matches this handler.
2. Immediate: C++ masks args with `0x3fff` before push.
3. Transfer: push idx then `jump(c3)` (not call).
4. Jump-time checks/shaping: `nargs` underflow checks and captured-stack branches.
5. Ordering: pushed idx participates in jump checks; caller tail is skipped after jump.
-/

private def jmpDictId : InstrId := { name := "JMPDICT" }

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def dispatchSentinel : Int := 64123
private def c3Marker : Int := 3303
private def tailMarker : Int := 4404
private def method8Tag : Int := 8001
private def method14Tag : Int := 14002

private def noiseCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def noiseCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[noiseCellA]

private def noiseSliceB : Slice :=
  Slice.ofCell noiseCellB

private def deepStackA : Array Value :=
  #[.null, intV 5, .cell noiseCellA]

private def deepStackB : Array Value :=
  #[.builder Builder.empty, .slice noiseSliceB, intV (-9)]

private def deepStackC : Array Value :=
  #[.cell noiseCellB, intV 123, .null]

private def range255 : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:255] do
      out := out.push (intV (Int.ofNat i))
    out

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def assembleNoRefBits! (label : String) (program : Array Instr) : BitString :=
  (assembleNoRefCell! label program).bits

private def mkDictRootWithMethod!
    (label : String)
    (key : Int)
    (n : Nat)
    (unsigned : Bool)
    (methodCode : Cell) : Cell :=
  let keyBits :=
    match dictKeyBits? key n unsigned with
    | some kb => kb
    | none => panic! s!"{label}: invalid key/range ({key}, n={n}, unsigned={unsigned})"
  let valueSlice : Slice := Slice.ofCell methodCode
  match dictSetSliceWithCells none keyBits valueSlice .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _ok, _created, _loaded) =>
      panic! s!"{label}: dict set returned none root"
  | .error e =>
      panic! s!"{label}: dict set failed: {e}"

private def mkPushRefCodeCell! (label : String) (refCell : Cell) (tail : Array Instr) : Cell :=
  Cell.mkOrdinary (natToBits 0x88 8 ++ assembleNoRefBits! s!"{label}/tail" tail) #[refCell]

private def mkPushRefContCodeCell! (label : String) (refCell : Cell) (tail : Array Instr) : Cell :=
  Cell.mkOrdinary (natToBits 0x8a 8 ++ assembleNoRefBits! s!"{label}/tail" tail) #[refCell]

private def jmpDictInstr (idx : Nat) : Instr :=
  .contExt (.jmpDict idx)

private def mkJmpDictViaC3Code!
    (label : String)
    (c3Code : Cell)
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Cell :=
  mkPushRefContCodeCell! label c3Code (#[.popCtr 3, jmpDictInstr idx] ++ tail)

private def methodCode8 : Cell :=
  assembleNoRefCell! "jmpdict/method8" #[.pushInt (.num method8Tag), .ret]

private def methodCode14 : Cell :=
  assembleNoRefCell! "jmpdict/method14" #[.pushInt (.num method14Tag), .ret]

private def dictSigned8Key7 : Cell :=
  mkDictRootWithMethod! "jmpdict/dict8" 7 8 false methodCode8

private def dictSigned14Key300 : Cell :=
  mkDictRootWithMethod! "jmpdict/dict14" 300 14 false methodCode14

private def c3CallN8 : Cell :=
  mkPushRefCodeCell! "jmpdict/c3-call-n8" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false true false, .pushInt (.num c3Marker), .ret]

private def c3CallN8PushZ : Cell :=
  mkPushRefCodeCell! "jmpdict/c3-call-n8-z" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false true true, .pushInt (.num c3Marker), .ret]

private def c3JumpN8 : Cell :=
  mkPushRefCodeCell! "jmpdict/c3-jump-n8" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false false false, .pushInt (.num c3Marker), .ret]

private def c3CallN14 : Cell :=
  mkPushRefCodeCell! "jmpdict/c3-call-n14" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false true false, .pushInt (.num c3Marker), .ret]

private def c3CallN14PushZ : Cell :=
  mkPushRefCodeCell! "jmpdict/c3-call-n14-z" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false true true, .pushInt (.num c3Marker), .ret]

private def c3JumpN14 : Cell :=
  mkPushRefCodeCell! "jmpdict/c3-jump-n14" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false false false, .pushInt (.num c3Marker), .ret]

private def c3TypeNNull : Cell :=
  mkPushRefCodeCell! "jmpdict/c3-type-n-null" dictSigned8Key7
    #[.pushNull, .dictGetExec false true false]

private def c3TypeDictFromIdx : Cell :=
  assembleNoRefCell! "jmpdict/c3-type-dict-from-idx"
    #[.pushInt (.num 8), .dictGetExec false true false]

private def c3RangeNTooLarge : Cell :=
  assembleNoRefCell! "jmpdict/c3-range-n-too-large"
    #[.pushInt (.num 1024), .dictGetExec false true false]

private def c3RangeNNegative : Cell :=
  assembleNoRefCell! "jmpdict/c3-range-n-negative"
    #[.pushInt (.num (-1)), .dictGetExec false true false]

private def ordinaryCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def envelopeCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .envelope (.quit 5) OrdCregs.empty { stack := captured, nargs := nargs }

private def runJmpDictDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt (jmpDictInstr idx) stack

private def runJmpDictDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runJmpDictRaw
    (idx : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowLoopExt (jmpDictInstr idx) (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected error {expected}, got success")
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def mkProgCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpDictId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpDictId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def progJmpOnly (idx : Nat) : Array Instr :=
  #[jmpDictInstr idx, .pushInt (.num tailMarker)]

private def progSetC3FromCtr (ctr : Nat) (idx : Nat) : Array Instr :=
  #[.pushCtr ctr, .popCtr 3, jmpDictInstr idx, .pushInt (.num tailMarker)]

private def progSetNumC3ThenJmp (more : Int) (idx : Nat) (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num more), .setNumVarArgs, .popCtr 3, jmpDictInstr idx] ++ tail

private def oracleCases : Array OracleCase :=
  #[
    -- Default c3 (quit 11): JMPDICT pushes idx then jumps to c3; caller tail is skipped.
    mkProgCase "default-c3/idx-0/empty" #[] (progJmpOnly 0),
    mkProgCase "default-c3/idx-1/deep-a" deepStackA (progJmpOnly 1),
    mkProgCase "default-c3/idx-42/deep-b" deepStackB (progJmpOnly 42),
    mkProgCase "default-c3/idx-255/deep-c" deepStackC (progJmpOnly 255),
    mkProgCase "default-c3/idx-256/empty" #[] (progJmpOnly 256),
    mkProgCase "default-c3/idx-257/deep-a" deepStackA (progJmpOnly 257),
    mkProgCase "default-c3/idx-4095/deep-b" deepStackB (progJmpOnly 4095),
    mkProgCase "default-c3/idx-16383/deep-c" deepStackC (progJmpOnly 16383),

    -- c3 retargeted from control registers.
    mkProgCase "set-c3/c0/idx-7" #[] (progSetC3FromCtr 0 7),
    mkProgCase "set-c3/c0/idx-1024" deepStackA (progSetC3FromCtr 0 1024),
    mkProgCase "set-c3/c1/idx-7" #[] (progSetC3FromCtr 1 7),
    mkProgCase "set-c3/c1/idx-1024" deepStackB (progSetC3FromCtr 1 1024),
    mkProgCase "set-c3/c2/idx-0" #[] (progSetC3FromCtr 2 0),
    mkProgCase "set-c3/c2/idx-255" deepStackA (progSetC3FromCtr 2 255),
    mkProgCase "set-c3/c2/idx-256" deepStackB (progSetC3FromCtr 2 256),
    mkProgCase "set-c3/c2/idx-16383" deepStackC (progSetC3FromCtr 2 16383),

    -- Jump-time nargs checks via synthesized c3 (`SETNUMVARARGS` + `POPCTR 3`).
    mkProgCase "setnum-c3/more0/idx-7/empty" #[] (progSetNumC3ThenJmp 0 7),
    mkProgCase "setnum-c3/more0/idx-255/deep-a" deepStackA (progSetNumC3ThenJmp 0 255),
    mkProgCase "setnum-c3/more1/idx-7/empty" #[] (progSetNumC3ThenJmp 1 7),
    mkProgCase "setnum-c3/more1/idx-7/deep-a" deepStackA (progSetNumC3ThenJmp 1 7),
    mkProgCase "setnum-c3/more1/idx-16383/deep-b" deepStackB (progSetNumC3ThenJmp 1 16383),
    mkProgCase "setnum-c3/more2/idx-7/empty-underflow" #[] (progSetNumC3ThenJmp 2 7),
    mkProgCase "setnum-c3/more2/idx-7/one-arg" #[intV 1] (progSetNumC3ThenJmp 2 7),
    mkProgCase "setnum-c3/more2/idx-7/two-args" #[intV 1, intV 2] (progSetNumC3ThenJmp 2 7),
    mkProgCase "setnum-c3/more2/idx-7/three-args" #[intV 1, intV 2, intV 3] (progSetNumC3ThenJmp 2 7),
    mkProgCase "setnum-c3/more3/idx-255/one-arg-underflow" #[intV 1] (progSetNumC3ThenJmp 3 255),
    mkProgCase "setnum-c3/more255/idx-0/depth255" range255 (progSetNumC3ThenJmp 255 0),
    mkProgCase "setnum-c3/more255/idx-0/empty-underflow" #[] (progSetNumC3ThenJmp 255 0),

    -- Custom c3 dictionary dispatch programs.
    mkCodeCase "dict-call/n8/hit/idx-7" #[] (mkJmpDictViaC3Code! "oracle/n8-hit-7" c3CallN8 7),
    mkCodeCase "dict-call/n8/miss/idx-6" #[] (mkJmpDictViaC3Code! "oracle/n8-miss-6" c3CallN8 6),
    mkCodeCase "dict-call/n8/range/idx-200" #[] (mkJmpDictViaC3Code! "oracle/n8-range-200" c3CallN8 200),
    mkCodeCase "dict-call/n14/hit/idx-300" #[] (mkJmpDictViaC3Code! "oracle/n14-hit-300" c3CallN14 300),
    mkCodeCase "dict-call/n14/miss/idx-301" #[] (mkJmpDictViaC3Code! "oracle/n14-miss-301" c3CallN14 301),
    mkCodeCase "dict-call/n14/range/idx-9000" #[] (mkJmpDictViaC3Code! "oracle/n14-range-9000" c3CallN14 9000),
    mkCodeCase "dict-call-z/n8/miss/idx-6" #[] (mkJmpDictViaC3Code! "oracle/n8z-miss-6" c3CallN8PushZ 6),
    mkCodeCase "dict-call-z/n14/range/idx-9000" #[] (mkJmpDictViaC3Code! "oracle/n14z-range-9000" c3CallN14PushZ 9000),
    mkCodeCase "dict-jump/n8/hit/idx-7" #[] (mkJmpDictViaC3Code! "oracle/n8j-hit-7" c3JumpN8 7),
    mkCodeCase "dict-jump/n8/miss/idx-6" #[] (mkJmpDictViaC3Code! "oracle/n8j-miss-6" c3JumpN8 6),
    mkCodeCase "dict-jump/n14/hit/idx-300" #[] (mkJmpDictViaC3Code! "oracle/n14j-hit-300" c3JumpN14 300),
    mkCodeCase "dict-jump/n14/miss/idx-301" #[] (mkJmpDictViaC3Code! "oracle/n14j-miss-301" c3JumpN14 301),

    -- Type/range ordering paths in downstream dict-get-exec continuations.
    mkCodeCase "dict-errors/type-n-null" #[] (mkJmpDictViaC3Code! "oracle/type-n-null" c3TypeNNull 7),
    mkCodeCase "dict-errors/type-dict-from-idx-int" #[] (mkJmpDictViaC3Code! "oracle/type-dict-from-idx" c3TypeDictFromIdx 7),
    mkCodeCase "dict-errors/range-n-too-large" #[] (mkJmpDictViaC3Code! "oracle/range-n-too-large" c3RangeNTooLarge 7),
    mkCodeCase "dict-errors/range-n-negative" #[] (mkJmpDictViaC3Code! "oracle/range-n-negative" c3RangeNNegative 7)
  ]

def suite : InstrSuite where
  id := jmpDictId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runJmpDictDispatchFallback .add deepStackA)
          (deepStackA ++ #[intV dispatchSentinel])
        expectOkStack "dispatch/matched-jmpdict"
          (runHandlerDirectWithNext execInstrFlowLoopExt (jmpDictInstr 7) (VM.push (intV dispatchSentinel)) #[])
          #[intV 7] }
    ,
    { name := "unit/raw/push-then-jump-c3-quit"
      run := do
        let regs : Regs := { Regs.initial with c3 := .quit 9 }
        let st ← expectRawOk "raw/c3-quit" (runJmpDictRaw 17 deepStackA regs)
        if st.stack != (deepStackA ++ #[intV 17]) then
          throw (IO.userError s!"raw/c3-quit: stack mismatch {reprStr st.stack}")
        else if st.cc != .quit 9 then
          throw (IO.userError s!"raw/c3-quit: expected cc=quit9, got {reprStr st.cc}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"raw/c3-quit: expected c0 unchanged quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/raw/jump-underflow-order-ordinary"
      run := do
        let needTwo : Continuation := ordinaryCont 2 #[]
        let regsNeedTwo : Regs := { Regs.initial with c3 := needTwo }
        let st ← expectRawErr "raw/nargs-underflow-ordinary" (runJmpDictRaw 5 #[] regsNeedTwo) .stkUnd
        if st.stack != #[intV 5] then
          throw (IO.userError s!"raw/nargs-underflow-ordinary: expected pushed idx preserved, got {reprStr st.stack}")
        else if st.cc != defaultCc then
          throw (IO.userError s!"raw/nargs-underflow-ordinary: cc changed to {reprStr st.cc}")
        else
          pure () }
    ,
    { name := "unit/raw/jump-underflow-order-envelope"
      run := do
        let envNeedThree : Continuation := envelopeCont 3 #[]
        let regsNeedThree : Regs := { Regs.initial with c3 := envNeedThree }
        let st ← expectRawErr "raw/nargs-underflow-envelope" (runJmpDictRaw 7 #[intV 11] regsNeedThree) .stkUnd
        if st.stack != #[intV 11, intV 7] then
          throw (IO.userError s!"raw/nargs-underflow-envelope: expected stack #[11,7], got {reprStr st.stack}")
        else if st.cc != defaultCc then
          throw (IO.userError s!"raw/nargs-underflow-envelope: cc changed to {reprStr st.cc}")
        else
          pure () }
    ,
    { name := "unit/raw/jump-captured-stack-ordinary"
      run := do
        let regs : Regs := { Regs.initial with c3 := ordinaryCont 1 #[intV 99] }
        let st ← expectRawOk "raw/captured-ordinary" (runJmpDictRaw 5 #[intV 11, intV 22] regs)
        if st.stack != #[intV 99, intV 5] then
          throw (IO.userError s!"raw/captured-ordinary: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/jump-captured-stack-envelope"
      run := do
        let regs : Regs := { Regs.initial with c3 := envelopeCont 1 #[intV 55] }
        let st ← expectRawOk "raw/captured-envelope" (runJmpDictRaw 7 #[intV 11, intV 22] regs)
        if st.stack != #[intV 55, intV 7] then
          throw (IO.userError s!"raw/captured-envelope: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/jump-nargs-zero-drops-stack"
      run := do
        let regs : Regs := { Regs.initial with c3 := ordinaryCont 0 #[] }
        let st ← expectRawOk "raw/nargs-zero" (runJmpDictRaw 33 deepStackB regs)
        if !st.stack.isEmpty then
          throw (IO.userError s!"raw/nargs-zero: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/stack-gas-for-captured-branch"
      run := do
        let captured : Array Value :=
          Id.run do
            let mut out : Array Value := #[]
            for i in [0:40] do
              out := out.push (intV (Int.ofNat (i + 1)))
            out
        let below : Array Value :=
          Id.run do
            let mut out : Array Value := #[]
            for i in [0:10] do
              out := out.push (intV (Int.ofNat (i + 1)))
            out
        let idx : Nat := 19
        let regs : Regs := { Regs.initial with c3 := ordinaryCont 10 captured }
        let st ← expectRawOk "raw/stack-gas" (runJmpDictRaw idx below regs)
        let source : Array Value := below ++ #[intV (Int.ofNat idx)]
        let args : Array Value := source.extract (source.size - 10) source.size
        let expectedStack : Array Value := captured ++ args
        let expectedDepth : Nat := expectedStack.size
        let expectedGas : Int :=
          Int.ofNat (expectedDepth - freeStackDepth) * stackEntryGasPrice
        if st.stack != expectedStack then
          throw (IO.userError s!"raw/stack-gas: expected {reprStr expectedStack}, got {reprStr st.stack}")
        else if st.gas.gasConsumed != expectedGas then
          throw (IO.userError
            s!"raw/stack-gas: expected gasConsumed={expectedGas}, got {st.gas.gasConsumed}")
        else
          pure () }
    ,
    { name := "unit/opcode/decode-width-and-range"
      run := do
        let seq : Array Instr := #[
          jmpDictInstr 0,
          jmpDictInstr 1,
          jmpDictInstr 255,
          jmpDictInstr 256,
          jmpDictInstr 16383,
          .callDict 7,
          .prepareDict 2,
          .add
        ]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/jmpdict-0" s0 (jmpDictInstr 0) 24
        let s2 ← expectDecodeStep "decode/jmpdict-1" s1 (jmpDictInstr 1) 24
        let s3 ← expectDecodeStep "decode/jmpdict-255" s2 (jmpDictInstr 255) 24
        let s4 ← expectDecodeStep "decode/jmpdict-256" s3 (jmpDictInstr 256) 24
        let s5 ← expectDecodeStep "decode/jmpdict-16383" s4 (jmpDictInstr 16383) 24
        let s6 ← expectDecodeStep "decode/calldict-7" s5 (.callDict 7) 16
        let s7 ← expectDecodeStep "decode/preparedict-2" s6 (.prepareDict 2) 24
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining != 0 then
          throw (IO.userError s!"decode/seq-end: expected exhausted bits, got {s8.bitsRemaining}")

        match encodeCp0 (jmpDictInstr 16384) with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"encode/jmpdict-16384: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "encode/jmpdict-16384: expected rangeChk, got success") }
    ,
    { name := "unit/raw/synthetic-idx-mask-regression"
      run := do
        -- Synthetic direct handler input (not cp0-decodable): mirror C++ arg mask.
        let huge : Nat := 0x12345
        let masked : Int := Int.ofNat (huge &&& 0x3fff)
        let regs : Regs := { Regs.initial with c3 := .quit 7 }
        let st ← expectRawOk "raw/idx-mask" (runJmpDictRaw huge #[] regs)
        if st.stack != #[intV masked] then
          throw (IO.userError s!"raw/idx-mask: expected masked idx {masked}, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec jmpDictId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.JMPDICT
