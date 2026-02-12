import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.CALLDICT

/-!
CALLDICT branch map (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/CallDict.lean`
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.call` transfer behavior)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (short/long decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (range and short/long encoding)
  - `TvmLean/Semantics/Exec/Dict/DictGetExec.lean` (dict-dispatch continuation path)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_calldict_short`, `exec_calldict`, registration)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::call`)
  - `/Users/daniil/Coding/ton/crypto/vm/dictops.cpp` (`exec_dict_get_exec`)

Branch map covered by this suite:
1) Dispatch:
- `.callDict _` executes this handler; non-matching opcodes must fall through to `next`.

2) Immediate decode/encode:
- short form: opcode `0xf0` + 8-bit idx (`0..255`) => 16-bit instruction;
- long form: prefix `0x3c4` + 14-bit idx (`0..16383`) => 24-bit instruction;
- encoding idx > 0x3fff must reject with `rangeChk`.

3) CALLDICT transfer core:
- push immediate idx on stack;
- call continuation from `c3` with normal `VM.call` semantics.

4) c3 continuation branch conditions:
- `quit`/`excQuit` targets;
- ordinary/envelope cdata `nargs` satisfaction vs `stkUnd`;
- has-`c0` continuations reducing call to jump semantics.

5) Related dict-cont behavior (via custom c3 continuation):
- dict hit -> transfer to method continuation;
- dict miss;
- key out-of-range (quiet miss);
- pushZ variants;
- doCall vs doJump transfer path;
- dict-get-exec type/range error ordering (`n` type/range before dict/key use).
-/

private def callDictId : InstrId := { name := "CALLDICT" }

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
  -- PUSHREF (0x88) + one ref, then no-ref tail.
  Cell.mkOrdinary (natToBits 0x88 8 ++ assembleNoRefBits! s!"{label}/tail" tail) #[refCell]

private def mkPushRefContCodeCell! (label : String) (refCell : Cell) (tail : Array Instr) : Cell :=
  -- PUSHREFCONT (0x8a) + one ref, then no-ref tail.
  Cell.mkOrdinary (natToBits 0x8a 8 ++ assembleNoRefBits! s!"{label}/tail" tail) #[refCell]

private def mkCallDictViaC3Code!
    (label : String)
    (c3Code : Cell)
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Cell :=
  mkPushRefContCodeCell! label c3Code (#[.popCtr 3, .callDict idx] ++ tail)

private def methodCode8 : Cell :=
  assembleNoRefCell! "calldict/method8" #[.pushInt (.num method8Tag), .ret]

private def methodCode14 : Cell :=
  assembleNoRefCell! "calldict/method14" #[.pushInt (.num method14Tag), .ret]

private def dictSigned8Key7 : Cell :=
  mkDictRootWithMethod! "calldict/dict8" 7 8 false methodCode8

private def dictSigned14Key300 : Cell :=
  mkDictRootWithMethod! "calldict/dict14" 300 14 false methodCode14

private def c3CallN8 : Cell :=
  mkPushRefCodeCell! "calldict/c3-call-n8" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false true false, .pushInt (.num c3Marker), .ret]

private def c3CallN8PushZ : Cell :=
  mkPushRefCodeCell! "calldict/c3-call-n8-z" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false true true, .pushInt (.num c3Marker), .ret]

private def c3JumpN8 : Cell :=
  mkPushRefCodeCell! "calldict/c3-jump-n8" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false false false, .pushInt (.num c3Marker), .ret]

private def c3CallN14 : Cell :=
  mkPushRefCodeCell! "calldict/c3-call-n14" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false true false, .pushInt (.num c3Marker), .ret]

private def c3CallN14PushZ : Cell :=
  mkPushRefCodeCell! "calldict/c3-call-n14-z" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false true true, .pushInt (.num c3Marker), .ret]

private def c3JumpN14 : Cell :=
  mkPushRefCodeCell! "calldict/c3-jump-n14" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false false false, .pushInt (.num c3Marker), .ret]

private def c3TypeNNull : Cell :=
  mkPushRefCodeCell! "calldict/c3-type-n-null" dictSigned8Key7
    #[.pushNull, .dictGetExec false true false]

private def c3TypeDictFromIdx : Cell :=
  assembleNoRefCell! "calldict/c3-type-dict-from-idx"
    #[.pushInt (.num 8), .dictGetExec false true false]

private def c3RangeNTooLarge : Cell :=
  assembleNoRefCell! "calldict/c3-range-n-too-large"
    #[.pushInt (.num 1024), .dictGetExec false true false]

private def c3RangeNNegative : Cell :=
  assembleNoRefCell! "calldict/c3-range-n-negative"
    #[.pushInt (.num (-1)), .dictGetExec false true false]

private def ordinaryCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def envelopeCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .envelope (.quit 5) OrdCregs.empty { stack := captured, nargs := nargs }

private def runCallDictDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowCallDict (.callDict idx) stack

private def runCallDictDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallDict instr (VM.push (intV dispatchSentinel)) stack

private def runCallDictRaw
    (idx : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowCallDict (.callDict idx) (pure ())).run st0

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
    instr := callDictId
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
    instr := callDictId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def progCallOnly (idx : Nat) : Array Instr :=
  #[.callDict idx, .pushInt (.num tailMarker)]

private def progSetC3FromCtr (ctr : Nat) (idx : Nat) : Array Instr :=
  #[.pushCtr ctr, .popCtr 3, .callDict idx, .pushInt (.num tailMarker)]

private def callDictFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "default-c3/",
      "set-c3/",
      "dict-call/",
      "dict-call-z/",
      "dict-jump/",
      "dict-errors/"
    ]
    -- Bias toward call/jump stack-shape perturbations while still exercising all mutation modes.
    mutationModes := #[
      0, 0, 0, 0,
      1, 1, 1,
      2, 2,
      3, 3, 3,
      4
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def callDictIdxPool : Array Nat := #[0, 1, 42, 255, 256, 1024, 4095, 16383]
private def callDictStackPool : Array (Array Value) := #[#[], deepStackA, deepStackB, deepStackC]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genCallDictFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let (idx, rng2) := pickFromPool callDictIdxPool rng1
  let (stack, rng3) := pickFromPool callDictStackPool rng2
  let case0 :=
    if shape = 0 then
      mkProgCase "fuzz/ok/default-c3" stack (progCallOnly idx)
    else if shape = 1 then
      mkProgCase "fuzz/ok/set-c3/c0" stack (progSetC3FromCtr 0 idx)
    else if shape = 2 then
      mkCodeCase "fuzz/ok/dict-call/n8-hit" #[] (mkCallDictViaC3Code! "fuzz/n8-hit" c3CallN8 7)
    else if shape = 3 then
      mkCodeCase "fuzz/ok/dict-call-z/n8-miss" #[] (mkCallDictViaC3Code! "fuzz/n8z-miss" c3CallN8PushZ 6)
    else if shape = 4 then
      mkCodeCase "fuzz/ok/dict-jump/n14-hit" #[] (mkCallDictViaC3Code! "fuzz/n14j-hit" c3JumpN14 300)
    else if shape = 5 then
      mkCodeCase "fuzz/err/dict/type-n-null" #[] (mkCallDictViaC3Code! "fuzz/type-n-null" c3TypeNNull 7)
    else if shape = 6 then
      mkCodeCase "fuzz/err/dict/range-n-too-large" #[] (mkCallDictViaC3Code! "fuzz/range-n" c3RangeNTooLarge 7)
    else
      mkCodeCase "fuzz/err/dict/type-dict-from-idx" #[] (mkCallDictViaC3Code! "fuzz/type-dict" c3TypeDictFromIdx 7)
  let (tag, rng4) := randNat rng3 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

private def oracleCases : Array OracleCase :=
  #[
    -- Default c3 (quit 11): CALLDICT pushes idx then calls c3; trailing caller code is not reached.
    mkProgCase "default-c3/short/idx-0/empty" #[] (progCallOnly 0),
    mkProgCase "default-c3/short/idx-1/deep-a" deepStackA (progCallOnly 1),
    mkProgCase "default-c3/short/idx-42/deep-b" deepStackB (progCallOnly 42),
    mkProgCase "default-c3/short/idx-255/deep-c" deepStackC (progCallOnly 255),
    mkProgCase "default-c3/long/idx-256/empty" #[] (progCallOnly 256),
    mkProgCase "default-c3/long/idx-257/deep-a" deepStackA (progCallOnly 257),
    mkProgCase "default-c3/long/idx-4095/deep-b" deepStackB (progCallOnly 4095),
    mkProgCase "default-c3/long/idx-16383/deep-c" deepStackC (progCallOnly 16383),

    -- c3 retargeted via ctr ops (no initCregs dependence).
    mkProgCase "set-c3/c0/short/idx-7" #[] (progSetC3FromCtr 0 7),
    mkProgCase "set-c3/c0/long/idx-1024" deepStackA (progSetC3FromCtr 0 1024),
    mkProgCase "set-c3/c1/short/idx-7" #[] (progSetC3FromCtr 1 7),
    mkProgCase "set-c3/c1/long/idx-1024" deepStackB (progSetC3FromCtr 1 1024),
    mkProgCase "set-c3/c2/short/idx-0" #[] (progSetC3FromCtr 2 0),
    mkProgCase "set-c3/c2/short/idx-255" deepStackA (progSetC3FromCtr 2 255),
    mkProgCase "set-c3/c2/long/idx-256" deepStackB (progSetC3FromCtr 2 256),
    mkProgCase "set-c3/c2/long/idx-16383" deepStackC (progSetC3FromCtr 2 16383),

    -- Custom c3 dictionary dispatch: signed n=8/14, doCall path.
    mkCodeCase "dict-call/n8/hit/idx-7" #[] (mkCallDictViaC3Code! "oracle/n8-hit-7" c3CallN8 7),
    mkCodeCase "dict-call/n8/miss/idx-6" #[] (mkCallDictViaC3Code! "oracle/n8-miss-6" c3CallN8 6),
    mkCodeCase "dict-call/n8/range/idx-200" #[] (mkCallDictViaC3Code! "oracle/n8-range-200" c3CallN8 200),
    mkCodeCase "dict-call/n8/hit/deep-a" deepStackA (mkCallDictViaC3Code! "oracle/n8-hit-deep-a" c3CallN8 7),
    mkCodeCase "dict-call/n8/miss/deep-b" deepStackB (mkCallDictViaC3Code! "oracle/n8-miss-deep-b" c3CallN8 6),

    mkCodeCase "dict-call/n14/hit/idx-300" #[] (mkCallDictViaC3Code! "oracle/n14-hit-300" c3CallN14 300),
    mkCodeCase "dict-call/n14/miss/idx-301" #[] (mkCallDictViaC3Code! "oracle/n14-miss-301" c3CallN14 301),
    mkCodeCase "dict-call/n14/range/idx-9000" #[] (mkCallDictViaC3Code! "oracle/n14-range-9000" c3CallN14 9000),
    mkCodeCase "dict-call/n14/hit/deep-c" deepStackC (mkCallDictViaC3Code! "oracle/n14-hit-deep-c" c3CallN14 300),
    mkCodeCase "dict-call/n14/miss/deep-a" deepStackA (mkCallDictViaC3Code! "oracle/n14-miss-deep-a" c3CallN14 301),

    -- Custom c3 dictionary dispatch with pushZ=true.
    mkCodeCase "dict-call-z/n8/hit/idx-7" #[] (mkCallDictViaC3Code! "oracle/n8z-hit-7" c3CallN8PushZ 7),
    mkCodeCase "dict-call-z/n8/miss/idx-6" #[] (mkCallDictViaC3Code! "oracle/n8z-miss-6" c3CallN8PushZ 6),
    mkCodeCase "dict-call-z/n8/range/idx-200" #[] (mkCallDictViaC3Code! "oracle/n8z-range-200" c3CallN8PushZ 200),
    mkCodeCase "dict-call-z/n8/miss/deep-b" deepStackB (mkCallDictViaC3Code! "oracle/n8z-miss-deep-b" c3CallN8PushZ 6),
    mkCodeCase "dict-call-z/n14/miss/idx-301" #[] (mkCallDictViaC3Code! "oracle/n14z-miss-301" c3CallN14PushZ 301),
    mkCodeCase "dict-call-z/n14/range/idx-9000" #[] (mkCallDictViaC3Code! "oracle/n14z-range-9000" c3CallN14PushZ 9000),

    -- Custom c3 dictionary dispatch with doCall=false (jump transfer).
    mkCodeCase "dict-jump/n8/hit/idx-7" #[] (mkCallDictViaC3Code! "oracle/n8j-hit-7" c3JumpN8 7),
    mkCodeCase "dict-jump/n8/miss/idx-6" #[] (mkCallDictViaC3Code! "oracle/n8j-miss-6" c3JumpN8 6),
    mkCodeCase "dict-jump/n8/range/idx-200" #[] (mkCallDictViaC3Code! "oracle/n8j-range-200" c3JumpN8 200),
    mkCodeCase "dict-jump/n14/hit/idx-300" #[] (mkCallDictViaC3Code! "oracle/n14j-hit-300" c3JumpN14 300),
    mkCodeCase "dict-jump/n14/miss/idx-301" #[] (mkCallDictViaC3Code! "oracle/n14j-miss-301" c3JumpN14 301),
    mkCodeCase "dict-jump/n14/range/idx-9000" #[] (mkCallDictViaC3Code! "oracle/n14j-range-9000" c3JumpN14 9000),

    -- Type/range ordering paths inside custom c3 dict-get-exec continuations.
    mkCodeCase "dict-errors/type-n-null" #[] (mkCallDictViaC3Code! "oracle/type-n-null" c3TypeNNull 7),
    mkCodeCase "dict-errors/type-dict-from-idx-int" #[] (mkCallDictViaC3Code! "oracle/type-dict-from-idx" c3TypeDictFromIdx 7),
    mkCodeCase "dict-errors/range-n-too-large" #[] (mkCallDictViaC3Code! "oracle/range-n-too-large" c3RangeNTooLarge 7),
    mkCodeCase "dict-errors/range-n-negative" #[] (mkCallDictViaC3Code! "oracle/range-n-negative" c3RangeNNegative 7)
  ]

def suite : InstrSuite where
  id := callDictId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runCallDictDispatchFallback .add deepStackA)
          (deepStackA ++ #[intV dispatchSentinel])
        expectOkStack "dispatch/matched-calldict"
          (runHandlerDirectWithNext execInstrFlowCallDict (.callDict 7) (VM.push (intV dispatchSentinel)) #[])
          #[intV 7] }
    ,
    { name := "unit/raw/push-then-call-c3-quit"
      run := do
        let regs : Regs := { Regs.initial with c3 := .quit 9 }
        let st ← expectRawOk "raw/c3-quit" (runCallDictRaw 17 deepStackA regs)
        if st.stack != (deepStackA ++ #[intV 17]) then
          throw (IO.userError s!"raw/c3-quit: stack mismatch {reprStr st.stack}")
        else if st.cc != .quit 9 then
          throw (IO.userError s!"raw/c3-quit: expected cc=quit9, got {reprStr st.cc}")
        else
          match st.regs.c0 with
          | .ordinary _ _ _ _ => pure ()
          | other => throw (IO.userError s!"raw/c3-quit: expected return cont in c0, got {reprStr other}") }
    ,
    { name := "unit/raw/call-semantics-nargs-and-captured-stack"
      run := do
        let needTwo : Continuation := ordinaryCont 2 #[]
        let regsNeedTwo : Regs := { Regs.initial with c3 := needTwo }
        let _ ← expectRawErr "raw/nargs-underflow" (runCallDictRaw 5 #[] regsNeedTwo) .stkUnd

        let needOneCaptured : Continuation := ordinaryCont 1 #[intV 99]
        let regsNeedOneCaptured : Regs := { Regs.initial with c3 := needOneCaptured }
        let st ← expectRawOk "raw/nargs-one-captured" (runCallDictRaw 5 #[intV 11, intV 22] regsNeedOneCaptured)
        if st.stack != #[intV 99, intV 5] then
          throw (IO.userError s!"raw/nargs-one-captured: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/has-c0-reduces-call-to-jump"
      run := do
        let target : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0)
            { OrdCregs.empty with c0 := some (.quit 31337) }
            OrdCdata.empty
        let regs : Regs := { Regs.initial with c3 := target }
        let st ← expectRawOk "raw/has-c0" (runCallDictRaw 33 deepStackB regs)
        if st.cc != target then
          throw (IO.userError s!"raw/has-c0: expected jump to target, got {reprStr st.cc}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"raw/has-c0: c0 should remain unchanged, got {reprStr st.regs.c0}")
        else if st.stack != (deepStackB ++ #[intV 33]) then
          throw (IO.userError s!"raw/has-c0: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/envelope-underflow-and-success"
      run := do
        let envNeedThree : Continuation := envelopeCont 3 #[]
        let regsNeedThree : Regs := { Regs.initial with c3 := envNeedThree }
        let _ ← expectRawErr "raw/env-underflow" (runCallDictRaw 7 #[intV 1] regsNeedThree) .stkUnd

        let envCapturedOne : Continuation := envelopeCont 1 #[intV 55]
        let regsCapturedOne : Regs := { Regs.initial with c3 := envCapturedOne }
        let st ← expectRawOk "raw/env-captured" (runCallDictRaw 7 #[intV 11, intV 22] regsCapturedOne)
        if st.stack != #[intV 55, intV 7] then
          throw (IO.userError s!"raw/env-captured: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/opcode/decode-short-long-boundary-and-range"
      run := do
        let seq : Array Instr := #[
          .callDict 0,
          .callDict 255,
          .callDict 256,
          .callDict 16383,
          .contExt (.jmpDict 1),
          .prepareDict 2,
          .add
        ]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/cd-0" s0 (.callDict 0) 16
        let s2 ← expectDecodeStep "decode/cd-255" s1 (.callDict 255) 16
        let s3 ← expectDecodeStep "decode/cd-256" s2 (.callDict 256) 24
        let s4 ← expectDecodeStep "decode/cd-16383" s3 (.callDict 16383) 24
        let s5 ← expectDecodeStep "decode/jmpdict-1" s4 (.contExt (.jmpDict 1)) 24
        let s6 ← expectDecodeStep "decode/preparedict-2" s5 (.prepareDict 2) 24
        let s7 ← expectDecodeStep "decode/tail-add" s6 .add 8
        if s7.bitsRemaining != 0 then
          throw (IO.userError s!"decode/seq-end: expected exhausted bits, got {s7.bitsRemaining}")

        match encodeCp0 (.callDict 16384) with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"encode/cd-16384: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "encode/cd-16384: expected rangeChk, got success") }
    ,
    { name := "unit/raw/synthetic-idx-mask-regression"
      run := do
        -- Synthetic direct handler input (not cp0-decodable): match C++ handler arg mask behavior.
        let huge : Nat := 0x12345
        let masked : Int := Int.ofNat (huge &&& 0x3fff)
        let regs : Regs := { Regs.initial with c3 := .quit 7 }
        let st ← expectRawOk "raw/idx-mask" (runCallDictRaw huge #[] regs)
        if st.stack != #[intV masked] then
          throw (IO.userError s!"raw/idx-mask: expected masked idx {masked}, got {reprStr st.stack}")
        else
          pure () }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr callDictId
      count := 500
      gen := genCallDictFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.CALLDICT
