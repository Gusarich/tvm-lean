import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.CALLDICT_LONG

/-!
CALLDICT_LONG branch map (Lean + C++ reference):
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
- long form: prefix `0x3c4` + 14-bit idx (`0..16383`) => 24-bit instruction;
- short form remains valid for canonical encoding when `idx < 256`.

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

private def callDictLongId : InstrId := { name := "CALLDICT_LONG" }
private def callDictLongPrefix10 : Nat := 0x3c4

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

private def callDictLongWord (idx : Nat) : Nat :=
  (callDictLongPrefix10 <<< 14) + (idx &&& 0x3fff)

private def callDictLongBits (idx : Nat) : BitString :=
  natToBits (callDictLongWord idx) 24

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

private def mkCallDictLongCode!
    (label : String)
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Cell :=
  Cell.mkOrdinary (callDictLongBits idx ++ assembleNoRefBits! s!"{label}/tail" tail) #[]

private def mkSetC3FromCtrAndCallLongCode!
    (label : String)
    (ctr : Nat)
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Cell :=
  let preBits := assembleNoRefBits! s!"{label}/pre" #[.pushCtr ctr, .popCtr 3]
  let tailBits := assembleNoRefBits! s!"{label}/tail" tail
  Cell.mkOrdinary (preBits ++ callDictLongBits idx ++ tailBits) #[]

private def mkCallDictLongViaC3Code!
    (label : String)
    (c3Code : Cell)
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Cell :=
  -- PUSHREFCONT (0x8a) + c3 ref, then POPCTR 3 + CALLDICT_LONG + optional tail.
  let popC3Bits := assembleNoRefBits! s!"{label}/pop-c3" #[.popCtr 3]
  let tailBits := assembleNoRefBits! s!"{label}/tail" tail
  Cell.mkOrdinary (natToBits 0x8a 8 ++ popC3Bits ++ callDictLongBits idx ++ tailBits) #[c3Code]

private def methodCode8 : Cell :=
  assembleNoRefCell! "calldict-long/method8" #[.pushInt (.num method8Tag), .ret]

private def methodCode14 : Cell :=
  assembleNoRefCell! "calldict-long/method14" #[.pushInt (.num method14Tag), .ret]

private def dictSigned8Key7 : Cell :=
  mkDictRootWithMethod! "calldict-long/dict8" 7 8 false methodCode8

private def dictSigned14Key300 : Cell :=
  mkDictRootWithMethod! "calldict-long/dict14" 300 14 false methodCode14

private def c3CallN8 : Cell :=
  mkPushRefCodeCell! "calldict-long/c3-call-n8" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false true false, .pushInt (.num c3Marker), .ret]

private def c3CallN8PushZ : Cell :=
  mkPushRefCodeCell! "calldict-long/c3-call-n8-z" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false true true, .pushInt (.num c3Marker), .ret]

private def c3JumpN8 : Cell :=
  mkPushRefCodeCell! "calldict-long/c3-jump-n8" dictSigned8Key7
    #[.pushInt (.num 8), .dictGetExec false false false, .pushInt (.num c3Marker), .ret]

private def c3CallN14 : Cell :=
  mkPushRefCodeCell! "calldict-long/c3-call-n14" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false true false, .pushInt (.num c3Marker), .ret]

private def c3CallN14PushZ : Cell :=
  mkPushRefCodeCell! "calldict-long/c3-call-n14-z" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false true true, .pushInt (.num c3Marker), .ret]

private def c3JumpN14 : Cell :=
  mkPushRefCodeCell! "calldict-long/c3-jump-n14" dictSigned14Key300
    #[.pushInt (.num 14), .dictGetExec false false false, .pushInt (.num c3Marker), .ret]

private def c3TypeNNull : Cell :=
  mkPushRefCodeCell! "calldict-long/c3-type-n-null" dictSigned8Key7
    #[.pushNull, .dictGetExec false true false]

private def c3TypeDictFromIdx : Cell :=
  assembleNoRefCell! "calldict-long/c3-type-dict-from-idx"
    #[.pushInt (.num 8), .dictGetExec false true false]

private def c3RangeNTooLarge : Cell :=
  assembleNoRefCell! "calldict-long/c3-range-n-too-large"
    #[.pushInt (.num 1024), .dictGetExec false true false]

private def c3RangeNNegative : Cell :=
  assembleNoRefCell! "calldict-long/c3-range-n-negative"
    #[.pushInt (.num (-1)), .dictGetExec false true false]

private def ordinaryCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def envelopeCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .envelope (.quit 5) OrdCregs.empty { stack := captured, nargs := nargs }

private def runCallDictLongDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallDict instr (VM.push (intV dispatchSentinel)) stack

private def runCallDictLongRaw
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

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callDictLongId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def callDictLongOracleFamilies : Array String :=
  #[
    "long/default-c3/",
    "long/set-c3/",
    "long/dict-call/",
    "long/dict-call-z/",
    "long/dict-jump/",
    "long/dict-errors/"
  ]

private def callDictLongFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := callDictLongOracleFamilies
    -- Bias toward call/jump stack-shape perturbations while exercising all mutation modes.
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

private def oracleCases : Array OracleCase :=
  #[
    -- Default c3 (quit 11): CALLDICT_LONG pushes idx then calls c3; trailing caller code is not reached.
    mkCodeCase "long/default-c3/idx-0/empty" #[] (mkCallDictLongCode! "oracle/default-idx-0" 0),
    mkCodeCase "long/default-c3/idx-1/deep-a" deepStackA (mkCallDictLongCode! "oracle/default-idx-1" 1),
    mkCodeCase "long/default-c3/idx-42/deep-b" deepStackB (mkCallDictLongCode! "oracle/default-idx-42" 42),
    mkCodeCase "long/default-c3/idx-255/deep-c" deepStackC (mkCallDictLongCode! "oracle/default-idx-255" 255),
    mkCodeCase "long/default-c3/idx-256/empty" #[] (mkCallDictLongCode! "oracle/default-idx-256" 256),
    mkCodeCase "long/default-c3/idx-257/deep-a" deepStackA (mkCallDictLongCode! "oracle/default-idx-257" 257),
    mkCodeCase "long/default-c3/idx-4095/deep-b" deepStackB (mkCallDictLongCode! "oracle/default-idx-4095" 4095),
    mkCodeCase "long/default-c3/idx-16383/deep-c" deepStackC (mkCallDictLongCode! "oracle/default-idx-16383" 16383),

    -- c3 retargeted via ctr ops (no initCregs dependence).
    mkCodeCase "long/set-c3/c0/idx-7" #[] (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c0-7" 0 7),
    mkCodeCase "long/set-c3/c0/idx-1024" deepStackA (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c0-1024" 0 1024),
    mkCodeCase "long/set-c3/c1/idx-7" #[] (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c1-7" 1 7),
    mkCodeCase "long/set-c3/c1/idx-1024" deepStackB (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c1-1024" 1 1024),
    mkCodeCase "long/set-c3/c2/idx-0" #[] (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c2-0" 2 0),
    mkCodeCase "long/set-c3/c2/idx-255" deepStackA (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c2-255" 2 255),
    mkCodeCase "long/set-c3/c2/idx-256" deepStackB (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c2-256" 2 256),
    mkCodeCase "long/set-c3/c2/idx-16383" deepStackC (mkSetC3FromCtrAndCallLongCode! "oracle/set-c3-c2-16383" 2 16383),

    -- Custom c3 dictionary dispatch: signed n=8/14, doCall path.
    mkCodeCase "long/dict-call/n8/hit/idx-7" #[] (mkCallDictLongViaC3Code! "oracle/n8-hit-7" c3CallN8 7),
    mkCodeCase "long/dict-call/n8/miss/idx-6" #[] (mkCallDictLongViaC3Code! "oracle/n8-miss-6" c3CallN8 6),
    mkCodeCase "long/dict-call/n8/range/idx-200" #[] (mkCallDictLongViaC3Code! "oracle/n8-range-200" c3CallN8 200),
    mkCodeCase "long/dict-call/n8/hit/deep-a" deepStackA (mkCallDictLongViaC3Code! "oracle/n8-hit-deep-a" c3CallN8 7),
    mkCodeCase "long/dict-call/n8/miss/deep-b" deepStackB (mkCallDictLongViaC3Code! "oracle/n8-miss-deep-b" c3CallN8 6),

    mkCodeCase "long/dict-call/n14/hit/idx-300" #[] (mkCallDictLongViaC3Code! "oracle/n14-hit-300" c3CallN14 300),
    mkCodeCase "long/dict-call/n14/miss/idx-301" #[] (mkCallDictLongViaC3Code! "oracle/n14-miss-301" c3CallN14 301),
    mkCodeCase "long/dict-call/n14/range/idx-9000" #[] (mkCallDictLongViaC3Code! "oracle/n14-range-9000" c3CallN14 9000),
    mkCodeCase "long/dict-call/n14/hit/deep-c" deepStackC (mkCallDictLongViaC3Code! "oracle/n14-hit-deep-c" c3CallN14 300),
    mkCodeCase "long/dict-call/n14/miss/deep-a" deepStackA (mkCallDictLongViaC3Code! "oracle/n14-miss-deep-a" c3CallN14 301),

    -- Custom c3 dictionary dispatch with pushZ=true.
    mkCodeCase "long/dict-call-z/n8/hit/idx-7" #[] (mkCallDictLongViaC3Code! "oracle/n8z-hit-7" c3CallN8PushZ 7),
    mkCodeCase "long/dict-call-z/n8/miss/idx-6" #[] (mkCallDictLongViaC3Code! "oracle/n8z-miss-6" c3CallN8PushZ 6),
    mkCodeCase "long/dict-call-z/n8/range/idx-200" #[] (mkCallDictLongViaC3Code! "oracle/n8z-range-200" c3CallN8PushZ 200),
    mkCodeCase "long/dict-call-z/n8/miss/deep-b" deepStackB (mkCallDictLongViaC3Code! "oracle/n8z-miss-deep-b" c3CallN8PushZ 6),
    mkCodeCase "long/dict-call-z/n14/miss/idx-301" #[] (mkCallDictLongViaC3Code! "oracle/n14z-miss-301" c3CallN14PushZ 301),
    mkCodeCase "long/dict-call-z/n14/range/idx-9000" #[] (mkCallDictLongViaC3Code! "oracle/n14z-range-9000" c3CallN14PushZ 9000),

    -- Custom c3 dictionary dispatch with doCall=false (jump transfer).
    mkCodeCase "long/dict-jump/n8/hit/idx-7" #[] (mkCallDictLongViaC3Code! "oracle/n8j-hit-7" c3JumpN8 7),
    mkCodeCase "long/dict-jump/n8/miss/idx-6" #[] (mkCallDictLongViaC3Code! "oracle/n8j-miss-6" c3JumpN8 6),
    mkCodeCase "long/dict-jump/n8/range/idx-200" #[] (mkCallDictLongViaC3Code! "oracle/n8j-range-200" c3JumpN8 200),
    mkCodeCase "long/dict-jump/n14/hit/idx-300" #[] (mkCallDictLongViaC3Code! "oracle/n14j-hit-300" c3JumpN14 300),
    mkCodeCase "long/dict-jump/n14/miss/idx-301" #[] (mkCallDictLongViaC3Code! "oracle/n14j-miss-301" c3JumpN14 301),
    mkCodeCase "long/dict-jump/n14/range/idx-9000" #[] (mkCallDictLongViaC3Code! "oracle/n14j-range-9000" c3JumpN14 9000),

    -- Type/range ordering paths inside custom c3 dict-get-exec continuations.
    mkCodeCase "long/dict-errors/type-n-null" #[] (mkCallDictLongViaC3Code! "oracle/type-n-null" c3TypeNNull 7),
    mkCodeCase "long/dict-errors/type-dict-from-idx-int" #[] (mkCallDictLongViaC3Code! "oracle/type-dict-from-idx" c3TypeDictFromIdx 7),
    mkCodeCase "long/dict-errors/range-n-too-large" #[] (mkCallDictLongViaC3Code! "oracle/range-n-too-large" c3RangeNTooLarge 7),
    mkCodeCase "long/dict-errors/range-n-negative" #[] (mkCallDictLongViaC3Code! "oracle/range-n-negative" c3RangeNNegative 7)
  ]

def suite : InstrSuite where
  id := callDictLongId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runCallDictLongDispatchFallback .add deepStackA)
          (deepStackA ++ #[intV dispatchSentinel])
        expectOkStack "dispatch/matched-calldict"
          (runHandlerDirectWithNext execInstrFlowCallDict (.callDict 7) (VM.push (intV dispatchSentinel)) #[])
          #[intV 7] }
    ,
    { name := "unit/raw/push-then-call-c3-quit"
      run := do
        let regs : Regs := { Regs.initial with c3 := .quit 9 }
        let st ← expectRawOk "raw/c3-quit" (runCallDictLongRaw 17 deepStackA regs)
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
        let _ ← expectRawErr "raw/nargs-underflow" (runCallDictLongRaw 5 #[] regsNeedTwo) .stkUnd

        let needOneCaptured : Continuation := ordinaryCont 1 #[intV 99]
        let regsNeedOneCaptured : Regs := { Regs.initial with c3 := needOneCaptured }
        let st ← expectRawOk "raw/nargs-one-captured" (runCallDictLongRaw 5 #[intV 11, intV 22] regsNeedOneCaptured)
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
        let st ← expectRawOk "raw/has-c0" (runCallDictLongRaw 33 deepStackB regs)
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
        let _ ← expectRawErr "raw/env-underflow" (runCallDictLongRaw 7 #[intV 1] regsNeedThree) .stkUnd

        let envCapturedOne : Continuation := envelopeCont 1 #[intV 55]
        let regsCapturedOne : Regs := { Regs.initial with c3 := envCapturedOne }
        let st ← expectRawOk "raw/env-captured" (runCallDictLongRaw 7 #[intV 11, intV 22] regsCapturedOne)
        if st.stack != #[intV 55, intV 7] then
          throw (IO.userError s!"raw/env-captured: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/opcode/decode-long-width-and-range"
      run := do
        let rawBits :=
          callDictLongBits 0 ++
          callDictLongBits 1 ++
          callDictLongBits 255 ++
          callDictLongBits 256 ++
          callDictLongBits 16383 ++
          assembleNoRefBits! "decode-long/tail" #[.contExt (.jmpDict 1), .prepareDict 2, .add]
        let rawCode : Cell := Cell.mkOrdinary rawBits #[]
        let s0 := Slice.ofCell rawCode
        let s1 ← expectDecodeStep "decode/long-idx-0" s0 (.callDict 0) 24
        let s2 ← expectDecodeStep "decode/long-idx-1" s1 (.callDict 1) 24
        let s3 ← expectDecodeStep "decode/long-idx-255" s2 (.callDict 255) 24
        let s4 ← expectDecodeStep "decode/long-idx-256" s3 (.callDict 256) 24
        let s5 ← expectDecodeStep "decode/long-idx-16383" s4 (.callDict 16383) 24
        let s6 ← expectDecodeStep "decode/jmpdict-1" s5 (.contExt (.jmpDict 1)) 24
        let s7 ← expectDecodeStep "decode/preparedict-2" s6 (.prepareDict 2) 24
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining != 0 then
          throw (IO.userError s!"decode/long-seq-end: expected exhausted bits, got {s8.bitsRemaining}")

        match encodeCp0 (.callDict 255) with
        | .ok bits =>
            if bits.size != 16 then
              throw (IO.userError s!"encode/cd-255: expected canonical short size=16, got {bits.size}")
        | .error e => throw (IO.userError s!"encode/cd-255: expected success, got {e}")

        match encodeCp0 (.callDict 256) with
        | .ok bits =>
            if bits.size != 24 then
              throw (IO.userError s!"encode/cd-256: expected long size=24, got {bits.size}")
        | .error e => throw (IO.userError s!"encode/cd-256: expected success, got {e}")

        match encodeCp0 (.callDict 16384) with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"encode/cd-16384: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "encode/cd-16384: expected rangeChk, got success") }
    ,
    { name := "unit/raw/synthetic-idx-mask-regression"
      run := do
        -- Synthetic direct handler input (not cp0-decodable): match C++ long-handler arg mask behavior.
        let huge : Nat := 0x12345
        let masked : Int := Int.ofNat (huge &&& 0x3fff)
        let regs : Regs := { Regs.initial with c3 := .quit 7 }
        let st ← expectRawOk "raw/idx-mask" (runCallDictLongRaw huge #[] regs)
        if st.stack != #[intV masked] then
          throw (IO.userError s!"raw/idx-mask: expected masked idx {masked}, got {reprStr st.stack}")
        else
          pure () }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile callDictLongId callDictLongFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.CALLDICT_LONG
