import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.PREPAREDICT

/-!
PREPAREDICT branch map (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PrepareDict.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_preparedict`, opcode registration)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::step` loop semantics)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`push_smallint`, `push_cont`)

Coverage targets:
1) Dispatch: `.prepareDict _` must match handler; non-matching opcodes fall through to `next`.
2) Core semantics: `args &= 0x3fff`; push idx first, then current `c3`; no `call`/`jump`.
3) Decode/encode: 24-bit form only, 14-bit immediate boundaries and neighboring prefixes.
4) c3 observation: quit/excQuit/ordinary continuation values pushed from current `c3`.
5) Downstream effects: produced `(idx, cont)` pair is consumable by later ops (`POPCTR`, `ADD`, `EXECUTE`).
-/

private def prepareId : InstrId := { name := "PREPAREDICT" }
private def preparePrefix10 : Nat := 0xf180 >>> 6

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def dispatchSentinel : Int := 64123
private def tailMarker : Int := 4404
private def addMarker : Int := 97
private def c3Marker : Int := 3303

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
  #[.cell noiseCellB, intV 123, .tuple #[]]

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

private def mkPushRefContCodeCell! (label : String) (refCell : Cell) (tail : Array Instr) : Cell :=
  -- PUSHREFCONT (0x8a) + one ref, then no-ref tail.
  Cell.mkOrdinary (natToBits 0x8a 8 ++ assembleNoRefBits! s!"{label}/tail" tail) #[refCell]

private def mkPrepareViaC3Code!
    (label : String)
    (c3Code : Cell)
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Cell :=
  mkPushRefContCodeCell! label c3Code (#[.popCtr 3, .prepareDict idx] ++ tail)

private def prepareWord (idx : Nat) : Nat :=
  (preparePrefix10 <<< 14) + (idx &&& 0x3fff)

private def prepareBits (idx : Nat) : BitString :=
  natToBits (prepareWord idx) 24

private def c3OrdCode : Cell :=
  assembleNoRefCell! "preparedict/c3-ordinary" #[.pushInt (.num c3Marker), .ret]

private def rawBoundarySeqBits : BitString :=
  prepareBits 0 ++ natToBits 0x5b 8 ++
  prepareBits 255 ++ natToBits 0x5b 8 ++
  prepareBits 256 ++ natToBits 0x5b 8 ++
  prepareBits 16383 ++ natToBits 0x5b 8 ++
  assembleNoRefBits! "preparedict/raw-boundary/tail" #[.pushInt (.num tailMarker)]

private def rawBoundarySeqCode : Cell :=
  Cell.mkOrdinary rawBoundarySeqBits #[]

private def rawBoundarySeqC2Code : Cell :=
  let preBits := assembleNoRefBits! "preparedict/raw-boundary-c2/pre" #[.pushCtr 2, .popCtr 3]
  Cell.mkOrdinary (preBits ++ rawBoundarySeqBits) #[]

private def progPrepareTail
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Array Instr :=
  #[.prepareDict idx] ++ tail

private def progSetC3FromCtrThenPrepare
    (ctr : Nat)
    (idx : Nat)
    (tail : Array Instr := #[.pushInt (.num tailMarker)]) : Array Instr :=
  #[.pushCtr ctr, .popCtr 3, .prepareDict idx] ++ tail

private def progPreparePopC3ThenAdd (idx : Nat) (k : Int := addMarker) : Array Instr :=
  #[.prepareDict idx, .popCtr 3, .pushInt (.num k), .add]

private def progPrepareThenMutateC3 (idx : Nat) (ctr : Nat) : Array Instr :=
  #[.prepareDict idx, .pushCtr ctr, .popCtr 3, .pushInt (.num tailMarker)]

private def progSetC3ThenPrepareThenMutateC3 (setCtr : Nat) (idx : Nat) (mutateCtr : Nat) : Array Instr :=
  #[.pushCtr setCtr, .popCtr 3, .prepareDict idx, .pushCtr mutateCtr, .popCtr 3, .pushInt (.num tailMarker)]

private def progSetC3ThenPrepareExecute (ctr : Nat) (idx : Nat) : Array Instr :=
  #[.pushCtr ctr, .popCtr 3, .prepareDict idx, .execute]

private def progDecodeBoundarySeq : Array Instr :=
  #[
    .prepareDict 0, .drop2,
    .prepareDict 255, .drop2,
    .prepareDict 256, .drop2,
    .prepareDict 16383, .drop2,
    .pushInt (.num tailMarker)
  ]

private def runPrepareDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPrepareDict instr (VM.push (intV dispatchSentinel)) stack

private def runPrepareRaw
    (idx : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowPrepareDict (.prepareDict idx) (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def mkProgCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := prepareId
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
    instr := prepareId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def oracleCases : Array OracleCase :=
  #[
    -- default c3 (`quit 11`): no jump, tail must execute.
    mkProgCase "default/nojump/idx-0/empty" #[] (progPrepareTail 0),
    mkProgCase "default/nojump/idx-1/deep-a" deepStackA (progPrepareTail 1),
    mkProgCase "default/nojump/idx-42/deep-b" deepStackB (progPrepareTail 42),
    mkProgCase "default/nojump/idx-255/deep-c" deepStackC (progPrepareTail 255),
    mkProgCase "default/nojump/idx-256/empty" #[] (progPrepareTail 256),
    mkProgCase "default/nojump/idx-257/deep-a" deepStackA (progPrepareTail 257),
    mkProgCase "default/nojump/idx-1024/deep-b" deepStackB (progPrepareTail 1024),
    mkProgCase "default/nojump/idx-4095/deep-c" deepStackC (progPrepareTail 4095),
    mkProgCase "default/nojump/idx-16382/deep-a" deepStackA (progPrepareTail 16382),
    mkProgCase "default/nojump/idx-16383/deep-b" deepStackB (progPrepareTail 16383),

    -- c3 observed via control-register retargeting (`c1`, `c2`).
    mkProgCase "set-c3/c1/nojump/idx-7/empty" #[] (progSetC3FromCtrThenPrepare 1 7),
    mkProgCase "set-c3/c1/nojump/idx-255/deep-a" deepStackA (progSetC3FromCtrThenPrepare 1 255),
    mkProgCase "set-c3/c1/nojump/idx-256/deep-b" deepStackB (progSetC3FromCtrThenPrepare 1 256),
    mkProgCase "set-c3/c1/nojump/idx-16383/deep-c" deepStackC (progSetC3FromCtrThenPrepare 1 16383),
    mkProgCase "set-c3/c2/nojump/idx-0/empty" #[] (progSetC3FromCtrThenPrepare 2 0),
    mkProgCase "set-c3/c2/nojump/idx-255/deep-a" deepStackA (progSetC3FromCtrThenPrepare 2 255),
    mkProgCase "set-c3/c2/nojump/idx-256/deep-b" deepStackB (progSetC3FromCtrThenPrepare 2 256),
    mkProgCase "set-c3/c2/nojump/idx-16383/deep-c" deepStackC (progSetC3FromCtrThenPrepare 2 16383),

    -- c3 observed as ordinary continuation via PUSHREFCONT + POPCTR 3.
    mkCodeCase "set-c3/ordinary/nojump/idx-7/empty" #[]
      (mkPrepareViaC3Code! "oracle/c3-ord-7" c3OrdCode 7),
    mkCodeCase "set-c3/ordinary/nojump/idx-255/deep-a" deepStackA
      (mkPrepareViaC3Code! "oracle/c3-ord-255" c3OrdCode 255),
    mkCodeCase "set-c3/ordinary/nojump/idx-256/deep-b" deepStackB
      (mkPrepareViaC3Code! "oracle/c3-ord-256" c3OrdCode 256),
    mkCodeCase "set-c3/ordinary/nojump/idx-16383/deep-c" deepStackC
      (mkPrepareViaC3Code! "oracle/c3-ord-16383" c3OrdCode 16383),

    -- downstream idx consumption after removing pushed continuation.
    mkProgCase "downstream/popctr3-add/default/idx-0" #[] (progPreparePopC3ThenAdd 0),
    mkProgCase "downstream/popctr3-add/default/idx-255/deep-a" deepStackA (progPreparePopC3ThenAdd 255),
    mkProgCase "downstream/popctr3-add/default/idx-256/deep-b" deepStackB (progPreparePopC3ThenAdd 256),
    mkProgCase "downstream/popctr3-add/default/idx-16383/deep-c" deepStackC (progPreparePopC3ThenAdd 16383),
    mkProgCase "downstream/popctr3-add/c2/idx-9" #[]
      (progSetC3FromCtrThenPrepare 2 9 #[.popCtr 3, .pushInt (.num addMarker), .add]),
    mkCodeCase "downstream/popctr3-add/ordinary/idx-11" #[]
      (mkPrepareViaC3Code! "oracle/downstream-ord-add" c3OrdCode 11 #[.popCtr 3, .pushInt (.num addMarker), .add]),

    -- no-jump snapshot: mutating c3 after PREPAREDICT must not affect pushed continuation.
    mkProgCase "snapshot/default-then-set-c0/idx-17" #[] (progPrepareThenMutateC3 17 0),
    mkProgCase "snapshot/default-then-set-c2/idx-513/deep-a" deepStackA (progPrepareThenMutateC3 513 2),
    mkProgCase "snapshot/c2-then-set-c0/idx-33" #[] (progSetC3ThenPrepareThenMutateC3 2 33 0),
    mkCodeCase "snapshot/ordinary-then-set-c2/idx-44" #[]
      (mkPrepareViaC3Code! "oracle/snapshot-ord-set-c2" c3OrdCode 44 #[.pushCtr 2, .popCtr 3, .pushInt (.num tailMarker)]),

    -- downstream continuation execution from the produced pair.
    mkProgCase "downstream/execute/c0/idx-5" #[] (progSetC3ThenPrepareExecute 0 5),
    mkProgCase "downstream/execute/c1/idx-5" #[] (progSetC3ThenPrepareExecute 1 5),
    mkProgCase "downstream/execute/c2/idx-5" #[] (progSetC3ThenPrepareExecute 2 5),
    mkProgCase "downstream/execute/c2/idx-255/deep-a" deepStackA (progSetC3ThenPrepareExecute 2 255),
    mkCodeCase "downstream/execute/ordinary/idx-5/deep-b" deepStackB
      (mkPrepareViaC3Code! "oracle/execute-ord-5" c3OrdCode 5 #[.execute]),
    mkCodeCase "downstream/execute/ordinary/idx-256/deep-c" deepStackC
      (mkPrepareViaC3Code! "oracle/execute-ord-256" c3OrdCode 256 #[.execute]),

    -- decode-boundary execution via mixed assembled and raw code cells.
    mkProgCase "decode-seq/assembled/boundaries" #[] progDecodeBoundarySeq,
    mkCodeCase "decode-seq/raw/boundaries/default-c3" #[] rawBoundarySeqCode,
    mkCodeCase "decode-seq/raw/boundaries/c2/deep-a" deepStackA rawBoundarySeqC2Code,
    mkCodeCase "decode-seq/raw/boundaries/default-c3/deep-b" deepStackB rawBoundarySeqCode
  ]

def suite : InstrSuite where
  id := prepareId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runPrepareDispatchFallback .add deepStackA)
          (deepStackA ++ #[intV dispatchSentinel])
        expectOkStack "dispatch/matched-preparedict"
          (runHandlerDirectWithNext execInstrFlowPrepareDict (.prepareDict 7) (VM.push (intV dispatchSentinel)) #[])
          #[intV 7, .cont (Regs.initial.c3)] }
    ,
    { name := "unit/raw/push-order-no-jump"
      run := do
        let regs : Regs := { Regs.initial with c3 := .quit 9 }
        let st ← expectRawOk "raw/push-order" (runPrepareRaw 17 deepStackB regs)
        if st.stack != (deepStackB ++ #[intV 17, .cont (.quit 9)]) then
          throw (IO.userError s!"raw/push-order: stack mismatch {reprStr st.stack}")
        else if st.cc != defaultCc then
          throw (IO.userError s!"raw/push-order: cc changed unexpectedly to {reprStr st.cc}")
        else
          pure () }
    ,
    { name := "unit/raw/c3-observation-excquit-and-ordinary"
      run := do
        let regsExc : Regs := { Regs.initial with c3 := .excQuit }
        let stExc ← expectRawOk "raw/c3-exc" (runPrepareRaw 21 deepStackA regsExc)
        if stExc.stack != (deepStackA ++ #[intV 21, .cont (.excQuit)]) then
          throw (IO.userError s!"raw/c3-exc: stack mismatch {reprStr stExc.stack}")

        let ord : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        let regsOrd : Regs := { Regs.initial with c3 := ord }
        let stOrd ← expectRawOk "raw/c3-ord" (runPrepareRaw 22 deepStackC regsOrd)
        if stOrd.stack != (deepStackC ++ #[intV 22, .cont ord]) then
          throw (IO.userError s!"raw/c3-ord: stack mismatch {reprStr stOrd.stack}")
        else
          pure () }
    ,
    { name := "unit/opcode/decode-boundary-neighbors"
      run := do
        let seq : Array Instr := #[
          .prepareDict 0,
          .prepareDict 255,
          .prepareDict 256,
          .prepareDict 16383,
          .contExt (.jmpDict 1),
          .callDict 2,
          .add
        ]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/pd-0" s0 (.prepareDict 0) 24
        let s2 ← expectDecodeStep "decode/pd-255" s1 (.prepareDict 255) 24
        let s3 ← expectDecodeStep "decode/pd-256" s2 (.prepareDict 256) 24
        let s4 ← expectDecodeStep "decode/pd-16383" s3 (.prepareDict 16383) 24
        let s5 ← expectDecodeStep "decode/jmpdict-1" s4 (.contExt (.jmpDict 1)) 24
        let s6 ← expectDecodeStep "decode/calldict-2" s5 (.callDict 2) 16
        let s7 ← expectDecodeStep "decode/tail-add" s6 .add 8
        if s7.bitsRemaining != 0 then
          throw (IO.userError s!"decode/seq-end: expected exhausted bits, got {s7.bitsRemaining}")

        let rawBits :=
          natToBits ((0x3c4 <<< 14) + 7) 24 ++
          natToBits ((0x3c5 <<< 14) + 8) 24 ++
          natToBits ((preparePrefix10 <<< 14) + 9) 24 ++
          natToBits ((0x3c7 <<< 14) + 0) 24
        let rawCode : Cell := Cell.mkOrdinary rawBits #[]
        let r0 := Slice.ofCell rawCode
        let r1 ← expectDecodeStep "decode/raw-calldict-7" r0 (.callDict 7) 24
        let r2 ← expectDecodeStep "decode/raw-jmpdict-8" r1 (.contExt (.jmpDict 8)) 24
        let r3 ← expectDecodeStep "decode/raw-preparedict-9" r2 (.prepareDict 9) 24
        match decodeCp0WithBits r3 with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/raw-prefix-0x3c7: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/raw-prefix-0x3c7: expected failure, got {reprStr instr} bits={bits}") }
    ,
    { name := "unit/opcode/encode-width-and-range"
      run := do
        match encodeCp0 (.prepareDict 0) with
        | .ok bits =>
            if bits.size != 24 then
              throw (IO.userError s!"encode/pd-0: expected size=24, got {bits.size}")
        | .error e => throw (IO.userError s!"encode/pd-0: expected success, got {e}")

        match encodeCp0 (.prepareDict 16383) with
        | .ok bits =>
            if bits.size != 24 then
              throw (IO.userError s!"encode/pd-16383: expected size=24, got {bits.size}")
            else if bitsToNat bits != prepareWord 16383 then
              throw (IO.userError s!"encode/pd-16383: word mismatch got={bitsToNat bits}")
        | .error e => throw (IO.userError s!"encode/pd-16383: expected success, got {e}")

        match encodeCp0 (.prepareDict 16384) with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"encode/pd-16384: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "encode/pd-16384: expected rangeChk, got success") }
    ,
    { name := "unit/raw/synthetic-idx-mask-regression"
      run := do
        -- Synthetic direct handler input (not cp0-decodable): match C++ args mask behavior.
        let huge : Nat := 0x12345
        let masked : Int := Int.ofNat (huge &&& 0x3fff)
        let regs : Regs := { Regs.initial with c3 := .quit 7 }
        let st ← expectRawOk "raw/idx-mask" (runPrepareRaw huge #[] regs)
        if st.stack != #[intV masked, .cont (.quit 7)] then
          throw (IO.userError s!"raw/idx-mask: expected masked idx {masked}, got {reprStr st.stack}")
        else if st.cc != defaultCc then
          throw (IO.userError s!"raw/idx-mask: cc changed unexpectedly to {reprStr st.cc}")
        else
          pure () }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.PREPAREDICT
