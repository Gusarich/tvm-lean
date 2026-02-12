import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.REPEATBRK

/-!
REPEATBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean`
    (`execInstrFlowLoopExt`, `.repeat true`, `popSmallintRepeatCount`)
  - `TvmLean/Semantics/Step/Step.lean`
    (`.repeatBody` runtime continuation branches)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` / `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`REPEATBRK` opcode `0xe314` decode/encode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_repeat`, opcode registration)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp`
    (`VmState::repeat`, `RepeatCont::jump/_w`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp`
    (`extract_cc(1)`, `c1_envelope_if`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range` path and type/range behavior)

Branch map used here:
- Dispatch: `.contExt (.repeat true)` handled vs fallback to `next`.
- Handled REPEATBRK path:
  1. `checkUnderflow(2)` success/failure (`stkUnd`);
  2. `popCont` success/type failure (`typeChk`);
  3. count pop/range gate (`typeChk` for non-int, `rangeChk` for NaN/out-of-range smallint);
  4. `count <= 0` fast return (no loop continuation installation);
  5. `count > 0` extracts `after := extract_cc(1)`, envelopes via `c1_envelope_if`,
     and installs `.repeatBody`.
- Runtime `.repeatBody` path:
  - `count = 0` -> jump to `after` (`ordinary` and non-ordinary subpaths),
  - `count > 0 && body.hasC0` -> jump to body without rewriting `c0`,
  - `count > 0 && !body.hasC0` -> set `c0 := repeatBody(..., count-1)` and jump body.
-/

private def repeatBrkId : InstrId := { name := "REPEATBRK" }

private def repeatBrkInstr : Instr := .contExt (.repeat true)

private def dispatchSentinel : Int := 9417

private def kCont : Value := .cont (.quit 0)

private def minInt32 : Int := -0x80000000

private def maxInt32 : Int := 0x7fffffff

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def emptyOrdCont : Continuation := mkOrdCont

private def bodyRet : Continuation := emptyOrdCont

private def bodyRetWithC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 19) }
    OrdCdata.empty

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

private def refCellA : Cell :=
  Cell.ofUInt 8 0xa5

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice :=
  Slice.ofCell refCellA

private def fullSliceB : Slice :=
  Slice.ofCell refCellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceB, .builder Builder.empty, .tuple #[]]

private def bytesToBits (bytes : Array Nat) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits (b % 256) 8) #[]

private def mkRawCodeCell (bytes : Array Nat) : Cell :=
  Cell.mkOrdinary (bytesToBits bytes) #[]

-- Raw cp0 snippets:
--   0x90       = PUSHCONT_SHORT len=0 (empty body continuation)
--   0x92       = PUSHCONT_SHORT len=2
--   0xdb30     = RET
--   0xdb31     = RETALT
--   0xe314     = REPEATBRK
--   0x71       = PUSHINT_4 1
--   0xa0       = ADD
private def repeatBrkPushContEmptyAfterAddCode : Cell :=
  mkRawCodeCell #[0x90, 0xe3, 0x14, 0x71, 0xa0]

private def repeatBrkPushContRetAfterAddCode : Cell :=
  mkRawCodeCell #[0x92, 0xdb, 0x30, 0xe3, 0x14, 0x71, 0xa0]

private def repeatBrkPushContRetAltAfterAddCode : Cell :=
  mkRawCodeCell #[0x92, 0xdb, 0x31, 0xe3, 0x14, 0x71, 0xa0]

private def withRepeatArgs
    (below : Array Value)
    (count : IntVal)
    (body : Value := kCont) : Array Value :=
  below ++ #[.int count, body]

private def withRepeatRawCount
    (below : Array Value)
    (count : Value) : Array Value :=
  below ++ #[count, kCont]

private def withRawCount
    (below : Array Value)
    (count : IntVal) : Array Value :=
  below ++ #[.int count]

private def mkRepeatBrkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[repeatBrkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := repeatBrkId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRepeatBrkCodeCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := repeatBrkId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRepeatBrkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt repeatBrkInstr stack

private def runRepeatBrkDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runRepeatBrkRaw
    (stack : Array Value)
    (cc : Continuation := emptyOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowLoopExt repeatBrkInstr (pure ())).run st0

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

private def stepOnce (st : VmState) : VmState :=
  match VmState.step stubHost st with
  | .continue st' => st'
  | .halt _ st' => st'

private def expectDecodeStep (label : String) (s : Slice) (expectedInstr : Instr) (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else
        pure s'

private def repeatBrkSetGasExact : Int :=
  computeExactGasBudget repeatBrkInstr

private def repeatBrkSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne repeatBrkInstr

private def progSetC0Quit1 (loopInstr : Instr) (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, loopInstr] ++ body

private def repeatBrkOracleFamilies : Array String :=
  #[
    "ok/nonpositive/",
    "ok/positive/",
    "err/underflow/",
    "err/type/",
    "err/range/",
    "raw/",
    "gas/"
  ]

private def repeatBrkFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := repeatBrkOracleFamilies
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

def suite : InstrSuite where
  id := repeatBrkId
  unit := #[
    { name := "unit/direct/errors-and-order"
      run := do
        expectErr "underflow/empty" (runRepeatBrkDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runRepeatBrkDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-cont" (runRepeatBrkDirect #[kCont]) .stkUnd

        expectErr "type/top-not-cont-int"
          (runRepeatBrkDirect (withRepeatArgs #[] (.num 1) (intV 9))) .typeChk
        expectErr "order/top-before-count"
          (runRepeatBrkDirect #[.int .nan, .cell refCellA]) .typeChk

        expectErr "type/count-null-after-cont"
          (runRepeatBrkDirect (withRepeatRawCount #[] (.null : Value))) .typeChk
        expectErr "type/count-cell-after-cont"
          (runRepeatBrkDirect (withRepeatRawCount #[] (.cell refCellA))) .typeChk

        expectErr "range/count-nan-after-cont"
          (runRepeatBrkDirect #[.int .nan, kCont]) .rangeChk
        expectErr "range/count-over-max32"
          (runRepeatBrkDirect #[intV (maxInt32 + 1), kCont]) .rangeChk
        expectErr "range/count-under-min32"
          (runRepeatBrkDirect #[intV (minInt32 - 1), kCont]) .rangeChk }
    ,
    { name := "unit/direct/pops-count-and-body"
      run := do
        expectOkStack "zero-count/pops-two"
          (runRepeatBrkDirect (withRepeatArgs #[.null, intV 5] (.num 0)))
          #[.null, intV 5]

        expectOkStack "negative-count/pops-two"
          (runRepeatBrkDirect (withRepeatArgs #[intV 9, .cell refCellA] (.num (-3))))
          #[intV 9, .cell refCellA]

        expectOkStack "positive-count/pops-two"
          (runRepeatBrkDirect (withRepeatArgs #[.slice fullSliceA, intV 12] (.num 2)))
          #[.slice fullSliceA, intV 12] }
    ,
    { name := "unit/state/brk-positive-installs-c1-envelope-data-and-repeatBody"
      run := do
        let st ← expectRawOk "state/brk-positive"
          (runRepeatBrkRaw (withRepeatArgs #[intV 44] (.num 3) (.cont bodyRet)) emptyOrdCont (.quit 9) (.quit 11))

        if st.stack != #[intV 44] then
          throw (IO.userError s!"state/brk-positive: unexpected stack {reprStr st.stack}")

        match st.cc with
        | .repeatBody body after count =>
              if count != 3 then
                throw (IO.userError s!"state/brk-positive: expected count=3, got {count}")
              else if body != bodyRet then
                throw (IO.userError s!"state/brk-positive: body mismatch {reprStr body}")
              else if st.regs.c1 != after then
                throw (IO.userError "state/brk-positive: expected c1 to equal loop-after continuation")
              else
                match after with
                | .ordinary _ saved cregs cdata =>
                    if saved != .quit 0 then
                      throw (IO.userError
                        s!"state/brk-positive: expected extracted after.saved=quit0, got {reprStr saved}")
                    else if cregs.c0 != some (.quit 9) then
                      throw (IO.userError
                        s!"state/brk-positive: expected captured c0=quit9, got {reprStr cregs.c0}")
                    else if cregs.c1 != some (.quit 11) then
                      throw (IO.userError
                        s!"state/brk-positive: expected captured c1=quit11, got {reprStr cregs.c1}")
                    else if !(cdataEmpty cdata) then
                      throw (IO.userError
                        s!"state/brk-positive: expected empty cdata, got {reprStr cdata}")
                    else
                      pure ()
                | _ =>
                    throw (IO.userError s!"state/brk-positive: expected ordinary after, got {reprStr after}")
        | _ =>
            throw (IO.userError s!"state/brk-positive: expected repeatBody cc, got {reprStr st.cc}")

        if st.regs.c0 == .quit 0 then
          pure ()
        else
          throw (IO.userError s!"state/brk-positive: expected c0 reset to quit0 by extractCc(1), got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/brk-nonpositive-fast-return-keeps-cc-and-c1"
      run := do
        let st ← expectRawOk "state/brk-nonpositive"
          (runRepeatBrkRaw (withRepeatArgs #[.null, intV 17] (.num 0) (.cont bodyRet)) emptyOrdCont (.quit 5) (.quit 6))

        if st.stack != #[.null, intV 17] then
          throw (IO.userError s!"state/brk-nonpositive: unexpected stack {reprStr st.stack}")
        else if st.cc != emptyOrdCont then
          throw (IO.userError s!"state/brk-nonpositive: expected unchanged cc, got {reprStr st.cc}")
        else if st.regs.c0 != .quit 5 then
          throw (IO.userError s!"state/brk-nonpositive: expected unchanged c0=quit5, got {reprStr st.regs.c0}")
        else if st.regs.c1 != .quit 6 then
          throw (IO.userError s!"state/brk-nonpositive: expected unchanged c1=quit6, got {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/order/positive-path-requires-ordinary-cc"
      run := do
        let stPos ← expectRawErr "order/non-ordinary/positive-path"
          (runRepeatBrkRaw #[intV 1, kCont] (.quit 7) (.quit 9) (.quit 10)) .typeChk
        if !stPos.stack.isEmpty then
          throw (IO.userError
            s!"order/non-ordinary/positive-path: expected consumed args before extractCc failure, got {reprStr stPos.stack}")
        else if stPos.regs.c0 != .quit 9 then
          throw (IO.userError
            s!"order/non-ordinary/positive-path: c0 changed unexpectedly to {reprStr stPos.regs.c0}")
        else
          pure ()

        let stNonPos ← expectRawOk "order/non-ordinary/nonpositive-path"
          (runRepeatBrkRaw #[intV 0, kCont] (.quit 7) (.quit 9) (.quit 10))
        if stNonPos.cc != .quit 7 then
          throw (IO.userError
            s!"order/non-ordinary/nonpositive-path: expected unchanged cc=quit7, got {reprStr stNonPos.cc}")
        else if stNonPos.regs.c1 != .quit 10 then
          throw (IO.userError
            s!"order/non-ordinary/nonpositive-path: c1 changed unexpectedly to {reprStr stNonPos.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/repeatBody/runtime-branches"
      run := do
        let base := VmState.initial Cell.empty

        let afterOrd : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 9) OrdCregs.empty OrdCdata.empty
        let stDoneOrd0 : VmState :=
          { base with regs := { base.regs with c0 := .quit 3 }, cc := .repeatBody bodyRet afterOrd 0 }
        let stDoneOrd := stepOnce stDoneOrd0
        if stDoneOrd.regs.c0 != .quit 9 then
          throw (IO.userError s!"repeatBody/done-ordinary: expected c0=quit9, got {reprStr stDoneOrd.regs.c0}")
        match stDoneOrd.cc with
        | .ordinary _ saved _ _ =>
            if saved == .quit 0 then
              pure ()
            else
              throw (IO.userError s!"repeatBody/done-ordinary: expected cc.saved=quit0, got {reprStr saved}")
        | _ =>
            throw (IO.userError s!"repeatBody/done-ordinary: expected ordinary cc, got {reprStr stDoneOrd.cc}")

        let afterQuit : Continuation := .quit 8
        let stDoneNonOrd0 : VmState :=
          { base with regs := { base.regs with c0 := .quit 4 }, cc := .repeatBody bodyRet afterQuit 0 }
        let stDoneNonOrd := stepOnce stDoneNonOrd0
        if stDoneNonOrd.cc != afterQuit then
          throw (IO.userError s!"repeatBody/done-nonordinary: expected cc=after, got {reprStr stDoneNonOrd.cc}")
        if stDoneNonOrd.regs.c0 == .quit 4 then
          pure ()
        else
          throw (IO.userError
            s!"repeatBody/done-nonordinary: c0 changed unexpectedly to {reprStr stDoneNonOrd.regs.c0}")

        let stHasC00 : VmState :=
          { base with regs := { base.regs with c0 := .quit 5 }, cc := .repeatBody bodyRetWithC0 afterQuit 2 }
        let stHasC0 := stepOnce stHasC00
        if stHasC0.cc != bodyRetWithC0 then
          throw (IO.userError s!"repeatBody/body-has-c0: expected jump to body, got {reprStr stHasC0.cc}")
        if stHasC0.regs.c0 == .quit 5 then
          pure ()
        else
          throw (IO.userError
            s!"repeatBody/body-has-c0: c0 changed unexpectedly to {reprStr stHasC0.regs.c0}")

        let stStep0 : VmState :=
          { base with regs := { base.regs with c0 := .quit 6 }, cc := .repeatBody bodyRet afterQuit 2 }
        let stStep := stepOnce stStep0
        if stStep.cc != bodyRet then
          throw (IO.userError s!"repeatBody/step: expected body cc, got {reprStr stStep.cc}")
        else if stStep.regs.c0 != .repeatBody bodyRet afterQuit 1 then
          throw (IO.userError
            s!"repeatBody/step: expected c0 repeatBody(count=1), got {reprStr stStep.regs.c0}")
        else
          pure ()

        let afterNeedArg : Continuation :=
          .envelope (.quit 8) OrdCregs.empty { stack := #[], nargs := 1 }
        let stNeed0 : VmState :=
          { base with regs := { base.regs with c0 := .quit 2 }, cc := .repeatBody bodyRet afterNeedArg 0 }
        let stNeed := stepOnce stNeed0
        if stNeed.cc != base.regs.c2 then
          throw (IO.userError
            s!"repeatBody/after-nargs-underflow: expected exception jump to c2, got {reprStr stNeed.cc}")
        else if stNeed.stack != #[intV 0, intV Excno.stkUnd.toInt] then
          throw (IO.userError
            s!"repeatBody/after-nargs-underflow: expected [0, stkUnd], got {reprStr stNeed.stack}")
        else
          pure () }
    ,
    { name := "unit/dispatch-and-opcode-canonical"
      run := do
        expectOkStack "dispatch/matched-repeatbrk"
          (runRepeatBrkDispatchFallback repeatBrkInstr (withRepeatArgs #[] (.num 0)))
          #[]
        expectOkStack "dispatch/fallback"
          (runRepeatBrkDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]

        match encodeCp0 repeatBrkInstr with
        | .ok bits =>
            if bits != natToBits 0xe314 16 then
              throw (IO.userError s!"encode/repeatbrk: expected e314, got {reprStr bits}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"encode/repeatbrk failed: {e}")

        let code ←
          match assembleCp0 [repeatBrkInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/repeatbrk failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/repeatbrk" s0 repeatBrkInstr 16
        let s2 ← expectDecodeStep "decode/add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        let raw := Slice.ofCell (Cell.mkOrdinary (natToBits 0xe314 16 ++ natToBits 0xa0 8) #[])
        let r1 ← expectDecodeStep "decode/raw-repeatbrk" raw repeatBrkInstr 16
        let r2 ← expectDecodeStep "decode/raw-add" r1 .add 8
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits remaining") }
  ]
  oracle := #[
    -- Non-positive fast-return branch (`count <= 0`).
    mkRepeatBrkCase "ok/nonpositive/zero" (withRepeatArgs #[] (.num 0)),
    mkRepeatBrkCase "ok/nonpositive/minus-one" (withRepeatArgs #[] (.num (-1))),
    mkRepeatBrkCase "ok/nonpositive/min32" (withRepeatArgs #[] (.num minInt32)),
    mkRepeatBrkCase "ok/nonpositive/deep-noise-a" (withRepeatArgs noiseA (.num 0)),
    mkRepeatBrkCase "ok/nonpositive/deep-noise-b" (withRepeatArgs noiseB (.num (-3))),
    mkRepeatBrkCase "ok/nonpositive/zero/trailing-push-runs"
      (withRepeatArgs #[] (.num 0)) #[repeatBrkInstr, .pushInt (.num 777)],
    mkRepeatBrkCase "ok/nonpositive/zero/c0-quit1"
      (withRepeatArgs #[] (.num 0)) (progSetC0Quit1 repeatBrkInstr),

    -- Positive branch with oracle-supported continuation token `K=quit(0)`.
    mkRepeatBrkCase "ok/positive/one-quit-body" (withRepeatArgs #[] (.num 1)),
    mkRepeatBrkCase "ok/positive/two-quit-body" (withRepeatArgs #[] (.num 2)),
    mkRepeatBrkCase "ok/positive/max32-quit-body" (withRepeatArgs #[] (.num maxInt32)),
    mkRepeatBrkCase "ok/positive/deep-noise-a" (withRepeatArgs noiseA (.num 4)),
    mkRepeatBrkCase "ok/positive/deep-noise-b" (withRepeatArgs noiseB (.num 5)),

    -- Underflow before any type/range checks.
    mkRepeatBrkCase "err/underflow/empty" #[],
    mkRepeatBrkCase "err/underflow/one-int" #[intV 1],
    mkRepeatBrkCase "err/underflow/one-cont" #[kCont],

    -- Top pop (`popCont`) type checks and order.
    mkRepeatBrkCase "err/type/top-int" (withRepeatArgs #[] (.num 1) (intV 7)),
    mkRepeatBrkCase "err/type/top-null" (withRepeatArgs #[] (.num 1) (.null : Value)),
    mkRepeatBrkCase "err/type/top-cell" (withRepeatArgs #[] (.num 1) (.cell refCellA)),
    mkRepeatBrkCase "err/type/top-slice" (withRepeatArgs #[] (.num 1) (.slice fullSliceA)),
    mkRepeatBrkCase "err/type/top-builder" (withRepeatArgs #[] (.num 1) (.builder Builder.empty)),
    mkRepeatBrkCase "err/type/top-tuple" (withRepeatArgs #[] (.num 1) (.tuple #[])),
    mkRepeatBrkCase "err/type/order-top-before-count" #[.cell refCellA, .builder Builder.empty],

    -- Count pop type checks after successful `popCont`.
    mkRepeatBrkCase "err/type/count-null" (withRepeatRawCount #[] (.null : Value)),
    mkRepeatBrkCase "err/type/count-cell" (withRepeatRawCount #[] (.cell refCellA)),
    mkRepeatBrkCase "err/type/count-slice" (withRepeatRawCount #[] (.slice fullSliceA)),
    mkRepeatBrkCase "err/type/count-builder" (withRepeatRawCount #[] (.builder Builder.empty)),
    mkRepeatBrkCase "err/type/count-tuple" (withRepeatRawCount #[] (.tuple #[])),
    mkRepeatBrkCase "err/type/order-count-after-valid-cont" #[.slice fullSliceA, kCont],

    -- Smallint range checks (`pop_smallint_range` semantics).
    mkRepeatBrkCase "err/range/count-over-max32" #[intV (maxInt32 + 1), kCont],
    mkRepeatBrkCase "err/range/count-under-min32" #[intV (minInt32 - 1), kCont],
    mkRepeatBrkCase "err/range/count-max-int257" #[intV maxInt257, kCont],
    mkRepeatBrkCase "err/range/count-min-int257" #[intV minInt257, kCont],
    mkRepeatBrkCase "err/range/count-nan-via-program" #[kCont]
      #[.pushInt .nan, .xchg0 1, repeatBrkInstr],

    -- Raw cp0 loop bodies via PUSHCONT_SHORT (oracle deterministic + BRK continuation behavior).
    mkRepeatBrkCodeCase "raw/empty-body/count0-after-add"
      (withRawCount #[intV 40] (.num 0))
      repeatBrkPushContEmptyAfterAddCode,
    mkRepeatBrkCodeCase "raw/empty-body/count1-after-add"
      (withRawCount #[intV 40] (.num 1))
      repeatBrkPushContEmptyAfterAddCode,
    mkRepeatBrkCodeCase "raw/empty-body/count2-after-add"
      (withRawCount #[intV 40] (.num 2))
      repeatBrkPushContEmptyAfterAddCode,
    mkRepeatBrkCodeCase "raw/empty-body/count3-after-add"
      (withRawCount #[intV 40] (.num 3))
      repeatBrkPushContEmptyAfterAddCode,
    mkRepeatBrkCodeCase "raw/empty-body/count-neg2-after-add"
      (withRawCount #[intV 40] (.num (-2)))
      repeatBrkPushContEmptyAfterAddCode,
    mkRepeatBrkCodeCase "raw/empty-body/count-type-null"
      #[intV 40, .null]
      repeatBrkPushContEmptyAfterAddCode,
    mkRepeatBrkCodeCase "raw/empty-body/count-range-over-max32"
      #[intV 40, intV (maxInt32 + 1)]
      repeatBrkPushContEmptyAfterAddCode,
    mkRepeatBrkCodeCase "raw/empty-body/missing-count-underflow"
      #[]
      repeatBrkPushContEmptyAfterAddCode,

    mkRepeatBrkCodeCase "raw/ret-body/count1-after-add"
      (withRawCount #[intV 40] (.num 1))
      repeatBrkPushContRetAfterAddCode,
    mkRepeatBrkCodeCase "raw/ret-body/count2-after-add"
      (withRawCount #[intV 40] (.num 2))
      repeatBrkPushContRetAfterAddCode,
    mkRepeatBrkCodeCase "raw/ret-body/count4-after-add"
      (withRawCount #[intV 40] (.num 4))
      repeatBrkPushContRetAfterAddCode,

    mkRepeatBrkCodeCase "raw/retalt-body/count1-break-after-add"
      (withRawCount #[intV 40] (.num 1))
      repeatBrkPushContRetAltAfterAddCode,
    mkRepeatBrkCodeCase "raw/retalt-body/count2-break-after-add"
      (withRawCount #[intV 40] (.num 2))
      repeatBrkPushContRetAltAfterAddCode,
    mkRepeatBrkCodeCase "raw/retalt-body/count5-break-after-add"
      (withRawCount #[intV 40] (.num 5))
      repeatBrkPushContRetAltAfterAddCode,

    -- Deterministic gas cliff.
    mkRepeatBrkCase "gas/exact-zero-succeeds" (withRepeatArgs #[] (.num 0))
      #[.pushInt (.num repeatBrkSetGasExact), .tonEnvOp .setGasLimit, repeatBrkInstr],
    mkRepeatBrkCase "gas/exact-minus-one-zero-out-of-gas" (withRepeatArgs #[] (.num 0))
      #[.pushInt (.num repeatBrkSetGasExactMinusOne), .tonEnvOp .setGasLimit, repeatBrkInstr]
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile repeatBrkId repeatBrkFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.REPEATBRK
