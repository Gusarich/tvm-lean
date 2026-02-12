import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.REPEAT

/-!
REPEAT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean`
    (`execInstrFlowLoopExt`, `popSmallintRepeatCount`)
  - `TvmLean/Semantics/Step/Step.lean`
    (`.repeatBody` runtime branches)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` / `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`REPEAT` opcode `0xe4` decode/encode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_repeat`, opcode registration)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp`
    (`VmState::repeat`, `RepeatCont::jump/_w`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp`
    (`extract_cc(1)`, `c1_envelope_if` plumbing)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range` / `pop_long_range` / `pop_long`)

Branch map used for this suite:
- Dispatch: `.contExt (.repeat false)` handled vs fallback to `next`.
- Handled REPEAT path:
  1. `checkUnderflow(2)` success/failure (`stkUnd`);
  2. `popCont` success/type failure (`typeChk`);
  3. count pop/range gate (`typeChk` for non-int, `rangeChk` for NaN/out-of-range smallint);
  4. `count <= 0` fast return (no loop continuation installation);
  5. `count > 0` installs `.repeatBody` and defers to runtime loop continuation semantics.
- Runtime `.repeatBody` path:
  - `count = 0` -> jump to `after` (`ordinary` and non-ordinary subpaths),
  - `count > 0 && body.hasC0` -> jump to body without rewriting `c0`,
  - `count > 0 && !body.hasC0` -> set `c0 := repeatBody(..., count-1)` and jump body.

Oracle-harness constraint:
- Oracle stack tokens only support continuation token `K` (`quit(0)`),
  so additional code-cell oracle cases use raw cp0 bytes (`PUSHCONT_SHORT len=0`) to
  produce a returning body continuation and exercise loop-runtime branches deterministically.
-/

private def repeatId : InstrId := { name := "REPEAT" }

private def repeatInstr : Instr := .contExt (.repeat false)

private def dispatchSentinel : Int := 7193

private def kCont : Value :=
  .cont (.quit 0)

private def bodyRet : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def bodyRetWithC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 19) }
    OrdCdata.empty

private def refCellA : Cell :=
  Cell.ofUInt 8 0xa5

private def fullSliceA : Slice :=
  Slice.ofCell refCellA

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def bytesToBits (bytes : Array Nat) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits (b % 256) 8) #[]

private def mkRawCodeCell (bytes : Array Nat) : Cell :=
  Cell.mkOrdinary (bytesToBits bytes) #[]

-- Raw cp0 bytes:
--   0x90 = PUSHCONT_SHORT len=0 (push ordinary empty-code continuation)
--   0xe4 = REPEAT
--   0x71 = PUSHINT_4 1
--   0xa0 = ADD
private def repeatPushContEmptyAfterAddCode : Cell :=
  mkRawCodeCell #[0x90, 0xe4, 0x71, 0xa0]

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

private def mkRepeatCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[repeatInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := repeatId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRepeatCodeCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := repeatId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRepeatDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt repeatInstr stack

private def runRepeatDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runRepeatState (stack : Array Value) : Except Excno VmState := do
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrFlowLoopExt repeatInstr (pure ())).run st0
  match res with
  | .ok _ => pure st1
  | .error e => throw e

private def expectStateOk (label : String) (res : Except Excno VmState) : IO VmState := do
  match res with
  | .ok st => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

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

private def repeatSetGasExact : Int :=
  computeExactGasBudget repeatInstr

private def repeatSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne repeatInstr

private def repeatOracleFamilies : Array String :=
  #[
    "ok/nonpositive/",
    "ok/positive/",
    "err/underflow/",
    "err/type/top-",
    "err/type/count-",
    "err/type/order-",
    "err/range/",
    "raw/loop/",
    "raw/type/",
    "raw/range/",
    "raw/underflow/",
    "gas/"
  ]

private def repeatFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := repeatOracleFamilies
    -- Bias toward stack-shape and count perturbations while exercising all mutation modes.
    mutationModes := #[0, 0, 0, 1, 1, 1, 4, 4, 4, 2, 2, 3]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := repeatId
  unit := #[
    { name := "unit/direct/errors-and-order"
      run := do
        expectErr "underflow/empty" (runRepeatDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runRepeatDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-cont" (runRepeatDirect #[kCont]) .stkUnd

        expectErr "type/top-not-cont-int"
          (runRepeatDirect (withRepeatArgs #[] (.num 1) (intV 9))) .typeChk
        expectErr "order/top-before-count"
          (runRepeatDirect #[.int .nan, .cell refCellA]) .typeChk

        expectErr "type/count-null-after-cont"
          (runRepeatDirect (withRepeatRawCount #[] (.null : Value))) .typeChk
        expectErr "type/count-cell-after-cont"
          (runRepeatDirect (withRepeatRawCount #[] (.cell refCellA))) .typeChk

        expectErr "range/count-nan-after-cont"
          (runRepeatDirect #[.int .nan, kCont]) .rangeChk
        expectErr "range/count-over-max32"
          (runRepeatDirect #[intV 2147483648, kCont]) .rangeChk
        expectErr "range/count-under-min32"
          (runRepeatDirect #[intV (-2147483649), kCont]) .rangeChk }
    ,
    { name := "unit/direct/pops-count-and-body"
      run := do
        expectOkStack "zero-count/pops-two"
          (runRepeatDirect (withRepeatArgs #[.null, intV 5] (.num 0)))
          #[.null, intV 5]

        expectOkStack "negative-count/pops-two"
          (runRepeatDirect (withRepeatArgs #[intV 9, .cell refCellA] (.num (-3))))
          #[intV 9, .cell refCellA]

        expectOkStack "positive-count/pops-two"
          (runRepeatDirect (withRepeatArgs #[.slice fullSliceA, intV 12] (.num 2)))
          #[.slice fullSliceA, intV 12] }
    ,
    { name := "unit/state/positive-installs-repeatBody"
      run := do
        let st ← expectStateOk "state/positive"
          (runRepeatState (withRepeatArgs #[intV 44] (.num 3) (.cont bodyRet)))

        if st.stack != #[intV 44] then
          throw (IO.userError s!"state/positive: unexpected stack {reprStr st.stack}")

        match st.cc with
        | .repeatBody body after count =>
            if count != 3 then
              throw (IO.userError s!"state/positive: expected count=3, got {count}")
            if body != bodyRet then
              throw (IO.userError s!"state/positive: body mismatch {reprStr body}")
            match after with
            | .ordinary _ saved _ _ =>
                if saved == .quit 0 then
                  pure ()
                else
                  throw (IO.userError s!"state/positive: expected after.saved=quit0, got {reprStr saved}")
            | _ =>
                throw (IO.userError s!"state/positive: expected ordinary after, got {reprStr after}")
        | _ =>
            throw (IO.userError s!"state/positive: expected repeatBody cc, got {reprStr st.cc}")

        if st.regs.c0 == .quit 0 then
          pure ()
        else
          throw (IO.userError s!"state/positive: expected c0 unchanged quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/nonpositive-fast-return-keeps-cc"
      run := do
        let st ← expectStateOk "state/nonpositive"
          (runRepeatState (withRepeatArgs #[.null, intV 17] (.num 0) (.cont bodyRet)))
        let initial := VmState.initial Cell.empty

        if st.stack != #[.null, intV 17] then
          throw (IO.userError s!"state/nonpositive: unexpected stack {reprStr st.stack}")
        if st.cc != initial.cc then
          throw (IO.userError s!"state/nonpositive: expected unchanged cc, got {reprStr st.cc}")
        if st.regs.c0 == .quit 0 then
          pure ()
        else
          throw (IO.userError s!"state/nonpositive: expected c0=quit0, got {reprStr st.regs.c0}") }
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
          throw (IO.userError s!"repeatBody/done-nonordinary: c0 changed unexpectedly to {reprStr stDoneNonOrd.regs.c0}")

        let stHasC00 : VmState :=
          { base with regs := { base.regs with c0 := .quit 5 }, cc := .repeatBody bodyRetWithC0 afterQuit 2 }
        let stHasC0 := stepOnce stHasC00
        if stHasC0.cc != bodyRetWithC0 then
          throw (IO.userError s!"repeatBody/body-has-c0: expected jump to body, got {reprStr stHasC0.cc}")
        if stHasC0.regs.c0 == .quit 5 then
          pure ()
        else
          throw (IO.userError s!"repeatBody/body-has-c0: c0 changed unexpectedly to {reprStr stHasC0.regs.c0}")

        let stStep0 : VmState :=
          { base with regs := { base.regs with c0 := .quit 6 }, cc := .repeatBody bodyRet afterQuit 2 }
        let stStep := stepOnce stStep0
        if stStep.cc != bodyRet then
          throw (IO.userError s!"repeatBody/step: expected body cc, got {reprStr stStep.cc}")
        if stStep.regs.c0 == .repeatBody bodyRet afterQuit 1 then
          pure ()
        else
          throw (IO.userError s!"repeatBody/step: expected c0 repeatBody(count=1), got {reprStr stStep.regs.c0}") }
    ,
    { name := "unit/dispatch-and-opcode-canonical"
      run := do
        expectOkStack "dispatch/matched-repeat"
          (runRepeatDispatchFallback repeatInstr (withRepeatArgs #[] (.num 0)))
          #[]
        expectOkStack "dispatch/fallback"
          (runRepeatDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]

        let code ←
          match assembleCp0 [repeatInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/repeat failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/repeat" s0 repeatInstr 8
        let s2 ← expectDecodeStep "decode/add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        let raw := Slice.ofCell (Cell.mkOrdinary (natToBits 0xe4 8 ++ natToBits 0xa0 8) #[])
        let r1 ← expectDecodeStep "decode/raw-repeat" raw repeatInstr 8
        let r2 ← expectDecodeStep "decode/raw-add" r1 .add 8
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits remaining") }
  ]
  oracle := #[
    -- Non-positive fast-return branch (`count <= 0`).
    mkRepeatCase "ok/nonpositive/zero" (withRepeatArgs #[] (.num 0)),
    mkRepeatCase "ok/nonpositive/minus-one" (withRepeatArgs #[] (.num (-1))),
    mkRepeatCase "ok/nonpositive/min32" (withRepeatArgs #[] (.num (-2147483648))),
    mkRepeatCase "ok/nonpositive/deep-noise-a" (withRepeatArgs noiseA (.num 0)),
    mkRepeatCase "ok/nonpositive/deep-noise-b" (withRepeatArgs noiseB (.num (-3))),

    -- Positive branch with oracle-supported continuation token `K=quit(0)`.
    mkRepeatCase "ok/positive/one-quit-body" (withRepeatArgs #[] (.num 1)),
    mkRepeatCase "ok/positive/two-quit-body" (withRepeatArgs #[] (.num 2)),
    mkRepeatCase "ok/positive/max32-quit-body" (withRepeatArgs #[] (.num 2147483647)),
    mkRepeatCase "ok/positive/deep-noise-a" (withRepeatArgs noiseA (.num 4)),
    mkRepeatCase "ok/positive/deep-noise-b" (withRepeatArgs noiseB (.num 5)),

    -- Underflow before any type/range checks.
    mkRepeatCase "err/underflow/empty" #[],
    mkRepeatCase "err/underflow/one-int" #[intV 1],
    mkRepeatCase "err/underflow/one-cont" #[kCont],

    -- Top pop (`popCont`) type checks and order.
    mkRepeatCase "err/type/top-int" (withRepeatArgs #[] (.num 1) (intV 7)),
    mkRepeatCase "err/type/top-null" (withRepeatArgs #[] (.num 1) (.null : Value)),
    mkRepeatCase "err/type/top-cell" (withRepeatArgs #[] (.num 1) (.cell refCellA)),
    mkRepeatCase "err/type/top-slice" (withRepeatArgs #[] (.num 1) (.slice fullSliceA)),
    mkRepeatCase "err/type/top-builder" (withRepeatArgs #[] (.num 1) (.builder Builder.empty)),
    mkRepeatCase "err/type/top-tuple" (withRepeatArgs #[] (.num 1) (.tuple #[])),
    mkRepeatCase "err/type/order-top-before-count" #[.cell refCellA, .builder Builder.empty],

    -- Count pop type checks after successful `popCont`.
    mkRepeatCase "err/type/count-null" (withRepeatRawCount #[] (.null : Value)),
    mkRepeatCase "err/type/count-cell" (withRepeatRawCount #[] (.cell refCellA)),
    mkRepeatCase "err/type/count-slice" (withRepeatRawCount #[] (.slice fullSliceA)),
    mkRepeatCase "err/type/count-builder" (withRepeatRawCount #[] (.builder Builder.empty)),
    mkRepeatCase "err/type/count-tuple" (withRepeatRawCount #[] (.tuple #[])),
    mkRepeatCase "err/type/order-count-after-valid-cont" #[.slice fullSliceA, kCont],

    -- Smallint range checks (`pop_smallint_range` semantics).
    mkRepeatCase "err/range/count-over-max32" #[intV 2147483648, kCont],
    mkRepeatCase "err/range/count-under-min32" #[intV (-2147483649), kCont],
    mkRepeatCase "err/range/count-max-int257" #[intV maxInt257, kCont],
    mkRepeatCase "err/range/count-min-int257" #[intV minInt257, kCont],
    mkRepeatCase "err/range/count-nan-via-program" #[kCont]
      #[.pushInt .nan, .xchg0 1, repeatInstr],

    -- Raw cp0 program with returning body continuation via PUSHCONT_SHORT len=0.
    mkRepeatCodeCase "raw/loop/zero-after-add"
      (withRawCount #[intV 40] (.num 0))
      repeatPushContEmptyAfterAddCode,
    mkRepeatCodeCase "raw/loop/one-after-add"
      (withRawCount #[intV 40] (.num 1))
      repeatPushContEmptyAfterAddCode,
    mkRepeatCodeCase "raw/loop/two-after-add"
      (withRawCount #[intV 40] (.num 2))
      repeatPushContEmptyAfterAddCode,
    mkRepeatCodeCase "raw/loop/three-after-add"
      (withRawCount #[intV 40] (.num 3))
      repeatPushContEmptyAfterAddCode,
    mkRepeatCodeCase "raw/loop/negative-after-add"
      (withRawCount #[intV 40] (.num (-2)))
      repeatPushContEmptyAfterAddCode,
    mkRepeatCodeCase "raw/type/count-null-after-pushcont"
      #[intV 40, .null]
      repeatPushContEmptyAfterAddCode,
    mkRepeatCodeCase "raw/range/count-over-max32-after-pushcont"
      #[intV 40, intV 2147483648]
      repeatPushContEmptyAfterAddCode,
    mkRepeatCodeCase "raw/underflow/missing-count-after-pushcont"
      #[]
      repeatPushContEmptyAfterAddCode,

    -- Deterministic gas cliff.
    mkRepeatCase "gas/exact-zero-succeeds" (withRepeatArgs #[] (.num 0))
      #[.pushInt (.num repeatSetGasExact), .tonEnvOp .setGasLimit, repeatInstr],
    mkRepeatCase "gas/exact-minus-one-zero-out-of-gas" (withRepeatArgs #[] (.num 0))
      #[.pushInt (.num repeatSetGasExactMinusOne), .tonEnvOp .setGasLimit, repeatInstr]
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile repeatId repeatFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.REPEAT
