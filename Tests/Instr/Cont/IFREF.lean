import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFREF

/-
IFREF branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Ifref.lean` (`execInstrFlowIfref`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xe300` decode with one attached ref)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifref _` rejected by standalone encoder)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`IFREF` registration at `0xe300`: `exec_do_with_cell(... pop_bool ? call(ref_to_cont(cell)) : 0)`).

Branch map covered by this suite:
- dispatch: `.ifref _` handled vs fallback to `next`;
- decode/ref gate: `have_refs(1)` / `takeRefInv` success vs `invOpcode` failure;
- condition pop: `popBool` underflow/type/intov paths;
- branch split:
  - true: register cell load + call referenced continuation (`call`, not jump);
  - false: no ref-load side effects, no continuation transfer.
-/

private def ifrefId : InstrId := { name := "IFREF" }

private def ifrefOpcode : Nat := 0xe300

private def dispatchSentinel : Int := 9302

private def ifrefInstr (refCell : Cell) : Instr :=
  .ifref (Slice.ofCell refCell)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b10101 5) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0x13 5) #[refLeafA, refLeafB]

private def bodyEmpty : Cell :=
  Cell.empty

private def bodyBits : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def bodyDeep : Cell :=
  Cell.mkOrdinary (natToBits 0x12f 9) #[refLeafB, refLeafC]

private def assembleProg! (label : String) (prog : List Instr) : Cell :=
  match assembleCp0 prog with
  | .ok c => c
  | .error e => panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def bodyPush7 : Cell :=
  assembleProg! "bodyPush7" [.pushInt (.num 7)]

private def bodyAdd : Cell :=
  assembleProg! "bodyAdd" [.add]

private def sliceNoiseA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x5a 8) #[refLeafA])

private def sliceNoiseB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x1ace 13) #[refLeafB, refLeafC])

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refLeafA]

private def noiseB : Array Value :=
  #[.slice sliceNoiseA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[.cont (.quit 0), intV (-9), .cell refLeafC, .slice sliceNoiseB]

private def withCond (below : Array Value) (cond : Int) : Array Value :=
  below ++ #[intV cond]

private def withCondRaw (below : Array Value) (cond : Value) : Array Value :=
  below ++ #[cond]

private def runIfrefDirect (refCell : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfref (ifrefInstr refCell) stack

private def runIfrefDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfref instr (VM.push (intV dispatchSentinel)) stack

private def runIfrefRaw
    (refCell : Cell)
    (stack : Array Value)
    (loaded : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, loadedCells := loaded }
  (execInstrFlowIfref (ifrefInstr refCell) (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
  match res with
  | (.ok _, st) => pure st
  | (.error e, _) =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  match res with
  | (.error e, st) =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")
  | (.ok _, st) =>
      throw (IO.userError s!"{label}: expected error {expected}, got success with state {reprStr st}")

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got instr={reprStr instr}, bits={bits}")

private def mkIfrefCodeCell
    (refCell : Cell)
    (tail : Array Instr := #[]) : Except String Cell := do
  let tailCell ←
    match assembleCp0 tail.toList with
    | .ok c => pure c
    | .error e => throw s!"assembleCp0 tail failed: {reprStr e}"
  if tailCell.refs.isEmpty then
    pure (Cell.mkOrdinary (natToBits ifrefOpcode 16 ++ tailCell.bits) #[refCell])
  else
    throw s!"tail unexpectedly assembled with refs: {tailCell.refs.size}"

private def mkIfrefCodeCell! (refCell : Cell) (tail : Array Instr := #[]) : Cell :=
  match mkIfrefCodeCell refCell tail with
  | .ok c => c
  | .error e => panic! s!"mkIfrefCodeCell!: {e}"

private def ifrefMissingRefCode : Cell :=
  Cell.mkOrdinary (natToBits ifrefOpcode 16) #[]

private def ifrefTruncatedCode15 : Cell :=
  Cell.mkOrdinary (natToBits ifrefOpcode 15) #[]

private def mkIfrefOracleCase
    (name : String)
    (initStack : Array Value)
    (refCell : Cell := bodyEmpty)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifrefId
    codeCell? := some (mkIfrefCodeCell! refCell tail)
    initStack := initStack
    gasLimits := gasLimits
    fuel := fuel }

private def mkMissingRefOracleCase
    (name : String)
    (initStack : Array Value)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifrefId
    codeCell? := some ifrefMissingRefCode
    initStack := initStack
    fuel := fuel }

private def mkTruncatedOracleCase
    (name : String)
    (initStack : Array Value)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifrefId
    codeCell? := some ifrefTruncatedCode15
    initStack := initStack
    fuel := fuel }

private def runIfrefLean (code : Cell) (initStack : Array Value) (fuel : Nat := 200_000) : StepResult :=
  let st0 : VmState := { (VmState.initial code) with stack := initStack }
  VmState.run nativeHost fuel st0

private def expectExit (label : String) (expectedExit : Int) (res : StepResult) : IO VmState := do
  match res with
  | .halt exitCode st =>
      if exitCode = expectedExit then
        pure st
      else
        throw (IO.userError s!"{label}: expected exit {expectedExit}, got {exitCode}")
  | .continue _ =>
      throw (IO.userError s!"{label}: execution did not halt")

private def expectTopIntNum (label : String) (expected : Int) (st : VmState) : IO Unit := do
  match st.stack.back? with
  | some (.int (.num n)) =>
      if n = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected top int {expected}, got {n}")
  | some v =>
      throw (IO.userError s!"{label}: expected top int, got {reprStr v}")
  | none =>
      throw (IO.userError s!"{label}: expected non-empty stack")

def suite : InstrSuite where
  id := ifrefId
  unit := #[
    { name := "unit/state/true-loads-cell-and-calls"
      run := do
        let st ← expectRawOk "state/true/fresh"
          (runIfrefRaw bodyBits (withCond #[] 1))
        if st.stack != #[] then
          throw (IO.userError s!"state/true/fresh: expected empty stack, got {reprStr st.stack}")
        match st.cc with
        | .ordinary code saved _ _ =>
            if code != Slice.ofCell bodyBits then
              throw (IO.userError
                s!"state/true/fresh: expected cc code from bodyBits, got {reprStr code}")
            if saved != .quit 0 then
              throw (IO.userError
                s!"state/true/fresh: expected saved c0 quit0, got {reprStr saved}")
        | other =>
            throw (IO.userError s!"state/true/fresh: expected ordinary cc, got {reprStr other}")
        match st.regs.c0 with
        | .ordinary retCode _ cregs cdata =>
            if retCode != Slice.ofCell Cell.empty then
              throw (IO.userError
                s!"state/true/fresh: expected return code from current cc, got {reprStr retCode}")
            match cregs.c0 with
            | some (.quit 0) => pure ()
            | _ =>
                throw (IO.userError
                  s!"state/true/fresh: expected return cont to capture old c0=quit0, got {reprStr cregs.c0}")
            if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError
                s!"state/true/fresh: unexpected return cdata {reprStr cdata}")
        | other =>
            throw (IO.userError
              s!"state/true/fresh: expected ordinary return c0 (call semantics), got {reprStr other}")
        let expectedHash := Cell.hashBytes bodyBits
        if st.loadedCells != #[expectedHash] then
          throw (IO.userError
            s!"state/true/fresh: expected loadedCells to contain body hash, got {reprStr st.loadedCells}")
        if st.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError
            s!"state/true/fresh: expected gas={cellLoadGasPrice}, got {st.gas.gasConsumed}") }
    ,
    { name := "unit/state/true-reload-cost-when-already-loaded"
      run := do
        let h := Cell.hashBytes bodyBits
        let st ← expectRawOk "state/true/reload"
          (runIfrefRaw bodyBits (withCond #[] (-1)) #[h])
        if st.loadedCells != #[h] then
          throw (IO.userError
            s!"state/true/reload: expected loaded set unchanged, got {reprStr st.loadedCells}")
        if st.gas.gasConsumed != cellReloadGasPrice then
          throw (IO.userError
            s!"state/true/reload: expected gas={cellReloadGasPrice}, got {st.gas.gasConsumed}") }
    ,
    { name := "unit/state/false-skips-load-and-call"
      run := do
        let below := noiseB ++ #[intV 33]
        let st ← expectRawOk "state/false"
          (runIfrefRaw bodyDeep (withCond below 0))
        if st.stack != below then
          throw (IO.userError s!"state/false: expected stack {reprStr below}, got {reprStr st.stack}")
        if st.gas.gasConsumed != 0 then
          throw (IO.userError s!"state/false: expected zero gas, got {st.gas.gasConsumed}")
        if st.loadedCells != #[] then
          throw (IO.userError s!"state/false: expected no loaded cells, got {reprStr st.loadedCells}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"state/false: expected c0 unchanged quit0, got {reprStr st.regs.c0}")
        let initialCc := (VmState.initial Cell.empty).cc
        if st.cc != initialCc then
          throw (IO.userError s!"state/false: expected cc unchanged, got {reprStr st.cc}") }
    ,
    { name := "unit/direct/errors-and-pop-bool-side-effects"
      run := do
        expectErr "direct/underflow-empty" (runIfrefDirect bodyBits #[]) .stkUnd
        let typeState ← expectRawErr "raw/type-null"
          (runIfrefRaw bodyBits (withCondRaw #[] (.null : Value))) .typeChk
        if typeState.stack != #[] then
          throw (IO.userError s!"raw/type-null: expected consumed bad bool value, got {reprStr typeState.stack}")
        if typeState.gas.gasConsumed != 0 then
          throw (IO.userError s!"raw/type-null: expected no cell-load gas, got {typeState.gas.gasConsumed}")
        let nanState ← expectRawErr "raw/intov-nan"
          (runIfrefRaw bodyBits (withCondRaw #[] (.int .nan))) .intOv
        if nanState.stack != #[] then
          throw (IO.userError s!"raw/intov-nan: expected consumed NaN bool value, got {reprStr nanState.stack}")
        if nanState.gas.gasConsumed != 0 then
          throw (IO.userError s!"raw/intov-nan: expected no cell-load gas, got {nanState.gas.gasConsumed}") }
    ,
    { name := "unit/direct/deep-stack-preserved-on-both-branches"
      run := do
        let below := noiseC ++ #[.builder Builder.empty, .tuple #[]]
        expectOkStack "deep/false"
          (runIfrefDirect bodyEmpty (withCond below 0))
          below
        expectOkStack "deep/true-empty-body"
          (runIfrefDirect bodyEmpty (withCond below 9))
          below }
    ,
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/non-ifref-fallback"
          (runIfrefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/matching-ifref"
          (runIfrefDispatchFallback (ifrefInstr bodyEmpty) #[intV 1])
          #[] }
    ,
    { name := "unit/decode/opcode-boundaries-and-asm-rejection"
      run := do
        let bits : BitString :=
          natToBits 0xe300 16 ++
          natToBits 0xe301 16 ++
          natToBits 0xe302 16 ++
          natToBits 0xa0 8
        let code : Cell := Cell.mkOrdinary bits #[bodyBits, bodyDeep, bodyEmpty]
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ifref" s0 (ifrefInstr bodyBits) 16
        let s2 ← expectDecodeStep "decode/ifnotref" s1 (.ifnotref (Slice.ofCell bodyDeep)) 16
        let s3 ← expectDecodeStep "decode/ifjmpref" s2 (.ifjmpref (Slice.ofCell bodyEmpty)) 16
        let s4 ← expectDecodeStep "decode/add-tail" s3 .add 8
        if s4.bitsRemaining = 0 && s4.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/sequence-end: expected exhausted slice, got bits={s4.bitsRemaining} refs={s4.refsRemaining}")

        expectDecodeErr "decode/missing-ref"
          (Slice.ofCell ifrefMissingRefCode) .invOpcode
        expectDecodeErr "decode/truncated-15-bits"
          (Slice.ofCell ifrefTruncatedCode15) .invOpcode

        match assembleCp0 [ifrefInstr bodyBits] with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"asm/ifref: expected invOpcode, got {e}")
        | .ok c =>
            throw (IO.userError s!"asm/ifref: expected invOpcode, got assembled code {reprStr c}") }
    ,
    { name := "unit/full-run/call-semantics-and-branch-gating"
      run := do
        let codeTail := mkIfrefCodeCell! bodyEmpty #[.pushInt (.num 9)]
        let stTrue ← expectExit "full/call-tail/true" (~~~ 0)
          (runIfrefLean codeTail #[intV 1])
        expectTopIntNum "full/call-tail/true" 9 stTrue
        let stFalse ← expectExit "full/call-tail/false" (~~~ 0)
          (runIfrefLean codeTail #[intV 0])
        expectTopIntNum "full/call-tail/false" 9 stFalse

        let codeFailingBody := mkIfrefCodeCell! bodyAdd #[.pushInt (.num 9)]
        let _ ← expectExit "full/branch-gating/true-body-runs" (~~~ Excno.stkUnd.toInt)
          (runIfrefLean codeFailingBody #[intV 1])
        let stSkip ← expectExit "full/branch-gating/false-body-skipped" (~~~ 0)
          (runIfrefLean codeFailingBody #[intV 0])
        expectTopIntNum "full/branch-gating/false-body-skipped" 9 stSkip }
  ]
  oracle := #[
    -- True branch: condition non-zero => load ref + call body continuation.
    mkIfrefOracleCase "ok/true/basic-1" (withCond #[] 1) bodyEmpty,
    mkIfrefOracleCase "ok/true/basic-neg1" (withCond #[] (-1)) bodyEmpty,
    mkIfrefOracleCase "ok/true/basic-2" (withCond #[] 2) bodyBits,
    mkIfrefOracleCase "ok/true/basic-neg2" (withCond #[] (-2)) bodyBits,
    mkIfrefOracleCase "ok/true/max-int257" (withCond #[] maxInt257) bodyDeep,
    mkIfrefOracleCase "ok/true/min-int257" (withCond #[] minInt257) bodyDeep,
    mkIfrefOracleCase "ok/true/deep-noise-a" (withCond noiseA 7) bodyBits,
    mkIfrefOracleCase "ok/true/deep-noise-b" (withCond noiseB (-5)) bodyDeep,
    mkIfrefOracleCase "ok/true/deep-noise-c" (withCond noiseC 255) bodyDeep,

    -- False branch: condition zero => no ref load/call.
    mkIfrefOracleCase "ok/false/basic-zero" (withCond #[] 0) bodyEmpty,
    mkIfrefOracleCase "ok/false/deep-noise-a" (withCond noiseA 0) bodyBits,
    mkIfrefOracleCase "ok/false/deep-noise-b" (withCond noiseB 0) bodyBits,
    mkIfrefOracleCase "ok/false/deep-noise-c" (withCond noiseC 0) bodyDeep,
    mkIfrefOracleCase "ok/false/preserve-max" (withCond #[intV maxInt257] 0) bodyBits,
    mkIfrefOracleCase "ok/false/preserve-min" (withCond #[intV minInt257] 0) bodyBits,
    mkIfrefOracleCase "ok/false/slice-builder" (withCond #[.slice sliceNoiseA, .builder Builder.empty] 0) bodyDeep,
    mkIfrefOracleCase "ok/false/tuple-cont" (withCond #[.tuple #[], .cont (.quit 0)] 0) bodyDeep,

    -- popBool failures with present inline ref.
    mkIfrefOracleCase "err/underflow/empty-stack" #[] bodyBits,
    mkIfrefOracleCase "err/type/bool-null" (withCondRaw #[] (.null : Value)) bodyBits,
    mkIfrefOracleCase "err/type/bool-cell" (withCondRaw #[] (.cell refLeafA)) bodyBits,
    mkIfrefOracleCase "err/type/bool-slice" (withCondRaw #[] (.slice sliceNoiseB)) bodyBits,
    mkIfrefOracleCase "err/type/bool-builder" (withCondRaw #[] (.builder Builder.empty)) bodyBits,
    mkIfrefOracleCase "err/type/bool-tuple" (withCondRaw #[] (.tuple #[])) bodyBits,
    mkIfrefOracleCase "err/type/bool-cont" (withCondRaw #[] (.cont (.quit 0))) bodyBits,

    -- Decode/ref gate failures must happen before condition pop/type checks.
    mkMissingRefOracleCase "err/decode/missing-ref-empty" #[],
    mkMissingRefOracleCase "err/decode/missing-ref-cond-1" #[intV 1],
    mkMissingRefOracleCase "err/decode/missing-ref-bool-null" #[.null],
    mkMissingRefOracleCase "err/decode/missing-ref-bool-cell" #[.cell refLeafA],
    mkTruncatedOracleCase "err/decode/truncated-15-empty" #[],
    mkTruncatedOracleCase "err/decode/truncated-15-cond-1" #[intV 1],

    -- Call-vs-jump behavior and body execution gating.
    mkIfrefOracleCase "ok/call-tail/true-empty-body" #[intV 1] bodyEmpty #[.pushInt (.num 9)],
    mkIfrefOracleCase "ok/call-tail/false-empty-body" #[intV 0] bodyEmpty #[.pushInt (.num 9)],
    mkIfrefOracleCase "ok/call-tail/true-body-push7" #[intV 1] bodyPush7 #[.pushInt (.num 9)],
    mkIfrefOracleCase "ok/call-tail/false-body-push7" #[intV 0] bodyPush7 #[.pushInt (.num 9)],
    mkIfrefOracleCase "err/branch/true-body-add-underflow" #[intV 1] bodyAdd #[.pushInt (.num 9)],
    mkIfrefOracleCase "ok/branch/false-skips-body-add" #[intV 0] bodyAdd #[.pushInt (.num 9)]
  ]
  fuzz := #[ mkReplayOracleFuzzSpec ifrefId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.IFREF
