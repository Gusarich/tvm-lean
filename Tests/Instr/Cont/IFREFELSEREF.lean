import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFREFELSEREF

/-
IFREFELSEREF branch-map audit (Lean vs C++ `exec_ifref_elseref`):
- Lean sources:
  - `TvmLean/Semantics/Exec/Flow/IfrefElseRef.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xe30f` decode with two refs)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifrefElseRef _ _` rejected by assembler)
- C++ source:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_ifref_elseref`)

Covered branches:
- decode/ref gate: opcode prefix + two refs required; missing refs/truncation => `invOpcode`;
- dispatch: `.ifrefElseRef` handled vs fallback `next`;
- bool pop order: `pop_bool`/`popBool` happens before selected-ref conversion;
- selection: nonzero => first ref, zero => second ref;
- selected-cell continuation conversion + call semantics:
  - selected ref only is loaded and converted (`ref_to_cont`/`.ordinary ...`),
  - load gas charged before special-cell rejection (`cellUnd`),
  - call path uses call semantics (`st->call` / `VM.call`), not jump.
-/

private def ifrefElseRefId : InstrId := { name := "IFREFELSEREF" }

private def ifrefElseRefOpcode : Nat := 0xe30f

private def dispatchSentinel : Int := 68421

private def tailMarker : Int := 909

private def trueMarker : Int := 111

private def falseMarker : Int := 222

private def ifrefElseRefInstr (t f : Cell) : Instr :=
  .ifrefElseRef (Slice.ofCell t) (Slice.ofCell f)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 5) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 0x13 5) #[refLeafA, refLeafB]

private def assembleNoRefCell! (label : String) (prog : Array Instr) : Cell :=
  match assembleCp0 prog.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def bodyNoop : Cell :=
  Cell.empty

private def bodyPushTrue : Cell :=
  assembleNoRefCell! "bodyPushTrue" #[.pushInt (.num trueMarker)]

private def bodyPushFalse : Cell :=
  assembleNoRefCell! "bodyPushFalse" #[.pushInt (.num falseMarker)]

private def bodyPush7 : Cell :=
  assembleNoRefCell! "bodyPush7" #[.pushInt (.num 7)]

private def bodyPush8 : Cell :=
  assembleNoRefCell! "bodyPush8" #[.pushInt (.num 8)]

private def bodyAdd : Cell :=
  assembleNoRefCell! "bodyAdd" #[.add]

private def bodyDeepTrue : Cell :=
  Cell.mkOrdinary (natToBits 0x2d 6) #[refLeafA, refLeafB]

private def bodyDeepFalse : Cell :=
  Cell.mkOrdinary (natToBits 0x1b 5) #[refLeafC]

private def specialTrueCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def specialFalseCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 true
    refs := #[]
    special := true
    levelMask := 0 }

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

private def mkIfrefElseRefCodeCell
    (t f : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "mkIfrefElseRefCodeCell/tail" tail
  Cell.mkOrdinary
    (natToBits ifrefElseRefOpcode 16 ++ tailCell.bits)
    (#[t, f] ++ tailCell.refs)

private def mkPrefixedIfrefElseRefCodeCell
    (pre : Array Instr)
    (t f : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let preCell := assembleNoRefCell! "mkPrefixedIfrefElseRefCodeCell/pre" pre
  let tailCell := assembleNoRefCell! "mkPrefixedIfrefElseRefCodeCell/tail" tail
  Cell.mkOrdinary
    (preCell.bits ++ natToBits ifrefElseRefOpcode 16 ++ tailCell.bits)
    (preCell.refs ++ #[t, f] ++ tailCell.refs)

private def codeObserveMarkers : Cell :=
  mkIfrefElseRefCodeCell bodyPushTrue bodyPushFalse #[.pushInt (.num tailMarker)]

private def codeTrueAddTail : Cell :=
  mkIfrefElseRefCodeCell bodyAdd bodyNoop #[.pushInt (.num tailMarker)]

private def codeFalseAddTail : Cell :=
  mkIfrefElseRefCodeCell bodyNoop bodyAdd #[.pushInt (.num tailMarker)]

private def ifrefElseRefMissingRef0Code : Cell :=
  Cell.mkOrdinary (natToBits ifrefElseRefOpcode 16) #[]

private def ifrefElseRefMissingRef1Code : Cell :=
  Cell.mkOrdinary (natToBits ifrefElseRefOpcode 16) #[bodyNoop]

private def ifrefElseRefTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xe3 8) #[bodyPushTrue, bodyPushFalse]

private def ifrefElseRefTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits ifrefElseRefOpcode 15) #[bodyPushTrue, bodyPushFalse]

private def runIfrefElseRefDirect
    (t f : Cell)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfrefElseRef (ifrefElseRefInstr t f) stack

private def runIfrefElseRefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfrefElseRef instr (VM.push (intV dispatchSentinel)) stack

private def runIfrefElseRefRaw
    (t f : Cell)
    (stack : Array Value)
    (cc : Continuation := .quit 71)
    (loaded : Array (Array UInt8) := #[])
    (gasLimit : Int := 1_000_000) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      loadedCells := loaded
      gas := GasLimits.ofLimits gasLimit gasLimit 0 }
  (execInstrFlowIfrefElseRef (ifrefElseRefInstr t f) (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  match res with
  | (.ok _, st) =>
      pure st
  | (.error e, _) =>
      throw (IO.userError s!"{label}: expected success, got {e}")

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

private def sameSlice (a b : Slice) : Bool :=
  a.bitPos == b.bitPos && a.refPos == b.refPos && a.cell == b.cell

private def runIfrefElseRefLean (code : Cell) (initStack : Array Value) (fuel : Nat := 200_000) : StepResult :=
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

private def mkCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifrefElseRefId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkIfrefElseRefCase
    (name : String)
    (stack : Array Value)
    (t f : Cell := bodyNoop)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkIfrefElseRefCodeCell t f tail) gasLimits fuel

private def mkPrefixedIfrefElseRefCase
    (name : String)
    (stack : Array Value)
    (pre : Array Instr)
    (t f : Cell)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkPrefixedIfrefElseRefCodeCell pre t f tail) gasLimits fuel

def suite : InstrSuite where
  id := ifrefElseRefId
  unit := #[
    { name := "unit/raw/branch-selection-and-call-semantics"
      run := do
        let ccOrd : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

        let stTrue ← expectRawOk "raw/true"
          (runIfrefElseRefRaw bodyPushTrue bodyPushFalse (withCond #[intV 9] 1) ccOrd)
        if stTrue.stack != #[intV 9] then
          throw (IO.userError s!"raw/true: stack mismatch {reprStr stTrue.stack}")
        match stTrue.cc with
        | .ordinary code saved _ _ =>
            if !(sameSlice code (Slice.ofCell bodyPushTrue)) then
              throw (IO.userError s!"raw/true: expected cc code from first ref, got {reprStr code}")
            if saved != .quit 0 then
              throw (IO.userError s!"raw/true: expected saved=quit0, got {reprStr saved}")
        | other =>
            throw (IO.userError s!"raw/true: expected ordinary cc, got {reprStr other}")
        match stTrue.regs.c0 with
        | .ordinary retCode _ cregs cdata =>
            if !(sameSlice retCode (Slice.ofCell Cell.empty)) then
              throw (IO.userError s!"raw/true: return continuation code mismatch {reprStr retCode}")
            match cregs.c0 with
            | some (.quit 0) =>
                pure ()
            | _ =>
                throw (IO.userError s!"raw/true: expected captured old c0=quit0, got {reprStr cregs.c0}")
            if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError s!"raw/true: return continuation cdata mismatch {reprStr cdata}")
        | other =>
            throw (IO.userError s!"raw/true: expected ordinary return c0, got {reprStr other}")
        let hashTrue := Cell.hashBytes bodyPushTrue
        if stTrue.loadedCells != #[hashTrue] then
          throw (IO.userError s!"raw/true: loadedCells mismatch {reprStr stTrue.loadedCells}")
        if stTrue.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError s!"raw/true: expected gas {cellLoadGasPrice}, got {stTrue.gas.gasConsumed}")

        let stFalse ← expectRawOk "raw/false"
          (runIfrefElseRefRaw bodyPushTrue bodyPushFalse (withCond #[intV 10] 0) ccOrd)
        if stFalse.stack != #[intV 10] then
          throw (IO.userError s!"raw/false: stack mismatch {reprStr stFalse.stack}")
        match stFalse.cc with
        | .ordinary code saved _ _ =>
            if !(sameSlice code (Slice.ofCell bodyPushFalse)) then
              throw (IO.userError s!"raw/false: expected cc code from second ref, got {reprStr code}")
            if saved != .quit 0 then
              throw (IO.userError s!"raw/false: expected saved=quit0, got {reprStr saved}")
        | other =>
            throw (IO.userError s!"raw/false: expected ordinary cc, got {reprStr other}")
        let hashFalse := Cell.hashBytes bodyPushFalse
        if stFalse.loadedCells != #[hashFalse] then
          throw (IO.userError s!"raw/false: loadedCells mismatch {reprStr stFalse.loadedCells}")
        if stFalse.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError s!"raw/false: expected gas {cellLoadGasPrice}, got {stFalse.gas.gasConsumed}") }
    ,
    { name := "unit/raw/reload-cost-and-selected-cell-only-load"
      run := do
        let hashTrue := Cell.hashBytes bodyPushTrue
        let hashFalse := Cell.hashBytes bodyPushFalse

        let stReload ← expectRawOk "reload/true"
          (runIfrefElseRefRaw bodyPushTrue bodyPushFalse (withCond #[] (-1)) (.quit 71) #[hashTrue])
        if stReload.loadedCells != #[hashTrue] then
          throw (IO.userError s!"reload/true: expected loaded set unchanged, got {reprStr stReload.loadedCells}")
        if stReload.gas.gasConsumed != cellReloadGasPrice then
          throw (IO.userError s!"reload/true: expected reload gas {cellReloadGasPrice}, got {stReload.gas.gasConsumed}")

        let stOther ← expectRawOk "reload/false"
          (runIfrefElseRefRaw bodyPushTrue bodyPushFalse (withCond #[] 0) (.quit 71) #[hashTrue])
        if stOther.loadedCells != #[hashTrue, hashFalse] then
          throw (IO.userError s!"reload/false: expected second ref loaded only, got {reprStr stOther.loadedCells}")
        if stOther.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError s!"reload/false: expected load gas {cellLoadGasPrice}, got {stOther.gas.gasConsumed}") }
    ,
    { name := "unit/raw/pop-bool-errors-before-load"
      run := do
        expectErr "direct/underflow-empty" (runIfrefElseRefDirect bodyPushTrue bodyPushFalse #[]) .stkUnd

        let stType ← expectRawErr "raw/type-null"
          (runIfrefElseRefRaw bodyPushTrue bodyPushFalse (withCondRaw #[intV 6] (.null : Value)))
          .typeChk
        if stType.stack != #[intV 6] then
          throw (IO.userError s!"raw/type-null: expected bool consumed, got {reprStr stType.stack}")
        if !stType.loadedCells.isEmpty then
          throw (IO.userError s!"raw/type-null: expected no loaded cells, got {reprStr stType.loadedCells}")
        if stType.gas.gasConsumed != 0 then
          throw (IO.userError s!"raw/type-null: expected zero gas, got {stType.gas.gasConsumed}")

        let stNan ← expectRawErr "raw/intov-nan"
          (runIfrefElseRefRaw bodyPushTrue bodyPushFalse (withCondRaw #[intV 7] (.int .nan)))
          .intOv
        if stNan.stack != #[intV 7] then
          throw (IO.userError s!"raw/intov-nan: expected bool consumed, got {reprStr stNan.stack}")
        if !stNan.loadedCells.isEmpty then
          throw (IO.userError s!"raw/intov-nan: expected no loaded cells, got {reprStr stNan.loadedCells}")
        if stNan.gas.gasConsumed != 0 then
          throw (IO.userError s!"raw/intov-nan: expected zero gas, got {stNan.gas.gasConsumed}") }
    ,
    { name := "unit/raw/special-cell-conversion-and-branch-order"
      run := do
        let hashSpecialTrue := Cell.hashBytes specialTrueCell
        let hashSpecialFalse := Cell.hashBytes specialFalseCell
        let hashNoop := Cell.hashBytes bodyNoop

        let stTakenSpecial ← expectRawErr "special/true-selected"
          (runIfrefElseRefRaw specialTrueCell bodyNoop (withCond #[] 1))
          .cellUnd
        if stTakenSpecial.loadedCells != #[hashSpecialTrue] then
          throw (IO.userError
            s!"special/true-selected: expected selected special loaded before error, got {reprStr stTakenSpecial.loadedCells}")
        if stTakenSpecial.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError s!"special/true-selected: expected load gas, got {stTakenSpecial.gas.gasConsumed}")

        let stTakenFalseSpecial ← expectRawErr "special/false-selected"
          (runIfrefElseRefRaw bodyNoop specialFalseCell (withCond #[] 0))
          .cellUnd
        if stTakenFalseSpecial.loadedCells != #[hashSpecialFalse] then
          throw (IO.userError
            s!"special/false-selected: expected selected special loaded before error, got {reprStr stTakenFalseSpecial.loadedCells}")

        let stSkipFirstSpecial ← expectRawOk "special/skip-first-special"
          (runIfrefElseRefRaw specialTrueCell bodyNoop (withCond #[] 0))
        if stSkipFirstSpecial.loadedCells != #[hashNoop] then
          throw (IO.userError
            s!"special/skip-first-special: expected only second ref load, got {reprStr stSkipFirstSpecial.loadedCells}")

        let stSkipSecondSpecial ← expectRawOk "special/skip-second-special"
          (runIfrefElseRefRaw bodyNoop specialFalseCell (withCond #[] 7))
        if stSkipSecondSpecial.loadedCells != #[hashNoop] then
          throw (IO.userError
            s!"special/skip-second-special: expected only first ref load, got {reprStr stSkipSecondSpecial.loadedCells}") }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfrefElseRefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]

        expectOkStack "dispatch/match-ifrefelseref"
          (runIfrefElseRefDispatchFallback (ifrefElseRefInstr bodyNoop bodyNoop) #[intV 1])
          #[] }
    ,
    { name := "unit/decode/2ref-guard-and-asm-rejection"
      run := do
        let codeOk : Cell := mkIfrefElseRefCodeCell bodyPushTrue bodyPushFalse #[.add]
        let s0 : Slice := Slice.ofCell codeOk
        let s1 ← expectDecodeStep "decode/ifrefelseref"
          s0
          (ifrefElseRefInstr bodyPushTrue bodyPushFalse)
          16
        let s2 ← expectDecodeStep "decode/add-tail" s1 .add 8
        if s2.bitsRemaining = 0 && s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got bits={s2.bitsRemaining} refs={s2.refsRemaining}")

        expectDecodeErr "decode/missing-0-ref"
          (Slice.ofCell ifrefElseRefMissingRef0Code) .invOpcode
        expectDecodeErr "decode/missing-1-ref"
          (Slice.ofCell ifrefElseRefMissingRef1Code) .invOpcode
        expectDecodeErr "decode/truncated-8"
          (Slice.ofCell ifrefElseRefTruncated8Code) .invOpcode
        expectDecodeErr "decode/truncated-15"
          (Slice.ofCell ifrefElseRefTruncated15Code) .invOpcode

        match assembleCp0 [ifrefElseRefInstr bodyPushTrue bodyPushFalse] with
        | .error .invOpcode =>
            pure ()
        | .error e =>
            throw (IO.userError s!"asm/ifrefelseref: expected invOpcode, got {e}")
        | .ok c =>
            throw (IO.userError
              s!"asm/ifrefelseref: expected invOpcode, got assembled code {reprStr c}") }
    ,
    { name := "unit/full-run/call-semantics-and-branch-gating"
      run := do
        let codeNoopTail := mkIfrefElseRefCodeCell bodyNoop bodyNoop #[.pushInt (.num tailMarker)]
        let stNoopTrue ← expectExit "full/noop-tail/true" (~~~ 0)
          (runIfrefElseRefLean codeNoopTail #[intV 1])
        expectTopIntNum "full/noop-tail/true" tailMarker stNoopTrue
        let stNoopFalse ← expectExit "full/noop-tail/false" (~~~ 0)
          (runIfrefElseRefLean codeNoopTail #[intV 0])
        expectTopIntNum "full/noop-tail/false" tailMarker stNoopFalse

        let codeBranchTail := mkIfrefElseRefCodeCell bodyPush7 bodyPush8 #[.pushInt (.num tailMarker)]
        let stBranchTrue ← expectExit "full/branch-tail/true" (~~~ 0)
          (runIfrefElseRefLean codeBranchTail #[intV 1])
        if stBranchTrue.stack != #[intV 7, intV tailMarker] then
          throw (IO.userError s!"full/branch-tail/true: stack mismatch {reprStr stBranchTrue.stack}")
        let stBranchFalse ← expectExit "full/branch-tail/false" (~~~ 0)
          (runIfrefElseRefLean codeBranchTail #[intV 0])
        if stBranchFalse.stack != #[intV 8, intV tailMarker] then
          throw (IO.userError s!"full/branch-tail/false: stack mismatch {reprStr stBranchFalse.stack}")

        let _ ← expectExit "full/true-add-selected-underflow" (~~~ Excno.stkUnd.toInt)
          (runIfrefElseRefLean codeTrueAddTail #[intV 1])
        let stSkipTrueAdd ← expectExit "full/true-add-skipped" (~~~ 0)
          (runIfrefElseRefLean codeTrueAddTail #[intV 0])
        expectTopIntNum "full/true-add-skipped" tailMarker stSkipTrueAdd

        let _ ← expectExit "full/false-add-selected-underflow" (~~~ Excno.stkUnd.toInt)
          (runIfrefElseRefLean codeFalseAddTail #[intV 0])
        let stSkipFalseAdd ← expectExit "full/false-add-skipped" (~~~ 0)
          (runIfrefElseRefLean codeFalseAddTail #[intV 1])
        expectTopIntNum "full/false-add-skipped" tailMarker stSkipFalseAdd }
  ]
  oracle := #[
    -- True branch: non-zero condition selects first ref continuation.
    mkIfrefElseRefCase "ok/true/basic-1" (withCond #[] 1) bodyNoop bodyPushFalse,
    mkIfrefElseRefCase "ok/true/basic-neg1" (withCond #[] (-1)) bodyNoop bodyPushFalse,
    mkIfrefElseRefCase "ok/true/basic-2" (withCond #[] 2) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "ok/true/max-int257" (withCond #[] maxInt257) bodyDeepTrue bodyDeepFalse,
    mkIfrefElseRefCase "ok/true/min-int257" (withCond #[] minInt257) bodyDeepTrue bodyDeepFalse,
    mkIfrefElseRefCase "ok/true/deep-noise-a" (withCond noiseA 7) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "ok/true/deep-noise-b" (withCond noiseB (-5)) bodyDeepTrue bodyDeepFalse,
    mkIfrefElseRefCase "ok/true/deep-noise-c" (withCond noiseC 255) bodyDeepTrue bodyDeepFalse,
    mkIfrefElseRefCase "ok/true/selects-first-observable" #[intV 1] bodyPushTrue bodyPushFalse #[.pushInt (.num tailMarker)],
    mkIfrefElseRefCase "ok/true/skips-second-special" #[intV 1] bodyNoop specialFalseCell #[.pushInt (.num tailMarker)],

    -- False branch: zero condition selects second ref continuation.
    mkIfrefElseRefCase "ok/false/basic-zero" (withCond #[] 0) bodyPushTrue bodyNoop,
    mkIfrefElseRefCase "ok/false/deep-noise-a" (withCond noiseA 0) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "ok/false/deep-noise-b" (withCond noiseB 0) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "ok/false/deep-noise-c" (withCond noiseC 0) bodyDeepTrue bodyDeepFalse,
    mkIfrefElseRefCase "ok/false/selects-second-observable" #[intV 0] bodyPushTrue bodyPushFalse #[.pushInt (.num tailMarker)],
    mkIfrefElseRefCase "ok/false/skips-first-special" #[intV 0] specialTrueCell bodyNoop #[.pushInt (.num tailMarker)],
    mkIfrefElseRefCase "ok/false/preserve-max-below" (withCond #[intV maxInt257] 0) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "ok/false/preserve-min-below" (withCond #[intV minInt257] 0) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "ok/false/slice-builder-below" (withCond #[.slice sliceNoiseA, .builder Builder.empty] 0)
      bodyDeepTrue bodyDeepFalse,

    -- popBool failures with valid inline refs.
    mkIfrefElseRefCase "err/popbool/underflow-empty" #[] bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "err/popbool/type-null" (withCondRaw #[] (.null : Value)) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "err/popbool/type-cell" (withCondRaw #[] (.cell refLeafA)) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "err/popbool/type-slice" (withCondRaw #[] (.slice sliceNoiseB)) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "err/popbool/type-builder" (withCondRaw #[] (.builder Builder.empty)) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "err/popbool/type-tuple" (withCondRaw #[] (.tuple #[])) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "err/popbool/type-cont" (withCondRaw #[] (.cont (.quit 0))) bodyPushTrue bodyPushFalse,
    mkIfrefElseRefCase "err/popbool/type-null-with-below" (withCondRaw #[intV 77] (.null : Value)) bodyPushTrue bodyPushFalse,
    mkPrefixedIfrefElseRefCase "err/popbool/intov-nan-prefix" #[] #[.pushInt .nan] bodyNoop bodyNoop #[.pushInt (.num tailMarker)],

    -- Selected special ref conversion errors (`cellUnd`) and order checks.
    mkIfrefElseRefCase "err/special/selected-first" #[intV 1] specialTrueCell bodyNoop #[.pushInt (.num tailMarker)],
    mkIfrefElseRefCase "err/special/selected-second" #[intV 0] bodyNoop specialFalseCell #[.pushInt (.num tailMarker)],

    -- Decode/ref guard failures must precede bool-stack checks.
    mkCase "err/decode/missing-0-ref/empty" #[] ifrefElseRefMissingRef0Code,
    mkCase "err/decode/missing-0-ref/int" #[intV 1] ifrefElseRefMissingRef0Code,
    mkCase "err/decode/missing-0-ref/type-null" #[.null] ifrefElseRefMissingRef0Code,
    mkCase "err/decode/missing-1-ref/empty" #[] ifrefElseRefMissingRef1Code,
    mkCase "err/decode/missing-1-ref/int" #[intV 0] ifrefElseRefMissingRef1Code,
    mkCase "err/decode/missing-1-ref/type-cell" #[.cell refLeafA] ifrefElseRefMissingRef1Code,
    mkCase "err/decode/truncated-8-prefix" #[intV 0] ifrefElseRefTruncated8Code,
    mkCase "err/decode/truncated-15-prefix" #[intV 1] ifrefElseRefTruncated15Code,

    -- Call semantics and body/tail observability.
    mkCase "ok/call-tail/true-empty-body" #[intV 1] (mkIfrefElseRefCodeCell bodyNoop bodyNoop #[.pushInt (.num tailMarker)]),
    mkCase "ok/call-tail/false-empty-body" #[intV 0] (mkIfrefElseRefCodeCell bodyNoop bodyNoop #[.pushInt (.num tailMarker)]),
    mkCase "ok/call-tail/true-marker-body" #[intV 1] codeObserveMarkers,
    mkCase "ok/call-tail/false-marker-body" #[intV 0] codeObserveMarkers,
    mkCase "ok/call-tail/true-push7" #[intV 1] (mkIfrefElseRefCodeCell bodyPush7 bodyPush8 #[.pushInt (.num tailMarker)]),
    mkCase "ok/call-tail/false-push8" #[intV 0] (mkIfrefElseRefCodeCell bodyPush7 bodyPush8 #[.pushInt (.num tailMarker)]),

    -- Branch-gated body failures.
    mkCase "err/branch/true-selected-add-underflow" #[intV 1] codeTrueAddTail,
    mkCase "ok/branch/false-skips-true-add" #[intV 0] codeTrueAddTail,
    mkCase "err/branch/false-selected-add-underflow" #[intV 0] codeFalseAddTail,
    mkCase "ok/branch/true-skips-false-add" #[intV 1] codeFalseAddTail
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.IFREFELSEREF
