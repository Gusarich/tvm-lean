import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CALLREF

/-!
CALLREF branch map (Lean vs C++ `contops.cpp` + `vm.h`/`CellSlice.cpp`):

- decode/ref gate:
  - cp0 `0xdb3c` decodes only with one attached ref (`takeRefInv`);
  - missing/truncated ref path is `invOpcode` before handler execution.
- dispatch:
  - only `.callRef _` is handled; all other instructions fall through to `next`.
- ref-to-cont conversion branch:
  - C++ `ref_to_cont(load_cell_slice_ref(ref))` charges cell-load gas and rejects
    special/exotic cells (`cell_und`);
  - Lean mirrors this in CALLREF handler: `registerCellLoad` then special-cell rejection.
- call semantics branch:
  - C++ invokes `st->call(cont)`;
  - Lean invokes `VM.call` (baseline call-family semantics), including return-cont installation in `c0`.
-/

private def callrefId : InstrId := { name := "CALLREF" }
private def callrefOpcode : Nat := 0xdb3c
private def jmprefOpcode : Nat := 0xdb3d
private def dispatchSentinel : Int := 39039

private def q0 : Value := .cont (.quit 0)

private def ccOrdEmpty : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x15 5) #[refLeafA]

private def sliceNoiseA : Slice := Slice.ofCell refLeafA
private def sliceNoiseB : Slice := Slice.ofCell refLeafB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refLeafA]

private def noiseB : Array Value :=
  #[.slice sliceNoiseA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[q0, intV (-9), .cell refLeafB, .slice sliceNoiseB]

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

private def bodyEmpty : Cell := Cell.empty

private def bodyPush7 : Cell :=
  assembleNoRefCell! "bodyPush7" #[.pushInt (.num 7)]

private def bodyPushNeg2 : Cell :=
  assembleNoRefCell! "bodyPushNeg2" #[.pushInt (.num (-2))]

private def bodyAdd : Cell :=
  assembleNoRefCell! "bodyAdd" #[.add]

private def bodyImplicitJmpRef : Cell :=
  Cell.mkOrdinary #[] #[bodyPush7]

private def specialTargetCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def callrefInstr (target : Cell) : Instr :=
  .callRef (Slice.ofCell target)

private def mkPrefixedCallrefCode
    (pre : Array Instr)
    (target : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let preCell := assembleNoRefCell! "callref/pre" pre
  let tailCell := assembleNoRefCell! "callref/tail" tail
  Cell.mkOrdinary
    (preCell.bits ++ natToBits callrefOpcode 16 ++ tailCell.bits)
    (preCell.refs ++ #[target] ++ tailCell.refs)

private def mkCallrefCode
    (target : Cell)
    (tail : Array Instr := #[]) : Cell :=
  mkPrefixedCallrefCode #[] target tail

private def mkTwoCallrefCode
    (targetA targetB : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "callref/two/tail" tail
  Cell.mkOrdinary
    (natToBits callrefOpcode 16 ++ natToBits callrefOpcode 16 ++ tailCell.bits)
    (#[targetA, targetB] ++ tailCell.refs)

private def mkTwoCallrefOneRefCode
    (targetA : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "callref/two-one-ref/tail" tail
  Cell.mkOrdinary
    (natToBits callrefOpcode 16 ++ natToBits callrefOpcode 16 ++ tailCell.bits)
    (#[targetA] ++ tailCell.refs)

private def missingRefCode : Cell :=
  Cell.mkOrdinary (natToBits callrefOpcode 16) #[]

private def missingRefWithTailCode : Cell :=
  Cell.mkOrdinary
    (natToBits callrefOpcode 16 ++ assembleNoRefBits! "callref/missing-ref/tail" #[.pushInt (.num 9)])
    #[]

private def truncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits callrefOpcode 16).take 15) #[]

private def oneBytePrefixCode : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def runCallrefDirect
    (target : Cell)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowCallRef (callrefInstr target) stack

private def runCallrefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallRef instr (VM.push (intV dispatchSentinel)) stack

private def runCallrefRaw
    (target : Cell)
    (stack : Array Value)
    (cc : Continuation := ccOrdEmpty)
    (loaded : Array (Array UInt8) := #[])
    (gas : GasLimits := GasLimits.default) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      loadedCells := loaded
      gas := gas }
  (execInstrFlowCallRef (callrefInstr target) (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  match res with
  | (.ok _, st) => pure st
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
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | (.ok _, st) =>
      throw (IO.userError s!"{label}: expected error {expected}, got success with state {reprStr st}")

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
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .ok (instr, bits, rest) =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure rest
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got error {e}")

private def runCallrefLean
    (code : Cell)
    (initStack : Array Value)
    (fuel : Nat := 200_000) : StepResult :=
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
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callrefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCallrefCase
    (name : String)
    (stack : Array Value)
    (target : Cell)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkCallrefCode target tail) gasLimits fuel

private def mkPrefixedCallrefCase
    (name : String)
    (stack : Array Value)
    (pre : Array Instr)
    (target : Cell)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkPrefixedCallrefCode pre target tail) gasLimits fuel

private def mkTwoCallrefCase
    (name : String)
    (stack : Array Value)
    (targetA targetB : Cell)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkTwoCallrefCode targetA targetB tail) gasLimits fuel

private def oracleCases : Array OracleCase := #[
  -- Success paths.
  mkCallrefCase "ok/basic/empty-stack-empty-body" #[] bodyEmpty,
  mkCallrefCase "ok/basic/int-stack-empty-body" #[intV 5] bodyEmpty,
  mkCallrefCase "ok/basic/deep-mixed-stack-empty-body" (noiseA ++ noiseB) bodyEmpty,
  mkCallrefCase "ok/body/push7" #[] bodyPush7,
  mkCallrefCase "ok/body/pushneg2" #[intV 11] bodyPushNeg2,
  mkCallrefCase "ok/body/add-two-args" #[intV 4, intV 6] bodyAdd,
  mkCallrefCase "ok/body/add-deep-below" (noiseA ++ #[intV 1, intV 2]) bodyAdd,
  mkCallrefCase "ok/tail/push9-after-empty-body" #[] bodyEmpty #[.pushInt (.num 9)],
  mkCallrefCase "ok/tail/push9-add-after-push7" #[intV 2] bodyPush7 #[.pushInt (.num 9), .add],
  mkPrefixedCallrefCase "ok/prelude/push3-before-call-add" #[intV 4] #[.pushInt (.num 3)] bodyAdd,
  mkTwoCallrefCase "ok/two-callrefs/empty-empty" #[] bodyEmpty bodyEmpty,
  mkTwoCallrefCase "ok/two-callrefs/push7-then-pushneg2" #[] bodyPush7 bodyPushNeg2,
  mkTwoCallrefCase "ok/two-callrefs/same-target-reload" #[] bodyPush7 bodyPush7,
  mkCallrefCase "ok/target/implicit-jmpref" #[] bodyImplicitJmpRef,
  mkCallrefCase "ok/target/implicit-jmpref-with-tail" #[] bodyImplicitJmpRef #[.pushInt (.num 8), .add],
  mkCallrefCase "ok/stack/nonint-values-preserved"
    #[.null, .cell refLeafA, .slice sliceNoiseA, .builder Builder.empty, .tuple #[], q0]
    bodyEmpty,
  mkCallrefCase "ok/boundary/max-int257-preserved" #[intV maxInt257] bodyEmpty,
  mkCallrefCase "ok/boundary/min-int257-preserved" #[intV minInt257] bodyEmpty,

  -- Runtime errors.
  mkCallrefCase "err/body/add-underflow-empty" #[] bodyAdd,
  mkCallrefCase "err/body/add-underflow-one-arg" #[intV 1] bodyAdd,
  mkCallrefCase "err/special/default-gas" #[] specialTargetCell,
  mkCallrefCase "err/special/deep-stack" noiseC specialTargetCell,
  mkCallrefCase "err/special/with-tail" #[intV 5] specialTargetCell #[.pushInt (.num 9)],
  mkTwoCallrefCase "err/special/second-callref" #[] bodyEmpty specialTargetCell #[.pushInt (.num 9)],
  -- Oracle runner currently executes with default gas/c7 and does not apply
  -- `OracleGasLimits`; keep tight-gas expectations in unit/raw tests instead.

  -- Decode/ref-gate failures.
  mkCase "err/decode/missing-ref-empty" #[] missingRefCode,
  mkCase "err/decode/missing-ref-int" #[intV 1] missingRefCode,
  mkCase "err/decode/missing-ref-mixed" noiseB missingRefCode,
  mkCase "err/decode/missing-ref-with-tail" #[intV 9] missingRefWithTailCode,
  mkCase "err/decode/truncated15-empty" #[] truncated15Code,
  mkCase "err/decode/truncated15-int" #[intV 5] truncated15Code,
  mkCase "err/decode/one-byte-prefix" #[] oneBytePrefixCode,
  mkCase "err/decode/second-callref-missing-second-ref"
    #[]
    (mkTwoCallrefOneRefCode bodyEmpty #[.pushInt (.num 9)]),
  mkCase "err/decode/missing-ref-nonint-stack" #[.null, q0] missingRefCode,
  mkCase "err/decode/second-callref-missing-second-ref-deep"
    noiseA
    (mkTwoCallrefOneRefCode bodyPush7)
]

def suite : InstrSuite where
  id := callrefId
  unit := #[
    { name := "unit/raw/call-side-effects-and-return-cont"
      run := do
        let st ← expectRawOk "raw/call-side-effects"
          (runCallrefRaw bodyPush7 noiseA)
        if st.stack != noiseA then
          throw (IO.userError s!"raw/call-side-effects: expected stack {reprStr noiseA}, got {reprStr st.stack}")
        match st.cc with
        | .ordinary code saved cregs cdata =>
            if code != Slice.ofCell bodyPush7 then
              throw (IO.userError s!"raw/call-side-effects: unexpected cc code {reprStr code}")
            if saved != .quit 0 then
              throw (IO.userError s!"raw/call-side-effects: expected saved c0 quit0, got {reprStr saved}")
            if cregs.c0.isSome || cregs.c1.isSome || cregs.c2.isSome || cregs.c3.isSome ||
               cregs.c4.isSome || cregs.c5.isSome || cregs.c7.isSome then
              throw (IO.userError s!"raw/call-side-effects: expected empty callee cregs, got {reprStr cregs}")
            if !cdata.stack.isEmpty || cdata.nargs != -1 then
              throw (IO.userError s!"raw/call-side-effects: expected empty callee cdata, got {reprStr cdata}")
        | other =>
            throw (IO.userError s!"raw/call-side-effects: expected ordinary callee, got {reprStr other}")
        match st.regs.c0 with
        | .ordinary retCode _ retCregs retCdata =>
            if retCode != Slice.ofCell Cell.empty then
              throw (IO.userError s!"raw/call-side-effects: unexpected return code {reprStr retCode}")
            match retCregs.c0 with
            | some (.quit 0) => pure ()
            | _ =>
                throw (IO.userError
                  s!"raw/call-side-effects: expected captured old c0=quit0, got {reprStr retCregs.c0}")
            if !retCdata.stack.isEmpty || retCdata.nargs != -1 then
              throw (IO.userError s!"raw/call-side-effects: unexpected return cdata {reprStr retCdata}")
        | other =>
            throw (IO.userError s!"raw/call-side-effects: expected ordinary return c0, got {reprStr other}")
        let expectedHash := Cell.hashBytes bodyPush7
        if st.loadedCells != #[expectedHash] then
          throw (IO.userError s!"raw/call-side-effects: unexpected loaded cells {reprStr st.loadedCells}")
        if st.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError
            s!"raw/call-side-effects: expected gas={cellLoadGasPrice}, got {st.gas.gasConsumed}") }
    ,
    { name := "unit/raw/reload-gas-path"
      run := do
        let h := Cell.hashBytes bodyPush7
        let st ← expectRawOk "raw/reload"
          (runCallrefRaw bodyPush7 #[] (loaded := #[h]))
        if st.loadedCells != #[h] then
          throw (IO.userError s!"raw/reload: expected loaded set unchanged, got {reprStr st.loadedCells}")
        if st.gas.gasConsumed != cellReloadGasPrice then
          throw (IO.userError
            s!"raw/reload: expected gas={cellReloadGasPrice}, got {st.gas.gasConsumed}") }
    ,
    { name := "unit/raw/special-rejection-after-load"
      run := do
        let ccInit : Continuation := .quit 71
        let st ← expectRawErr "raw/special"
          (runCallrefRaw specialTargetCell noiseB (cc := ccInit))
          .cellUnd
        if st.stack != noiseB then
          throw (IO.userError s!"raw/special: stack changed {reprStr st.stack}")
        if st.cc != ccInit then
          throw (IO.userError s!"raw/special: cc changed {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"raw/special: c0 changed {reprStr st.regs.c0}")
        if st.loadedCells != #[Cell.hashBytes specialTargetCell] then
          throw (IO.userError s!"raw/special: expected loaded special hash, got {reprStr st.loadedCells}")
        if st.gas.gasConsumed != cellLoadGasPrice then
          throw (IO.userError s!"raw/special: expected gas={cellLoadGasPrice}, got {st.gas.gasConsumed}") }
    ,
    { name := "unit/raw/oog-preempts-special-rejection"
      run := do
        let ccInit : Continuation := .quit 99
        let tight : GasLimits := GasLimits.ofLimits (cellLoadGasPrice - 1) (cellLoadGasPrice - 1) 0
        let st ← expectRawErr "raw/oog-special"
          (runCallrefRaw specialTargetCell noiseA (cc := ccInit) (gas := tight))
          .outOfGas
        if st.stack != noiseA then
          throw (IO.userError s!"raw/oog-special: stack changed {reprStr st.stack}")
        if st.cc != ccInit then
          throw (IO.userError s!"raw/oog-special: cc changed {reprStr st.cc}")
        if st.loadedCells != #[Cell.hashBytes specialTargetCell] then
          throw (IO.userError s!"raw/oog-special: expected loaded special hash, got {reprStr st.loadedCells}") }
    ,
    { name := "unit/dispatch-decode-and-asm-gates"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runCallrefDispatchFallback .add noiseA)
          (noiseA ++ #[intV dispatchSentinel])
        expectOkStack "dispatch/match-callref-no-next"
          (runCallrefDispatchFallback (callrefInstr bodyEmpty) #[])
          #[]

        let seqBits : BitString :=
          natToBits callrefOpcode 16 ++
          natToBits jmprefOpcode 16 ++
          natToBits 0xa0 8
        let seqCode : Cell := Cell.mkOrdinary seqBits #[bodyEmpty, bodyPush7]
        let s0 := Slice.ofCell seqCode
        let s1 ← expectDecodeStep "decode/callref" s0 (callrefInstr bodyEmpty) 16
        let s2 ← expectDecodeStep "decode/jmpref" s1 (.jmpRef (Slice.ofCell bodyPush7)) 16
        let s3 ← expectDecodeStep "decode/add-tail" s2 .add 8
        if s3.bitsRemaining = 0 && s3.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/sequence-end: expected exhausted slice, got bits={s3.bitsRemaining} refs={s3.refsRemaining}")

        expectDecodeErr "decode/missing-ref" missingRefCode .invOpcode
        expectDecodeErr "decode/truncated-15" truncated15Code .invOpcode
        expectDecodeErr "decode/one-byte-prefix" oneBytePrefixCode .invOpcode

        match assembleCp0 [callrefInstr bodyPush7] with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"asm/callref: expected invOpcode, got {e}")
        | .ok c =>
            throw (IO.userError s!"asm/callref: expected invOpcode, got assembled code {reprStr c}") }
    ,
    { name := "unit/full-run/call-return-and-error-gating"
      run := do
        let okCode := mkCallrefCode bodyPush7 #[.pushInt (.num 9), .add]
        let stOk ← expectExit "full/ok" (~~~ 0) (runCallrefLean okCode #[intV 2])
        if stOk.stack != #[intV 2, intV 16] then
          throw (IO.userError s!"full/ok: expected stack #[2,16], got {reprStr stOk.stack}")
        expectTopIntNum "full/ok/top" 16 stOk

        let _ ← expectExit "full/decode-missing-ref-before-tail"
          (~~~ Excno.invOpcode.toInt)
          (runCallrefLean missingRefWithTailCode #[intV 1])

        let specialCode := mkCallrefCode specialTargetCell #[.pushInt (.num 9)]
        let _ ← expectExit "full/special-cell-und"
          (~~~ Excno.cellUnd.toInt)
          (runCallrefLean specialCode #[]) }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.CALLREF
