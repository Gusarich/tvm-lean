import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CALLCC

/-!
CALLCC branch mapping (Lean vs C++):
- Lean:
  - `TvmLean/Semantics/Exec/Flow/Callcc.lean` (`.callcc` branch)
  - `TvmLean/Semantics/Exec/Common.lean` (`VM.extractCc`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.jump`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xdb34` decode)
- C++:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_callcc`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::extract_cc`, `VmState::jump`)

Covered branch families:
- decode: exact `0xdb34` vs truncated/invalid prefixes;
- dispatch: `.callcc` handler match vs fallback `next`;
- runtime order: underflow/type at `pop_cont`, then `extract_cc(3)`, push old `cc`, jump;
- extraction effects: save/reset `{c0,c1}` and preserve `c2`;
- jump-time behavior inherited from full `VM.jump` (nargs checks, captured-stack merge);
- gas-visible paths where oracle can observe them (ref load and closure-stack plumbing).
-/

private def callccId : InstrId := { name := "CALLCC" }
private def callccOpcode : Nat := 0xdb34
private def pushRefContOpcode : Nat := 0x8a
private def dispatchSentinel : Int := 45045

private def q0 : Value := .cont (.quit 0)

private def markerCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0x2b 6) #[]

private def ccOrdMarked : Continuation :=
  .ordinary (Slice.ofCell markerCodeCell) (.quit 0) OrdCregs.empty OrdCdata.empty

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x15 5) #[refLeafA]

private def sliceNoiseA : Slice := Slice.ofCell refLeafA

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refLeafB, .builder Builder.empty, .tuple #[]]

private def noiseB : Array Value :=
  #[.slice sliceNoiseA, intV (-9)]

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

private def bodyDrop : Cell :=
  assembleNoRefCell! "callcc/body/drop" #[.pop 0]

private def bodyAdd : Cell :=
  assembleNoRefCell! "callcc/body/add" #[.add]

private def bodyDropAdd : Cell :=
  assembleNoRefCell! "callcc/body/drop-add" #[.pop 0, .add]

private def bodyPush7 : Cell :=
  assembleNoRefCell! "callcc/body/push7" #[.pushInt (.num 7)]

private def bodyDropPush7 : Cell :=
  assembleNoRefCell! "callcc/body/drop-push7" #[.pop 0, .pushInt (.num 7)]

private def bodyRet : Cell :=
  assembleNoRefCell! "callcc/body/ret" #[.ret]

private def bodyRetAlt : Cell :=
  assembleNoRefCell! "callcc/body/retalt" #[.retAlt]

private def bodyResumeOldCc : Cell :=
  assembleNoRefCell! "callcc/body/resume-oldcc" #[.jmpx]

private def bodyImplicitJmpRef : Cell :=
  Cell.mkOrdinary #[] #[bodyPush7]

private def specialTargetCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def mkCallccCode (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "callcc/code/tail" tail
  Cell.mkOrdinary
    (natToBits callccOpcode 16 ++ tailCell.bits)
    tailCell.refs

private def mkPrefixedCallccCode
    (pre : Array Instr)
    (tail : Array Instr := #[]) : Cell :=
  let preCell := assembleNoRefCell! "callcc/code/pre" pre
  let tailCell := assembleNoRefCell! "callcc/code/pre-tail" tail
  Cell.mkOrdinary
    (preCell.bits ++ natToBits callccOpcode 16 ++ tailCell.bits)
    (preCell.refs ++ tailCell.refs)

private def mkPushRefContCallccCode
    (target : Cell)
    (pre : Array Instr := #[])
    (mid : Array Instr := #[])
    (tail : Array Instr := #[]) : Cell :=
  let preCell := assembleNoRefCell! "callcc/code/ref-pre" pre
  let midCell := assembleNoRefCell! "callcc/code/ref-mid" mid
  let tailCell := assembleNoRefCell! "callcc/code/ref-tail" tail
  Cell.mkOrdinary
    (preCell.bits
      ++ natToBits pushRefContOpcode 8
      ++ midCell.bits
      ++ natToBits callccOpcode 16
      ++ tailCell.bits)
    (preCell.refs ++ #[target] ++ midCell.refs ++ tailCell.refs)

private def mkTwoPushRefContCallccCode
    (targetA targetB : Cell)
    (tail : Array Instr := #[]) : Cell :=
  let tailCell := assembleNoRefCell! "callcc/code/two-tail" tail
  Cell.mkOrdinary
    (natToBits pushRefContOpcode 8
      ++ natToBits callccOpcode 16
      ++ natToBits pushRefContOpcode 8
      ++ natToBits callccOpcode 16
      ++ tailCell.bits)
    (#[targetA, targetB] ++ tailCell.refs)

private def missingContRefCode : Cell :=
  Cell.mkOrdinary
    (natToBits pushRefContOpcode 8 ++ natToBits callccOpcode 16)
    #[]

private def missingContRefWithTailCode : Cell :=
  Cell.mkOrdinary
    (natToBits pushRefContOpcode 8
      ++ natToBits callccOpcode 16
      ++ assembleNoRefBits! "callcc/code/missing-ref-tail" #[.pushInt (.num 9)])
    #[]

private def truncatedCallcc15Code : Cell :=
  Cell.mkOrdinary ((natToBits callccOpcode 16).take 15) #[]

private def oneByteDbCode : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def pushRefThenTruncatedCallccCode (target : Cell) : Cell :=
  Cell.mkOrdinary
    (natToBits pushRefContOpcode 8 ++ (natToBits callccOpcode 16).take 15)
    #[target]

private def runCallccDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowCallcc .callcc stack

private def runCallccDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallcc instr (VM.push (intV dispatchSentinel)) stack

private def runCallccRaw
    (stack : Array Value)
    (cc : Continuation := ccOrdMarked)
    (regs : Regs := (VmState.initial Cell.empty).regs) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := regs }
  (execInstrFlowCallcc .callcc (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  match out with
  | (.ok _, st) => pure st
  | (.error e, _) =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  match out with
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

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callccId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def mkProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callccId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCallccCase
    (name : String)
    (stack : Array Value)
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkCallccCode tail) fuel

private def mkPrefixedCallccCase
    (name : String)
    (stack : Array Value)
    (pre : Array Instr)
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkPrefixedCallccCode pre tail) fuel

private def mkPushRefContCallccCase
    (name : String)
    (stack : Array Value)
    (target : Cell)
    (pre : Array Instr := #[])
    (mid : Array Instr := #[])
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkPushRefContCallccCode target pre mid tail) fuel

private def mkSetContArgsCallccCase
    (name : String)
    (stack : Array Value)
    (target : Cell)
    (copy : Nat)
    (more : Int)
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkPushRefContCallccCase name stack target #[] #[.setContArgs copy more] tail fuel

private def mkTwoPushRefContCallccCase
    (name : String)
    (stack : Array Value)
    (targetA targetB : Cell)
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkTwoPushRefContCallccCode targetA targetB tail) fuel

private def callccFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/direct/program/",
      "err/direct/program/",
      "ok/ref/",
      "err/ref/",
      "ok/setcontargs/",
      "err/setcontargs/",
      "err/decode/",
      "ok/dispatch/"
    ]
    mutationModes := #[
      0, 0, 0,
      1, 1, 1,
      2, 2,
      3, 3,
      4
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def callccNoisePool : Array (Array Value) :=
  #[#[], noiseA, noiseB, noiseA ++ noiseB]

private def callccTargetPool : Array Cell :=
  #[bodyEmpty, bodyDrop, bodyAdd, bodyPush7, bodyImplicitJmpRef]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genCallccFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (noise, rng2) := pickFromPool callccNoisePool rng1
  let (target, rng3) := pickFromPool callccTargetPool rng2
  let case0 :=
    if shape = 0 then
      mkProgramCase "fuzz/ok/direct" (noise ++ #[q0]) #[.callcc]
    else if shape = 1 then
      mkProgramCase "fuzz/err/underflow/empty" #[] #[.callcc]
    else if shape = 2 then
      mkProgramCase "fuzz/err/type/top-int" #[intV 1] #[.callcc]
    else if shape = 3 then
      mkProgramCase "fuzz/err/type/top-null" #[.null] #[.callcc]
    else if shape = 4 then
      mkPushRefContCallccCase "fuzz/ok/ref/basic" noise target
    else if shape = 5 then
      mkPushRefContCallccCase "fuzz/err/ref/special-target" noise specialTargetCell
    else if shape = 6 then
      mkSetContArgsCallccCase "fuzz/ok/setcontargs/nargs1" #[] bodyDrop 0 1
    else if shape = 7 then
      mkSetContArgsCallccCase "fuzz/err/setcontargs/underflow" #[] bodyEmpty 0 2
    else if shape = 8 then
      mkCase "fuzz/err/decode/missing-ref" #[] missingContRefCode
    else if shape = 9 then
      mkCase "fuzz/err/decode/truncated15" #[] truncatedCallcc15Code
    else
      mkProgramCase "fuzz/ok/dispatch/no-callcc" #[] #[.ret]
  let (tag, rng4) := randNat rng3 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

private def oracleCases : Array OracleCase := #[
  -- Direct CALLCC from assembled program.
  mkProgramCase "ok/direct/program/basic-empty-below" #[q0] #[.callcc],
  mkProgramCase "ok/direct/program/basic-int-below" #[intV 7, q0] #[.callcc],
  mkProgramCase "ok/direct/program/basic-mixed-below" (noiseA ++ noiseB ++ #[q0]) #[.callcc],
  mkProgramCase "ok/direct/program/max-int257-below" #[intV maxInt257, q0] #[.callcc],
  mkProgramCase "ok/direct/program/min-int257-below" #[intV minInt257, q0] #[.callcc],
  mkProgramCase "ok/direct/program/prelude-push-before-callcc" #[q0] #[.pushInt (.num 3), .callcc],
  mkProgramCase "ok/direct/program/tail-after-callcc-not-reached" #[q0] #[.callcc, .pushInt (.num 9), .add],
  mkProgramCase "ok/direct/program/double-callcc-first-jumps-away" #[q0, q0] #[.callcc, .callcc],

  mkProgramCase "err/direct/program/underflow-empty" #[] #[.callcc],
  mkProgramCase "err/direct/program/type-top-int" #[intV 1] #[.callcc],
  mkProgramCase "err/direct/program/type-top-null" #[.null] #[.callcc],
  mkProgramCase "err/direct/program/type-top-cell" #[.cell refLeafA] #[.callcc],
  mkProgramCase "err/direct/program/type-top-slice" #[.slice sliceNoiseA] #[.callcc],
  mkProgramCase "err/direct/program/type-top-builder" #[.builder Builder.empty] #[.callcc],
  mkProgramCase "err/direct/program/type-top-empty-tuple" #[.tuple #[]] #[.callcc],
  mkProgramCase "err/direct/program/top-type-before-below-cont" #[q0, intV 1] #[.callcc],
  mkProgramCase "err/direct/program/top-type-before-below-cont-deep" (noiseA ++ #[q0, .null]) #[.callcc],

  -- PUSHREFCONT + CALLCC paths (decode with refs + CALLCC transfer).
  mkPushRefContCallccCase "ok/ref/basic-empty-stack-target-empty" #[] bodyEmpty,
  mkPushRefContCallccCase "ok/ref/basic-int-stack-target-empty" #[intV 4] bodyEmpty,
  mkPushRefContCallccCase "ok/ref/arg-passing/drop-oldcc" #[intV 9] bodyDrop,
  mkPushRefContCallccCase "ok/ref/arg-passing/drop-oldcc-add" #[intV 2, intV 3] bodyDropAdd,
  mkPushRefContCallccCase "err/ref/arg-passing/add-without-drop" #[intV 2, intV 3] bodyAdd,
  mkPushRefContCallccCase "ok/ref/arg-passing/drop-oldcc-push7" #[intV 5] bodyDropPush7,
  mkPushRefContCallccCase "ok/ref/target-ret-uses-reset-c0" #[intV 11] bodyRet,
  mkPushRefContCallccCase "ok/ref/target-retalt-uses-reset-c1" #[intV 12] bodyRetAlt,
  mkPushRefContCallccCase "ok/ref/target-implicit-jmpref" #[] bodyImplicitJmpRef,
  mkPushRefContCallccCase
    "ok/ref/resume-oldcc-via-jmpx-tail"
    #[]
    bodyResumeOldCc
    #[] #[] #[.pushInt (.num 9)],
  mkPushRefContCallccCase
    "ok/ref/resume-oldcc-via-jmpx-tail-add"
    #[intV 2]
    bodyResumeOldCc
    #[] #[] #[.pushInt (.num 9), .add],
  mkPushRefContCallccCase "err/ref/special-target-cellund" #[intV 5] specialTargetCell,
  mkCase "err/ref/decode-missing-target-ref" #[] missingContRefCode,
  mkCase "err/ref/decode-missing-target-ref-with-tail" #[intV 9] missingContRefWithTailCode,
  mkCase "err/ref/decode-pushref-then-truncated-callcc" #[] (pushRefThenTruncatedCallccCode bodyEmpty),
  mkTwoPushRefContCallccCase
    "ok/ref/two-sequences-first-jumps-away"
    #[]
    bodyDrop
    bodyPush7
    #[.pushInt (.num 1)],

  -- CALLCC must delegate to full `jump` behavior.
  mkSetContArgsCallccCase "ok/setcontargs/nargs1-satisfied-by-oldcc" #[] bodyDrop 0 1,
  mkSetContArgsCallccCase "err/setcontargs/nargs2-underflow" #[] bodyEmpty 0 2,
  mkSetContArgsCallccCase "ok/setcontargs/nargs2-with-extra-arg" #[intV 8] bodyDrop 0 2,
  mkSetContArgsCallccCase "err/setcontargs/copy1-underflow-before-callcc" #[] bodyEmpty 1 (-1),
  mkSetContArgsCallccCase "ok/setcontargs/copy1-more0-captured-only" #[intV 4] bodyEmpty 1 0,
  mkSetContArgsCallccCase "err/setcontargs/copy1-more2-underflow-after-cc-push" #[intV 4] bodyEmpty 1 2,

  -- Decode/dispatch-only scaffolding.
  mkCase "err/decode/truncated15-callcc" #[] truncatedCallcc15Code,
  mkCase "err/decode/one-byte-db" #[] oneByteDbCode,
  mkProgramCase "ok/dispatch/program-ret-no-callcc" #[] #[.ret],
  mkProgramCase "ok/dispatch/program-pushint-no-callcc" #[] #[.pushInt (.num 6)]
]

def suite : InstrSuite where
  id := callccId
  unit := #[
    { name := "unit/decode/callcc-then-ret"
      run := do
        let code : Cell := mkCallccCode #[.ret]
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/callcc" s0 .callcc 16
        let s2 ← expectDecodeStep "decode/ret" s1 .ret 16
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected bits=0 refs=0, got bits={s2.bitsRemaining} refs={s2.refsRemaining}") }
    ,
    { name := "unit/decode/truncated15-is-invOpcode"
      run := do
        expectDecodeErr "decode/truncated15" truncatedCallcc15Code .invOpcode }
    ,
    { name := "unit/dispatch/non-callcc-falls-through-next"
      run := do
        expectOkStack "dispatch/fallback"
          (runCallccDispatchFallback .ret #[])
          #[intV dispatchSentinel] }
    ,
    { name := "unit/raw/extract-cc-saves-c0-c1-and-resets-regs"
      run := do
        let regs0 := (VmState.initial Cell.empty).regs
        let regs : Regs := { regs0 with c0 := .quit 7, c1 := .quit 8, c2 := .quit 9 }
        let st ← expectRawOk "raw/extract-cc" (runCallccRaw #[intV 5, q0] ccOrdMarked regs)
        if st.cc != .quit 0 then
          throw (IO.userError s!"raw/extract-cc: expected cc=quit0, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"raw/extract-cc: expected c0 reset to quit0, got {reprStr st.regs.c0}")
        if st.regs.c1 != .quit 1 then
          throw (IO.userError s!"raw/extract-cc: expected c1 reset to quit1, got {reprStr st.regs.c1}")
        if st.regs.c2 != .quit 9 then
          throw (IO.userError s!"raw/extract-cc: expected c2 preserved, got {reprStr st.regs.c2}")
        match st.stack with
        | #[.int (.num 5), .cont (.ordinary code saved cregs cdata)] =>
            if code != Slice.ofCell markerCodeCell then
              throw (IO.userError s!"raw/extract-cc: expected captured code marker, got {reprStr code}")
            if saved != .quit 0 then
              throw (IO.userError s!"raw/extract-cc: expected saved=quit0, got {reprStr saved}")
            if cregs.c0 != some (.quit 7) then
              throw (IO.userError s!"raw/extract-cc: expected cregs.c0=quit7, got {reprStr cregs.c0}")
            if cregs.c1 != some (.quit 8) then
              throw (IO.userError s!"raw/extract-cc: expected cregs.c1=quit8, got {reprStr cregs.c1}")
            if cregs.c2.isSome then
              throw (IO.userError s!"raw/extract-cc: expected cregs.c2 none for saveCr=3, got {reprStr cregs.c2}")
            if !cdata.stack.isEmpty ∨ cdata.nargs != -1 then
              throw (IO.userError s!"raw/extract-cc: unexpected cdata {reprStr cdata}")
        | other =>
            throw (IO.userError s!"raw/extract-cc: unexpected stack {reprStr other}") }
    ,
    { name := "unit/raw/nonordinary-cc-typechk-after-popcont"
      run := do
        let st ← expectRawErr "raw/nonordinary-cc" (runCallccRaw #[intV 3, q0] (.quit 77)) .typeChk
        if st.stack != #[intV 3] then
          throw (IO.userError s!"raw/nonordinary-cc: expected popped cont before failure, got {reprStr st.stack}")
        if st.cc != .quit 77 then
          throw (IO.userError s!"raw/nonordinary-cc: expected cc unchanged, got {reprStr st.cc}") }
    ,
    { name := "unit/regression/callcc-uses-full-jump-nargs-check"
      run := do
        let need2 : Continuation :=
          .ordinary (Slice.ofCell bodyEmpty) (.quit 0) OrdCregs.empty { stack := #[], nargs := 2 }
        let st ← expectRawErr "raw/jump-nargs" (runCallccRaw #[.cont need2]) .stkUnd
        if st.cc != ccOrdMarked then
          throw (IO.userError s!"raw/jump-nargs: expected cc unchanged on jump error, got {reprStr st.cc}")
        if st.stack.size != 1 then
          throw (IO.userError s!"raw/jump-nargs: expected one pushed old-cc value, got {reprStr st.stack}") }
    ,
    { name := "unit/regression/callcc-uses-full-jump-captured-stack-merge"
      run := do
        let capturedCont : Continuation :=
          .ordinary (Slice.ofCell bodyEmpty) (.quit 0) OrdCregs.empty { stack := #[intV 42], nargs := 0 }
        let st ← expectRawOk "raw/jump-captured" (runCallccRaw #[intV 5, .cont capturedCont])
        if st.stack != #[intV 42] then
          throw (IO.userError s!"raw/jump-captured: expected captured-only stack, got {reprStr st.stack}")
        if st.cc != capturedCont then
          throw (IO.userError s!"raw/jump-captured: expected cc=capturedCont, got {reprStr st.cc}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr callccId
      count := 500
      gen := genCallccFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.CALLCC
