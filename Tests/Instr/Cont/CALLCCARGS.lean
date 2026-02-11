import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CALLCCARGS

private def callccArgsId : InstrId := { name := "CALLCCARGS" }
private def callccArgsOpcode : Nat := 0xdb36
private def dispatchSentinel : Int := 47219

private def q0 : Value := .cont (.quit 0)
private def cellA : Cell := Cell.ofUInt 8 0xa5
private def sliceA : Slice := Slice.ofCell cellA

private def markerCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0x2b 6) #[]

private def ccOrdMarked : Continuation :=
  .ordinary (Slice.ofCell markerCodeCell) (.quit 0) OrdCregs.empty OrdCdata.empty

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def mkStack (below : Array Value) (cont : Value := q0) : Array Value :=
  below ++ #[cont]

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def rawArgsByte (params : Nat) (retVals : Int) : Nat :=
  let lo : Nat := if retVals = -1 then 15 else retVals.toNat
  (params <<< 4) + lo

private def rawCallccArgsCode (params : Nat) (retVals : Int) : Cell :=
  Cell.mkOrdinary
    (natToBits callccArgsOpcode 16 ++ natToBits (rawArgsByte params retVals) 8)
    #[]

private def callccArgsThenRetCode : Cell :=
  assembleNoRefCell! "callccargs/code/seq" #[.callccArgs 3 (-1), .ret]

private def callccArgsTruncated16Code : Cell :=
  Cell.mkOrdinary (natToBits callccArgsOpcode 16) #[]

private def callccArgsTruncated23Code : Cell :=
  Cell.mkOrdinary ((natToBits callccArgsOpcode 16 ++ natToBits 0x5a 8).take 23) #[]

private def callccArgsOneByteDbCode : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def runDirect (params : Nat) (retVals : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowCallcc (.callccArgs params retVals) stack

private def runFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallcc instr (VM.push (intV dispatchSentinel)) stack

private def runRaw
    (params : Nat)
    (retVals : Int)
    (stack : Array Value)
    (cc : Continuation := ccOrdMarked)
    (regs : Regs := (VmState.initial Cell.empty).regs) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := regs }
  (execInstrFlowCallcc (.callccArgs params retVals) (pure ())).run st0

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

private def expectAssembleErr
    (label : String)
    (program : Array Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program.toList with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")
  | .ok c =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got code {reprStr c}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (params : Nat)
    (retVals : Int)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callccArgsId
    program := #[.callccArgs params retVals]
    initStack := stack
    fuel := fuel }

private def mkCaseProg
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callccArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callccArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetNumCallccArgs (nargs : Int) (params : Nat) (retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num nargs), .setNumVarArgs, .callccArgs params retVals]

private def progSetContVarCallccArgs (copy more : Int) (params : Nat) (retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num copy), .pushInt (.num more), .setContVarArgs, .callccArgs params retVals]

private def oracleCases : Array OracleCase := #[
  -- params/retvals boundaries.
  mkCase "ok/basic/p0-r-1-empty" (mkStack #[]) 0 (-1),
  mkCase "ok/basic/p0-r0-empty" (mkStack #[]) 0 0,
  mkCase "ok/basic/p0-r14-empty" (mkStack #[]) 0 14,
  mkCase "ok/basic/p1-r0-one-arg" (mkStack #[intV 7]) 1 0,
  mkCase "ok/basic/p1-r14-two-args" (mkStack #[intV 7, intV 8]) 1 14,
  mkCase "ok/basic/p2-r0-two-args" (mkStack #[intV 7, intV 8]) 2 0,
  mkCase "ok/basic/p2-r14-three-args" (mkStack #[intV 1, intV 2, intV 3]) 2 14,
  mkCase "ok/basic/p3-r0-three-args" (mkStack #[intV 1, intV 2, intV 3]) 3 0,
  mkCase "ok/basic/p3-r14-four-args" (mkStack #[intV 1, intV 2, intV 3, intV 4]) 3 14,
  mkCase "ok/basic/p15-r0-exact-depth" (mkStack (intStackAsc 15)) 15 0,
  mkCase "ok/basic/p15-r14-depth16-drop-bottom" (mkStack (intStackAsc 16)) 15 14,
  mkCase "ok/basic/p15-r-1-depth16" (mkStack (intStackAsc 16)) 15 (-1),

  -- Downstream behavior and jump ordering.
  mkCaseProg "ok/order/tail-skipped-push" (mkStack #[]) #[.callccArgs 0 0, .pushInt (.num 77)],
  mkCaseProg "ok/order/tail-skipped-add-underflow" (mkStack #[]) #[.callccArgs 0 0, .add],
  mkCase "ok/order/p1-preserves-top-order" (mkStack #[intV 1, intV 2, intV 3]) 1 0,
  mkCase "ok/order/p2-preserves-top-order" (mkStack #[intV 1, intV 2, intV 3, intV 4]) 2 0,
  mkCase "ok/order/p2-mixed-types" (mkStack #[.cell cellA, .slice sliceA, .builder Builder.empty]) 2 0,
  mkCase "ok/order/p0-captures-all-before-jump" (mkStack #[intV 9]) 0 (-1),

  -- Underflow, type, and error ordering.
  mkCase "err/underflow/p0-empty" #[] 0 0,
  mkCase "err/underflow/p1-only-cont" (mkStack #[]) 1 0,
  mkCase "err/underflow/p2-one-arg" (mkStack #[intV 7]) 2 0,
  mkCase "err/underflow/p15-short" (mkStack #[intV 1, intV 2]) 15 0,
  mkCase "err/type/cont-int" #[intV 1] 0 0,
  mkCase "err/type/cont-null" #[.null] 0 0,
  mkCase "err/type/cont-cell" #[.cell cellA] 0 0,
  mkCase "err/type/cont-slice" #[.slice sliceA] 0 0,
  mkCase "err/type/cont-builder" #[.builder Builder.empty] 0 0,
  mkCase "err/type/cont-tuple" #[.tuple #[]] 0 0,
  mkCase "err/type/cont-after-need-pass1" #[intV 7, intV 8] 1 0,
  mkCase "err/type/cont-after-need-pass2" #[intV 7, intV 8, intV 9] 2 0,
  mkCase "err/order/underflow-before-cont-type" #[intV 8, intV 1] 2 0,
  mkCase "err/order/top-type-before-below-cont" #[q0, intV 1] 0 0,
  mkCase "err/order/top-type-before-below-cont-deep" #[intV 3, .null, q0, intV 1] 0 0,
  mkCase "err/order/underflow-before-below-cont-type" #[q0, intV 1] 2 0,
  mkCase "err/order/need-check-before-top-type-largeparams" #[q0, intV 1, intV 2] 15 0,

  -- Delegation to full jump behavior (`nargs`, captured stack).
  mkCaseProg "ok/jump/setnum/nargs1-params0" #[] (progSetNumCallccArgs 1 0 0),
  mkCaseProg "err/jump/setnum/nargs2-params0" #[] (progSetNumCallccArgs 2 0 0),
  mkCaseProg "ok/jump/setnum/nargs2-params1" #[intV 9] (progSetNumCallccArgs 2 1 0),
  mkCaseProg "err/jump/setnum/nargs3-params1" #[intV 9] (progSetNumCallccArgs 3 1 0),
  mkCaseProg "ok/jump/setnum/nargs3-params2" #[intV 9, intV 10] (progSetNumCallccArgs 3 2 0),
  mkCaseProg "ok/jump/setcont/copy1-more1-params0" #[intV 10] (progSetContVarCallccArgs 1 1 0 0),
  mkCaseProg "err/jump/setcont/copy1-more2-params0" #[intV 10] (progSetContVarCallccArgs 1 2 0 0),
  mkCaseProg "ok/jump/setcont/copy1-more-neg1-params0" #[intV 10] (progSetContVarCallccArgs 1 (-1) 0 0),
  mkCaseProg "ok/jump/setcont/copy1-more-neg1-params1" #[intV 10, intV 11]
    (progSetContVarCallccArgs 1 (-1) 1 0),
  mkCaseProg "err/jump/setcont/copy1-more3-params1" #[intV 10, intV 11]
    (progSetContVarCallccArgs 1 3 1 0),

  -- Decode gate and raw opcode coverage.
  mkCaseCode "ok/decode/raw-p15-rminus1" (mkStack (intStackAsc 15)) (rawCallccArgsCode 15 (-1)),
  mkCaseCode "ok/decode/raw-p0-r14" (mkStack #[]) (rawCallccArgsCode 0 14),
  mkCaseCode "err/decode/truncated16-prefix" #[] callccArgsTruncated16Code,
  mkCaseCode "err/decode/truncated23-prefix" (mkStack #[]) callccArgsTruncated23Code,
  mkCaseCode "err/decode/one-byte-db" #[] callccArgsOneByteDbCode
]

def suite : InstrSuite where
  id := callccArgsId
  unit := #[
    { name := "unit/direct/dispatch-fallback"
      run :=
        expectOkStack "dispatch/fallback"
          (runFallback .ret #[])
          #[intV dispatchSentinel] }
    ,
    { name := "unit/direct/order-underflow-before-cont-type"
      run :=
        expectErr "direct/underflow-before-type"
          (runDirect 2 0 #[intV 8, intV 1])
          .stkUnd }
    ,
    { name := "unit/direct/order-cont-type-after-need-check"
      run :=
        expectErr "direct/type-after-need"
          (runDirect 2 0 #[intV 7, intV 8, intV 1])
          .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let s0 := Slice.ofCell callccArgsThenRetCode
        let s1 ← expectDecodeStep "decode/callccargs" s0 (.callccArgs 3 (-1)) 24
        let s2 ← expectDecodeStep "decode/ret" s1 .ret 16
        if s2.bitsRemaining != 0 ∨ s2.refsRemaining != 0 then
          throw (IO.userError
            s!"decode/end: expected bits=0 refs=0, got bits={s2.bitsRemaining} refs={s2.refsRemaining}")
        expectDecodeErr "decode/truncated16" callccArgsTruncated16Code .invOpcode
        expectDecodeErr "decode/truncated23" callccArgsTruncated23Code .invOpcode
        expectDecodeErr "decode/one-byte-db" callccArgsOneByteDbCode .invOpcode
        expectAssembleErr "asm/params-overflow" #[.callccArgs 16 0] .rangeChk
        expectAssembleErr "asm/retvals-overflow" #[.callccArgs 0 15] .rangeChk
        expectAssembleErr "asm/retvals-underflow" #[.callccArgs 0 (-2)] .rangeChk }
    ,
    { name := "unit/raw/extract-cc-params-captures-bottom"
      run := do
        let regs0 := (VmState.initial Cell.empty).regs
        let regs : Regs := { regs0 with c0 := .quit 7, c1 := .quit 8, c2 := .quit 9 }
        let st ← expectRawOk "raw/extract-cc" (runRaw 2 14 #[intV 5, intV 6, intV 7, q0] ccOrdMarked regs)
        if st.cc != .quit 0 then
          throw (IO.userError s!"raw/extract-cc: expected cc=quit0, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"raw/extract-cc: expected c0 reset to quit0, got {reprStr st.regs.c0}")
        if st.regs.c1 != .quit 1 then
          throw (IO.userError s!"raw/extract-cc: expected c1 reset to quit1, got {reprStr st.regs.c1}")
        if st.regs.c2 != .quit 9 then
          throw (IO.userError s!"raw/extract-cc: expected c2 preserved, got {reprStr st.regs.c2}")
        if st.stack[0]? != some (intV 6) then
          throw (IO.userError s!"raw/extract-cc: expected stack[0]=6, got {reprStr (st.stack[0]?)}")
        if st.stack[1]? != some (intV 7) then
          throw (IO.userError s!"raw/extract-cc: expected stack[1]=7, got {reprStr (st.stack[1]?)}")
        match st.stack[2]? with
        | some (Value.cont k) =>
            match k with
            | .ordinary code saved cregs cdata =>
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
                if cdata.stack != #[intV 5] ∨ cdata.nargs != 14 then
                  throw (IO.userError s!"raw/extract-cc: unexpected cdata {reprStr cdata}")
            | _ =>
                throw (IO.userError s!"raw/extract-cc: expected ordinary continuation, got {reprStr k}")
        | other =>
            throw (IO.userError s!"raw/extract-cc: expected continuation at stack[2], got {reprStr other}") }
    ,
    { name := "unit/raw/nonordinary-cc-typechk-after-popcont"
      run := do
        let st ← expectRawErr "raw/nonordinary-cc" (runRaw 0 0 #[intV 3, q0] (.quit 77)) .typeChk
        if st.stack != #[intV 3] then
          throw (IO.userError s!"raw/nonordinary-cc: expected popped cont before failure, got {reprStr st.stack}")
        if st.cc != .quit 77 then
          throw (IO.userError s!"raw/nonordinary-cc: expected cc unchanged, got {reprStr st.cc}") }
    ,
    { name := "unit/regression/callccargs-uses-full-jump-nargs-check"
      run := do
        let need2 : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := #[], nargs := 2 }
        let st ← expectRawErr "raw/jump-nargs" (runRaw 0 0 #[.cont need2]) .stkUnd
        if st.cc != ccOrdMarked then
          throw (IO.userError s!"raw/jump-nargs: expected cc unchanged on jump error, got {reprStr st.cc}")
        if st.stack.size != 1 then
          throw (IO.userError s!"raw/jump-nargs: expected one pushed old-cc value, got {reprStr st.stack}") }
    ,
    { name := "unit/regression/callccargs-uses-full-jump-captured-stack-merge"
      run := do
        let capturedCont : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := #[intV 42], nargs := 0 }
        let st ← expectRawOk "raw/jump-captured" (runRaw 0 0 #[.cont capturedCont])
        if st.stack != #[intV 42] then
          throw (IO.userError s!"raw/jump-captured: expected captured-only stack, got {reprStr st.stack}") }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.CALLCCARGS
