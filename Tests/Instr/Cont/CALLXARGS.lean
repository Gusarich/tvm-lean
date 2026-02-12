import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CALLXARGS

private def callxArgsId : InstrId := { name := "CALLXARGS" }
private def callxArgsOpcode : Nat := 0xda
private def dispatchSentinel : Int := 51603

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def sliceA : Slice := Slice.ofCell cellA

private def markerCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0x2b 6) #[]

private def ccOrdMarked : Continuation :=
  .ordinary (Slice.ofCell markerCodeCell) (.quit 0) OrdCregs.empty OrdCdata.empty

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def mkStack (below : Array Value) (cont : Value := q0) : Array Value :=
  below ++ #[cont]

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[])
    (c0? : Option Continuation := none)
    (code : Cell := Cell.empty) : Continuation :=
  .ordinary (Slice.ofCell code) (.quit 0) { OrdCregs.empty with c0 := c0? } { stack := captured, nargs := nargs }

private def callRetCode : Cell :=
  assembleNoRefCell! "callxargs/callee/ret" #[.ret]

private def callPush7RetCode : Cell :=
  assembleNoRefCell! "callxargs/callee/push7-ret" #[.pushInt (.num 7), .ret]

private def callPush7Push8RetCode : Cell :=
  assembleNoRefCell! "callxargs/callee/push7-push8-ret" #[.pushInt (.num 7), .pushInt (.num 8), .ret]

private def contRet : Value := .cont (mkOrdCont (code := callRetCode))
private def contPush7Ret : Value := .cont (mkOrdCont (code := callPush7RetCode))
private def contPush7Push8Ret : Value := .cont (mkOrdCont (code := callPush7Push8RetCode))

private def contHasC0 : Value :=
  .cont (mkOrdCont (c0? := some (.quit 9)))

private def rawCallxArgsCode (params : Nat) (retVals : Nat) : Cell :=
  let args8 : Nat := (params <<< 4) + retVals
  Cell.mkOrdinary (natToBits callxArgsOpcode 8 ++ natToBits args8 8) #[]

private def rawCallxArgsMinus1Code (params : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (0xdb00 + params) 16) #[]

private def callxArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits callxArgsOpcode 8) #[]

private def callxArgsTruncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits 0xda00 16).take 15) #[]

private def callxArgsOneByteDbCode : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def runDirect (params : Nat) (retVals : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowCallxArgs (.callxArgs params retVals) stack

private def runFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallxArgs instr (VM.push (intV dispatchSentinel)) stack

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
  (execInstrFlowCallxArgs (.callxArgs params retVals) (pure ())).run st0

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

private def expectDecodeCallxArgs
    (label : String)
    (code : Cell)
    (params : Nat)
    (retVals : Int)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .callxArgs params retVals then
        throw (IO.userError s!"{label}: expected .callxArgs {params},{retVals}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (params : Nat)
    (retVals : Int)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callxArgsId
    program := #[.callxArgs params retVals]
    initStack := stack
    fuel := fuel }

private def mkCaseProg
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callxArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callxArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetNumCallxArgs (nargs : Int) (params : Nat) (retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num nargs), .setNumVarArgs, .callxArgs params retVals]

private def progSetContVarCallxArgs (copy more : Int) (params : Nat) (retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num copy), .pushInt (.num more), .setContVarArgs, .callxArgs params retVals]

private def depth15 : Array Value := intStackAsc 15
private def depth16 : Array Value := intStackAsc 16

private def callxArgsFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/basic/",
      "ok/order/",
      "err/underflow/",
      "err/type/",
      "err/order/",
      "ok/call/",
      "err/call/",
      "ok/frame/",
      "ok/decode/",
      "err/decode/"
    ]
    -- Bias toward argument-shape, ordering, call-frame, and decode interaction perturbations.
    mutationModes := #[0, 0, 0, 0, 2, 2, 2, 4, 4, 1, 1, 3]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- params/retvals immediate boundaries.
  mkCase "ok/basic/p0-r0-empty" (mkStack #[]) 0 0,
  mkCase "ok/basic/p0-r15-empty" (mkStack #[]) 0 15,
  mkCase "ok/basic/p1-r0-one-arg" (mkStack #[intV 7]) 1 0,
  mkCase "ok/basic/p1-r15-two-args" (mkStack #[intV 7, intV 8]) 1 15,
  mkCase "ok/basic/p2-r0-two-args" (mkStack #[intV 1, intV 2]) 2 0,
  mkCase "ok/basic/p2-r15-three-args" (mkStack #[intV 1, intV 2, intV 3]) 2 15,
  mkCase "ok/basic/p3-r0-three-args" (mkStack #[intV 1, intV 2, intV 3]) 3 0,
  mkCase "ok/basic/p3-r15-four-args" (mkStack #[intV 1, intV 2, intV 3, intV 4]) 3 15,
  mkCase "ok/basic/p15-r0-exact-depth" (mkStack depth15) 15 0,
  mkCase "ok/basic/p15-r15-depth15" (mkStack depth15) 15 15,
  mkCase "ok/basic/p15-r15-depth16-drop-bottom" (mkStack depth16) 15 15,
  mkCase "ok/basic/p2-r7-mixed" (mkStack #[.null, .cell cellA, .builder Builder.empty]) 2 7,

  -- Ordering around control transfer and argument slicing.
  mkCaseProg "ok/order/tail-skipped-push" (mkStack #[]) #[.callxArgs 0 0, .pushInt (.num 999)],
  mkCaseProg "ok/order/tail-skipped-add-underflow" (mkStack #[]) #[.callxArgs 0 0, .add],
  mkCase "ok/order/p1-preserves-top-order" (mkStack #[intV 1, intV 2, intV 3]) 1 0,
  mkCase "ok/order/p2-preserves-top-order" (mkStack #[intV 1, intV 2, intV 3, intV 4]) 2 0,
  mkCase "ok/order/p2-r15-preserves-top-order" (mkStack #[intV 1, intV 2, intV 3, intV 4]) 2 15,

  -- Underflow/type and error-precedence probes.
  mkCase "err/underflow/empty-stack" #[] 0 0,
  mkCase "err/underflow/p1-only-cont" (mkStack #[]) 1 0,
  mkCase "err/underflow/p2-one-arg" (mkStack #[intV 7]) 2 0,
  mkCase "err/underflow/p15-short" (mkStack #[intV 1, intV 2]) 15 0,
  mkCase "err/type/top-int" #[intV 1] 0 0,
  mkCase "err/type/top-null" #[.null] 0 0,
  mkCase "err/type/top-cell" #[.cell cellA] 0 0,
  mkCase "err/type/top-slice" #[.slice sliceA] 0 0,
  mkCase "err/type/top-builder" #[.builder Builder.empty] 0 0,
  mkCase "err/type/top-tuple" #[.tuple #[]] 0 0,
  mkCase "err/order/top-type-before-pass-underflow" #[q0, intV 1] 2 0,
  mkCase "err/order/pass-underflow-before-below-type" #[.null, q0] 2 0,
  mkCase "err/order/pass-underflow-before-below-cont-type" #[intV 1, q0] 15 0,
  mkCase "err/order/top-type-before-below-cont-deep" #[intV 3, .null, q0, intV 1] 0 0,

  -- Delegation to full `VM.call` (`nargs`, captured stack, c0->jump reduction).
  mkCaseProg "ok/call/setnum/nargs1-pass1" #[intV 9] (progSetNumCallxArgs 1 1 0),
  mkCaseProg "err/call/setnum/nargs1-pass0" #[intV 9] (progSetNumCallxArgs 1 0 0),
  mkCaseProg "ok/call/setnum/nargs2-pass2" #[intV 1, intV 2] (progSetNumCallxArgs 2 2 0),
  mkCaseProg "err/call/setnum/nargs2-pass1" #[intV 1, intV 2] (progSetNumCallxArgs 2 1 0),
  mkCaseProg "ok/call/setnum/nargs3-pass3" #[intV 1, intV 2, intV 3] (progSetNumCallxArgs 3 3 0),
  mkCaseProg "err/call/setnum/nargs3-pass2" #[intV 1, intV 2, intV 3] (progSetNumCallxArgs 3 2 0),
  mkCaseProg "ok/call/setcont/copy1-more1-pass1" #[intV 10, intV 20] (progSetContVarCallxArgs 1 1 1 0),
  mkCaseProg "err/call/setcont/copy1-more2-pass1" #[intV 10, intV 20] (progSetContVarCallxArgs 1 2 1 0),
  mkCaseProg "ok/call/setcont/copy1-more-neg1-pass0" #[intV 10] (progSetContVarCallxArgs 1 (-1) 0 0),
  mkCaseProg "ok/call/setcont/copy1-more-neg1-pass-all" #[intV 10, intV 11]
    (progSetContVarCallxArgs 1 (-1) 1 0),
  -- Oracle-harness-compatible frame variants (quit(0) continuations only).
  mkCase "ok/call/pass0-r7-baseline" (mkStack #[]) 0 7,
  mkCase "err/call/pass2-underflow-baseline" (mkStack #[intV 1]) 2 0,

  -- Additional pass/ret combinations with oracle-compatible continuation tokens.
  mkCase "ok/frame/pass0-ret0-baseline" (mkStack #[]) 0 0,
  mkCase "ok/frame/pass1-ret1-baseline" (mkStack #[intV 42]) 1 1,
  mkCase "ok/frame/pass2-ret2-baseline" (mkStack #[intV 7, intV 8]) 2 2,
  mkCase "ok/frame/pass3-ret1-baseline" (mkStack #[intV 1, intV 2, intV 3]) 3 1,
  mkCase "ok/frame/pass1-ret0-baseline" (mkStack #[intV 9]) 1 0,

  -- Decode/raw opcode coverage.
  mkCaseCode "ok/decode/raw-da-p0-r0" (mkStack #[]) (rawCallxArgsCode 0 0),
  mkCaseCode "ok/decode/raw-da-p15-r15" (mkStack depth15) (rawCallxArgsCode 15 15),
  mkCaseCode "ok/decode/raw-db0-p9-rminus1" (mkStack (intStackAsc 9)) (rawCallxArgsMinus1Code 9),
  mkCaseCode "err/decode/truncated-8-da" (mkStack #[]) callxArgsTruncated8Code,
  mkCaseCode "err/decode/truncated-15-da00" (mkStack #[intV 1]) callxArgsTruncated15Code,
  mkCaseCode "err/decode/one-byte-db" (mkStack #[]) callxArgsOneByteDbCode,
  mkCaseCode "err/decode/empty" (mkStack #[]) Cell.empty
]

def suite : InstrSuite where
  id := callxArgsId
  unit := #[
    { name := "unit/direct/dispatch-fallback"
      run :=
        expectOkStack "dispatch/fallback"
          (runFallback .ret #[])
          #[intV dispatchSentinel] }
    ,
    { name := "unit/raw/typechk-pops-top-before-error"
      run := do
        let st ← expectRawErr "raw/typechk-pop" (runRaw 0 0 #[intV 7]) .typeChk
        if st.stack != #[] then
          throw (IO.userError s!"raw/typechk-pop: expected empty stack after pop_cont, got {reprStr st.stack}") }
    ,
    { name := "unit/raw/stkUnd-after-popcont"
      run := do
        let st ← expectRawErr "raw/stkund-pop" (runRaw 1 0 #[q0]) .stkUnd
        if st.stack != #[] then
          throw (IO.userError s!"raw/stkund-pop: expected empty stack after pop_cont, got {reprStr st.stack}") }
    ,
    { name := "unit/raw/call-installs-return-frame-retargs"
      run := do
        let st ← expectRawOk "raw/install-ret" (runRaw 1 5 #[intV 9, q0])
        if st.stack != #[intV 9] then
          throw (IO.userError s!"raw/install-ret: expected stack #[9], got {reprStr st.stack}")
        if st.cc != .quit 0 then
          throw (IO.userError s!"raw/install-ret: expected cc=quit0, got {reprStr st.cc}")
        match st.regs.c0 with
        | .ordinary _ saved cregs cdata =>
            if cdata.nargs != 5 ∨ cdata.stack != #[] then
              throw (IO.userError s!"raw/install-ret: unexpected return cdata {reprStr cdata}")
            if cregs.c0 != some (.quit 0) then
              throw (IO.userError s!"raw/install-ret: expected saved old c0=quit0, got {reprStr cregs.c0}")
            if saved != .quit 0 then
              throw (IO.userError s!"raw/install-ret: expected savedC0=quit0, got {reprStr saved}")
        | other =>
            throw (IO.userError s!"raw/install-ret: expected ordinary return continuation, got {reprStr other}") }
    ,
    { name := "unit/raw/callee-c0-reduces-call-to-jump"
      run := do
        let st ← expectRawOk "raw/c0-jump" (runRaw 0 7 #[contHasC0])
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"raw/c0-jump: expected c0 unchanged, got {reprStr st.regs.c0}")
        match st.cc with
        | .ordinary _ _ cregs cdata =>
            if cregs.c0 != some (.quit 9) then
              throw (IO.userError s!"raw/c0-jump: expected callee c0 marker, got {reprStr cregs.c0}")
            if cdata.stack != #[] ∨ cdata.nargs != -1 then
              throw (IO.userError s!"raw/c0-jump: expected empty cdata after jump, got {reprStr cdata}")
        | other =>
            throw (IO.userError s!"raw/c0-jump: expected ordinary callee in cc, got {reprStr other}") }
    ,
    { name := "unit/decode/raw-da-nibble-order"
      run :=
        expectDecodeCallxArgs "decode/da-9-13" (rawCallxArgsCode 9 13) 9 13 }
    ,
    { name := "unit/decode/raw-db0-minus1"
      run :=
        expectDecodeCallxArgs "decode/db0-6" (rawCallxArgsMinus1Code 6) 6 (-1) }
    ,
    { name := "unit/decode/truncated-da-8"
      run :=
        expectDecodeErr "decode/truncated-da8" callxArgsTruncated8Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile callxArgsId callxArgsFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.CALLXARGS
