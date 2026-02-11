import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CALLXARGS_1

private def callxArgs1Id : InstrId := { name := "CALLXARGS_1" }

private def callxArgs1Instr (params : Nat) : Instr := .callxArgs params (-1)

private def dispatchSentinel : Int := 73195

private def q0 : Value := .cont (.quit 0)

private def initialRegs : Regs := (VmState.initial Cell.empty).regs
private def initialCc : Continuation := (VmState.initial Cell.empty).cc

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def callxArgs1Code0 : Cell :=
  Cell.mkOrdinary (natToBits 0xdb00 16) #[]

private def callxArgs1Code7 : Cell :=
  Cell.mkOrdinary (natToBits 0xdb07 16) #[]

private def callxArgs1Code15 : Cell :=
  Cell.mkOrdinary (natToBits 0xdb0f 16) #[]

private def callxArgsArgs15Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdaff 16) #[]

private def callxArgs1Truncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def callxArgs1Truncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xdb00 >>> 1) 15) #[]

private def emptyCode : Cell :=
  Cell.empty

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
    (c0Opt : Option Continuation := none) : Continuation :=
  let cregs : OrdCregs := { OrdCregs.empty with c0 := c0Opt }
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) cregs { stack := captured, nargs := nargs }

private def runCallxArgs1Direct (params : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowCallxArgs (callxArgs1Instr params) stack

private def runCallxArgs1DispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallxArgs instr (VM.push (intV dispatchSentinel)) stack

private def runCallxArgs1Raw
    (params : Nat)
    (stack : Array Value)
    (cc : Continuation := initialCc)
    (regs : Regs := initialRegs) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc, regs := regs }
  (execInstrFlowCallxArgs (callxArgs1Instr params) (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

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
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectDecodeCallxArgs
    (label : String)
    (code : Cell)
    (expectedParams : Nat)
    (expectedRetVals : Int)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .callxArgs expectedParams expectedRetVals then
        throw (IO.userError
          s!"{label}: expected .callxArgs {expectedParams} {expectedRetVals}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits={expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

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
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callxArgs1Id
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
    instr := callxArgs1Id
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCallCase
    (name : String)
    (params : Nat)
    (below : Array Value)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name (mkStack below) (#[callxArgs1Instr params] ++ tail) gasLimits fuel

private def progSetNumCallxArgs
    (nargs : Int)
    (params : Nat)
    (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num nargs), .setNumVarArgs, callxArgs1Instr params] ++ tail

private def progSetContArgsCallxArgs
    (copy : Nat)
    (more : Int)
    (params : Nat)
    (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .setContArgs copy more, callxArgs1Instr params] ++ tail

private def depth15 : Array Value := intStackAsc 15
private def depth16 : Array Value := intStackAsc 16

private def oracleCases : Array OracleCase := #[
  -- Pass-arg shaping for CALLXARGS p,-1.
  mkCallCase "ok/pass0/empty" 0 #[],
  mkCallCase "ok/pass0/drop-one" 0 #[intV 7],
  mkCallCase "ok/pass0/drop-mixed" 0 #[.null, .cell cellA, .slice sliceA],
  mkCallCase "ok/pass1/exact-one" 1 #[intV 7],
  mkCallCase "ok/pass1/keep-top-of-two" 1 #[intV 7, intV 8],
  mkCallCase "ok/pass2/exact-two" 2 #[intV 7, intV 8],
  mkCallCase "ok/pass2/drop-bottom-of-three" 2 #[intV 7, intV 8, intV 9],
  mkCallCase "ok/pass3/keep-top-three-mixed" 3 #[intV 1, .null, .cell cellA, .slice sliceA],
  mkCallCase "ok/pass15/exact-depth" 15 depth15,
  mkCallCase "ok/pass15/drop-bottom" 15 depth16,

  -- CALLXARGS transfers control immediately; tail must be skipped.
  mkCallCase "order/tail-skipped/push" 0 #[] #[.pushInt (.num 777)],
  mkCallCase "order/tail-skipped/add-underflow" 0 #[] #[.add],
  mkCase "order/prelude/push-swap-callxargs1"
    #[q0]
    #[.pushInt (.num 9), .xchg0 1, callxArgs1Instr 1, .add],
  mkCase "order/prelude/push-push-callxargs2"
    #[q0]
    #[.pushInt (.num 4), .pushInt (.num 5), .xchg0 1, .xchg0 1, callxArgs1Instr 2, .add],
  mkCase "order/prelude/deep-and-tail"
    #[intV 5, q0]
    #[.pushInt (.num 7), .xchg0 1, callxArgs1Instr 1, .pushInt (.num 55)],

  -- Underflow/type ordering around pop_cont then call(passArgs,...).
  mkCase "err/underflow/empty-stack" #[] #[callxArgs1Instr 0],
  mkCase "err/type/top-int" #[intV 1] #[callxArgs1Instr 1],
  mkCase "err/type/top-null" #[.null] #[callxArgs1Instr 1],
  mkCase "err/type/top-cell" #[.cell cellA] #[callxArgs1Instr 1],
  mkCase "err/type/top-slice" #[.slice sliceB] #[callxArgs1Instr 1],
  mkCase "err/type/top-builder" #[.builder Builder.empty] #[callxArgs1Instr 1],
  mkCase "err/type/top-tuple" #[.tuple #[]] #[callxArgs1Instr 1],
  mkCase "err/underflow/pass1-after-pop" #[q0] #[callxArgs1Instr 1],
  mkCase "err/underflow/pass2-after-pop" #[intV 1, q0] #[callxArgs1Instr 2],
  mkCase "err/order/type-before-pass-underflow" #[q0, intV 1] #[callxArgs1Instr 2],
  mkCase "err/order/pass-underflow-before-below-type" #[.null, q0] #[callxArgs1Instr 2],
  mkCase "err/order/pass-underflow-before-deeper-type" #[intV 1, .tuple #[], q0] #[callxArgs1Instr 3],
  mkCase "err/order/type-before-deep-underflow" #[intV 1, q0, intV 2] #[callxArgs1Instr 3],

  -- Delegation to shared VM.call behavior (`nargs`, captured stack).
  mkCase "ok/nargs1/pass1" #[intV 7] (progSetNumCallxArgs 1 1),
  mkCase "ok/nargs0/pass0" #[] (progSetNumCallxArgs 0 0),
  mkCase "err/nargs1/pass0" #[] (progSetNumCallxArgs 1 0),
  mkCase "err/nargs2/pass1" #[intV 1, intV 2] (progSetNumCallxArgs 2 1),
  mkCase "ok/nargs2/pass2" #[intV 1, intV 2] (progSetNumCallxArgs 2 2),
  mkCase "err/nargs255/pass15-depth14" (intStackAsc 14) (progSetNumCallxArgs 255 15),
  mkCase "err/nargs255/pass15-depth15" depth15 (progSetNumCallxArgs 255 15),
  mkCase "order/nargs1/tail-skipped" #[intV 8] (progSetNumCallxArgs 1 1 #[.pushInt (.num 999)]),

  mkCase "ok/captured/copy2-pass1"
    #[intV 1, intV 2, intV 3]
    (progSetContArgsCallxArgs 2 (-1) 1),
  mkCase "err/captured/copy2-pass1-underflow"
    #[intV 1, intV 2]
    (progSetContArgsCallxArgs 2 (-1) 1),
  mkCase "ok/captured/copy2-more1-pass3"
    #[intV 1, intV 2, intV 3, intV 4, intV 5]
    (progSetContArgsCallxArgs 2 1 3),
  mkCase "err/captured/copy2-more2-pass1"
    #[intV 1, intV 2, intV 3]
    (progSetContArgsCallxArgs 2 2 1),
  mkCase "order/captured/tail-skipped"
    #[intV 1, intV 2, intV 3]
    (progSetContArgsCallxArgs 2 (-1) 1 #[.pushInt (.num 1001)]),

  -- Raw opcode/decode boundaries for 0xdb0 + 4-bit params.
  mkCodeCase "ok/decode/raw-param0" #[q0] callxArgs1Code0,
  mkCodeCase "ok/decode/raw-param7" (intStackAsc 7 ++ #[q0]) callxArgs1Code7,
  mkCodeCase "ok/decode/raw-param15" (depth15 ++ #[q0]) callxArgs1Code15,
  mkCodeCase "err/decode/truncated-8" #[q0] callxArgs1Truncated8Code,
  mkCodeCase "err/decode/truncated-15" #[intV 1, q0] callxArgs1Truncated15Code,
  mkCodeCase "err/decode/empty" #[q0] emptyCode
]

def suite : InstrSuite where
  id := callxArgs1Id
  unit := #[
    { name := "unit/dispatch/callxargs1-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runCallxArgs1DispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-callxargs1"
          (runCallxArgs1DispatchFallback (callxArgs1Instr 0) #[q0])
          #[] }
    ,
    { name := "unit/direct/pop-order-and-pass-underflow"
      run := do
        expectErr "underflow/empty"
          (runCallxArgs1Direct 0 #[])
          .stkUnd
        expectErr "type/top-int-before-pass-check"
          (runCallxArgs1Direct 2 #[intV 1])
          .typeChk
        expectErr "underflow/pass1-after-pop"
          (runCallxArgs1Direct 1 #[q0])
          .stkUnd
        expectErr "order/type-before-underflow"
          (runCallxArgs1Direct 2 #[q0, intV 1])
          .typeChk
        expectErr "order/underflow-before-below-type"
          (runCallxArgs1Direct 2 #[.null, q0])
          .stkUnd }
    ,
    { name := "unit/raw/retvals-minus1-installs-return-frame"
      run := do
        let st ← expectRawOk "raw/retvals-minus1" (runCallxArgs1Raw 1 #[intV 1, intV 2, q0])
        if st.stack != #[intV 2] then
          throw (IO.userError s!"raw/retvals-minus1: expected stack #[2], got {reprStr st.stack}")
        if st.cc != .quit 0 then
          throw (IO.userError s!"raw/retvals-minus1: expected cc=quit0, got {reprStr st.cc}")
        match st.regs.c0 with
        | .ordinary _ _ cregs cdata =>
            if cdata.nargs != -1 then
              throw (IO.userError s!"raw/retvals-minus1: expected c0.nargs=-1, got {cdata.nargs}")
            if cdata.stack != #[intV 1] then
              throw (IO.userError
                s!"raw/retvals-minus1: expected saved stack #[1], got {reprStr cdata.stack}")
            if cregs.c0 != some (.quit 0) then
              throw (IO.userError
                s!"raw/retvals-minus1: expected return-save c0=quit0, got {reprStr cregs.c0}")
        | other =>
            throw (IO.userError s!"raw/retvals-minus1: expected ordinary c0, got {reprStr other}") }
    ,
    { name := "unit/raw/delegates-to-jump-when-c0-predefined"
      run := do
        let delegated : Continuation := mkOrdCont 1 #[intV 42] (some (.quit 9))
        let st ← expectRawOk "raw/delegate-jump" (runCallxArgs1Raw 1 #[intV 7, .cont delegated])
        if st.stack != #[intV 42, intV 7] then
          throw (IO.userError s!"raw/delegate-jump: expected #[42,7], got {reprStr st.stack}")
        if st.regs.c0 != initialRegs.c0 then
          throw (IO.userError
            s!"raw/delegate-jump: expected c0 unchanged ({reprStr initialRegs.c0}), got {reprStr st.regs.c0}")
        match st.cc with
        | .ordinary _ _ cregs cdata =>
            if cregs.c0 != some (.quit 9) then
              throw (IO.userError
                s!"raw/delegate-jump: expected delegated c0 marker quit9, got {reprStr cregs.c0}")
            if cdata.stack != #[] ∨ cdata.nargs != -1 then
              throw (IO.userError
                s!"raw/delegate-jump: expected cdata consumed, got {reprStr cdata}")
        | other =>
            throw (IO.userError s!"raw/delegate-jump: expected ordinary cc, got {reprStr other}") }
    ,
    { name := "unit/raw/pop-before-call-error-keeps-rest-state"
      run := do
        let need2 : Continuation := mkOrdCont 2 #[]
        let cc0 : Continuation := .quit 99
        let st ← expectRawErr "raw/nargs>pass"
          (runCallxArgs1Raw 1 #[intV 1, intV 2, .cont need2] cc0)
          .stkUnd
        if st.stack != #[intV 1, intV 2] then
          throw (IO.userError s!"raw/nargs>pass: stack changed unexpectedly: {reprStr st.stack}")
        if st.cc != cc0 then
          throw (IO.userError s!"raw/nargs>pass: cc changed unexpectedly: {reprStr st.cc}")
        if st.regs.c0 != initialRegs.c0 then
          throw (IO.userError s!"raw/nargs>pass: c0 changed unexpectedly: {reprStr st.regs.c0}") }
    ,
    { name := "unit/decode/db0-plus-params-and-boundaries"
      run := do
        expectDecodeCallxArgs "decode/raw-param0" callxArgs1Code0 0 (-1)
        expectDecodeCallxArgs "decode/raw-param7" callxArgs1Code7 7 (-1)
        expectDecodeCallxArgs "decode/raw-param15" callxArgs1Code15 15 (-1)
        expectDecodeCallxArgs "decode/daff-is-ret15-not-minus1" callxArgsArgs15Code 15 15
        expectDecodeErr "decode/truncated-8" callxArgs1Truncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" callxArgs1Truncated15Code .invOpcode
        expectDecodeErr "decode/empty" emptyCode .invOpcode

        let asmNeg1 := assembleNoRefCell! "asm/callxargs-neg1" #[callxArgs1Instr 6]
        expectDecodeCallxArgs "asm/callxargs-neg1-uses-db0" asmNeg1 6 (-1)

        expectAssembleErr "asm/params-overflow" #[.callxArgs 16 (-1)] .rangeChk
        expectAssembleErr "asm/retvals-underflow" #[.callxArgs 0 (-2)] .rangeChk
        expectAssembleErr "asm/retvals-overflow" #[.callxArgs 0 16] .rangeChk }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.CALLXARGS_1
