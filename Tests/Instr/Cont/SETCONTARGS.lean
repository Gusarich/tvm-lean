import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETCONTARGS

private def setContArgsId : InstrId := { name := "SETCONTARGS" }
private def dispatchSentinel : Int := 48173

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x2d 6) #[]

private def sliceA : Slice := Slice.ofCell cellA

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat i))
    out

private def args15 : Array Value := intStackAsc 15
private def args16 : Array Value := intStackAsc 16

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def rawArgsByte (copy : Nat) (more : Int) : Nat :=
  let moreNib : Nat := if more = -1 then 15 else more.toNat
  (copy <<< 4) + moreNib

private def rawSetContArgsCode (copy : Nat) (more : Int) : Cell :=
  Cell.mkOrdinary
    (natToBits 0xec 8 ++ natToBits (rawArgsByte copy more) 8)
    #[]

private def setContArgsThenRetCode : Cell :=
  assembleNoRefCell! "setcontargs/code/seq" #[.setContArgs 3 (-1), .ret]

private def setContArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xec 8) #[]

private def runDirect (copy : Nat) (more : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContSetContArgs (.setContArgs copy more) stack

private def runFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContSetContArgs instr (VM.push (intV dispatchSentinel)) stack

private def runRaw (instr : Instr) (stack : Array Value) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContSetContArgs instr (pure ())).run st0

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
    (copy : Nat)
    (more : Int)
    (program : Array Instr := #[.setContArgs copy more])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetThenJmp (copy : Nat) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.setContArgs copy more, .jmpx] ++ tail

private def progSetNumThenSetCont (nargs : Int) (copy : Nat) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num nargs), .setNumVarArgs, .setContArgs copy more] ++ tail

private def progDoubleCaptureAppend : Array Instr :=
  #[.pushCtr 0, .setContArgs 1 (-1), .setContArgs 1 (-1), .jmpx]

private def setContArgsCopyPool : Array Nat := #[0, 1, 2, 3, 15]

private def setContArgsMorePool : Array Int := #[-1, 0, 1, 2, 14]

private def setContArgsNoisePool : Array (Array Value) :=
  #[
    #[],
    #[intV 9],
    #[intV 1, intV 2],
    #[.null],
    #[.cell cellA],
    #[.slice sliceA],
    #[.builder Builder.empty],
    #[.tuple #[]]
  ]

private def setContArgsBadContPool : Array Value :=
  #[
    .null,
    intV 1,
    .cell cellA,
    .slice sliceA,
    .builder Builder.empty,
    .tuple #[]
  ]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def mkDirectStack (copy : Nat) (below : Array Value := #[]) : Array Value :=
  below ++ intStackAsc copy ++ #[q0]

private def mkJumpReadyStack (copy : Nat) (more : Int) : Array Value :=
  let jumpNeed : Nat := if more = -1 then 0 else more.toNat
  intStackAsc jumpNeed ++ intStackAsc copy ++ #[q0]

private def genSetContArgsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (copy, rng2) := pickFromPool setContArgsCopyPool rng1
  let (more, rng3) := pickFromPool setContArgsMorePool rng2
  let (noise, rng4) := pickFromPool setContArgsNoisePool rng3
  let (badCont, rng5) := pickFromPool setContArgsBadContPool rng4
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/direct/basic-copy-more" (mkDirectStack copy noise) copy more
    else if shape = 1 then
      mkCase "fuzz/ok/direct/copy0-preserve-below" (noise ++ #[q0]) 0 (-1)
    else if shape = 2 then
      mkCase "fuzz/err/underflow/copy1-only-cont" #[q0] 1 0
    else if shape = 3 then
      mkCase "fuzz/err/underflow/copy15-short" #[intV 1, intV 2, q0] 15 0
    else if shape = 4 then
      mkCase "fuzz/err/type/top-not-cont" #[badCont] 0 (-1)
    else if shape = 5 then
      mkCase "fuzz/err/type/cont-after-need-pass2" #[intV 7, intV 8, intV 9] 2 0
    else if shape = 6 then
      mkCase "fuzz/err/order/underflow-before-cont-type" #[.null] 1 0
    else if shape = 7 then
      mkCase "fuzz/err/order/top-type-before-below-cont" #[q0, intV 1] 0 0
    else if shape = 8 then
      mkCase "fuzz/ok/jump/basic-copy-more"
        (mkJumpReadyStack copy more) copy more
        (progSetThenJmp copy more)
    else if shape = 9 then
      mkCase "fuzz/err/jump/copy0-more1-empty-underflow"
        #[q0] 0 1
        (progSetThenJmp 0 1)
    else if shape = 10 then
      mkCase "fuzz/err/stkov/setnum1-copy2"
        #[intV 9, intV 8] 0 0
        (progSetNumThenSetCont 1 2 0)
    else if shape = 11 then
      mkCase "fuzz/ok/order/jump-tail-skipped"
        (noise ++ #[q0]) 0 (-1)
        (progSetThenJmp 0 (-1) #[.pushInt (.num 999)])
    else if shape = 12 then
      mkCaseCode "fuzz/ok/decode/raw-copy-more"
        (mkDirectStack copy noise)
        (rawSetContArgsCode copy more)
    else if shape = 13 then
      mkCaseCode "fuzz/err/decode/truncated8-prefix" #[q0] setContArgsTruncated8Code
    else
      mkCase "fuzz/err/order/underflow-before-top-type-large-copy" #[q0, intV 1] 15 0
  let (tag, rng6) := randNat rng5 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng6)

private def oracleCases : Array OracleCase := #[
  -- Success paths and immediate bounds.
  mkCase "ok/direct/copy0-more-neg1-keep-quit-empty" #[q0] 0 (-1),
  mkCase "ok/direct/copy0-more-neg1-preserve-below" #[intV 7, q0] 0 (-1),
  mkCase "ok/direct/copy0-more0-force-envelope" #[q0] 0 0,
  mkCase "ok/direct/copy0-more14-force-envelope" #[q0] 0 14,
  mkCase "ok/direct/copy1-more-neg1-capture-one" #[intV 7, q0] 1 (-1),
  mkCase "ok/direct/copy1-more0-capture-one" #[intV 8, q0] 1 0,
  mkCase "ok/direct/copy2-more1-capture-two" #[intV 7, intV 8, q0] 2 1,
  mkCase "ok/direct/copy2-more14-capture-two" #[intV 1, intV 2, q0] 2 14,
  mkCase "ok/direct/copy15-more-neg1-exact-depth" (args15 ++ #[q0]) 15 (-1),
  mkCase "ok/direct/copy15-more14-depth16" (args16 ++ #[q0]) 15 14,

  -- Underflow checks.
  mkCase "err/underflow/empty" #[] 0 (-1),
  mkCase "err/underflow/copy1-only-cont" #[q0] 1 0,
  mkCase "err/underflow/copy2-one-arg" #[intV 1, q0] 2 0,
  mkCase "err/underflow/copy15-short" #[intV 1, intV 2, q0] 15 0,

  -- Continuation type checks.
  mkCase "err/type/cont-null" #[.null] 0 (-1),
  mkCase "err/type/cont-int" #[intV 1] 0 (-1),
  mkCase "err/type/cont-cell" #[.cell cellA] 0 0,
  mkCase "err/type/cont-slice" #[.slice sliceA] 0 0,
  mkCase "err/type/cont-builder" #[.builder Builder.empty] 0 0,
  mkCase "err/type/cont-tuple" #[.tuple #[]] 0 0,
  mkCase "err/type/cont-after-need-pass1" #[intV 7, intV 8] 1 0,
  mkCase "err/type/cont-after-need-pass2" #[intV 7, intV 8, intV 9] 2 0,

  -- Error ordering on encodable immediates.
  mkCase "err/order/underflow-before-cont-type" #[.null] 1 0,
  mkCase "err/order/top-type-before-below-cont" #[q0, intV 1] 0 0,
  mkCase "err/order/underflow-before-top-type-large-copy" #[q0, intV 1] 15 0,

  -- Integration with jump and nargs/captured-stack behavior.
  mkCase "ok/jump/copy0-more-neg1-empty"
    #[q0] 0 (-1)
    (progSetThenJmp 0 (-1)),
  mkCase "err/jump/copy0-more1-empty-underflow"
    #[q0] 0 1
    (progSetThenJmp 0 1),
  mkCase "ok/jump/copy0-more1-onearg"
    #[intV 5, q0] 0 1
    (progSetThenJmp 0 1),
  mkCase "ok/jump/copy1-more-neg1-captured-one"
    #[intV 6, q0] 1 (-1)
    (progSetThenJmp 1 (-1)),
  mkCase "ok/jump/copy2-more-neg1-order-preserved"
    #[intV 1, intV 2, q0] 2 (-1)
    (progSetThenJmp 2 (-1)),
  mkCase "ok/jump/double-capture-append-order"
    #[intV 10, intV 11] 0 (-1)
    progDoubleCaptureAppend,
  mkCase "err/stkov/setnum1-copy2"
    #[intV 9, intV 8] 0 0
    (progSetNumThenSetCont 1 2 0),
  mkCase "ok/jump/setnum1-copy1-nargs-decrement"
    #[intV 9] 0 0
    (progSetNumThenSetCont 1 1 (-1) #[.jmpx]),
  mkCase "err/jump/setnum2-copy0-more1-sentinel"
    #[intV 7] 0 0
    (progSetNumThenSetCont 2 0 1 #[.jmpx]),
  mkCase "ok/order/jump-tail-skipped"
    #[q0] 0 (-1)
    (progSetThenJmp 0 (-1) #[.pushInt (.num 999)]),

  -- Decode gate coverage.
  mkCaseCode "ok/decode/raw-copy15-more-neg1" (args15 ++ #[q0]) (rawSetContArgsCode 15 (-1)),
  mkCaseCode "ok/decode/raw-copy0-more14" #[q0] (rawSetContArgsCode 0 14),
  mkCaseCode "err/decode/truncated8-prefix" #[q0] setContArgsTruncated8Code
]

def suite : InstrSuite where
  id := setContArgsId
  unit := #[
    { name := "unit/direct/dispatch-fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched"
          (runFallback (.setContArgs 0 (-1)) #[q0])
          #[q0] }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let s0 := Slice.ofCell setContArgsThenRetCode
        let s1 ← expectDecodeStep "decode/setcontargs" s0 (.setContArgs 3 (-1)) 16
        let s2 ← expectDecodeStep "decode/ret" s1 .ret 16
        if s2.bitsRemaining != 0 ∨ s2.refsRemaining != 0 then
          throw (IO.userError
            s!"decode/end: expected bits=0 refs=0, got bits={s2.bitsRemaining} refs={s2.refsRemaining}")
        expectDecodeErr "decode/truncated8" setContArgsTruncated8Code .invOpcode
        expectAssembleErr "asm/copy-overflow" #[.setContArgs 16 0] .rangeChk
        expectAssembleErr "asm/more-overflow" #[.setContArgs 0 15] .rangeChk
        expectAssembleErr "asm/more-underflow" #[.setContArgs 0 (-2)] .rangeChk }
    ,
    { name := "unit/order/copy-range-before-underflow"
      run :=
        expectErr "order/copy-range-before-underflow"
          (runDirect 16 0 #[])
          .rangeChk }
    ,
    { name := "unit/order/underflow-before-cont-type"
      run :=
        expectErr "order/underflow-before-type"
          (runDirect 1 0 #[.null])
          .stkUnd }
    ,
    { name := "unit/order/top-type-after-need-check"
      run :=
        expectErr "order/type-after-need"
          (runDirect 2 0 #[intV 7, intV 8, intV 1])
          .typeChk }
    ,
    { name := "unit/raw/copy0-more-neg1-keeps-quit"
      run := do
        let st ← expectRawOk "raw/keep-quit"
          (runRaw (.setContArgs 0 (-1)) #[q0])
        if st.stack != #[q0] then
          throw (IO.userError s!"raw/keep-quit: expected #[q0], got {reprStr st.stack}") }
    ,
    { name := "unit/raw/copy0-more0-wraps-quit-and-sets-nargs"
      run := do
        let st ← expectRawOk "raw/wrap-quit"
          (runRaw (.setContArgs 0 0) #[q0])
        match st.stack with
        | #[.cont (.envelope ext _ cdata)] =>
            if ext != .quit 0 then
              throw (IO.userError s!"raw/wrap-quit: expected ext quit(0), got {reprStr ext}")
            else if cdata.nargs != 0 then
              throw (IO.userError s!"raw/wrap-quit: expected nargs=0, got {cdata.nargs}")
            else if !cdata.stack.isEmpty then
              throw (IO.userError s!"raw/wrap-quit: expected empty captured stack, got {reprStr cdata.stack}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"raw/wrap-quit: expected envelope continuation, got {reprStr st.stack}") }
    ,
    { name := "unit/raw/copy2-appends-to-existing-cdata-stack"
      run := do
        let cont : Continuation := .envelope (.quit 9) OrdCregs.empty { stack := #[intV 42], nargs := -1 }
        let st ← expectRawOk "raw/append-captured"
          (runRaw (.setContArgs 2 (-1)) #[intV 1, intV 2, .cont cont])
        match st.stack with
        | #[.cont (.envelope ext _ cdata)] =>
            if ext != .quit 9 then
              throw (IO.userError s!"raw/append-captured: expected ext quit(9), got {reprStr ext}")
            else if cdata.stack != #[intV 42, intV 1, intV 2] then
              throw (IO.userError
                s!"raw/append-captured: expected stack #[42,1,2], got {reprStr cdata.stack}")
            else if cdata.nargs != -1 then
              throw (IO.userError s!"raw/append-captured: expected nargs=-1, got {cdata.nargs}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"raw/append-captured: expected envelope continuation, got {reprStr st.stack}") }
    ,
    { name := "unit/raw/stkov-after-popcont-leaves-args"
      run := do
        let cont : Continuation := .envelope (.quit 5) OrdCregs.empty { stack := #[], nargs := 1 }
        let st ← expectRawErr "raw/stkov-popcont"
          (runRaw (.setContArgs 2 0) #[intV 1, intV 2, .cont cont])
          .stkOv
        if st.stack != #[intV 1, intV 2] then
          throw (IO.userError
            s!"raw/stkov-popcont: expected remaining #[1,2], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr setContArgsId
      count := 500
      gen := genSetContArgsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTARGS
