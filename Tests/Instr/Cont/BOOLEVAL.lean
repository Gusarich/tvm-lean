import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.BOOLEVAL

/-
BOOLEVAL branch map (Lean vs C++):
- C++ `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_booleval`):
  1) `pop_cont`; 2) `extract_cc(3)`; 3) `set_c0/set_c1` to push-int continuations; 4) `jump(cont)`.
- Ordering implications:
  - no upfront `check_underflow(2)` (single-item non-cont is `typeChk`, not `stkUnd`);
  - pop/type happens before `extract_cc`/jump checks;
  - jump-time `nargs` checks must still apply.
-/

private def boolevalId : InstrId := { name := "BOOLEVAL" }

private def boolevalInstr : Instr := .contExt .booleval

private def dispatchSentinel : Int := 53991

private def q0 : Value := .cont (.quit 0)

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def sliceA : Slice := Slice.ofCell refCellA

private def markerCell : Cell :=
  Cell.mkOrdinary (natToBits 0x2d 6) #[]

private def ccMarked : Continuation :=
  .ordinary (Slice.ofCell markerCell) (.quit 0) OrdCregs.empty OrdCdata.empty

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice sliceA, .builder Builder.empty, .tuple #[]]

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[])
    (saved : Continuation := .quit 0) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) saved OrdCregs.empty { stack := captured, nargs := nargs }

private def runBoolevalDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContAtExit boolevalInstr stack

private def runBoolevalDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContAtExit instr (VM.push (intV dispatchSentinel)) stack

private def runBoolevalRaw
    (stack : Array Value)
    (cc : Continuation := ccMarked)
    (regs : Regs := Regs.initial) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := regs }
  (execInstrContAtExit boolevalInstr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  match out with
  | (.ok _, st) =>
      pure st
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
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectCapturedCc
    (label : String)
    (k : Continuation)
    (expectedCode : Slice)
    (oldC0 oldC1 : Continuation) : IO Unit := do
  match k with
  | .ordinary code saved cregs cdata =>
      if code != expectedCode then
        throw (IO.userError s!"{label}: captured cc code mismatch: {reprStr code}")
      else if saved != .quit 0 then
        throw (IO.userError s!"{label}: captured cc saved mismatch: {reprStr saved}")
      else if cregs.c0 != some oldC0 then
        throw (IO.userError s!"{label}: captured cc c0 mismatch: {reprStr cregs.c0}")
      else if cregs.c1 != some oldC1 then
        throw (IO.userError s!"{label}: captured cc c1 mismatch: {reprStr cregs.c1}")
      else if cregs.c2.isSome || cregs.c3.isSome || cregs.c4.isSome || cregs.c5.isSome || cregs.c7.isSome then
        throw (IO.userError s!"{label}: captured cc unexpected cregs payload: {reprStr cregs}")
      else if cdata.stack != #[] || cdata.nargs != -1 then
        throw (IO.userError s!"{label}: captured cc unexpected cdata: {reprStr cdata}")
      else
        pure ()
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary captured cc, got {reprStr k}")

private def expectPushIntCont
    (label : String)
    (k : Continuation)
    (expectedVal : Int)
    (expectedCapturedCode : Slice)
    (oldC0 oldC1 : Continuation) : IO Unit := do
  match k with
  | .ordinary code saved cregs cdata =>
      if saved != .quit 0 then
        throw (IO.userError s!"{label}: push-int saved mismatch: {reprStr saved}")
      else if cdata.stack != #[] || cdata.nargs != -1 then
        throw (IO.userError s!"{label}: push-int unexpected cdata: {reprStr cdata}")
      else
        match decodeCp0WithBits code with
        | .ok (instr, _, rest) =>
            if instr != .pushInt (.num expectedVal) then
              throw (IO.userError s!"{label}: expected PUSHINT {expectedVal}, got {reprStr instr}")
            else if rest.bitsRemaining + rest.refsRemaining != 0 then
              throw (IO.userError s!"{label}: expected empty push-int code tail, got {reprStr rest}")
            else
              match cregs.c0 with
              | some captured =>
                  if cregs.c1.isSome || cregs.c2.isSome || cregs.c3.isSome
                      || cregs.c4.isSome || cregs.c5.isSome || cregs.c7.isSome then
                    throw (IO.userError s!"{label}: push-int unexpected cregs payload: {reprStr cregs}")
                  else
                    expectCapturedCc s!"{label}/captured" captured expectedCapturedCode oldC0 oldC1
              | none =>
                  throw (IO.userError s!"{label}: expected c0 to hold captured cc")
        | .error e =>
            throw (IO.userError s!"{label}: push-int decode failed with {e}")
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary push-int continuation, got {reprStr k}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[boolevalInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := boolevalId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := boolevalId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progTailPush : Array Instr :=
  #[boolevalInstr, .pushInt (.num 77)]

private def progPushBeforeBooleval : Array Instr :=
  #[.pushInt (.num 5), boolevalInstr]

private def progDoubleBooleval : Array Instr :=
  #[boolevalInstr, boolevalInstr]

private def progMakeNargsAndBooleval (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num n), .setNumVarArgs, boolevalInstr] ++ tail

private def progCaptureAndBooleval (copy : Nat) (more : Int) : Array Instr :=
  #[.pushCtr 0, .setContArgs copy more, boolevalInstr]

private def boolevalCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf9 16) #[]

private def boolevalTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def boolevalTruncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits 0xedf9 16).take 15) #[]

private def oracleCases : Array OracleCase := #[
  -- Direct success paths.
  mkCase "ok/basic/empty-below" #[q0],
  mkCase "ok/basic/int-below" #[intV 7, q0],
  mkCase "ok/basic/noise-a" (noiseA ++ #[q0]),
  mkCase "ok/basic/noise-b" (noiseB ++ #[q0]),
  mkCase "ok/basic/max-int257" #[intV maxInt257, q0],
  mkCase "ok/basic/min-int257" #[intV minInt257, q0],
  mkCase "ok/basic/deep-mixed"
    #[.null, .cell refCellB, .slice sliceA, .builder Builder.empty, .tuple #[], q0],
  mkCase "ok/order/tail-skipped" #[intV 3, q0] progTailPush,
  mkCase "ok/order/double-first-jumps" #[q0, q0] progDoubleBooleval,
  mkCase "ok/order/prelude-push-before-booleval" #[q0] progPushBeforeBooleval,

  -- Pop/type order (`pop_cont` first, no upfront underflow check for 2 args).
  mkCase "err/pop/underflow-empty" #[],
  mkCase "err/pop/type-null" #[.null],
  mkCase "err/pop/type-int" #[intV 1],
  mkCase "err/pop/type-cell" #[.cell refCellA],
  mkCase "err/pop/type-slice" #[.slice sliceA],
  mkCase "err/pop/type-builder" #[.builder Builder.empty],
  mkCase "err/pop/type-tuple" #[.tuple #[]],
  mkCase "err/order/type-before-below-cont" #[q0, .null],
  mkCase "err/order/type-before-below-cont-deep" (noiseA ++ #[q0, .cell refCellA]),

  -- Jump-time nargs checks (must be reached via `VM.jump`).
  mkCase "err/jump/nargs1-underflow-empty" #[] (progMakeNargsAndBooleval 1),
  mkCase "ok/jump/nargs1-one-arg" #[intV 8] (progMakeNargsAndBooleval 1),
  mkCase "ok/jump/nargs1-two-arg-truncate" #[intV 8, intV 9] (progMakeNargsAndBooleval 1),
  mkCase "err/jump/nargs2-underflow-one-arg" #[intV 8] (progMakeNargsAndBooleval 2),
  mkCase "ok/jump/nargs2-two-arg" #[intV 8, intV 9] (progMakeNargsAndBooleval 2),
  mkCase "ok/jump/nargs0-drop-all" #[intV 8, intV 9] (progMakeNargsAndBooleval 0),
  mkCase "ok/jump/nargs0-tail-skipped" #[intV 8] (progMakeNargsAndBooleval 0 #[.pushInt (.num 42)]),
  mkCase "err/jump/nargs3-underflow-two-arg" #[intV 8, intV 9] (progMakeNargsAndBooleval 3),
  mkCase "ok/jump/nargs3-three-arg" #[intV 1, intV 2, intV 3] (progMakeNargsAndBooleval 3),

  -- Jump-time captured-stack merge via SETCONTARGS-produced continuation.
  mkCase "ok/jump/capture1-more-1-one-arg" #[intV 4] (progCaptureAndBooleval 1 (-1)),
  mkCase "ok/jump/capture1-more-1-two-arg" #[intV 4, intV 5] (progCaptureAndBooleval 1 (-1)),
  mkCase "ok/jump/capture1-more0-two-arg" #[intV 4, intV 5] (progCaptureAndBooleval 1 0),
  mkCase "err/jump/capture1-more2-underflow" #[intV 4, intV 5] (progCaptureAndBooleval 1 2),
  mkCase "ok/jump/capture2-more1-three-arg" #[intV 4, intV 5, intV 6] (progCaptureAndBooleval 2 1),
  mkCase "err/jump/capture2-more1-underflow-two-arg" #[intV 5, intV 6] (progCaptureAndBooleval 2 1),
  mkCase "ok/jump/capture2-more0-three-arg" #[intV 4, intV 5, intV 6] (progCaptureAndBooleval 2 0),
  mkCase "ok/jump/capture1-more-1-with-noise" #[.null, intV 7] (progCaptureAndBooleval 1 (-1)),

  -- Decode boundaries around `0xedf9`.
  mkCodeCase "ok/decode/raw-exact-edf9" #[q0] boolevalCode,
  mkCodeCase "err/decode/truncated-8" #[] boolevalTruncated8Code,
  mkCodeCase "err/decode/truncated-15" #[q0] boolevalTruncated15Code
]

def suite : InstrSuite where
  id := boolevalId
  unit := #[
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback"
          (runBoolevalDispatchFallback .add #[intV 2])
          #[intV 2, intV dispatchSentinel]
        expectOkStack "dispatch/match"
          (runBoolevalDirect #[q0])
          #[] }
    ,
    { name := "unit/error-order/underflow-vs-singleton-type"
      run := do
        expectErr "underflow/empty" (runBoolevalDirect #[]) .stkUnd
        expectErr "type/singleton-null" (runBoolevalDirect #[.null]) .typeChk
        expectErr "type/singleton-int" (runBoolevalDirect #[intV 1]) .typeChk }
    ,
    { name := "unit/error-order/top-type-pop-consumes-top"
      run := do
        let regs0 := { Regs.initial with c0 := .quit 11, c1 := .quit 12 }
        let st ← expectRawErr "top-type-pop" (runBoolevalRaw #[intV 9, .null] ccMarked regs0) .typeChk
        if st.stack != #[intV 9] then
          throw (IO.userError s!"top-type-pop: expected stack #[9], got {reprStr st.stack}")
        else if st.regs.c0 != .quit 11 then
          throw (IO.userError s!"top-type-pop: c0 changed unexpectedly to {reprStr st.regs.c0}")
        else if st.regs.c1 != .quit 12 then
          throw (IO.userError s!"top-type-pop: c1 changed unexpectedly to {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/error-order/pop-before-extractcc-on-nonordinary-cc"
      run := do
        let regs0 := { Regs.initial with c0 := .quit 21, c1 := .quit 22 }
        let st ← expectRawErr "nonordinary-cc" (runBoolevalRaw #[q0] (.quit 99) regs0) .typeChk
        if st.stack != #[] then
          throw (IO.userError s!"nonordinary-cc: expected empty stack after pop_cont, got {reprStr st.stack}")
        else if st.regs.c0 != .quit 21 then
          throw (IO.userError s!"nonordinary-cc: c0 changed unexpectedly to {reprStr st.regs.c0}")
        else if st.regs.c1 != .quit 22 then
          throw (IO.userError s!"nonordinary-cc: c1 changed unexpectedly to {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/state/success-sets-pushint-cregs-and-jumps"
      run := do
        let oldC0 : Continuation := .quit 31
        let oldC1 : Continuation := .quit 32
        let oldC2 : Continuation := .quit 33
        let regs0 := { Regs.initial with c0 := oldC0, c1 := oldC1, c2 := oldC2 }
        let target : Continuation := .quit 77
        let st ← expectRawOk "success-sets-pushint-cregs"
          (runBoolevalRaw #[intV 5, .cont target] ccMarked regs0)
        if st.stack != #[intV 5] then
          throw (IO.userError s!"success-sets-pushint-cregs: stack mismatch {reprStr st.stack}")
        else if st.cc != target then
          throw (IO.userError s!"success-sets-pushint-cregs: expected cc target, got {reprStr st.cc}")
        else if st.regs.c2 != oldC2 then
          throw (IO.userError s!"success-sets-pushint-cregs: c2 changed to {reprStr st.regs.c2}")
        else do
          expectPushIntCont "success/c0" st.regs.c0 (-1) (Slice.ofCell markerCell) oldC0 oldC1
          expectPushIntCont "success/c1" st.regs.c1 0 (Slice.ofCell markerCell) oldC0 oldC1 }
    ,
    { name := "unit/state/jump-underflow-after-pop-and-after-c0-c1-update"
      run := do
        let oldC0 : Continuation := .quit 41
        let oldC1 : Continuation := .quit 42
        let regs0 := { Regs.initial with c0 := oldC0, c1 := oldC1 }
        let targetNeed1 : Continuation := mkOrdCont 1 #[]
        let st ← expectRawErr "jump-underflow-after-pop" (runBoolevalRaw #[.cont targetNeed1] ccMarked regs0) .stkUnd
        if st.stack != #[] then
          throw (IO.userError s!"jump-underflow-after-pop: expected empty stack, got {reprStr st.stack}")
        else if st.cc != ccMarked then
          throw (IO.userError s!"jump-underflow-after-pop: cc changed unexpectedly to {reprStr st.cc}")
        else do
          expectPushIntCont "jump-underflow/c0" st.regs.c0 (-1) (Slice.ofCell markerCell) oldC0 oldC1
          expectPushIntCont "jump-underflow/c1" st.regs.c1 0 (Slice.ofCell markerCell) oldC0 oldC1 }
    ,
    { name := "unit/state/jump-nargs-truncates-stack"
      run := do
        let targetNeed1 : Continuation := mkOrdCont 1 #[]
        let st ← expectRawOk "jump-nargs-truncates"
          (runBoolevalRaw #[intV 4, intV 5, .cont targetNeed1])
        if st.stack != #[intV 5] then
          throw (IO.userError s!"jump-nargs-truncates: expected #[5], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/state/jump-captured-stack-merge"
      run := do
        let targetCaptured : Continuation := mkOrdCont 1 #[intV 99]
        let st ← expectRawOk "jump-captured-stack-merge"
          (runBoolevalRaw #[intV 4, intV 5, .cont targetCaptured])
        if st.stack != #[intV 99, intV 5] then
          throw (IO.userError
            s!"jump-captured-stack-merge: expected #[99,5], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/decode/opcode-and-truncated-prefix"
      run := do
        let assembled ←
          match assembleCp0 [boolevalInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/booleval failed: {reprStr e}")
        if assembled.bits != natToBits 0xedf9 16 then
          throw (IO.userError s!"opcode/booleval expected 0xedf9, got {reprStr assembled.bits}")

        let rawBits : BitString := natToBits 0xedf9 16 ++ natToBits 0xa0 8
        let s0 := Slice.ofCell (Cell.mkOrdinary rawBits #[])
        match decodeCp0WithBits s0 with
        | .ok (instr, bits, rest) =>
            if instr != boolevalInstr then
              throw (IO.userError s!"decode/raw-head expected booleval, got {reprStr instr}")
            else if bits != 16 then
              throw (IO.userError s!"decode/raw-head expected 16 bits, got {bits}")
            else
              match decodeCp0WithBits rest with
              | .ok (tail, tailBits, rest2) =>
                  if tail != .add then
                    throw (IO.userError s!"decode/raw-tail expected add, got {reprStr tail}")
                  else if tailBits != 8 then
                    throw (IO.userError s!"decode/raw-tail expected 8 bits, got {tailBits}")
                  else if rest2.bitsRemaining + rest2.refsRemaining != 0 then
                    throw (IO.userError s!"decode/raw-tail expected exhausted input, got {reprStr rest2}")
                  else
                    pure ()
              | .error e =>
                  throw (IO.userError s!"decode/raw-tail failed: {e}")
        | .error e =>
            throw (IO.userError s!"decode/raw-head failed: {e}")

        expectDecodeErr "decode/truncated-8" boolevalTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" boolevalTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec boolevalId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.BOOLEVAL
