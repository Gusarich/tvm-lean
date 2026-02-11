import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.COMPOSBOTH

private def composBothId : InstrId := { name := "COMPOSBOTH" }

private def composBothInstr : Instr := .composBoth

private def dispatchSentinel : Int := 60421

private def q0 : Value := .cont (.quit 0)

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice :=
  Slice.ofCell refCellA

private def fullSliceB : Slice :=
  Slice.ofCell refCellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceB, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[intV (-5), .null, .builder Builder.empty]

private def mkStack
    (below : Array Value)
    (cont : Value := q0)
    (val : Value := q0) : Array Value :=
  below ++ #[cont, val]

private def runComposBothDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContComposBoth composBothInstr stack

private def runComposBothFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContComposBoth instr (VM.push (intV dispatchSentinel)) stack

private def runComposBothRaw
    (stack : Array Value)
    (instr : Instr := composBothInstr) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContComposBoth instr (pure ())).run st0

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

private def expectSingleTopCont
    (label : String)
    (res : Except Excno (Array Value)) : IO Continuation := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.size != 1 then
        throw (IO.userError s!"{label}: expected one stack item, got {reprStr st}")
      match st[0]? with
      | some v =>
          match v with
          | .cont k => pure k
          | _ =>
              throw (IO.userError s!"{label}: expected top continuation, got {reprStr st}")
      | none =>
          throw (IO.userError s!"{label}: expected top continuation, got {reprStr st}")

private def mkEnvCont
    (ext : Continuation := .quit 0)
    (c0 : Option Continuation := none)
    (c1 : Option Continuation := none) : Continuation :=
  .envelope ext { OrdCregs.empty with c0 := c0, c1 := c1 } OrdCdata.empty

private def mkOrdCont
    (saved : Continuation := .quit 0)
    (c0 : Option Continuation := none)
    (c1 : Option Continuation := none) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) saved { OrdCregs.empty with c0 := c0, c1 := c1 } OrdCdata.empty

private def readC0C1 (k : Continuation) : Option Continuation × Option Continuation :=
  match k with
  | .ordinary _ _ cregs _ => (cregs.c0, cregs.c1)
  | .envelope _ cregs _ => (cregs.c0, cregs.c1)
  | _ => (none, none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[composBothInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := composBothId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := composBothId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def composBothCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf2 16) #[]

private def composBothTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def composBothTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf2 >>> 1) 15) #[]

def suite : InstrSuite where
  id := composBothId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runComposBothFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        match runComposBothFallback composBothInstr #[q0, q0] with
        | .ok st =>
            if st.size != 1 then
              throw (IO.userError s!"dispatch/matched: expected one item, got {reprStr st}")
            else
              match st[0]? with
              | some v =>
                  match v with
                  | .cont _ => pure ()
                  | _ =>
                      throw (IO.userError s!"dispatch/matched: expected continuation, got {reprStr st}")
              | none =>
                  throw (IO.userError s!"dispatch/matched: expected continuation, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/matched: expected success, got {e}") }
    ,
    { name := "unit/order/underflow-before-type-on-single-item"
      run := do
        let stNull ←
          expectRawErr "order/underflow-before-type/null"
            (runComposBothRaw #[.null]) .stkUnd
        if stNull.stack != #[.null] then
          throw (IO.userError
            s!"order/underflow-before-type/null: expected stack #[null], got {reprStr stNull.stack}")

        let stInt ←
          expectRawErr "order/underflow-before-type/int"
            (runComposBothRaw #[intV 7]) .stkUnd
        if stInt.stack != #[intV 7] then
          throw (IO.userError
            s!"order/underflow-before-type/int: expected stack #[7], got {reprStr stInt.stack}") }
    ,
    { name := "unit/order/type-pop-consumption"
      run := do
        let stFirst ←
          expectRawErr "order/type-first-pop"
            (runComposBothRaw #[intV 7, .null]) .typeChk
        if stFirst.stack != #[intV 7] then
          throw (IO.userError
            s!"order/type-first-pop: expected stack #[7], got {reprStr stFirst.stack}")

        let stSecond ←
          expectRawErr "order/type-second-pop"
            (runComposBothRaw #[intV 7, .null, q0]) .typeChk
        if stSecond.stack != #[intV 7] then
          throw (IO.userError
            s!"order/type-second-pop: expected stack #[7], got {reprStr stSecond.stack}") }
    ,
    { name := "unit/internal/wrap-quit-and-define-both"
      run := do
        let cont : Continuation := .quit 41
        let val : Continuation := .quit 9
        let out ← expectSingleTopCont "internal/wrap-quit-and-define-both"
          (runComposBothDirect #[.cont cont, .cont val])
        match out with
        | .envelope ext cregs _ =>
            if ext != cont then
              throw (IO.userError
                s!"internal/wrap-quit-and-define-both: expected ext quit 41, got {reprStr ext}")
            else if cregs.c0 != some val then
              throw (IO.userError
                s!"internal/wrap-quit-and-define-both: expected c0=quit 9, got {reprStr cregs.c0}")
            else if cregs.c1 != some val then
              throw (IO.userError
                s!"internal/wrap-quit-and-define-both: expected c1=quit 9, got {reprStr cregs.c1}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"internal/wrap-quit-and-define-both: expected envelope, got {reprStr out}") }
    ,
    { name := "unit/internal/ordinary-path-define-both"
      run := do
        let cont := mkOrdCont (.quit 3)
        let val : Continuation := .quit 8
        let out ← expectSingleTopCont "internal/ordinary-path-define-both"
          (runComposBothDirect #[.cont cont, .cont val])
        match out with
        | .ordinary _ saved cregs _ =>
            if saved != .quit 3 then
              throw (IO.userError
                s!"internal/ordinary-path-define-both: savedC0 changed unexpectedly: {reprStr saved}")
            else if cregs.c0 != some val then
              throw (IO.userError
                s!"internal/ordinary-path-define-both: expected c0=quit 8, got {reprStr cregs.c0}")
            else if cregs.c1 != some val then
              throw (IO.userError
                s!"internal/ordinary-path-define-both: expected c1=quit 8, got {reprStr cregs.c1}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"internal/ordinary-path-define-both: expected ordinary, got {reprStr out}") }
    ,
    { name := "unit/internal/no-overwrite-existing-c0-c1"
      run := do
        let old0 : Continuation := .quit 11
        let old1 : Continuation := .quit 12
        let val : Continuation := .quit 99

        let outC0 ← expectSingleTopCont "internal/no-overwrite-existing-c0"
          (runComposBothDirect #[.cont (mkEnvCont (.quit 70) (some old0) none), .cont val])
        let (c0After, c1After) := readC0C1 outC0
        if c0After != some old0 then
          throw (IO.userError
            s!"internal/no-overwrite-existing-c0: expected c0=quit 11, got {reprStr c0After}")
        else if c1After != some val then
          throw (IO.userError
            s!"internal/no-overwrite-existing-c0: expected c1=quit 99, got {reprStr c1After}")

        let outC1 ← expectSingleTopCont "internal/no-overwrite-existing-c1"
          (runComposBothDirect #[.cont (mkEnvCont (.quit 71) none (some old1)), .cont val])
        let (c0After2, c1After2) := readC0C1 outC1
        if c0After2 != some val then
          throw (IO.userError
            s!"internal/no-overwrite-existing-c1: expected c0=quit 99, got {reprStr c0After2}")
        else if c1After2 != some old1 then
          throw (IO.userError
            s!"internal/no-overwrite-existing-c1: expected c1=quit 12, got {reprStr c1After2}")

        let outBoth ← expectSingleTopCont "internal/no-overwrite-existing-both"
          (runComposBothDirect #[.cont (mkEnvCont (.quit 72) (some old0) (some old1)), .cont val])
        let (c0After3, c1After3) := readC0C1 outBoth
        if c0After3 != some old0 then
          throw (IO.userError
            s!"internal/no-overwrite-existing-both: expected c0=quit 11, got {reprStr c0After3}")
        else if c1After3 != some old1 then
          throw (IO.userError
            s!"internal/no-overwrite-existing-both: expected c1=quit 12, got {reprStr c1After3}")
        else
          pure () }
    ,
    { name := "unit/raw/success-preserves-below"
      run := do
        let st ← expectRawOk "raw/success-preserves-below"
          (runComposBothRaw #[intV 4, .cell refCellA, q0, q0])
        if st.stack.size != 3 then
          throw (IO.userError
            s!"raw/success-preserves-below: expected stack size 3, got {st.stack.size}")
        else if st.stack[0]! != intV 4 then
          throw (IO.userError
            s!"raw/success-preserves-below: expected bottom int 4, got {reprStr st.stack[0]!}")
        else if st.stack[1]! != .cell refCellA then
          throw (IO.userError
            s!"raw/success-preserves-below: expected next cellA, got {reprStr st.stack[1]!}")
        else
          match st.stack[2]? with
          | some v =>
              match v with
              | .cont _ => pure ()
              | _ =>
                  throw (IO.userError
                    s!"raw/success-preserves-below: expected top continuation, got {reprStr st.stack}")
          | none =>
              throw (IO.userError
                s!"raw/success-preserves-below: expected top continuation, got {reprStr st.stack}") }
  ]
  oracle := #[
    -- Success matrix
    mkCase "ok/basic/quit-quit" (mkStack #[]),
    mkCase "ok/basic/noiseA" (mkStack noiseA),
    mkCase "ok/basic/noiseB" (mkStack noiseB),
    mkCase "ok/basic/noiseC" (mkStack noiseC),
    mkCase "ok/basic/maxint-below" (mkStack #[intV maxInt257]),
    mkCase "ok/basic/minint-below" (mkStack #[intV minInt257]),
    mkCase "ok/program/pushctr0-then-composboth" #[q0] #[.pushCtr 0, composBothInstr],
    mkCase "ok/program/pushctr1-then-composboth" #[q0] #[.pushCtr 1, composBothInstr],
    mkCase "ok/program/setcontctr0-then-composboth"
      #[q0, q0] #[.setContCtr 0, .pushCtr 0, composBothInstr],
    mkCase "ok/program/setcontctr1-then-composboth"
      #[q0, q0] #[.setContCtr 1, .pushCtr 0, composBothInstr],
    mkCase "ok/program/chain-two-composboth" #[q0, q0, q0] #[composBothInstr, composBothInstr],
    mkCase "ok/program/chain-two-composboth-deep"
      #[intV 9, .cell refCellB, q0, q0, q0] #[composBothInstr, composBothInstr],
    mkCase "ok/program/composboth-then-pushint"
      (mkStack #[]) #[composBothInstr, .pushInt (.num 5)],
    mkCase "ok/program/composboth-then-pushctr0"
      (mkStack #[intV 2]) #[composBothInstr, .pushCtr 0],

    -- Underflow + underflow-before-type ordering
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/one-cont" #[q0],
    mkCase "err/order/underflow-before-type-one-null" #[.null],
    mkCase "err/order/underflow-before-type-one-int" #[intV 1],

    -- Type path: first pop (top value)
    mkCase "err/type/first-pop-null" #[q0, .null],
    mkCase "err/type/first-pop-int" #[q0, intV 0],
    mkCase "err/type/first-pop-cell" #[q0, .cell refCellA],
    mkCase "err/type/first-pop-slice" #[q0, .slice fullSliceA],
    mkCase "err/type/first-pop-builder" #[q0, .builder Builder.empty],
    mkCase "err/type/first-pop-tuple" #[q0, .tuple #[]],
    mkCase "err/type/first-pop-maxint-range-not-applicable" #[q0, intV maxInt257],
    mkCase "err/type/first-pop-minint-range-not-applicable" #[q0, intV minInt257],

    -- Type path: second pop (below top)
    mkCase "err/type/second-pop-null" #[.null, q0],
    mkCase "err/type/second-pop-int" #[intV 0, q0],
    mkCase "err/type/second-pop-cell" #[.cell refCellA, q0],
    mkCase "err/type/second-pop-slice" #[.slice fullSliceB, q0],
    mkCase "err/type/second-pop-builder" #[.builder Builder.empty, q0],
    mkCase "err/type/second-pop-tuple" #[.tuple #[], q0],
    mkCase "err/type/second-pop-maxint-range-not-applicable" #[intV maxInt257, q0],
    mkCase "err/type/second-pop-minint-range-not-applicable" #[intV minInt257, q0],

    -- Ordering behavior with deeper stacks
    mkCase "err/order/first-pop-type-preserves-deeper" #[intV 7, q0, .null],
    mkCase "err/order/second-pop-type-after-first-success" #[intV 7, .null, q0],

    -- NaN type paths via program prefixes
    mkCase "err/type/first-pop-nan-via-program" #[q0] #[.pushInt .nan, composBothInstr],
    mkCase "err/type/second-pop-nan-via-program" #[q0] #[.pushInt .nan, .xchg0 1, composBothInstr],

    -- Decode/code-cell boundaries
    mkCaseCode "ok/decode/exact-16bit-codecell" (mkStack #[]) composBothCode,
    mkCaseCode "err/decode/truncated-8bit-prefix" #[] composBothTruncated8Code,
    mkCaseCode "err/decode/truncated-15bit-prefix" #[q0] composBothTruncated15Code
  ]
  fuzz := #[ mkReplayOracleFuzzSpec composBothId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.COMPOSBOTH
