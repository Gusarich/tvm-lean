import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native.Host.StubHost

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.REPEATENDBRK

/-!
REPEATENDBRK branch map and runtime continuation behavior (Lean vs C++):
- Lean audited files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.repeatEnd true`)
  - `TvmLean/Semantics/Step/Step.lean` (`.repeatBody` runtime branches)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (`childStep` `.repeatBody` path)
- C++ audited files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_repeat_end` with `brk=true`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::repeat`, `RepeatCont::jump/_w`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `ret`, `c1_envelope_if`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_smallint_range`)

Handler branches (`.contExt (.repeatEnd true)`):
1. dispatch vs fallback to `next`
2. `checkUnderflow(1)` before all pop/type/range work
3. count parse (`typeChk` for non-int, `rangeChk` for NaN/out-of-32-bit)
4. `c <= 0` -> `ret` path (no `c1` envelope)
5. `c > 0` -> `body := extractCc 0`, `after := c1_envelope(get_c0())`, install `.repeatBody`

Runtime continuation branches (`.repeatBody` / `RepeatCont`):
- `count = 0` -> transfer to `after` (with jump-time args checks)
- `count > 0 && body.hasC0` -> jump body directly
- `count > 0 && !body.hasC0` -> set decremented repeat continuation in `c0`, jump body
-/

private def repeatEndBrkId : InstrId := { name := "REPEATENDBRK" }

private def repeatEndBrkInstr : Instr := .contExt (.repeatEnd true)

private def dispatchSentinel : Int := 60319

private def minInt32 : Int := -0x80000000

private def maxInt32 : Int := 0x7fffffff

private def int32TooLarge : Int := maxInt32 + 1

private def int32TooSmall : Int := minInt32 - 1

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceB : Slice := Slice.ofCell refCellB

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

private def cregsEmpty (cregs : OrdCregs) : Bool :=
  cregs.c0.isNone &&
  cregs.c1.isNone &&
  cregs.c2.isNone &&
  cregs.c3.isNone &&
  cregs.c4.isNone &&
  cregs.c5.isNone &&
  cregs.c7.isNone

private def bodyRet : Continuation :=
  mkOrdCont

private def bodyRetWithC0 : Continuation :=
  mkOrdCont (Slice.ofCell Cell.empty) (.quit 0)
    ({ OrdCregs.empty with c0 := some (.quit 19) })

private def runRepeatEndBrkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt repeatEndBrkInstr stack

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runRepeatEndBrkRaw
    (stack : Array Value)
    (cc : Continuation := mkOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowLoopExt repeatEndBrkInstr (pure ())).run st0

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

private def stepOnce (st : VmState) : VmState :=
  match VmState.step stubHost st with
  | .continue st' => st'
  | .halt _ st' => st'

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[repeatEndBrkInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := repeatEndBrkId
    program := program
    initStack := stack
    fuel := fuel }

private def progBodyPush (n : Int) : Array Instr :=
  #[repeatEndBrkInstr, .pushInt (.num n)]

private def progBodyAdd (a b : Int) : Array Instr :=
  #[repeatEndBrkInstr, .pushInt (.num a), .pushInt (.num b), .add]

private def progBodyRetAlt : Array Instr :=
  #[repeatEndBrkInstr, .retAlt]

private def progBodyRet : Array Instr :=
  #[repeatEndBrkInstr, .ret]

private def progSetC0Quit1 (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, repeatEndBrkInstr] ++ body

private def progSetC0Nargs (n : Int) (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, repeatEndBrkInstr] ++ body

def suite : InstrSuite where
  id := repeatEndBrkId
  unit := #[
    { name := "unit/dispatch/repeatendbrk-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[.null, intV 5])
          #[.null, intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-repeatendbrk"
          (runLoopExtFallback repeatEndBrkInstr #[intV 0])
          #[] }
    ,
    { name := "unit/errors/underflow-type-range-and-pop-order"
      run := do
        expectErr "underflow/empty" (runRepeatEndBrkDirect #[]) .stkUnd
        expectErr "type/top-null" (runRepeatEndBrkDirect #[.null]) .typeChk
        expectErr "range/top-nan" (runRepeatEndBrkDirect #[.int .nan]) .rangeChk
        expectErr "range/too-large" (runRepeatEndBrkDirect #[intV int32TooLarge]) .rangeChk
        expectErr "range/too-small" (runRepeatEndBrkDirect #[intV int32TooSmall]) .rangeChk

        let stType ← expectRawErr "pop-order/type"
          (runRepeatEndBrkRaw #[intV 77, .null]) .typeChk
        if stType.stack != #[intV 77] then
          throw (IO.userError s!"pop-order/type: stack mismatch {reprStr stType.stack}")

        let stNan ← expectRawErr "pop-order/range"
          (runRepeatEndBrkRaw #[intV 88, .int .nan]) .rangeChk
        if stNan.stack != #[intV 88] then
          throw (IO.userError s!"pop-order/range: stack mismatch {reprStr stNan.stack}") }
    ,
    { name := "unit/ret-path/nonpositive-uses-ret-and-leaves-c1"
      run := do
        let st ← expectRawOk "ret/zero"
          (runRepeatEndBrkRaw #[intV 42, intV 0] (mkOrdCont) (.quit 9) (.quit 6))
        if st.stack != #[intV 42] then
          throw (IO.userError s!"ret/zero: stack mismatch {reprStr st.stack}")
        else if st.cc != .quit 9 then
          throw (IO.userError s!"ret/zero: expected cc=quit9, got {reprStr st.cc}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"ret/zero: expected c0 reset to quit0, got {reprStr st.regs.c0}")
        else if st.regs.c1 != .quit 6 then
          throw (IO.userError s!"ret/zero: c1 changed unexpectedly to {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/positive/extract-cc0-and-brk-envelope"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let weirdCc : Continuation :=
          .ordinary bodySlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66) }
            { stack := #[intV 3], nargs := 2 }

        let st ← expectRawOk "extract-cc0/brk"
          (runRepeatEndBrkRaw #[intV 1] weirdCc (.quit 5) (.quit 6))

        match st.cc with
        | .repeatBody body after count =>
            if count != 1 then
              throw (IO.userError s!"extract-cc0/brk: expected count=1, got {count}")
            else
              match body with
              | .ordinary code saved cregs cdata =>
                  if code != bodySlice then
                    throw (IO.userError s!"extract-cc0/brk: code mismatch {reprStr code}")
                  else if saved != .quit 0 then
                    throw (IO.userError s!"extract-cc0/brk: expected saved=quit0, got {reprStr saved}")
                  else if !cregsEmpty cregs then
                    throw (IO.userError s!"extract-cc0/brk: expected empty cregs, got {reprStr cregs}")
                  else if !(cdataEmpty cdata) then
                    throw (IO.userError "extract-cc0/brk: expected empty cdata")
                  else
                    match after, st.regs.c1 with
                    | .envelope extA cregsA cdataA, .envelope extB cregsB cdataB =>
                        if extA != (Continuation.quit 5) then
                          throw (IO.userError s!"extract-cc0/brk: after ext mismatch {reprStr extA}")
                        else if extB != extA then
                          throw (IO.userError s!"extract-cc0/brk: c1 ext mismatch {reprStr extB}")
                        else if cregsA.c0 != some (.quit 5) then
                          throw (IO.userError s!"extract-cc0/brk: after c0 save mismatch {reprStr cregsA.c0}")
                        else if cregsA.c1 != some (.quit 6) then
                          throw (IO.userError s!"extract-cc0/brk: after c1 save mismatch {reprStr cregsA.c1}")
                        else if cregsB.c0 != cregsA.c0 ||
                            cregsB.c1 != cregsA.c1 ||
                            cregsB.c2 != cregsA.c2 ||
                            cregsB.c3 != cregsA.c3 ||
                            cregsB.c4 != cregsA.c4 ||
                            cregsB.c5 != cregsA.c5 ||
                            cregsB.c7 != cregsA.c7 then
                          throw (IO.userError "extract-cc0/brk: expected c1 to equal installed after envelope")
                        else if !(cdataEmpty cdataA) || !(cdataEmpty cdataB) then
                          throw (IO.userError "extract-cc0/brk: expected empty cdata in envelope")
                        else
                          pure ()
                    | _, _ =>
                        throw (IO.userError s!"extract-cc0/brk: expected envelope after/c1, got after={reprStr after}, c1={reprStr st.regs.c1}")
              | _ =>
                  throw (IO.userError s!"extract-cc0/brk: expected ordinary body, got {reprStr body}")
        | _ =>
            throw (IO.userError s!"extract-cc0/brk: expected repeatBody, got {reprStr st.cc}") }
    ,
    { name := "unit/order/c<=0-does-not-require-ordinary-cc-while-c>0-does"
      run := do
        let stRet ← expectRawOk "order/non-ordinary/ret-path"
          (runRepeatEndBrkRaw #[intV 0] (.quit 7) (.quit 9) (.quit 6))
        if stRet.cc != .quit 9 then
          throw (IO.userError s!"order/non-ordinary/ret-path: cc mismatch {reprStr stRet.cc}")
        else if stRet.regs.c0 != .quit 0 then
          throw (IO.userError s!"order/non-ordinary/ret-path: expected c0 reset, got {reprStr stRet.regs.c0}")
        else
          pure ()

        let stPos ← expectRawErr "order/non-ordinary/positive-path"
          (runRepeatEndBrkRaw #[intV 1] (.quit 7) (.quit 9) (.quit 6)) .typeChk
        if stPos.stack != #[] then
          throw (IO.userError s!"order/non-ordinary/positive-path: expected consumed count, got {reprStr stPos.stack}") }
    ,
    { name := "unit/brk/define-only-does-not-overwrite-existing-c0-c1"
      run := do
        let afterRaw : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0)
            { OrdCregs.empty with c0 := some (.quit 123), c1 := some (.quit 124) }
            OrdCdata.empty

        let st ← expectRawOk "brk/define-only"
          (runRepeatEndBrkRaw #[intV 1] (mkOrdCont) afterRaw (.quit 6))

        match st.cc with
        | .repeatBody _ after 1 =>
            match after, st.regs.c1 with
            | .ordinary _ _ cregsA _, .ordinary _ _ cregsB _ =>
                if cregsA.c0 != some (.quit 123) then
                  throw (IO.userError s!"brk/define-only: after c0 save changed to {reprStr cregsA.c0}")
                else if cregsA.c1 != some (.quit 124) then
                  throw (IO.userError s!"brk/define-only: after c1 save changed to {reprStr cregsA.c1}")
                else if cregsB.c0 != cregsA.c0 || cregsB.c1 != cregsA.c1 then
                  throw (IO.userError "brk/define-only: c1 continuation does not preserve saved c0/c1")
                else
                  pure ()
            | _, _ =>
                throw (IO.userError s!"brk/define-only: expected ordinary after/c1, got after={reprStr after}, c1={reprStr st.regs.c1}")
        | _ =>
            throw (IO.userError s!"brk/define-only: expected repeatBody count=1, got {reprStr st.cc}") }
    ,
    { name := "unit/repeatBody/runtime-branch-order"
      run := do
        let base := VmState.initial Cell.empty

        let afterNeedArg : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 8) OrdCregs.empty { stack := #[], nargs := 1 }
        let stUnd0 : VmState :=
          { base with cc := .repeatBody bodyRet afterNeedArg 0 }
        let stUnd := stepOnce stUnd0
        if stUnd.cc != base.regs.c2 then
          throw (IO.userError s!"repeatBody/runtime-underflow: expected jump to c2, got {reprStr stUnd.cc}")
        else if stUnd.stack != #[intV 0, intV Excno.stkUnd.toInt] then
          throw (IO.userError s!"repeatBody/runtime-underflow: stack mismatch {reprStr stUnd.stack}")
        else
          pure ()

        let afterOrd : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 9) OrdCregs.empty OrdCdata.empty
        let stDoneOrd0 : VmState :=
          { base with regs := { base.regs with c0 := .quit 3 }, cc := .repeatBody bodyRet afterOrd 0 }
        let stDoneOrd := stepOnce stDoneOrd0
        if stDoneOrd.regs.c0 != .quit 9 then
          throw (IO.userError s!"repeatBody/runtime-done-ordinary: expected c0=quit9, got {reprStr stDoneOrd.regs.c0}")
        else
          match stDoneOrd.cc with
          | .ordinary _ saved _ _ =>
              if saved != .quit 0 then
                throw (IO.userError s!"repeatBody/runtime-done-ordinary: expected cc.saved=quit0, got {reprStr saved}")
          | _ =>
              throw (IO.userError s!"repeatBody/runtime-done-ordinary: expected ordinary cc, got {reprStr stDoneOrd.cc}")

        let stHasC00 : VmState :=
          { base with regs := { base.regs with c0 := .quit 5 }, cc := .repeatBody bodyRetWithC0 (.quit 8) 2 }
        let stHasC0 := stepOnce stHasC00
        if stHasC0.cc != bodyRetWithC0 then
          throw (IO.userError s!"repeatBody/runtime-body-has-c0: expected body jump, got {reprStr stHasC0.cc}")
        else if stHasC0.regs.c0 != .quit 5 then
          throw (IO.userError s!"repeatBody/runtime-body-has-c0: c0 changed unexpectedly to {reprStr stHasC0.regs.c0}")
        else
          pure ()

        let stStep0 : VmState :=
          { base with regs := { base.regs with c0 := .quit 6 }, cc := .repeatBody bodyRet (.quit 8) 2 }
        let stStep := stepOnce stStep0
        if stStep.cc != bodyRet then
          throw (IO.userError s!"repeatBody/runtime-step: expected body cc, got {reprStr stStep.cc}")
        else if stStep.regs.c0 != .repeatBody bodyRet (.quit 8) 1 then
          throw (IO.userError s!"repeatBody/runtime-step: expected decremented repeat continuation in c0, got {reprStr stStep.regs.c0}")
        else
          pure () }
  ]
  oracle := #[
    -- Non-positive counts: REPEATENDBRK reduces to RET (no c1 envelope path).
    mkCase "ret/zero/default" #[intV 0],
    mkCase "ret/neg1/default" #[intV (-1)],
    mkCase "ret/min-int32/default" #[intV minInt32],
    mkCase "ret/zero/deep-null-int" #[.null, intV 7, intV 0],
    mkCase "ret/neg5/deep-cell" #[.cell refCellA, intV (-5)],
    mkCase "ret/zero/deep-builder-tuple-slice" #[.builder Builder.empty, .tuple #[], .slice fullSliceB, intV 0],
    mkCase "ret/zero/trailing-push-skipped" #[intV 0] #[repeatEndBrkInstr, .pushInt (.num 777)],
    mkCase "ret/zero/c0-quit1" #[intV 0] (progSetC0Quit1),
    mkCase "ret/neg1/c0-quit1" #[intV (-1)] (progSetC0Quit1),
    mkCase "ret/zero/c0-nargs1-underflow" #[intV 0] (progSetC0Nargs 1),
    mkCase "ret/zero/c0-nargs1-success" #[intV 41, intV 0] (progSetC0Nargs 1),
    mkCase "ret/neg1/c0-nargs2-underflow" #[intV 9, intV (-1)] (progSetC0Nargs 2),

    -- Positive counts: body is current continuation tail; BRK arms c1 for RETALT break.
    mkCase "repeat/count1/body-push7" #[intV 1] (progBodyPush 7),
    mkCase "repeat/count2/body-push7" #[intV 2] (progBodyPush 7),
    mkCase "repeat/count3/body-push7" #[intV 3] (progBodyPush 7),
    mkCase "repeat/count4/body-push-neg3" #[intV 4] (progBodyPush (-3)),
    mkCase "repeat/count2/deep-below-preserve" #[.null, intV 5, intV 2] (progBodyPush 13),
    mkCase "repeat/count3/body-add" #[intV 3] (progBodyAdd 2 3),
    mkCase "repeat/count2/body-add-with-below" #[.cell refCellB, intV 2] (progBodyAdd 8 (-3)),
    mkCase "repeat/count1/body-retalt-break" #[intV 1] progBodyRetAlt,
    mkCase "repeat/count3/body-retalt-break" #[intV 3] progBodyRetAlt,
    mkCase "repeat/count3/body-ret" #[intV 3] progBodyRet,
    mkCase "repeat/count1/body-empty" #[intV 1] #[repeatEndBrkInstr],
    mkCase "repeat/count2/body-empty" #[intV 2] #[repeatEndBrkInstr],
    mkCase "repeat/count1/c0-quit1-after" #[intV 1] (progSetC0Quit1 #[.pushInt (.num 4)]),
    mkCase "repeat/count2/c0-quit1-after" #[intV 2] (progSetC0Quit1 #[.pushInt (.num 4)]),
    mkCase "repeat/count1/c0-nargs1-underflow-after" #[intV 1] (progSetC0Nargs 1),
    mkCase "repeat/count1/c0-nargs1-success-after" #[intV 55, intV 1] (progSetC0Nargs 1),
    mkCase "repeat/count2/c0-nargs2-underflow-after" #[intV 55, intV 2] (progSetC0Nargs 2),
    mkCase "repeat/count1/body-retalt-with-below" #[.null, intV 1] progBodyRetAlt,
    mkCase "repeat/count2/body-retalt-with-below" #[.cell refCellA, intV 2] progBodyRetAlt,

    -- Error branches from pop_smallint_range.
    mkCase "err/underflow-empty" #[],
    mkCase "err/type-top-null" #[.null],
    mkCase "err/type-top-cell" #[.cell refCellA],
    mkCase "err/type-top-builder" #[.builder Builder.empty],
    mkCase "err/type-top-slice" #[.slice fullSliceB],
    mkCase "err/range-nan-via-program" #[] #[.pushInt .nan, repeatEndBrkInstr],
    mkCase "err/range-too-large" #[intV int32TooLarge],
    mkCase "err/range-too-small" #[intV int32TooSmall]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.REPEATENDBRK
