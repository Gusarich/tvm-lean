import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.REPEATEND

/-!
REPEATEND / REPEATENDBRK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/LoopExt.lean` (`.repeatEnd brk`)
  - `TvmLean/Semantics/Exec/Flow/Runvm.lean` (`.repeatBody` execution)
  - `TvmLean/Semantics/VM/Ops/State.lean` / `.../Stack.lean` (`ret`, pop/type/range paths)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_repeat_end`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`extract_cc`, `ret`, `c1_envelope_if`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`VmState::repeat`, `RepeatCont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_smallint_range`)

Branch map:
1. Dispatch: `.contExt (.repeatEnd brk)` handled vs fallback to `next`.
2. Pre-pop guard: `checkUnderflow(1)` must happen before pop/type/range checks.
3. Repeat count parse: `pop_smallint_range(INT32_MAX, INT32_MIN)`:
   - type error -> `typeChk`
   - NaN/non-finite -> `intOv`
   - out of signed 32-bit range -> `rangeChk`
4. Count split:
   - `c <= 0` -> `ret()`
   - `c > 0` -> build loop body from `extract_cc(0)`, compute `after`
     via `get_c0()` or `c1_envelope_if(brk, get_c0())`, then enter repeat loop.
5. Repeat runtime (`RepeatCont` / `.repeatBody`) split:
   - `count = 0` -> jump/call `after`
   - `count > 0` and body has `c0` -> jump body directly
   - `count > 0` and body has no `c0` -> set `c0 := repeat(count-1)` then jump body

Mismatch found and fixed:
- C++ uses `extract_cc(0)` for the loop body in `exec_repeat_end`.
- Lean previously reused `st.cc` directly.
- Patched Lean to call `VM.extractCc 0` in the `c > 0` branch.
-/

private def repeatEndId : InstrId := { name := "REPEATEND" }

private def repeatEndInstr : Instr := .contExt (.repeatEnd false)

private def repeatEndBrkInstr : Instr := .contExt (.repeatEnd true)

private def dispatchSentinel : Int := 49013

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

private def cregsEmpty (cregs : OrdCregs) : Bool :=
  cregs.c0.isNone &&
  cregs.c1.isNone &&
  cregs.c2.isNone &&
  cregs.c3.isNone &&
  cregs.c4.isNone &&
  cregs.c5.isNone &&
  cregs.c7.isNone

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

private def runRepeatEndDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowLoopExt repeatEndInstr stack

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runRepeatEndRaw
    (instr : Instr)
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
  (execInstrFlowLoopExt instr (pure ())).run st0

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

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[repeatEndInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := repeatEndId
    program := program
    initStack := stack
    fuel := fuel }

private def progBodyPush (loopInstr : Instr) (n : Int) : Array Instr :=
  #[loopInstr, .pushInt (.num n)]

private def progBodyAdd (loopInstr : Instr) (a b : Int) : Array Instr :=
  #[loopInstr, .pushInt (.num a), .pushInt (.num b), .add]

private def progBodyRetAlt (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .retAlt]

private def progBodyRet (loopInstr : Instr) : Array Instr :=
  #[loopInstr, .ret]

private def progSetC0Quit1 (loopInstr : Instr) (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, loopInstr] ++ body

private def progSetC0Nargs (n : Int) (loopInstr : Instr) (body : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, loopInstr] ++ body

def suite : InstrSuite where
  id := repeatEndId
  unit := #[
    { name := "unit/dispatch/repeatend-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[.null, intV 5])
          #[.null, intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-repeatend"
          (runLoopExtFallback repeatEndInstr #[intV 0])
          #[] }
    ,
    { name := "unit/errors/underflow-type-intov-range-and-pop-order"
      run := do
        expectErr "underflow/empty" (runRepeatEndDirect #[]) .stkUnd
        expectErr "type/top-null" (runRepeatEndDirect #[.null]) .typeChk
        expectErr "range/top-nan" (runRepeatEndDirect #[.int .nan]) .rangeChk
        expectErr "range/too-large" (runRepeatEndDirect #[intV int32TooLarge]) .rangeChk
        expectErr "range/too-small" (runRepeatEndDirect #[intV int32TooSmall]) .rangeChk

        let stType ← expectRawErr "pop-order/type"
          (runRepeatEndRaw repeatEndInstr #[intV 77, .null]) .typeChk
        if stType.stack != #[intV 77] then
          throw (IO.userError s!"pop-order/type: stack mismatch {reprStr stType.stack}")

        let stNan ← expectRawErr "pop-order/range"
          (runRepeatEndRaw repeatEndInstr #[intV 88, .int .nan]) .rangeChk
        if stNan.stack != #[intV 88] then
          throw (IO.userError s!"pop-order/range: stack mismatch {reprStr stNan.stack}") }
    ,
    { name := "unit/ret-path/swap-c0-and-jump"
      run := do
        let st ← expectRawOk "ret/zero"
          (runRepeatEndRaw repeatEndInstr #[intV 42, intV 0] (mkOrdCont) (.quit 9))
        if st.stack != #[intV 42] then
          throw (IO.userError s!"ret/zero: stack mismatch {reprStr st.stack}")
        else if st.cc != .quit 9 then
          throw (IO.userError s!"ret/zero: expected cc=quit9, got {reprStr st.cc}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"ret/zero: expected c0 reset to quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/regression/positive-branch-uses-extract-cc0"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let weirdCc : Continuation :=
          .ordinary bodySlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66) }
            { stack := #[intV 3], nargs := 2 }

        let st ← expectRawOk "extract-cc0/regression"
          (runRepeatEndRaw repeatEndInstr #[intV 1] weirdCc (.quit 5))

        match st.cc with
        | .repeatBody body after count =>
            if count != 1 then
              throw (IO.userError s!"extract-cc0/regression: expected count=1, got {count}")
            else if after != .quit 5 then
              throw (IO.userError s!"extract-cc0/regression: after mismatch {reprStr after}")
            else
              match body with
              | .ordinary code saved _ _ =>
                  if code != bodySlice then
                    throw (IO.userError
                      s!"extract-cc0/regression: code mismatch {reprStr code}")
                  else if saved != .quit 0 then
                    throw (IO.userError
                      s!"extract-cc0/regression: expected saved=quit0, got {reprStr saved}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError
                    s!"extract-cc0/regression: expected ordinary body, got {reprStr body}")
        | _ =>
            throw (IO.userError s!"extract-cc0/regression: expected repeatBody, got {reprStr st.cc}") }
    ,
    { name := "unit/order/c<=0-does-not-require-ordinary-cc-while-c>0-does"
      run := do
        let stRet ← expectRawOk "order/non-ordinary/ret-path"
          (runRepeatEndRaw repeatEndInstr #[intV 0] (.quit 7) (.quit 9))
        if stRet.cc != .quit 9 then
          throw (IO.userError s!"order/non-ordinary/ret-path: cc mismatch {reprStr stRet.cc}")
        else if stRet.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"order/non-ordinary/ret-path: expected c0 reset, got {reprStr stRet.regs.c0}")
        else
          pure ()

        let stPos ← expectRawErr "order/non-ordinary/positive-path"
          (runRepeatEndRaw repeatEndInstr #[intV 1] (.quit 7) (.quit 9)) .typeChk
        if stPos.stack != #[] then
          throw (IO.userError
            s!"order/non-ordinary/positive-path: expected consumed count, got {reprStr stPos.stack}") }
    ,
    { name := "unit/brk/c1-envelope-and-ret-order"
      run := do
        let stBrk ← expectRawOk "brk/positive"
          (runRepeatEndRaw repeatEndBrkInstr #[intV 1] (mkOrdCont) (.quit 5) (.quit 6))
        match stBrk.cc with
        | .repeatBody _ after 1 =>
            if stBrk.regs.c1 != after then
              throw (IO.userError "brk/positive: expected c1 to equal loop-after continuation")
            else
              match after with
              | .envelope ext cregs cdata =>
                  if ext != .quit 5 then
                    throw (IO.userError s!"brk/positive: envelope ext mismatch {reprStr ext}")
                  else if cregs.c0 != some (.quit 5) then
                    throw (IO.userError s!"brk/positive: expected captured c0=quit5, got {reprStr cregs.c0}")
                  else if cregs.c1 != some (.quit 6) then
                    throw (IO.userError s!"brk/positive: expected captured c1=quit6, got {reprStr cregs.c1}")
                  else if !(cdataEmpty cdata) then
                    throw (IO.userError "brk/positive: expected empty cdata in envelope")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"brk/positive: expected envelope after, got {reprStr after}")
        | _ =>
            throw (IO.userError s!"brk/positive: expected repeatBody count=1, got {reprStr stBrk.cc}")

        let stRet ← expectRawOk "brk/non-positive"
          (runRepeatEndRaw repeatEndBrkInstr #[intV 0] (mkOrdCont) (.quit 5) (.quit 6))
        if stRet.cc != .quit 5 then
          throw (IO.userError s!"brk/non-positive: cc mismatch {reprStr stRet.cc}")
        else if stRet.regs.c1 != .quit 6 then
          throw (IO.userError s!"brk/non-positive: c1 changed unexpectedly to {reprStr stRet.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/ret-path/delegates-jump-underflow-checks"
      run := do
        let c0NeedArg : Continuation :=
          .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := 1 }
        let st ← expectRawErr "ret/delegates-jump-underflow"
          (runRepeatEndRaw repeatEndInstr #[intV 0] (mkOrdCont) c0NeedArg) .stkUnd
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"ret/delegates-jump-underflow: expected c0 reset before jump, got {reprStr st.regs.c0}")
        else if !st.stack.isEmpty then
          throw (IO.userError
            s!"ret/delegates-jump-underflow: expected empty stack after count pop, got {reprStr st.stack}")
        else
          pure () }
  ]
  oracle := #[
    -- Non-positive counts: REPEATEND reduces to RET.
    mkCase "ret/zero/default" #[intV 0],
    mkCase "ret/neg1/default" #[intV (-1)],
    mkCase "ret/min-int32/default" #[intV minInt32],
    mkCase "ret/zero/deep-null-int" #[.null, intV 7, intV 0],
    mkCase "ret/neg5/deep-cell" #[.cell refCellA, intV (-5)],
    mkCase "ret/zero/deep-builder-tuple-slice" #[.builder Builder.empty, .tuple #[], .slice fullSliceB, intV 0],
    mkCase "ret/zero/trailing-push-skipped" #[intV 0] #[repeatEndInstr, .pushInt (.num 777)],
    mkCase "ret/zero/c0-quit1" #[intV 0] (progSetC0Quit1 repeatEndInstr),
    mkCase "ret/neg1/c0-quit1" #[intV (-1)] (progSetC0Quit1 repeatEndInstr),
    mkCase "ret/zero/c0-nargs1-underflow" #[intV 0] (progSetC0Nargs 1 repeatEndInstr),
    mkCase "ret/zero/c0-nargs1-success" #[intV 41, intV 0] (progSetC0Nargs 1 repeatEndInstr),
    mkCase "ret/neg1/c0-nargs2-underflow" #[intV 9, intV (-1)] (progSetC0Nargs 2 repeatEndInstr),

    -- Positive counts: loop body is current continuation tail.
    mkCase "repeat/count1/body-push7" #[intV 1] (progBodyPush repeatEndInstr 7),
    mkCase "repeat/count2/body-push7" #[intV 2] (progBodyPush repeatEndInstr 7),
    mkCase "repeat/count3/body-push7" #[intV 3] (progBodyPush repeatEndInstr 7),
    mkCase "repeat/count4/body-push-neg3" #[intV 4] (progBodyPush repeatEndInstr (-3)),
    mkCase "repeat/count2/deep-below-preserve" #[.null, intV 5, intV 2] (progBodyPush repeatEndInstr 13),
    mkCase "repeat/count3/body-add" #[intV 3] (progBodyAdd repeatEndInstr 2 3),
    mkCase "repeat/count2/body-add-with-below" #[.cell refCellB, intV 2] (progBodyAdd repeatEndInstr 8 (-3)),
    mkCase "repeat/count1/body-retalt" #[intV 1] (progBodyRetAlt repeatEndInstr),
    mkCase "repeat/count2/body-retalt" #[intV 2] (progBodyRetAlt repeatEndInstr),
    mkCase "repeat/count3/body-ret" #[intV 3] (progBodyRet repeatEndInstr),
    mkCase "repeat/count1/body-empty" #[intV 1] #[repeatEndInstr],
    mkCase "repeat/count2/body-empty" #[intV 2] #[repeatEndInstr],
    mkCase "repeat/count1/c0-quit1-after" #[intV 1] (progSetC0Quit1 repeatEndInstr #[.pushInt (.num 4)]),
    mkCase "repeat/count2/c0-quit1-after" #[intV 2] (progSetC0Quit1 repeatEndInstr #[.pushInt (.num 4)]),
    mkCase "repeat/count1/c0-nargs1-underflow-after" #[intV 1] (progSetC0Nargs 1 repeatEndInstr),
    mkCase "repeat/count1/c0-nargs1-success-after" #[intV 55, intV 1] (progSetC0Nargs 1 repeatEndInstr),
    mkCase "repeat/count2/c0-nargs2-underflow-after" #[intV 55, intV 2] (progSetC0Nargs 2 repeatEndInstr),

    -- Error branches from pop_smallint_range.
    mkCase "err/underflow-empty" #[],
    mkCase "err/type-top-null" #[.null],
    mkCase "err/type-top-cell" #[.cell refCellA],
    mkCase "err/type-top-builder" #[.builder Builder.empty],
    mkCase "err/range-nan-via-program" #[] #[.pushInt .nan, repeatEndInstr],
    mkCase "err/range-too-large" #[intV int32TooLarge],
    mkCase "err/range-too-small" #[intV int32TooSmall],

    -- Related VM op branch: REPEATENDBRK.
    mkCase "brk/count1/body-retalt-break" #[intV 1] (progBodyRetAlt repeatEndBrkInstr),
    mkCase "brk/count3/body-retalt-break" #[intV 3] (progBodyRetAlt repeatEndBrkInstr),
    mkCase "brk/count2/body-push7" #[intV 2] (progBodyPush repeatEndBrkInstr 7),
    mkCase "brk/count1/c0-quit1-after" #[intV 1] (progSetC0Quit1 repeatEndBrkInstr #[.pushInt (.num 6)]),
    mkCase "brk/zero-ret" #[intV 0] #[repeatEndBrkInstr],
    mkCase "brk/neg1-ret" #[intV (-1)] #[repeatEndBrkInstr],
    mkCase "brk/type-top-null" #[.null] #[repeatEndBrkInstr],
    mkCase "brk/range-too-large" #[intV int32TooLarge] #[repeatEndBrkInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.REPEATEND
