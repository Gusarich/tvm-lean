import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.RETDATA

private def retDataId : InstrId := { name := "RETDATA" }

private def retDataInstr : Instr := .retData

private def dispatchSentinel : Int := 49057

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def fullSliceB : Slice :=
  Slice.ofCell cellB

private def partialSliceB : Slice :=
  { cell := cellB, bitPos := 2, refPos := 1 }

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice fullSliceB, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[.cell cellB, .null, intV (-4), .builder Builder.empty]

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def c0NeedArgs (n : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := n }

private def c0Captured (captured : Array Value) (nargs : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := captured, nargs := nargs }

private def runRetDataFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowRetData instr (VM.push (intV dispatchSentinel)) stack

private def runRetDataRaw
    (stack : Array Value)
    (cc : Continuation := mkOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1)
    (instr : Instr := retDataInstr) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowRetData instr (pure ())).run st0

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

private def expectDecodeRetData
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .retData then
        throw (IO.userError s!"{label}: expected .retData, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[retDataInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retDataId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retDataId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC0FromC1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, .retData] ++ tail

private def progSetC0Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, .retData] ++ tail

private def progSetC0Captured (capture : Int) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 0,
    .retData] ++ tail

private def retDataTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def retDataTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xdb3f >>> 1) 15) #[]

def suite : InstrSuite where
  id := retDataId
  unit := #[
    { name := "unit/dispatch/retdata-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runRetDataFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]

        let st ← expectRawOk "dispatch/matched-retdata"
          (runRetDataRaw #[intV 5] (mkOrdCont partialSliceB))
        if st.cc != .quit 0 then
          throw (IO.userError s!"dispatch/matched-retdata: expected cc=quit0, got {reprStr st.cc}")
        match st.stack.back? with
        | some (.slice s) =>
            if s != partialSliceB then
              throw (IO.userError
                s!"dispatch/matched-retdata: pushed slice mismatch {reprStr s}")
        | some v =>
            throw (IO.userError s!"dispatch/matched-retdata: expected pushed slice, got {reprStr v}")
        | none =>
            throw (IO.userError "dispatch/matched-retdata: expected non-empty stack") }
    ,
    { name := "unit/order/push-before-ret-satisfies-nargs1"
      run := do
        let c0Need1 := c0NeedArgs 1
        let st ← expectRawOk "order/push-before-ret-satisfies-nargs1"
          (runRetDataRaw #[] (mkOrdCont partialSliceB) c0Need1)
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"order/push-before-ret-satisfies-nargs1: expected c0 reset to quit0, got {reprStr st.regs.c0}")
        else if st.cc != c0Need1 then
          throw (IO.userError
            s!"order/push-before-ret-satisfies-nargs1: expected jump target c0, got {reprStr st.cc}")
        else if st.stack != #[.slice partialSliceB] then
          throw (IO.userError
            s!"order/push-before-ret-satisfies-nargs1: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/push-before-ret-underflow-nargs2-and-c0-reset"
      run := do
        let c0Need2 := c0NeedArgs 2
        let st ← expectRawErr "order/push-before-ret-underflow-nargs2"
          (runRetDataRaw #[] (mkOrdCont partialSliceB) c0Need2) .stkUnd
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"order/push-before-ret-underflow-nargs2: expected c0 reset, got {reprStr st.regs.c0}")
        else if st.cc != mkOrdCont partialSliceB then
          throw (IO.userError
            s!"order/push-before-ret-underflow-nargs2: expected cc unchanged on jump error, got {reprStr st.cc}")
        else if st.stack != #[.slice partialSliceB] then
          throw (IO.userError
            s!"order/push-before-ret-underflow-nargs2: expected pushed slice before error, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/non-ordinary-cc-fails-before-ret"
      run := do
        let c0Need2 := c0NeedArgs 2
        let st ← expectRawErr "order/non-ordinary-cc-fails-before-ret"
          (runRetDataRaw #[intV 9] (.quit 7) c0Need2) .typeChk
        if st.regs.c0 != c0Need2 then
          throw (IO.userError
            s!"order/non-ordinary-cc-fails-before-ret: expected c0 unchanged, got {reprStr st.regs.c0}")
        else if st.stack != #[intV 9] then
          throw (IO.userError
            s!"order/non-ordinary-cc-fails-before-ret: expected stack unchanged, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/pushes-exact-current-code-slice"
      run := do
        let st ← expectRawOk "pushes-exact-current-code-slice"
          (runRetDataRaw #[intV 42] (mkOrdCont partialSliceB) (.quit 9))
        if st.cc != .quit 9 then
          throw (IO.userError s!"pushes-exact-current-code-slice: expected cc=quit9, got {reprStr st.cc}")
        else if st.stack != #[intV 42, .slice partialSliceB] then
          throw (IO.userError
            s!"pushes-exact-current-code-slice: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/ret-jump/closure-stack-merge"
      run := do
        let c0Cap := c0Captured #[intV 100] (-1)
        let st ← expectRawOk "ret-jump/closure-stack-merge"
          (runRetDataRaw #[intV 7] (mkOrdCont partialSliceB) c0Cap)
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"ret-jump/closure-stack-merge: expected c0 reset, got {reprStr st.regs.c0}")
        else if st.stack != #[intV 100, intV 7, .slice partialSliceB] then
          throw (IO.userError
            s!"ret-jump/closure-stack-merge: stack mismatch {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/decode/retdata-and-truncated-prefix"
      run := do
        expectDecodeRetData "decode/retdata" (Cell.mkOrdinary (natToBits 0xdb3f 16) #[])
        expectDecodeErr "decode/truncated-8" retDataTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" retDataTruncated15Code .invOpcode }
  ]
  oracle := #[
    -- Basic RETDATA behavior: push remaining code and return to c0.
    mkCase "ok/basic/empty" #[],
    mkCase "ok/basic/int-prefix" #[intV 5],
    mkCase "ok/basic/null-int-prefix" #[.null, intV 9],
    mkCase "ok/basic/cell-prefix" #[.cell cellA],
    mkCase "ok/basic/slice-prefix" #[.slice fullSliceB],
    mkCase "ok/basic/builder-prefix" #[.builder Builder.empty],
    mkCase "ok/basic/tuple-prefix" #[.tuple #[]],
    mkCase "ok/basic/noise-a" noiseA,
    mkCase "ok/basic/noise-b" noiseB,
    mkCase "ok/basic/noise-c" noiseC,
    mkCase "ok/basic/trailing-push-skipped" #[] #[retDataInstr, .pushInt (.num 777)],
    mkCase "ok/basic/trailing-add-skipped" #[intV 6] #[retDataInstr, .pushInt (.num 2), .pushInt (.num 3), .add],

    -- Retarget c0 to c1 (quit1), still via RETDATA.
    mkCase "ok/c0-from-c1/basic" #[] (progSetC0FromC1),
    mkCase "ok/c0-from-c1/prefix-int" #[intV 12] (progSetC0FromC1),
    mkCase "ok/c0-from-c1/prefix-noise" noiseA (progSetC0FromC1),
    mkCase "ok/c0-from-c1/trailing-push-skipped" #[] (progSetC0FromC1 #[.pushInt (.num 111)]),
    mkCase "ok/c0-from-c1/trailing-add-skipped"
      #[intV 1] (progSetC0FromC1 #[.pushInt (.num 2), .pushInt (.num 3), .add]),

    -- c0 nargs branch coverage (RET jump checks happen after push_code side effect).
    mkCase "ok/nargs0/empty" #[] (progSetC0Nargs 0),
    mkCase "ok/nargs0/prefix-int-null" #[intV 7, .null] (progSetC0Nargs 0),
    mkCase "ok/nargs1/empty" #[] (progSetC0Nargs 1),
    mkCase "ok/nargs1/prefix-int" #[intV 33] (progSetC0Nargs 1),
    mkCase "ok/nargs1/prefix-noise" noiseB (progSetC0Nargs 1),
    mkCase "err/nargs2/empty-underflow" #[] (progSetC0Nargs 2),
    mkCase "ok/nargs2/one-int" #[intV 44] (progSetC0Nargs 2),
    mkCase "ok/nargs2/two-noise" #[.null, intV 5] (progSetC0Nargs 2),
    mkCase "err/nargs3/one-int-underflow" #[intV 55] (progSetC0Nargs 3),
    mkCase "ok/nargs3/two-int" #[intV 2, intV 3] (progSetC0Nargs 3),
    mkCase "ok/nargs1/trailing-skipped" #[intV 7] (progSetC0Nargs 1 #[.pushInt (.num 999)]),

    -- c0 closure-stack merge branch (nargs + captured stack from SETCONTVARARGS).
    mkCase "ok/captured/more0-empty-init" #[] (progSetC0Captured 72 0),
    mkCase "ok/captured/more1-empty-init" #[] (progSetC0Captured 73 1),
    mkCase "err/captured/more2-underflow" #[] (progSetC0Captured 74 2),
    mkCase "ok/captured/more2-one-init" #[intV 9] (progSetC0Captured 75 2),
    mkCase "ok/captured/more2-two-init" #[intV 1, intV 2] (progSetC0Captured 76 2),
    mkCase "ok/captured/more0-trailing-skipped" #[intV 4]
      (progSetC0Captured 77 0 #[.pushInt (.num 1234)]),

    -- Decode errors around RETDATA prefix width.
    mkCaseCode "err/decode/truncated-8-prefix" #[] retDataTruncated8Code,
    mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] retDataTruncated15Code
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.RETDATA
