import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.RETALT

private def retAltId : InstrId := { name := "RETALT" }

private def retAltInstr : Instr := .retAlt

private def dispatchSentinel : Int := 49123

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def fullSliceA : Slice :=
  Slice.ofCell cellA

private def fullSliceB : Slice :=
  Slice.ofCell cellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[.cont (.quit 0), .null, intV (-4), .cell cellB]

private def c1NeedArgs (n : Int) : Continuation :=
  .envelope (.quit 0) OrdCregs.empty { stack := #[], nargs := n }

private def c1Captured (captured : Array Value) (nargs : Int) : Continuation :=
  .envelope (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def runRetAltFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowRetAlt instr (VM.push (intV dispatchSentinel)) stack

private def runRetAltRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc)
    (instr : Instr := retAltInstr) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowRetAlt instr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

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

private def expectDecodeRetAlt
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .retAlt then
        throw (IO.userError s!"{label}: expected .retAlt, got {reprStr instr}")
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
    (program : Array Instr := #[retAltInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retAltId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retAltId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC1FromC0 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .popCtr 1, .retAlt] ++ tail

private def progSetC1Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num n), .setNumVarArgs, .popCtr 1, .retAlt] ++ tail

private def progSetC1Captured (capture : Int) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 0, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 1,
    .retAlt] ++ tail

private def retAltTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def retAltTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xdb31 >>> 1) 15) #[]

def suite : InstrSuite where
  id := retAltId
  unit := #[
    { name := "unit/dispatch/retalt-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runRetAltFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]

        let st ← expectRawOk "dispatch/matched-retalt"
          (runRetAltRaw #[intV 5])
        if st.stack != #[intV 5] then
          throw (IO.userError
            s!"dispatch/matched-retalt: expected unchanged stack [5], got {reprStr st.stack}")
        if st.cc != .quit 1 then
          throw (IO.userError s!"dispatch/matched-retalt: expected cc=quit1, got {reprStr st.cc}")
        if st.regs.c1 != .quit 1 then
          throw (IO.userError s!"dispatch/matched-retalt: expected c1 reset to quit1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/order/c1-reset-before-jump-underflow"
      run := do
        let target : Continuation := c1NeedArgs 2
        let regs : Regs := { Regs.initial with c1 := target }
        let st ← expectRawErr "retalt/jump-underflow"
          (runRetAltRaw #[intV 9] regs) .stkUnd
        if st.stack != #[intV 9] then
          throw (IO.userError s!"retalt/jump-underflow: expected stack [9], got {reprStr st.stack}")
        if st.cc != defaultCc then
          throw (IO.userError s!"retalt/jump-underflow: expected cc unchanged, got {reprStr st.cc}")
        if st.regs.c1 != .quit 1 then
          throw (IO.userError s!"retalt/jump-underflow: expected c1 reset to quit1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/raw/closure-stack-merge-path"
      run := do
        let target : Continuation := c1Captured #[intV 100] 1
        let regs : Regs := { Regs.initial with c1 := target }
        let st ← expectRawOk "retalt/closure-stack-merge"
          (runRetAltRaw #[intV 4, intV 5] regs)
        if st.stack != #[intV 100, intV 5] then
          throw (IO.userError
            s!"retalt/closure-stack-merge: expected [100,5], got {reprStr st.stack}")
        if st.cc != target then
          throw (IO.userError
            s!"retalt/closure-stack-merge: expected jump to target continuation, got {reprStr st.cc}")
        if st.regs.c1 != .quit 1 then
          throw (IO.userError
            s!"retalt/closure-stack-merge: expected c1 reset to quit1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/opcode/decode-and-truncated-prefix"
      run := do
        let assembled ←
          match assembleCp0 [retAltInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/retalt failed: {reprStr e}")
        if assembled.bits = natToBits 0xdb31 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/retalt: expected 0xdb31, got {reprStr assembled.bits}")

        expectDecodeRetAlt "decode/retalt" (Cell.mkOrdinary (natToBits 0xdb31 16) #[])
        expectDecodeErr "decode/truncated-8" retAltTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" retAltTruncated15Code .invOpcode }
  ]
  oracle := #[
    -- Basic RETALT with default c1=quit1.
    mkCase "ok/basic/empty" #[],
    mkCase "ok/basic/int" #[intV 5],
    mkCase "ok/basic/null-int" #[.null, intV 9],
    mkCase "ok/basic/cell" #[.cell cellA],
    mkCase "ok/basic/slice" #[.slice fullSliceB],
    mkCase "ok/basic/builder" #[.builder Builder.empty],
    mkCase "ok/basic/tuple-empty" #[.tuple #[]],
    mkCase "ok/basic/cont-quit0" #[.cont (.quit 0)],
    mkCase "ok/basic/noise-a" noiseA,
    mkCase "ok/basic/noise-b" noiseB,
    mkCase "ok/basic/noise-c" noiseC,
    mkCase "ok/basic/trailing-push-skipped" #[intV 3] #[retAltInstr, .pushInt (.num 777)],
    mkCase "ok/basic/trailing-add-skipped" #[intV 6, intV 2] #[retAltInstr, .add],

    -- Retarget c1 from c0 (quit0), then RETALT.
    mkCase "ok/c1-from-c0/empty" #[] (progSetC1FromC0),
    mkCase "ok/c1-from-c0/int" #[intV 12] (progSetC1FromC0),
    mkCase "ok/c1-from-c0/noise-a" noiseA (progSetC1FromC0),
    mkCase "ok/c1-from-c0/noise-b" noiseB (progSetC1FromC0),
    mkCase "ok/c1-from-c0/trailing-push-skipped" #[intV 4] (progSetC1FromC0 #[.pushInt (.num 111)]),
    mkCase "ok/c1-from-c0/trailing-add-skipped"
      #[intV 1, intV 2] (progSetC1FromC0 #[.add]),

    -- c1 nargs branch coverage via SETNUMVARARGS.
    mkCase "ok/nargs0/empty" #[] (progSetC1Nargs 0),
    mkCase "ok/nargs0/noise-a" noiseA (progSetC1Nargs 0),
    mkCase "err/nargs1/empty-underflow" #[] (progSetC1Nargs 1),
    mkCase "ok/nargs1/one-int" #[intV 33] (progSetC1Nargs 1),
    mkCase "ok/nargs1/one-null" #[.null] (progSetC1Nargs 1),
    mkCase "err/nargs2/empty-underflow" #[] (progSetC1Nargs 2),
    mkCase "err/nargs2/one-underflow" #[intV 44] (progSetC1Nargs 2),
    mkCase "ok/nargs2/two-int" #[intV 4, intV 5] (progSetC1Nargs 2),
    mkCase "ok/nargs2/two-noise" #[.null, intV 5] (progSetC1Nargs 2),
    mkCase "err/nargs3/two-underflow" #[intV 2, intV 3] (progSetC1Nargs 3),
    mkCase "ok/nargs3/three-int" #[intV 1, intV 2, intV 3] (progSetC1Nargs 3),
    mkCase "ok/nargs1/trailing-skipped" #[intV 7] (progSetC1Nargs 1 #[.pushInt (.num 999)]),

    -- c1 closure-stack merge coverage via SETCONTVARARGS(copy=1).
    mkCase "ok/captured/more0/empty-init" #[] (progSetC1Captured 72 0),
    mkCase "err/captured/more1/empty-underflow" #[] (progSetC1Captured 73 1),
    mkCase "ok/captured/more1/one-init" #[intV 9] (progSetC1Captured 74 1),
    mkCase "err/captured/more2/one-underflow" #[intV 9] (progSetC1Captured 75 2),
    mkCase "ok/captured/more2/two-init" #[intV 1, intV 2] (progSetC1Captured 76 2),
    mkCase "ok/captured/more0/noise-init" noiseA (progSetC1Captured 77 0),
    mkCase "ok/captured/more0/trailing-skipped" #[intV 4]
      (progSetC1Captured 78 0 #[.pushInt (.num 1234)]),
    mkCase "ok/captured/more1/two-init" #[intV 8, intV 9] (progSetC1Captured 79 1),

    -- Decode errors around RETALT prefix width.
    mkCaseCode "err/decode/truncated-8-prefix" #[] retAltTruncated8Code,
    mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] retAltTruncated15Code
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.RETALT
