import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETALTCTR

private def setAltCtrId : InstrId := { name := "SETALTCTR" }
private def setAltCtr (idx : Nat) : Instr := .contExt (.setAltCtr idx)

private def dispatchSentinel : Int := 49741

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q9 : Continuation := .quit 9

private def q0V : Value := .cont q0

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def fullSliceA : Slice := Slice.ofCell cellA

private def noiseA : Array Value :=
  #[.null, intV 7]

private def noiseB : Array Value :=
  #[.cell cellA, .builder Builder.empty]

private def tupleKeep : Array Value :=
  #[intV 42, .null]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def setAltTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def setAltTruncated15 : Cell :=
  Cell.mkOrdinary (natToBits (0xed80 >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr) : OracleCase :=
  { name := name
    instr := setAltCtrId
    program := program
    initStack := stack }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell) : OracleCase :=
  { name := name
    instr := setAltCtrId
    codeCell? := some codeCell
    initStack := stack }

private def progSetAlt (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[setAltCtr idx] ++ tail

private def runSetAltDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt (setAltCtr idx) stack

private def runSetAltFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSetAltRaw
    (idx : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, regs := regs }
  (execInstrContChangeExt (setAltCtr idx) (pure ())).run st0

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

private def assertCdataEmpty (label : String) (cdata : OrdCdata) : IO Unit := do
  if cdata.nargs != -1 then
    throw (IO.userError s!"{label}: expected cdata.nargs = -1, got {cdata.nargs}")
  else if !cdata.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty cdata.stack, got {reprStr cdata.stack}")
  else
    pure ()

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

private def expectDecodeSetAltCtr
    (label : String)
    (code : Cell)
    (idx : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  let expectedInstr := setAltCtr idx
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def setAltCtrOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/flow/",
    "ok/redefine/",
    "ok/raw/",
    "err/flow/",
    "err/underflow/",
    "err/type/",
    "err/order/",
    "err/redefine/",
    "err/raw/"
  ]

private def setAltCtrFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := setAltCtrOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success over supported index classes.
  mkCase "ok/basic/idx0-cont" #[q0V] (progSetAlt 0),
  mkCase "ok/basic/idx1-cont" #[q0V] (progSetAlt 1),
  mkCase "ok/basic/idx2-cont" #[q0V] (progSetAlt 2),
  mkCase "ok/basic/idx3-cont" #[q0V] (progSetAlt 3),
  mkCase "ok/basic/idx4-cell" #[.cell cellA] (progSetAlt 4),
  mkCase "ok/basic/idx5-cell" #[.cell cellB] (progSetAlt 5),
  mkCase "ok/basic/idx7-tuple" #[.tuple #[]] (progSetAlt 7),
  mkCase "ok/basic/idx0-noise-a" (noiseA ++ #[q0V]) (progSetAlt 0),
  mkCase "ok/basic/idx4-noise-b" (noiseB ++ #[.cell cellA]) (progSetAlt 4),
  mkCase "ok/basic/idx7-noise-a" (noiseA ++ #[.tuple #[]]) (progSetAlt 7),
  mkCase "ok/basic/idx3-noise-b" (noiseB ++ #[q0V]) (progSetAlt 3),

  -- Control flow: SETALTCTR is non-jumping.
  mkCase "ok/flow/tail-push-runs" #[q0V] (progSetAlt 0 #[.pushInt (.num 7)]),
  mkCase "ok/flow/tail-add-runs" #[intV 2, intV 3, q0V] (progSetAlt 0 #[.add]),
  mkCase "err/flow/tail-add-underflow" #[q0V] (progSetAlt 0 #[.add]),
  mkCase "ok/flow/tail-pushctr1-runs" #[q0V] (progSetAlt 0 #[.pushCtr 1]),
  mkCase "ok/flow/tail-popctr1-runs" #[q0V, q0V] (progSetAlt 0 #[.pushCtr 1, .popCtr 1]),

  -- Underflow/type errors.
  mkCase "err/underflow/empty" #[] (progSetAlt 0),
  mkCase "err/type/idx0-int" #[intV 1] (progSetAlt 0),
  mkCase "err/type/idx0-null" #[.null] (progSetAlt 0),
  mkCase "err/type/idx0-cell" #[.cell cellA] (progSetAlt 0),
  mkCase "err/type/idx0-slice" #[.slice fullSliceA] (progSetAlt 0),
  mkCase "err/type/idx0-builder" #[.builder Builder.empty] (progSetAlt 0),
  mkCase "err/type/idx0-tuple" #[.tuple #[]] (progSetAlt 0),
  mkCase "err/type/idx4-cont" #[q0V] (progSetAlt 4),
  mkCase "err/type/idx4-int" #[intV 4] (progSetAlt 4),
  mkCase "err/type/idx5-null" #[.null] (progSetAlt 5),
  mkCase "err/type/idx7-cont" #[q0V] (progSetAlt 7),
  mkCase "err/type/idx7-cell" #[.cell cellA] (progSetAlt 7),
  mkCase "err/type/idx7-int" #[intV 7] (progSetAlt 7),
  mkCase "err/type/idx7-builder" #[.builder Builder.empty] (progSetAlt 7),
  mkCase "err/type/nan-via-program" #[] #[.pushInt .nan, setAltCtr 0],
  mkCase "err/order/top-first-idx0" #[q0V, .null] (progSetAlt 0),
  mkCase "err/order/top-first-idx4" #[.cell cellA, q0V] (progSetAlt 4),

  -- Re-definition behavior.
  mkCase "err/redefine/idx0-twice" #[q0V, q0V] #[setAltCtr 0, setAltCtr 0],
  mkCase "err/redefine/idx1-twice" #[q0V, q0V] #[setAltCtr 1, setAltCtr 1],
  mkCase "err/redefine/idx4-twice" #[.cell cellA, .cell cellA] #[setAltCtr 4, setAltCtr 4],
  mkCase "err/redefine/idx5-twice" #[.cell cellA, .cell cellA] #[setAltCtr 5, setAltCtr 5],
  mkCase "ok/redefine/idx7-twice" #[.tuple #[], .tuple #[]] #[setAltCtr 7, setAltCtr 7],
  mkCase "ok/redefine/idx7-twice-tail" #[.tuple #[], .tuple #[]]
    #[setAltCtr 7, setAltCtr 7, .pushInt (.num 9)],

  -- Raw decode boundaries.
  mkRawCase "ok/raw/opcode-ed80-idx0" #[q0V] (rawOp16 0xed80),
  mkRawCase "ok/raw/opcode-ed85-idx5" #[.cell cellA] (rawOp16 0xed85),
  mkRawCase "ok/raw/opcode-ed87-idx7" #[.tuple #[]] (rawOp16 0xed87),
  mkRawCase "err/raw/opcode-hole-ed86" #[q0V] (rawOp16 0xed86),
  mkRawCase "err/raw/opcode-near-ed88" #[q0V] (rawOp16 0xed88),
  mkRawCase "err/raw/opcode-near-ed7f" #[q0V] (rawOp16 0xed7f),
  mkRawCase "err/raw/opcode-truncated-8" #[q0V] setAltTruncated8,
  mkRawCase "err/raw/opcode-truncated-15" #[q0V] setAltTruncated15
]

def suite : InstrSuite where
  id := setAltCtrId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSetAltFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-idx0"
          (runSetAltFallback (setAltCtr 0) #[q0V])
          #[] }
    ,
    { name := "unit/errors/underflow-type-and-direct-idx6"
      run := do
        expectErr "underflow/empty" (runSetAltDirect 0 #[]) .stkUnd
        expectErr "type/idx0-int" (runSetAltDirect 0 #[intV 1]) .typeChk
        expectErr "type/idx4-cont" (runSetAltDirect 4 #[q0V]) .typeChk
        expectErr "type/idx7-int" (runSetAltDirect 7 #[intV 7]) .typeChk
        expectErr "direct/idx6-typechk" (runSetAltDirect 6 #[q0V]) .typeChk }
    ,
    { name := "unit/order/type-error-after-pop"
      run := do
        let st ← expectRawErr "order/type-after-pop"
          (runSetAltRaw 0 #[q0V, .null]) .typeChk
        if st.stack != #[q0V] then
          throw (IO.userError
            s!"order/type-after-pop: expected stack #[q0], got {reprStr st.stack}")
        else
          match st.regs.c1 with
          | .quit n =>
              if n != 1 then
                throw (IO.userError
                  s!"order/type-after-pop: expected c1=quit1, got quit{n}")
              else
                pure ()
          | _ =>
              throw (IO.userError
                s!"order/type-after-pop: expected c1 quit1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/raw/force-cdata-wraps-c1"
      run := do
        let regs : Regs := { Regs.initial with c1 := q9 }
        let st ← expectRawOk "raw/force-cdata-wraps-c1"
          (runSetAltRaw 0 #[q0V] regs)
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"raw/force-cdata-wraps-c1: expected empty stack, got {reprStr st.stack}")
        else
          match st.regs.c1 with
          | .envelope ext cregs cdata =>
              if ext != q9 then
                throw (IO.userError
                  s!"raw/force-cdata-wraps-c1: expected ext quit9, got {reprStr ext}")
              else if cregs.c0 != some q0 then
                throw (IO.userError
                  s!"raw/force-cdata-wraps-c1: expected c0=quit0, got {reprStr cregs.c0}")
              else if cregs.c1.isSome || cregs.c2.isSome || cregs.c3.isSome
                  || cregs.c4.isSome || cregs.c5.isSome || cregs.c7.isSome then
                throw (IO.userError
                  s!"raw/force-cdata-wraps-c1: unexpected extra cregs {reprStr cregs}")
              else
                assertCdataEmpty "raw/force-cdata-wraps-c1" cdata
          | _ =>
              throw (IO.userError
                s!"raw/force-cdata-wraps-c1: expected envelope c1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/raw/redefine-c0-fails-and-preserves-c1"
      run := do
        let preC1 : Continuation :=
          .envelope q9 ({ OrdCregs.empty with c0 := some q1 }) OrdCdata.empty
        let regs : Regs := { Regs.initial with c1 := preC1 }
        let st ← expectRawErr "raw/redefine-c0-fails"
          (runSetAltRaw 0 #[q0V] regs) .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"raw/redefine-c0-fails: expected empty stack, got {reprStr st.stack}")
        else
          match st.regs.c1 with
          | .envelope ext cregs cdata =>
              if ext != q9 then
                throw (IO.userError
                  s!"raw/redefine-c0-fails: expected ext quit9, got {reprStr ext}")
              else if cregs.c0 != some q1 then
                throw (IO.userError
                  s!"raw/redefine-c0-fails: expected preserved c0=quit1, got {reprStr cregs.c0}")
              else
                assertCdataEmpty "raw/redefine-c0-fails" cdata
          | _ =>
              throw (IO.userError
                s!"raw/redefine-c0-fails: expected envelope c1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/raw/idx7-keeps-existing-c7"
      run := do
        let preC1 : Continuation :=
          .envelope q9 ({ OrdCregs.empty with c7 := some tupleKeep }) OrdCdata.empty
        let regs : Regs := { Regs.initial with c1 := preC1 }
        let st ← expectRawOk "raw/idx7-keeps-existing-c7"
          (runSetAltRaw 7 #[.tuple #[]] regs)
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"raw/idx7-keeps-existing-c7: expected empty stack, got {reprStr st.stack}")
        else
          match st.regs.c1 with
          | .envelope ext cregs cdata =>
              if ext != q9 then
                throw (IO.userError
                  s!"raw/idx7-keeps-existing-c7: expected ext quit9, got {reprStr ext}")
              else if cregs.c7 != some tupleKeep then
                throw (IO.userError
                  s!"raw/idx7-keeps-existing-c7: expected c7={reprStr tupleKeep}, got {reprStr cregs.c7}")
              else
                assertCdataEmpty "raw/idx7-keeps-existing-c7" cdata
          | _ =>
              throw (IO.userError
                s!"raw/idx7-keeps-existing-c7: expected envelope c1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/decode/opcode-and-truncation"
      run := do
        expectDecodeSetAltCtr "decode/ed80" (rawOp16 0xed80) 0
        expectDecodeSetAltCtr "decode/ed85" (rawOp16 0xed85) 5
        expectDecodeSetAltCtr "decode/ed87" (rawOp16 0xed87) 7
        expectDecodeErr "decode/hole-ed86" (rawOp16 0xed86) .invOpcode
        expectDecodeErr "decode/near-ed88" (rawOp16 0xed88) .invOpcode
        expectDecodeErr "decode/near-ed7f" (rawOp16 0xed7f) .invOpcode
        expectDecodeErr "decode/truncated-8" setAltTruncated8 .invOpcode
        expectDecodeErr "decode/truncated-15" setAltTruncated15 .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile setAltCtrId setAltCtrFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SETALTCTR
