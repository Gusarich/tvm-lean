import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETRETCTR

private def setRetCtrId : InstrId := { name := "SETRETCTR" }
private def setRetCtrInstr (idx : Nat) : Instr := .contExt (.setRetCtr idx)

private def dispatchSentinel : Int := 49129

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def tupleA : Array Value := #[intV 99, .null]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def setRetCtrTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def setRetCtrTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xed70 >>> 1) 15) #[]

private def runSetRetCtrDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt (setRetCtrInstr idx) stack

private def runSetRetCtrFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSetRetCtrRaw
    (idx : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, regs := regs }
  (execInstrContChangeExt (setRetCtrInstr idx) (pure ())).run st0

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

private def expectDecodeSetRetCtr
    (label : String)
    (code : Cell)
    (expectedIdx : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != setRetCtrInstr expectedIdx then
        throw (IO.userError
          s!"{label}: expected {reprStr (setRetCtrInstr expectedIdx)}, got {reprStr instr}")
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
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setRetCtrId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setRetCtrId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetRet (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[setRetCtrInstr idx] ++ tail

private def progSetRet2 (idx1 idx2 : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[setRetCtrInstr idx1, setRetCtrInstr idx2] ++ tail

private def setRetCtrOracleFamilies : Array String :=
  #[
    "ok/index/",
    "ok/flow/",
    "ok/reapply/",
    "ok/raw/",
    "err/underflow/",
    "err/value-type/",
    "err/redefine/",
    "err/order/",
    "err/raw/"
  ]

private def setRetCtrFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := setRetCtrOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success matrix.
  mkCase "ok/index/idx0-basic" #[q0] (progSetRet 0),
  mkCase "ok/index/idx1-basic" #[q0] (progSetRet 1),
  mkCase "ok/index/idx2-basic" #[q0] (progSetRet 2),
  mkCase "ok/index/idx3-basic" #[q0] (progSetRet 3),
  mkCase "ok/index/idx4-cell" #[.cell cellA] (progSetRet 4),
  mkCase "ok/index/idx5-cell" #[.cell cellB] (progSetRet 5),
  mkCase "ok/index/idx7-empty-tuple" #[.tuple #[]] (progSetRet 7),
  mkCase "ok/index/idx0-noise" #[.null, intV 7, q0] (progSetRet 0),
  mkCase "ok/index/idx4-noise" #[intV 9, .cell cellA] (progSetRet 4),
  mkCase "ok/index/idx5-noise" #[.cell cellA, .cell cellB] (progSetRet 5),
  mkCase "ok/index/idx7-noise" #[intV 11, .cell cellB, .tuple #[]] (progSetRet 7),
  mkCase "ok/flow/tail-runs-after-setret4"
    #[intV 2, intV 3, .cell cellA] (progSetRet 4 #[.add]),
  mkCase "ok/reapply/different-idx4-idx5"
    #[.cell cellA, .cell cellB] (progSetRet2 4 5),
  mkCase "ok/reapply/idx7-second-define-allowed"
    #[.tuple #[], .tuple #[]] (progSetRet2 7 7),

  -- Underflow.
  mkCase "err/underflow/idx0-empty" #[] (progSetRet 0),
  mkCase "err/underflow/idx4-empty" #[] (progSetRet 4),
  mkCase "err/underflow/second-setret-after-first-success"
    #[q0] (progSetRet2 0 0),

  -- Value-type failures by index class.
  mkCase "err/value-type/idx0-int" #[intV 5] (progSetRet 0),
  mkCase "err/value-type/idx0-null" #[.null] (progSetRet 0),
  mkCase "err/value-type/idx1-cell" #[.cell cellA] (progSetRet 1),
  mkCase "err/value-type/idx2-empty-tuple" #[.tuple #[]] (progSetRet 2),
  mkCase "err/value-type/idx3-builder" #[.builder Builder.empty] (progSetRet 3),
  mkCase "err/value-type/idx4-cont" #[q0] (progSetRet 4),
  mkCase "err/value-type/idx4-int" #[intV 9] (progSetRet 4),
  mkCase "err/value-type/idx5-null" #[.null] (progSetRet 5),
  mkCase "err/value-type/idx5-empty-tuple" #[.tuple #[]] (progSetRet 5),
  mkCase "err/value-type/idx5-cont" #[q0] (progSetRet 5),
  mkCase "err/value-type/idx7-cont" #[q0] (progSetRet 7),
  mkCase "err/value-type/idx7-cell" #[.cell cellA] (progSetRet 7),
  mkCase "err/value-type/idx7-null" #[.null] (progSetRet 7),
  mkCase "err/value-type/idx7-int" #[intV 3] (progSetRet 7),
  mkCase "err/value-type/idx0-nan-via-program" #[] #[.pushInt .nan, setRetCtrInstr 0],

  -- Re-define failures (`define` for c0..c5 is single-assignment).
  mkCase "err/redefine/idx0-second-fails" #[q0, q0] (progSetRet2 0 0),
  mkCase "err/redefine/idx1-second-fails" #[q0, q0] (progSetRet2 1 1),
  mkCase "err/redefine/idx2-second-fails" #[q0, q0] (progSetRet2 2 2),
  mkCase "err/redefine/idx3-second-fails" #[q0, q0] (progSetRet2 3 3),
  mkCase "err/redefine/idx4-second-fails" #[.cell cellA, .cell cellB] (progSetRet2 4 4),
  mkCase "err/redefine/idx5-second-fails" #[.cell cellA, .cell cellB] (progSetRet2 5 5),

  -- Error ordering around pop/define.
  mkCase "err/order/type-after-pop-idx4"
    #[intV 55, intV 7] (progSetRet 4 #[.add]),
  mkCase "err/order/redefine-before-tail"
    #[q0, q0] (progSetRet2 0 0 #[.pushInt (.num 1)]),
  mkCase "err/order/underflow-after-first-success"
    #[q0] (progSetRet2 0 1),

  -- Raw opcode boundaries.
  mkCodeCase "ok/raw/opcode-ed70-idx0" #[q0] (rawOp16 0xed70),
  mkCodeCase "ok/raw/opcode-ed75-idx5" #[.cell cellA] (rawOp16 0xed75),
  mkCodeCase "ok/raw/opcode-ed77-idx7" #[.tuple #[]] (rawOp16 0xed77),
  mkCodeCase "err/raw/opcode-ed76-hole-c6" #[q0] (rawOp16 0xed76),
  mkCodeCase "err/raw/opcode-ed78-neighbor" #[q0] (rawOp16 0xed78),
  mkCodeCase "err/raw/opcode-ed6f-neighbor" #[q0] (rawOp16 0xed6f),
  mkCodeCase "err/raw/opcode-truncated8" #[q0] setRetCtrTruncated8Code,
  mkCodeCase "err/raw/opcode-truncated15" #[q0] setRetCtrTruncated15Code
]

def suite : InstrSuite where
  id := setRetCtrId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSetRetCtrFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-setret4"
          (runSetRetCtrFallback (setRetCtrInstr 4) #[.cell cellA])
          #[] }
    ,
    { name := "unit/decode/opcode-boundaries"
      run := do
        expectDecodeSetRetCtr "decode/ed70-idx0" (rawOp16 0xed70) 0
        expectDecodeSetRetCtr "decode/ed75-idx5" (rawOp16 0xed75) 5
        expectDecodeSetRetCtr "decode/ed77-idx7" (rawOp16 0xed77) 7
        expectDecodeErr "decode/ed76-hole-c6" (rawOp16 0xed76) .invOpcode
        expectDecodeErr "decode/ed78-neighbor" (rawOp16 0xed78) .invOpcode
        expectDecodeErr "decode/truncated8" setRetCtrTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated15" setRetCtrTruncated15Code .invOpcode }
    ,
    { name := "unit/order/underflow-before-any-mutation"
      run := do
        let st ← expectRawErr "underflow-before-mutation"
          (runSetRetCtrRaw 0 #[]) .stkUnd
        if st.stack != #[] then
          throw (IO.userError s!"underflow-before-mutation: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"underflow-before-mutation: expected c0=quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/order/typechk-pops-value-before-define"
      run := do
        let st ← expectRawErr "typechk-pops-value"
          (runSetRetCtrRaw 4 #[intV 55, intV 7]) .typeChk
        if st.stack != #[intV 55] then
          throw (IO.userError s!"typechk-pops-value: expected #[55], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/redefine-pops-second-value"
      run := do
        let st1 ← expectRawOk "redefine-step1" (runSetRetCtrRaw 0 #[q0, q0])
        let (res2, st2) := (execInstrContChangeExt (setRetCtrInstr 0) (pure ())).run st1
        match res2 with
        | .error e =>
            if e != .typeChk then
              throw (IO.userError s!"redefine-step2: expected typeChk, got {e}")
            else if st2.stack != #[] then
              throw (IO.userError s!"redefine-step2: expected empty stack, got {reprStr st2.stack}")
            else
              pure ()
        | .ok _ =>
            throw (IO.userError "redefine-step2: expected failure, got success") }
    ,
    { name := "unit/raw/force-cregs-wraps-quit0"
      run := do
        let st ← expectRawOk "force-cregs-wraps-quit0" (runSetRetCtrRaw 4 #[.cell cellA])
        match st.regs.c0 with
        | .envelope ext cregs cdata =>
            if ext != .quit 0 then
              throw (IO.userError s!"force-cregs: expected ext quit0, got {reprStr ext}")
            else if cregs.c4 != some cellA then
              throw (IO.userError s!"force-cregs: expected c4=cellA, got {reprStr cregs.c4}")
            else if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError s!"force-cregs: unexpected cdata {reprStr cdata}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"force-cregs: expected envelope c0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/idx7-define-keeps-existing-c7"
      run := do
        let preC0 : Continuation :=
          .envelope (.quit 0) ({ OrdCregs.empty with c7 := some tupleA }) OrdCdata.empty
        let regs1 : Regs := { Regs.initial with c0 := preC0 }
        let st ← expectRawOk "idx7-keep-existing-c7"
          (runSetRetCtrRaw 7 #[.tuple #[]] regs1)
        match st.regs.c0 with
        | .envelope _ cregs _ =>
            if cregs.c7 != some tupleA then
              throw (IO.userError
                s!"idx7-keep-existing-c7: expected c7={reprStr tupleA}, got {reprStr cregs.c7}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"idx7-keep-existing-c7: unexpected c0 {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/direct-ast-invalid-idx-maps-typechk"
      run := do
        let st6 ← expectRawErr "invalid-idx6" (runSetRetCtrRaw 6 #[q0]) .typeChk
        if st6.stack != #[] then
          throw (IO.userError s!"invalid-idx6: expected empty stack, got {reprStr st6.stack}")
        else
          pure ()
        let st8 ← expectRawErr "invalid-idx8" (runSetRetCtrRaw 8 #[q0]) .typeChk
        if st8.stack != #[] then
          throw (IO.userError s!"invalid-idx8: expected empty stack, got {reprStr st8.stack}")
        else
          pure () }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile setRetCtrId setRetCtrFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SETRETCTR
