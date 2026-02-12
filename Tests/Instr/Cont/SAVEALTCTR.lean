import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SAVEALTCTR

private def saveAltCtrId : InstrId := { name := "SAVEALTCTR" }
private def saveAltCtrInstr (idx : Nat) : Instr := .contExt (.saveAltCtr idx)

private def dispatchSentinel : Int := 51173

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q8 : Continuation := .quit 8
private def q9 : Continuation := .quit 9

private def q0V : Value := .cont q0
private def q8V : Value := .cont q8
private def q9V : Value := .cont q9

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def tupleKeep : Array Value :=
  #[intV 42, .null]

private def noiseA : Array Value :=
  #[intV 5, .null]

private def noiseB : Array Value :=
  #[.cell cellA, .builder Builder.empty]

private def noiseC : Array Value :=
  #[.slice (Slice.ofCell cellA), intV 11, .tuple #[]]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def saveAltCode0 : Cell := rawOp16 0xedb0
private def saveAltCode5 : Cell := rawOp16 0xedb5
private def saveAltCode7 : Cell := rawOp16 0xedb7
private def saveAltCodeHole6 : Cell := rawOp16 0xedb6
private def saveAltCodeUnassignedB8 : Cell := rawOp16 0xedb8
private def saveAltCodeNeighborAf : Cell := rawOp16 0xedaf

private def saveAltTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def saveAltTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedb0 >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := saveAltCtrId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := saveAltCtrId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSaveAlt (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[saveAltCtrInstr idx] ++ tail

private def progSaveAlt2 (idx1 idx2 : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[saveAltCtrInstr idx1, saveAltCtrInstr idx2] ++ tail

private def runSaveAltDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt (saveAltCtrInstr idx) stack

private def runSaveAltFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSaveAltRaw
    (instr : Instr)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (next : VM Unit := pure ()) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with stack := stack, regs := regs }
  (execInstrContChangeExt instr next).run st0

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

private def expectDecodeSaveAltCtr
    (label : String)
    (code : Cell)
    (expectedIdx : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      let expectedInstr := saveAltCtrInstr expectedIdx
      if instr != expectedInstr then
        throw (IO.userError
          s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def saveAltCtrOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/noise/",
    "ok/flow/",
    "ok/redefine/",
    "ok/probe/",
    "ok/raw/",
    "err/flow/",
    "err/redefine/",
    "err/order/",
    "err/probe/",
    "err/raw/"
  ]

private def saveAltCtrFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := saveAltCtrOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success across all valid indices.
  mkCase "ok/basic/idx0-empty" #[] (progSaveAlt 0),
  mkCase "ok/basic/idx1-empty" #[] (progSaveAlt 1),
  mkCase "ok/basic/idx2-empty" #[] (progSaveAlt 2),
  mkCase "ok/basic/idx3-empty" #[] (progSaveAlt 3),
  mkCase "ok/basic/idx4-empty" #[] (progSaveAlt 4),
  mkCase "ok/basic/idx5-empty" #[] (progSaveAlt 5),
  mkCase "ok/basic/idx7-empty" #[] (progSaveAlt 7),
  mkCase "ok/noise/idx0" noiseA (progSaveAlt 0),
  mkCase "ok/noise/idx1" noiseB (progSaveAlt 1),
  mkCase "ok/noise/idx4" noiseC (progSaveAlt 4),
  mkCase "ok/noise/idx5" (noiseA ++ noiseB) (progSaveAlt 5),
  mkCase "ok/noise/idx7" (noiseB ++ noiseA) (progSaveAlt 7),

  -- Control flow: SAVEALTCTR does not jump/call and does not pop stack.
  mkCase "ok/flow/tail-push-runs" #[] (progSaveAlt 0 #[.pushInt (.num 7)]),
  mkCase "ok/flow/tail-add-runs" #[intV 2, intV 3] (progSaveAlt 1 #[.add]),
  mkCase "ok/flow/tail-pushctr1-runs" #[] (progSaveAlt 0 #[.pushCtr 1]),
  mkCase "ok/flow/tail-pushctr4-runs" #[] (progSaveAlt 4 #[.pushCtr 4]),
  mkCase "ok/flow/tail-popctr1-runs" #[q0V] (progSaveAlt 0 #[.pushCtr 1, .popCtr 1]),
  mkCase "ok/flow/tail-popctr5-runs" #[.cell cellB]
    (progSaveAlt 4 #[.pushCtr 4, .popCtr 5, .pushCtr 5]),
  mkCase "err/flow/tail-add-underflow" #[] (progSaveAlt 0 #[.add]),

  -- Duplicate-define behavior.
  mkCase "err/redefine/idx0-second-fails" #[] (progSaveAlt2 0 0),
  mkCase "err/redefine/idx1-second-fails" #[] (progSaveAlt2 1 1),
  mkCase "err/redefine/idx2-second-fails" #[] (progSaveAlt2 2 2),
  mkCase "err/redefine/idx3-second-fails" #[] (progSaveAlt2 3 3),
  mkCase "err/redefine/idx4-second-fails" #[] (progSaveAlt2 4 4),
  mkCase "err/redefine/idx5-second-fails" #[] (progSaveAlt2 5 5),
  mkCase "ok/redefine/idx7-second-allowed" #[] (progSaveAlt2 7 7),
  mkCase "ok/redefine/idx7-second-tail-runs" #[] (progSaveAlt2 7 7 #[.pushInt (.num 9)]),
  mkCase "err/order/redefine-before-tail-idx0" noiseA
    (progSaveAlt2 0 0 #[.pushInt (.num 1)]),
  mkCase "err/order/redefine-before-tail-idx1" noiseB
    (progSaveAlt2 1 1 #[.pushInt (.num 1)]),
  mkCase "err/order/redefine-before-tail-idx4" noiseC
    (progSaveAlt2 4 4 #[.pushInt (.num 1)]),

  -- Extra probes for register-visible effects.
  mkCase "ok/probe/idx0-then-pushctr0" #[] (progSaveAlt 0 #[.pushCtr 0]),
  mkCase "ok/probe/idx1-then-pushctr1" #[] (progSaveAlt 1 #[.pushCtr 1]),
  mkCase "ok/probe/idx4-roundtrip-c4-to-c5" #[.cell cellA]
    (progSaveAlt 4 #[.pushCtr 4, .popCtr 5, .pushCtr 5]),
  mkCase "ok/probe/idx7-roundtrip-c7" #[]
    (progSaveAlt 7 #[.pushCtr 7, .popCtr 7, .pushCtr 7]),
  mkCase "ok/probe/idx5-tail-add-with-noise" #[intV 2, intV 3] (progSaveAlt 5 #[.add]),
  mkCase "err/probe/idx0-duplicate-after-tail" #[]
    #[saveAltCtrInstr 0, .pushInt (.num 1), saveAltCtrInstr 0],
  mkCase "ok/probe/idx7-double-then-pushctr1" #[] #[saveAltCtrInstr 7, saveAltCtrInstr 7, .pushCtr 1],
  mkCase "ok/noise/deep-mixed-idx3" (noiseA ++ noiseC ++ #[q0V]) (progSaveAlt 3),

  -- Raw opcodes and decode boundaries.
  mkCaseCode "ok/raw/opcode-edb0-idx0" #[] saveAltCode0,
  mkCaseCode "ok/raw/opcode-edb5-idx5" #[] saveAltCode5,
  mkCaseCode "ok/raw/opcode-edb7-idx7" #[] saveAltCode7,
  mkCaseCode "err/raw/opcode-hole-edb6" #[] saveAltCodeHole6,
  mkCaseCode "err/raw/opcode-unassigned-edb8" #[] saveAltCodeUnassignedB8,
  mkCaseCode "err/raw/opcode-neighbor-edaf" #[] saveAltCodeNeighborAf,
  mkCaseCode "err/raw/opcode-truncated-8" #[] saveAltTruncated8Code,
  mkCaseCode "err/raw/opcode-truncated-15" #[] saveAltTruncated15Code
]

def suite : InstrSuite where
  id := saveAltCtrId
  unit := #[
    { name := "unit/dispatch/savealtctr-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSaveAltFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-savealtctr"
          (runSaveAltFallback (saveAltCtrInstr 0) #[])
          #[] }
    ,
    { name := "unit/order/no-stack-pop-on-success-and-redefine-error"
      run := do
        let stOk ← expectRawOk "order/success-keeps-stack"
          (runSaveAltRaw (saveAltCtrInstr 4) noiseA)
        if stOk.stack != noiseA then
          throw (IO.userError
            s!"order/success-keeps-stack: expected {reprStr noiseA}, got {reprStr stOk.stack}")
        else
          pure ()
        let preC1 : Continuation :=
          .envelope q9 ({ OrdCregs.empty with c4 := some cellA }) OrdCdata.empty
        let regs1 : Regs := { Regs.initial with c1 := preC1 }
        let stErr ← expectRawErr "order/redefine-keeps-stack"
          (runSaveAltRaw (saveAltCtrInstr 4) noiseB regs1) .typeChk
        if stErr.stack != noiseB then
          throw (IO.userError
            s!"order/redefine-keeps-stack: expected {reprStr noiseB}, got {reprStr stErr.stack}")
        else if stErr.regs.c1 != preC1 then
          throw (IO.userError
            s!"order/redefine-keeps-stack: expected unchanged c1, got {reprStr stErr.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/raw/force-cdata-wraps-c1-and-saves-c0"
      run := do
        let st ← expectRawOk "raw/force-cdata"
          (runSaveAltRaw (saveAltCtrInstr 0) #[])
        if !st.stack.isEmpty then
          throw (IO.userError s!"raw/force-cdata: expected empty stack, got {reprStr st.stack}")
        else
          match st.regs.c1 with
          | .envelope ext cregs cdata =>
              if ext != q1 then
                throw (IO.userError s!"raw/force-cdata: expected ext quit1, got {reprStr ext}")
              else if cregs.c0 != some q0 then
                throw (IO.userError
                  s!"raw/force-cdata: expected saved c0=quit0, got {reprStr cregs.c0}")
              else if cregs.c1.isSome || cregs.c2.isSome || cregs.c3.isSome
                  || cregs.c4.isSome || cregs.c5.isSome || cregs.c7.isSome then
                throw (IO.userError s!"raw/force-cdata: unexpected extra saves {reprStr cregs}")
              else
                assertCdataEmpty "raw/force-cdata" cdata
          | _ =>
              throw (IO.userError s!"raw/force-cdata: expected envelope c1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/raw/idx1-captures-old-c1"
      run := do
        let regs1 : Regs := { Regs.initial with c1 := q9 }
        let st ← expectRawOk "raw/idx1-captures-old-c1"
          (runSaveAltRaw (saveAltCtrInstr 1) #[] regs1)
        match st.regs.c1 with
        | .envelope ext cregs cdata =>
            if ext != q9 then
              throw (IO.userError
                s!"raw/idx1-captures-old-c1: expected ext quit9, got {reprStr ext}")
            else if cregs.c1 != some q9 then
              throw (IO.userError
                s!"raw/idx1-captures-old-c1: expected saved c1=quit9, got {reprStr cregs.c1}")
            else
              assertCdataEmpty "raw/idx1-captures-old-c1" cdata
        | _ =>
            throw (IO.userError
              s!"raw/idx1-captures-old-c1: expected envelope c1, got {reprStr st.regs.c1}") }
    ,
    { name := "unit/raw/idx7-keeps-existing-c7"
      run := do
        let preC1 : Continuation :=
          .envelope q9 ({ OrdCregs.empty with c7 := some tupleKeep }) OrdCdata.empty
        let regs1 : Regs := { Regs.initial with c1 := preC1 }
        let st ← expectRawOk "raw/idx7-keeps-existing-c7"
          (runSaveAltRaw (saveAltCtrInstr 7) #[] regs1)
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
    { name := "unit/raw/direct-ast-invalid-idx-maps-typechk"
      run := do
        let st6 ← expectRawErr "invalid-idx6"
          (runSaveAltRaw (saveAltCtrInstr 6) noiseA) .typeChk
        if st6.stack != noiseA then
          throw (IO.userError s!"invalid-idx6: expected stack {reprStr noiseA}, got {reprStr st6.stack}")
        else if st6.regs.c1 != q1 then
          throw (IO.userError s!"invalid-idx6: expected c1 unchanged quit1, got {reprStr st6.regs.c1}")
        else
          pure ()
        let st8 ← expectRawErr "invalid-idx8"
          (runSaveAltRaw (saveAltCtrInstr 8) noiseB) .typeChk
        if st8.stack != noiseB then
          throw (IO.userError s!"invalid-idx8: expected stack {reprStr noiseB}, got {reprStr st8.stack}")
        else if st8.regs.c1 != q1 then
          throw (IO.userError s!"invalid-idx8: expected c1 unchanged quit1, got {reprStr st8.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/direct/basic-and-invalid"
      run := do
        expectOkStack "direct/idx0-success" (runSaveAltDirect 0 noiseA) noiseA
        expectErr "direct/idx6-typechk" (runSaveAltDirect 6 noiseA) .typeChk
        expectErr "direct/idx8-typechk" (runSaveAltDirect 8 noiseA) .typeChk }
    ,
    { name := "unit/decode/savealtctr-opcodes-and-boundaries"
      run := do
        expectDecodeSaveAltCtr "decode/edb0" saveAltCode0 0
        expectDecodeSaveAltCtr "decode/edb5" saveAltCode5 5
        expectDecodeSaveAltCtr "decode/edb7" saveAltCode7 7
        expectDecodeErr "decode/hole-edb6" saveAltCodeHole6 .invOpcode
        expectDecodeErr "decode/unassigned-edb8" saveAltCodeUnassignedB8 .invOpcode
        expectDecodeErr "decode/neighbor-edaf" saveAltCodeNeighborAf .invOpcode
        expectDecodeErr "decode/truncated-8" saveAltTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" saveAltTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile saveAltCtrId saveAltCtrFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SAVEALTCTR
