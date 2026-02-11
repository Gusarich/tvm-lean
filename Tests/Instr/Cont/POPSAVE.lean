import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.POPSAVE

private def popSaveId : InstrId := { name := "POPSAVE" }

private def popSaveInstr (idx : Nat) : Instr :=
  .contExt (.popSave idx)

private def dispatchSentinel : Int := 62951

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q7 : Continuation := .quit 7
private def q8 : Continuation := .quit 8
private def q9 : Continuation := .quit 9

private def q0V : Value := .cont q0
private def q8V : Value := .cont q8
private def q9V : Value := .cont q9

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def fullSliceA : Slice := Slice.ofCell cellA

private def tupleA : Array Value :=
  #[intV 1, .null]

private def tupleB : Array Value :=
  #[.cell cellA, intV 2]

private def noiseA : Array Value :=
  #[intV 5, .null]

private def noiseB : Array Value :=
  #[.cell cellA, .builder Builder.empty]

private def withTop (xs : Array Value) (v : Value) : Array Value :=
  xs ++ #[v]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def popSaveCode0 : Cell := rawOp16 0xed90
private def popSaveCode5 : Cell := rawOp16 0xed95
private def popSaveCode7 : Cell := rawOp16 0xed97
private def popSaveCodeHole6 : Cell := rawOp16 0xed96
private def popSaveCodeUnassigned98 : Cell := rawOp16 0xed98

private def popSaveTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def popSaveTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xed90 >>> 1) 15) #[]

private def popSaveGasProbeInstr : Instr := popSaveInstr 1

private def popSaveGasExact : Int :=
  computeExactGasBudget popSaveGasProbeInstr

private def popSaveGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne popSaveGasProbeInstr

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := popSaveId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := popSaveId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runPopSaveDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt (popSaveInstr idx) stack

private def runPopSaveFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runPopSaveRaw
    (instr : Instr)
    (stack : Array Value)
    (c0 : Continuation := q0)
    (c1 : Continuation := q1)
    (next : VM Unit := pure ()) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { regs0 with c0 := c0, c1 := c1 } }
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

private def expectDecodePopSave
    (label : String)
    (code : Cell)
    (idx : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      let expectedInstr := popSaveInstr idx
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

private def oracleCases : Array OracleCase := #[
  -- Baseline valid updates.
  mkCase "ok/basic/idx0-cont-q0" #[q0V] #[popSaveInstr 0],
  mkCase "ok/basic/idx1-cont-q0" #[q0V] #[popSaveInstr 1],
  mkCase "ok/basic/idx2-cont-q0" #[q0V] #[popSaveInstr 2],
  mkCase "ok/basic/idx3-cont-q0" #[q0V] #[popSaveInstr 3],
  mkCase "ok/basic/idx4-cellA" #[.cell cellA] #[popSaveInstr 4],
  mkCase "ok/basic/idx5-cellB" #[.cell cellB] #[popSaveInstr 5],
  mkCase "ok/basic/idx7-tuple-empty" #[.tuple #[]] #[popSaveInstr 7],
  mkCase "ok/noise/idx0-cont" (withTop noiseA q0V) #[popSaveInstr 0],
  mkCase "ok/noise/idx1-cont" (withTop noiseB q0V) #[popSaveInstr 1],
  mkCase "ok/noise/idx4-cell" (withTop noiseA (.cell cellA)) #[popSaveInstr 4],
  mkCase "ok/noise/idx5-cell" (withTop noiseB (.cell cellB)) #[popSaveInstr 5],
  mkCase "ok/noise/idx7-tuple-empty" (withTop noiseA (.tuple #[])) #[popSaveInstr 7],
  mkCase "ok/noise/idx0-cont-mixed" #[.cell cellA, intV 12, q0V] #[popSaveInstr 0],
  mkCase "ok/noise/idx7-empty-tuple-mixed" #[.null, .builder Builder.empty, .tuple #[]] #[popSaveInstr 7],

  -- Follow-up probes.
  mkCase "ok/program/idx0-then-pushctr0" #[q0V] #[popSaveInstr 0, .pushCtr 0],
  mkCase "ok/program/idx1-then-pushctr1" #[q0V] #[popSaveInstr 1, .pushCtr 1],
  mkCase "ok/program/idx2-then-pushctr2" #[q0V] #[popSaveInstr 2, .pushCtr 2],
  mkCase "ok/program/idx3-then-pushctr3" #[q0V] #[popSaveInstr 3, .pushCtr 3],
  mkCase "ok/program/idx4-then-pushctr4" #[.cell cellA] #[popSaveInstr 4, .pushCtr 4],
  mkCase "ok/program/idx5-then-pushctr5" #[.cell cellB] #[popSaveInstr 5, .pushCtr 5],
  mkCase "ok/program/idx7-then-pushctr7" #[.tuple #[]] #[popSaveInstr 7, .pushCtr 7],
  mkCase "ok/program/idx4-roundtrip-popctr5"
    #[.cell cellB] #[popSaveInstr 4, .pushCtr 4, .popCtr 5, .pushCtr 5],
  mkCase "ok/program/idx7-roundtrip-popctr7"
    #[.tuple #[]] #[popSaveInstr 7, .pushCtr 7, .popCtr 7, .pushCtr 7],
  mkCase "ok/program/tail-add-after-idx0"
    #[q0V] #[popSaveInstr 0, .pushInt (.num 2), .pushInt (.num 3), .add],
  mkCase "ok/program/tail-add-after-idx4"
    #[.cell cellA] #[popSaveInstr 4, .pushInt (.num 4), .pushInt (.num 5), .add],

  -- Underflow and type failures.
  mkCase "err/underflow/empty-idx0" #[] #[popSaveInstr 0],
  mkCase "err/underflow/empty-idx4" #[] #[popSaveInstr 4],
  mkCase "err/type/idx0-int" #[intV 11] #[popSaveInstr 0],
  mkCase "err/type/idx0-null" #[.null] #[popSaveInstr 0],
  mkCase "err/type/idx0-cell" #[.cell cellA] #[popSaveInstr 0],
  mkCase "err/type/idx1-cell" #[.cell cellA] #[popSaveInstr 1],
  mkCase "err/type/idx2-int" #[intV 12] #[popSaveInstr 2],
  mkCase "err/type/idx3-tuple" #[.tuple #[]] #[popSaveInstr 3],
  mkCase "err/type/idx4-int" #[intV 13] #[popSaveInstr 4],
  mkCase "err/type/idx4-builder" #[.builder Builder.empty] #[popSaveInstr 4],
  mkCase "err/type/idx5-cont" #[q0V] #[popSaveInstr 5],
  mkCase "err/type/idx5-tuple" #[.tuple #[]] #[popSaveInstr 5],
  mkCase "err/type/idx7-int" #[intV 14] #[popSaveInstr 7],
  mkCase "err/type/idx7-cell" #[.cell cellA] #[popSaveInstr 7],
  mkCase "err/type/idx7-cont" #[q0V] #[popSaveInstr 7],
  mkCase "err/type/idx7-slice" #[.slice fullSliceA] #[popSaveInstr 7],

  -- Duplicate-save probes.
  mkCase "ok/duplicate-save/idx1-twice"
    #[q0V, q0V] #[popSaveInstr 1, popSaveInstr 1, .pushCtr 1],
  mkCase "ok/duplicate-save/idx4-twice"
    #[.cell cellA, .cell cellB] #[popSaveInstr 4, popSaveInstr 4, .pushCtr 4],
  mkCase "ok/duplicate-save/idx5-twice"
    #[.cell cellA, .cell cellB] #[popSaveInstr 5, popSaveInstr 5, .pushCtr 5],
  mkCase "ok/duplicate-save/idx7-twice"
    #[.tuple #[], .tuple #[]] #[popSaveInstr 7, popSaveInstr 7, .pushCtr 7],
  mkCase "ok/duplicate-save/idx0-after-savectr0"
    #[q0V] #[.saveCtr 0, popSaveInstr 0, .pushCtr 0],

  -- Raw opcode and decode boundaries.
  mkCaseCode "ok/raw/opcode-ed90-idx0" #[q0V] popSaveCode0,
  mkCaseCode "ok/raw/opcode-ed95-idx5" #[.cell cellB] popSaveCode5,
  mkCaseCode "ok/raw/opcode-ed97-idx7" #[.tuple #[]] popSaveCode7,
  mkCaseCode "err/raw/opcode-hole-ed96" #[q0V] popSaveCodeHole6,
  mkCaseCode "err/raw/opcode-unassigned-ed98" #[q0V] popSaveCodeUnassigned98,
  mkCaseCode "err/decode/truncated-8" #[] popSaveTruncated8Code,
  mkCaseCode "err/decode/truncated-15" #[q0V] popSaveTruncated15Code,

  -- Gas boundary.
  mkCase "gas/exact-budget"
    #[q0V]
    #[.pushInt (.num popSaveGasExact), .tonEnvOp .setGasLimit, popSaveGasProbeInstr],
  mkCase "gas/exact-minus-one"
    #[q0V]
    #[.pushInt (.num popSaveGasExactMinusOne), .tonEnvOp .setGasLimit, popSaveGasProbeInstr]
]

def suite : InstrSuite where
  id := popSaveId
  unit := #[
    { name := "unit/dispatch/popsave-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-next-only"
          (runPopSaveFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-popsave"
          (runPopSaveDirect 1 #[q9V])
          #[] }
    ,
    { name := "unit/order/underflow-and-idx0-type-pop"
      run := do
        expectErr "underflow/empty"
          (runPopSaveDirect 0 #[]) .stkUnd

        let st ← expectRawErr "idx0/type-pop"
          (runPopSaveRaw (popSaveInstr 0) #[q0V, intV 7]) .typeChk
        if st.stack != #[q0V] then
          throw (IO.userError s!"idx0/type-pop: expected stack #[q0], got {reprStr st.stack}")
        else if st.regs.c0 != q0 then
          throw (IO.userError s!"idx0/type-pop: expected c0 unchanged, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/raw/idx1-captures-old-c1-into-c0-save"
      run := do
        let st ← expectRawOk "idx1/capture" (runPopSaveRaw (popSaveInstr 1) #[q9V] q0 q1)
        if !st.stack.isEmpty then
          throw (IO.userError s!"idx1/capture: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c1 != q9 then
          throw (IO.userError s!"idx1/capture: expected c1=quit9, got {reprStr st.regs.c1}")
        else
          match st.regs.c0 with
          | .envelope ext cregs _ =>
              if ext != q0 then
                throw (IO.userError s!"idx1/capture: expected envelope ext quit0, got {reprStr ext}")
              else if cregs.c1 != some q1 then
                throw (IO.userError
                  s!"idx1/capture: expected saved c1=quit1, got {reprStr cregs.c1}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"idx1/capture: expected envelope c0, got {reprStr other}") }
    ,
    { name := "unit/order/idx4-type-error-pops-only-top"
      run := do
        let st ← expectRawErr "idx4/type-pop"
          (runPopSaveRaw (popSaveInstr 4) #[intV 55, intV 777]) .typeChk
        if st.stack != #[intV 55] then
          throw (IO.userError s!"idx4/type-pop: expected stack #[55], got {reprStr st.stack}")
        else if st.regs.c4 != Cell.empty then
          throw (IO.userError s!"idx4/type-pop: expected c4 unchanged, got {reprStr st.regs.c4}")
        else
          pure () }
    ,
    { name := "unit/decode/popsave-opcodes-and-boundaries"
      run := do
        expectDecodePopSave "decode/ed90" popSaveCode0 0
        expectDecodePopSave "decode/ed95" popSaveCode5 5
        expectDecodePopSave "decode/ed97" popSaveCode7 7
        expectDecodeErr "decode/hole-ed96" popSaveCodeHole6 .invOpcode
        expectDecodeErr "decode/unassigned-ed98" popSaveCodeUnassigned98 .invOpcode
        expectDecodeErr "decode/truncated-8" popSaveTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" popSaveTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.POPSAVE
