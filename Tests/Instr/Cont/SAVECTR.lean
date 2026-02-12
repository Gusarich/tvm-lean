import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SAVECTR

private def saveCtrId : InstrId := { name := "SAVECTR" }
private def saveCtrInstr (idx : Nat) : Instr := .saveCtr idx

private def dispatchSentinel : Int := 50061

private def q0 : Continuation := .quit 0
private def q0V : Value := .cont q0

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def noiseA : Array Value :=
  #[.null, intV 7]

private def noiseB : Array Value :=
  #[.cell cellA, .tuple #[]]

private def tupleKeep : Array Value :=
  #[intV 42, .null]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def saveCtrTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def saveCtrTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xeda0 >>> 1) 15) #[]

private def runSaveCtrDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContSaveCtr (saveCtrInstr idx) stack

private def runSaveCtrFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContSaveCtr instr (VM.push (intV dispatchSentinel)) stack

private def runSaveCtrRaw
    (idx : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, regs := regs }
  (execInstrContSaveCtr (saveCtrInstr idx) (pure ())).run st0

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

private def expectDecodeSaveCtr
    (label : String)
    (code : Cell)
    (idx : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  let expectedInstr := saveCtrInstr idx
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

private def expectAssembleErr
    (label : String)
    (program : List Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")
  | .ok c =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got code {reprStr c}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := saveCtrId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := saveCtrId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSave (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[saveCtrInstr idx] ++ tail

private def progSave2 (idx1 idx2 : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[saveCtrInstr idx1, saveCtrInstr idx2] ++ tail

private def saveCtrOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/flow/",
    "ok/program/",
    "ok/redefine/",
    "ok/stack-preserved/",
    "ok/raw/",
    "err/redefine/",
    "err/order/",
    "err/raw/"
  ]

private def saveCtrFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := saveCtrOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success matrix over all decoded indices.
  mkCase "ok/basic/idx0-empty" #[] (progSave 0),
  mkCase "ok/basic/idx1-empty" #[] (progSave 1),
  mkCase "ok/basic/idx2-empty" #[] (progSave 2),
  mkCase "ok/basic/idx3-empty" #[] (progSave 3),
  mkCase "ok/basic/idx4-empty" #[] (progSave 4),
  mkCase "ok/basic/idx5-empty" #[] (progSave 5),
  mkCase "ok/basic/idx7-empty" #[] (progSave 7),
  mkCase "ok/basic/idx0-noise-a" noiseA (progSave 0),
  mkCase "ok/basic/idx4-noise-b" noiseB (progSave 4),
  mkCase "ok/basic/idx5-noise-a" noiseA (progSave 5),
  mkCase "ok/basic/idx7-noise-b" noiseB (progSave 7),
  mkCase "ok/basic/idx0-noise-with-k" (noiseA ++ #[q0V]) (progSave 0),

  -- Non-jump behavior: tail instructions must run.
  mkCase "ok/flow/tail-add-after-save0" #[intV 2, intV 3] (progSave 0 #[.add]),
  mkCase "ok/flow/tail-pushctr4-after-save4" #[] (progSave 4 #[.pushCtr 4]),
  mkCase "ok/flow/tail-pushctr5-after-save5" #[intV 9] (progSave 5 #[.pushCtr 5]),
  mkCase "ok/flow/tail-pushctr7-after-save7" #[intV 11] (progSave 7 #[.pushCtr 7]),
  mkCase "ok/flow/tail-roundtrip-c5-after-save4"
    #[] (progSave 4 #[.pushCtr 4, .popCtr 5, .pushCtr 5]),
  mkCase "ok/flow/tail-roundtrip-c7-after-save7"
    #[.tuple #[]] (progSave 7 #[.pushCtr 7, .popCtr 7, .pushCtr 7]),

  -- Multi-save success combinations.
  mkCase "ok/program/save0-then-save1" #[] (progSave2 0 1),
  mkCase "ok/program/save4-then-save5" #[] (progSave2 4 5),
  mkCase "ok/program/save7-then-save4" #[] (progSave2 7 4),
  mkCase "ok/program/save7-then-save5-tail-add"
    #[intV 6, intV 8] (progSave2 7 5 #[.add]),

  -- Duplicate define failures for c0..c5.
  mkCase "err/redefine/idx0-second-fails" #[] (progSave2 0 0),
  mkCase "err/redefine/idx1-second-fails" #[] (progSave2 1 1),
  mkCase "err/redefine/idx2-second-fails" #[] (progSave2 2 2),
  mkCase "err/redefine/idx3-second-fails" #[] (progSave2 3 3),
  mkCase "err/redefine/idx4-second-fails" #[] (progSave2 4 4),
  mkCase "err/redefine/idx5-second-fails" #[] (progSave2 5 5),
  mkCase "err/order/redefine-idx4-before-tail"
    #[] (progSave2 4 4 #[.pushInt (.num 1)]),
  mkCase "err/order/redefine-idx0-before-tail-add"
    #[intV 2, intV 3] (progSave2 0 0 #[.add]),
  mkCase "err/order/redefine-idx5-before-tail-pushctr5"
    #[intV 99] (progSave2 5 5 #[.pushCtr 5]),

  -- c7 duplicate define is non-failing (keeps prior c7 save).
  mkCase "ok/redefine/idx7-second-allowed" #[] (progSave2 7 7),
  mkCase "ok/redefine/idx7-third-allowed"
    #[] #[saveCtrInstr 7, saveCtrInstr 7, saveCtrInstr 7],
  mkCase "ok/redefine/idx7-second-allowed-tail-add"
    #[intV 4, intV 5] (progSave2 7 7 #[.add]),

  -- Stack-preservation probes (SAVECTR does not pop).
  mkCase "ok/stack-preserved/no-pop-idx4" (noiseA ++ #[.cell cellB]) (progSave 4),
  mkCase "ok/stack-preserved/no-pop-idx0" (noiseB ++ #[q0V]) (progSave 0),
  mkCase "ok/stack-preserved/no-pop-idx7" (noiseA ++ #[.tuple #[]]) (progSave 7),

  -- Raw opcode boundaries and truncation.
  mkCodeCase "ok/raw/opcode-eda0-idx0" #[] (rawOp16 0xeda0),
  mkCodeCase "ok/raw/opcode-eda5-idx5" #[] (rawOp16 0xeda5),
  mkCodeCase "ok/raw/opcode-eda7-idx7" #[] (rawOp16 0xeda7),
  mkCodeCase "err/raw/opcode-hole-eda6" #[] (rawOp16 0xeda6),
  mkCodeCase "err/raw/opcode-neighbor-eda8" #[] (rawOp16 0xeda8),
  mkCodeCase "err/raw/opcode-neighbor-ed9f" #[] (rawOp16 0xed9f),
  mkCodeCase "err/raw/opcode-neighbor-edaf" #[] (rawOp16 0xedaf),
  mkCodeCase "err/raw/opcode-truncated8" #[] saveCtrTruncated8Code,
  mkCodeCase "err/raw/opcode-truncated15" #[] saveCtrTruncated15Code
]

def suite : InstrSuite where
  id := saveCtrId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSaveCtrFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-save4-no-pop"
          (runSaveCtrFallback (saveCtrInstr 4) #[intV 7])
          #[intV 7] }
    ,
    { name := "unit/decode/opcode-boundaries"
      run := do
        expectDecodeSaveCtr "decode/eda0" (rawOp16 0xeda0) 0
        expectDecodeSaveCtr "decode/eda5" (rawOp16 0xeda5) 5
        expectDecodeSaveCtr "decode/eda7" (rawOp16 0xeda7) 7
        expectDecodeErr "decode/hole-eda6" (rawOp16 0xeda6) .invOpcode
        expectDecodeErr "decode/neighbor-eda8" (rawOp16 0xeda8) .invOpcode
        expectDecodeErr "decode/neighbor-ed9f" (rawOp16 0xed9f) .invOpcode
        expectDecodeErr "decode/truncated8" saveCtrTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated15" saveCtrTruncated15Code .invOpcode }
    ,
    { name := "unit/asm/index-range-boundaries"
      run := do
        match assembleCp0 [saveCtrInstr 0] with
        | .ok c => expectDecodeSaveCtr "asm/save0-decodes" c 0
        | .error e => throw (IO.userError s!"asm/save0: expected success, got {e}")
        match assembleCp0 [saveCtrInstr 5] with
        | .ok c => expectDecodeSaveCtr "asm/save5-decodes" c 5
        | .error e => throw (IO.userError s!"asm/save5: expected success, got {e}")
        match assembleCp0 [saveCtrInstr 7] with
        | .ok c => expectDecodeSaveCtr "asm/save7-decodes" c 7
        | .error e => throw (IO.userError s!"asm/save7: expected success, got {e}")
        expectAssembleErr "asm/hole-idx6" [saveCtrInstr 6] .rangeChk
        expectAssembleErr "asm/idx8-oob" [saveCtrInstr 8] .rangeChk
        expectAssembleErr "asm/idx16-oob" [saveCtrInstr 16] .rangeChk }
    ,
    { name := "unit/order/no-stack-touch-on-success"
      run := do
        let regs : Regs := { Regs.initial with c4 := cellA }
        let st ← expectRawOk "no-stack-touch" (runSaveCtrRaw 4 #[intV 7, intV 8] regs)
        if st.stack != #[intV 7, intV 8] then
          throw (IO.userError s!"no-stack-touch: expected unchanged stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/error/invalid-idx6-typechk-no-mutation"
      run := do
        let st ← expectRawErr "invalid-idx6-typechk" (runSaveCtrRaw 6 #[intV 5]) .typeChk
        if st.stack != #[intV 5] then
          throw (IO.userError s!"invalid-idx6: expected unchanged stack, got {reprStr st.stack}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"invalid-idx6: expected c0=quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/error/mask-22-to-6-typechk"
      run := do
        let st ← expectRawErr "mask22-typechk" (runSaveCtrRaw 22 #[]) .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError s!"mask22-typechk: expected empty stack, got {reprStr st.stack}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"mask22-typechk: expected c0=quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/raw/mask-16-to-0"
      run := do
        let st ← expectRawOk "mask16-to-0" (runSaveCtrRaw 16 #[])
        match st.regs.c0 with
        | .envelope ext cregs cdata =>
            if ext != .quit 0 then
              throw (IO.userError s!"mask16-to-0: expected ext quit0, got {reprStr ext}")
            else if cregs.c0 != some (.quit 0) then
              throw (IO.userError s!"mask16-to-0: expected saved c0=quit0, got {reprStr cregs.c0}")
            else
              assertCdataEmpty "mask16-to-0" cdata
        | _ =>
            throw (IO.userError s!"mask16-to-0: expected envelope c0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/force-cdata-wrap-and-save-c4"
      run := do
        let regs : Regs := { Regs.initial with c4 := cellA }
        let st ← expectRawOk "force-cdata-save-c4" (runSaveCtrRaw 4 #[] regs)
        match st.regs.c0 with
        | .envelope ext cregs cdata =>
            if ext != .quit 0 then
              throw (IO.userError s!"force-cdata-save-c4: expected ext quit0, got {reprStr ext}")
            else if cregs.c4 != some cellA then
              throw (IO.userError s!"force-cdata-save-c4: expected c4=cellA, got {reprStr cregs.c4}")
            else
              assertCdataEmpty "force-cdata-save-c4" cdata
        | _ =>
            throw (IO.userError s!"force-cdata-save-c4: expected envelope c0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/redefine-c4-fails-and-preserves-c0"
      run := do
        let preC0 : Continuation :=
          .envelope (.quit 0) ({ OrdCregs.empty with c4 := some cellA }) OrdCdata.empty
        let regs : Regs := { Regs.initial with c0 := preC0, c4 := cellB }
        let st ← expectRawErr "redefine-c4-fails" (runSaveCtrRaw 4 #[] regs) .typeChk
        if st.regs.c0 != preC0 then
          throw (IO.userError
            s!"redefine-c4-fails: expected preserved c0={reprStr preC0}, got {reprStr st.regs.c0}")
        else if !st.stack.isEmpty then
          throw (IO.userError s!"redefine-c4-fails: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/idx7-define-keeps-existing-c7"
      run := do
        let preC0 : Continuation :=
          .envelope (.quit 0) ({ OrdCregs.empty with c7 := some tupleKeep }) OrdCdata.empty
        let regs : Regs := { Regs.initial with c0 := preC0, c7 := #[] }
        let st ← expectRawOk "idx7-keep-existing" (runSaveCtrRaw 7 #[] regs)
        match st.regs.c0 with
        | .envelope ext cregs cdata =>
            if ext != .quit 0 then
              throw (IO.userError s!"idx7-keep-existing: expected ext quit0, got {reprStr ext}")
            else if cregs.c7 != some tupleKeep then
              throw (IO.userError
                s!"idx7-keep-existing: expected c7={reprStr tupleKeep}, got {reprStr cregs.c7}")
            else
              assertCdataEmpty "idx7-keep-existing" cdata
        | _ =>
            throw (IO.userError s!"idx7-keep-existing: expected envelope c0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile saveCtrId saveCtrFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SAVECTR
