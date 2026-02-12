import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SAVEBOTHCTR

private def saveBothCtrId : InstrId := { name := "SAVEBOTHCTR" }
private def saveBothCtrInstr (idx : Nat) : Instr := .contExt (.saveBothCtr idx)

private def dispatchSentinel : Int := 50627

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q7 : Continuation := .quit 7
private def q8 : Continuation := .quit 8
private def q9 : Continuation := .quit 9

private def q0V : Value := .cont q0

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def fullSliceA : Slice := Slice.ofCell cellA

private def tupleKeepA : Array Value := #[intV 41, .null]
private def tupleNewA : Array Value := #[intV 7]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def saveBothCode0 : Cell := rawOp16 0xedc0
private def saveBothCode5 : Cell := rawOp16 0xedc5
private def saveBothCode7 : Cell := rawOp16 0xedc7
private def saveBothCodeHole6 : Cell := rawOp16 0xedc6
private def saveBothCodeUnassigned8 : Cell := rawOp16 0xedc8
private def saveBothCodeBeforeRange : Cell := rawOp16 0xedbf

private def saveBothTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def saveBothTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedc0 >>> 1) 15) #[]

private def progSaveBoth (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[saveBothCtrInstr idx] ++ tail

private def progSaveBothTwice (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[saveBothCtrInstr idx, saveBothCtrInstr idx] ++ tail

private def progSaveBothThrice (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[saveBothCtrInstr idx, saveBothCtrInstr idx, saveBothCtrInstr idx] ++ tail

private def progC0DupThenCheckC1 (idx : Nat) : Array Instr :=
  #[.pushCtr idx, .contExt (.setRetCtr idx), saveBothCtrInstr idx, .pushCtr idx, .contExt (.setAltCtr idx)]

private def progC1DupThenCheckC0 (idx : Nat) : Array Instr :=
  #[.pushCtr idx, .contExt (.setAltCtr idx), saveBothCtrInstr idx, .pushCtr idx, .contExt (.setRetCtr idx)]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := saveBothCtrId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := saveBothCtrId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runSaveBothDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt (saveBothCtrInstr idx) stack

private def runSaveBothFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSaveBothRaw
    (idx : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, regs := regs }
  (execInstrContChangeExt (saveBothCtrInstr idx) (pure ())).run st0

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

private def ordSavedSlot? (cregs : OrdCregs) (idx : Nat) : Option Value :=
  match idx with
  | 0 => cregs.c0.map Value.cont
  | 1 => cregs.c1.map Value.cont
  | 2 => cregs.c2.map Value.cont
  | 3 => cregs.c3.map Value.cont
  | 4 => cregs.c4.map Value.cell
  | 5 => cregs.c5.map Value.cell
  | 7 => cregs.c7.map Value.tuple
  | _ => none

private def contSavedSlot? (k : Continuation) (idx : Nat) : Option Value :=
  match k.forceCdata with
  | .ordinary _ _ cregs _ => ordSavedSlot? cregs idx
  | .envelope _ cregs _ => ordSavedSlot? cregs idx
  | _ => none

private def expectSavedSlot
    (label : String)
    (k : Continuation)
    (idx : Nat)
    (expected : Option Value) : IO Unit := do
  let got := contSavedSlot? k idx
  if got != expected then
    throw (IO.userError s!"{label}: expected slot[{idx}]={reprStr expected}, got {reprStr got}")
  else
    pure ()

private def expectRegsEq (label : String) (got expected : Regs) : IO Unit := do
  if got.c0 != expected.c0 then
    throw (IO.userError s!"{label}: c0 mismatch: expected {reprStr expected.c0}, got {reprStr got.c0}")
  else if got.c1 != expected.c1 then
    throw (IO.userError s!"{label}: c1 mismatch: expected {reprStr expected.c1}, got {reprStr got.c1}")
  else if got.c2 != expected.c2 then
    throw (IO.userError s!"{label}: c2 mismatch: expected {reprStr expected.c2}, got {reprStr got.c2}")
  else if got.c3 != expected.c3 then
    throw (IO.userError s!"{label}: c3 mismatch: expected {reprStr expected.c3}, got {reprStr got.c3}")
  else if got.c4 != expected.c4 then
    throw (IO.userError s!"{label}: c4 mismatch: expected {reprStr expected.c4}, got {reprStr got.c4}")
  else if got.c5 != expected.c5 then
    throw (IO.userError s!"{label}: c5 mismatch: expected {reprStr expected.c5}, got {reprStr got.c5}")
  else if got.c7 != expected.c7 then
    throw (IO.userError s!"{label}: c7 mismatch: expected {reprStr expected.c7}, got {reprStr got.c7}")
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

private def expectDecodeSaveBoth
    (label : String)
    (code : Cell)
    (idx : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  let expectedInstr := saveBothCtrInstr idx
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

private def preC0Slot4A : Continuation :=
  .envelope q0 ({ OrdCregs.empty with c4 := some cellA }) OrdCdata.empty

private def preC1Slot5A : Continuation :=
  .envelope q1 ({ OrdCregs.empty with c5 := some cellA }) OrdCdata.empty

private def preC0Slot0Q8 : Continuation :=
  .envelope q7 ({ OrdCregs.empty with c0 := some q8 }) OrdCdata.empty

private def preC1Slot0Q9 : Continuation :=
  .envelope q9 ({ OrdCregs.empty with c0 := some q7 }) OrdCdata.empty

private def preC0Slot7Keep : Continuation :=
  .envelope q0 ({ OrdCregs.empty with c7 := some tupleKeepA }) OrdCdata.empty

private def saveBothCtrOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/noise/",
    "ok/flow/",
    "ok/duplicate/",
    "err/order/",
    "ok/raw/",
    "err/raw/"
  ]

private def saveBothCtrFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := saveBothCtrOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success matrix across all legal indices.
  mkCase "ok/basic/idx0-empty" #[] (progSaveBoth 0),
  mkCase "ok/basic/idx1-empty" #[] (progSaveBoth 1),
  mkCase "ok/basic/idx2-empty" #[] (progSaveBoth 2),
  mkCase "ok/basic/idx3-empty" #[] (progSaveBoth 3),
  mkCase "ok/basic/idx4-empty" #[] (progSaveBoth 4),
  mkCase "ok/basic/idx5-empty" #[] (progSaveBoth 5),
  mkCase "ok/basic/idx7-empty" #[] (progSaveBoth 7),
  mkCase "ok/noise/idx0-ints" #[intV 1, intV 2] (progSaveBoth 0),
  mkCase "ok/noise/idx1-mixed" #[.null, .cell cellA] (progSaveBoth 1),
  mkCase "ok/noise/idx2-cont-q0" #[q0V] (progSaveBoth 2),
  mkCase "ok/noise/idx3-builder" #[.builder Builder.empty] (progSaveBoth 3),
  mkCase "ok/noise/idx4-cell-null" #[.cell cellA, .null] (progSaveBoth 4),
  mkCase "ok/noise/idx5-slice" #[.slice fullSliceA] (progSaveBoth 5),
  mkCase "ok/noise/idx7-emptytuple-int" #[.tuple #[], intV 9] (progSaveBoth 7),

  -- Non-jump behavior with tails.
  mkCase "ok/flow/idx0-tail-pushint" #[] (progSaveBoth 0 #[.pushInt (.num 7)]),
  mkCase "ok/flow/idx1-tail-add" #[intV 2, intV 3] (progSaveBoth 1 #[.add]),
  mkCase "ok/flow/idx4-tail-add" #[intV 5, intV 6] (progSaveBoth 4 #[.add]),
  mkCase "ok/flow/idx5-tail-pushctr5" #[] (progSaveBoth 5 #[.pushCtr 5]),
  mkCase "ok/flow/idx7-tail-pushctr7" #[] (progSaveBoth 7 #[.pushCtr 7]),

  -- Duplicate save behavior (must be non-throwing).
  mkCase "ok/duplicate/idx0-twice" #[] (progSaveBothTwice 0),
  mkCase "ok/duplicate/idx1-twice" #[] (progSaveBothTwice 1),
  mkCase "ok/duplicate/idx2-twice" #[] (progSaveBothTwice 2),
  mkCase "ok/duplicate/idx3-twice" #[] (progSaveBothTwice 3),
  mkCase "ok/duplicate/idx4-twice" #[] (progSaveBothTwice 4),
  mkCase "ok/duplicate/idx5-twice" #[] (progSaveBothTwice 5),
  mkCase "ok/duplicate/idx7-twice" #[] (progSaveBothTwice 7),
  mkCase "ok/duplicate/idx0-thrice" #[] (progSaveBothThrice 0),
  mkCase "ok/duplicate/idx4-thrice" #[] (progSaveBothThrice 4),
  mkCase "ok/duplicate/idx1-twice-tail-add" #[intV 8, intV 9] (progSaveBothTwice 1 #[.add]),
  mkCase "ok/duplicate/idx7-twice-tail-pushint" #[] (progSaveBothTwice 7 #[.pushInt (.num 13)]),

  -- Ordering/precedence checks: duplicate on one side must not block the other side.
  mkCase "err/order/c0-dup-still-updates-c1-idx0" #[] (progC0DupThenCheckC1 0),
  mkCase "err/order/c1-dup-still-updates-c0-idx0" #[] (progC1DupThenCheckC0 0),
  mkCase "err/order/c0-dup-still-updates-c1-idx4" #[] (progC0DupThenCheckC1 4),
  mkCase "err/order/c1-dup-still-updates-c0-idx4" #[] (progC1DupThenCheckC0 4),

  -- Raw opcode and decode boundaries.
  mkCodeCase "ok/raw/opcode-edc0-idx0" #[] saveBothCode0,
  mkCodeCase "ok/raw/opcode-edc5-idx5" #[] saveBothCode5,
  mkCodeCase "ok/raw/opcode-edc7-idx7" #[] saveBothCode7,
  mkCodeCase "err/raw/opcode-hole-edc6" #[] saveBothCodeHole6,
  mkCodeCase "err/raw/opcode-unassigned-edc8" #[] saveBothCodeUnassigned8,
  mkCodeCase "err/raw/opcode-before-range-edbf" #[] saveBothCodeBeforeRange,
  mkCodeCase "err/raw/opcode-truncated8" #[] saveBothTruncated8Code,
  mkCodeCase "err/raw/opcode-truncated15" #[] saveBothTruncated15Code
]

def suite : InstrSuite where
  id := saveBothCtrId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSaveBothFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-saveboth"
          (runSaveBothFallback (saveBothCtrInstr 0) #[intV 7, .null])
          #[intV 7, .null] }
    ,
    { name := "unit/decode/opcode-boundaries"
      run := do
        expectDecodeSaveBoth "decode/edc0" saveBothCode0 0
        expectDecodeSaveBoth "decode/edc5" saveBothCode5 5
        expectDecodeSaveBoth "decode/edc7" saveBothCode7 7
        expectDecodeErr "decode/hole-edc6" saveBothCodeHole6 .invOpcode
        expectDecodeErr "decode/unassigned-edc8" saveBothCodeUnassigned8 .invOpcode
        expectDecodeErr "decode/before-range-edbf" saveBothCodeBeforeRange .invOpcode
        expectDecodeErr "decode/truncated8" saveBothTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated15" saveBothTruncated15Code .invOpcode }
    ,
    { name := "unit/raw/fresh-idx4-defines-both-c0-c1"
      run := do
        let regs : Regs := { Regs.initial with c4 := cellB }
        let st ← expectRawOk "fresh-idx4" (runSaveBothRaw 4 #[intV 17] regs)
        if st.stack != #[intV 17] then
          throw (IO.userError s!"fresh-idx4: expected stack #[17], got {reprStr st.stack}")
        else
          expectSavedSlot "fresh-idx4/c0" st.regs.c0 4 (some (.cell cellB))
        expectSavedSlot "fresh-idx4/c1" st.regs.c1 4 (some (.cell cellB)) }
    ,
    { name := "unit/raw/order-c0-duplicate-still-updates-c1"
      run := do
        let regs : Regs := { Regs.initial with c0 := preC0Slot4A, c4 := cellB }
        let st ← expectRawOk "order-c0-dup" (runSaveBothRaw 4 #[intV 1] regs)
        if st.stack != #[intV 1] then
          throw (IO.userError s!"order-c0-dup: expected stack #[1], got {reprStr st.stack}")
        else
          expectSavedSlot "order-c0-dup/c0-unchanged" st.regs.c0 4 (some (.cell cellA))
        expectSavedSlot "order-c0-dup/c1-updated" st.regs.c1 4 (some (.cell cellB)) }
    ,
    { name := "unit/raw/order-c1-duplicate-still-updates-c0"
      run := do
        let regs : Regs := { Regs.initial with c1 := preC1Slot5A, c5 := cellB }
        let st ← expectRawOk "order-c1-dup" (runSaveBothRaw 5 #[intV 2] regs)
        if st.stack != #[intV 2] then
          throw (IO.userError s!"order-c1-dup: expected stack #[2], got {reprStr st.stack}")
        else
          expectSavedSlot "order-c1-dup/c0-updated" st.regs.c0 5 (some (.cell cellB))
        expectSavedSlot "order-c1-dup/c1-unchanged" st.regs.c1 5 (some (.cell cellA)) }
    ,
    { name := "unit/raw/duplicate-both-sides-is-noop"
      run := do
        let regs : Regs := { Regs.initial with c0 := preC0Slot0Q8, c1 := preC1Slot0Q9 }
        let st ← expectRawOk "duplicate-both-sides" (runSaveBothRaw 0 #[intV 3] regs)
        if st.stack != #[intV 3] then
          throw (IO.userError s!"duplicate-both-sides: expected stack #[3], got {reprStr st.stack}")
        else if st.regs.c0 != preC0Slot0Q8 then
          throw (IO.userError
            s!"duplicate-both-sides: expected c0 unchanged, got {reprStr st.regs.c0}")
        else if st.regs.c1 != preC1Slot0Q9 then
          throw (IO.userError
            s!"duplicate-both-sides: expected c1 unchanged, got {reprStr st.regs.c1}")
        else
          pure () }
    ,
    { name := "unit/raw/idx7-keeps-existing-c7-and-defines-peer"
      run := do
        let regs : Regs := { Regs.initial with c0 := preC0Slot7Keep, c7 := tupleNewA }
        let st ← expectRawOk "idx7-keep-existing-c7" (runSaveBothRaw 7 #[] regs)
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"idx7-keep-existing-c7: expected empty stack, got {reprStr st.stack}")
        else
          expectSavedSlot "idx7-keep-existing-c7/c0" st.regs.c0 7 (some (.tuple tupleKeepA))
        expectSavedSlot "idx7-keep-existing-c7/c1" st.regs.c1 7 (some (.tuple tupleNewA)) }
    ,
    { name := "unit/raw/direct-invalid-idx-rangechk-no-mutation"
      run := do
        let regs : Regs :=
          { Regs.initial with
            c0 := preC0Slot0Q8
            c1 := preC1Slot0Q9
            c4 := cellB
            c5 := cellA
            c7 := tupleNewA }

        let st6 ← expectRawErr "invalid-idx6" (runSaveBothRaw 6 #[intV 11] regs) .rangeChk
        if st6.stack != #[intV 11] then
          throw (IO.userError s!"invalid-idx6: expected stack #[11], got {reprStr st6.stack}")
        else
          expectRegsEq "invalid-idx6/regs-preserved" st6.regs regs

        let st8 ← expectRawErr "invalid-idx8" (runSaveBothRaw 8 #[intV 12, .null] regs) .rangeChk
        if st8.stack != #[intV 12, .null] then
          throw (IO.userError s!"invalid-idx8: expected stack #[12, null], got {reprStr st8.stack}")
        else
          expectRegsEq "invalid-idx8/regs-preserved" st8.regs regs }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile saveBothCtrId saveBothCtrFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SAVEBOTHCTR
