import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETCONTCTR

private def setContCtrId : InstrId := { name := "SETCONTCTR" }
private def setContCtrInstr (idx : Nat) : Instr := .setContCtr idx

private def dispatchSentinel : Int := 49031

private def q0 : Value := .cont (.quit 0)
private def q1 : Value := .cont (.quit 1)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def tupleA : Array Value := #[intV 11, .null]
private def tupleB : Array Value := #[intV 22]

private def stackFor (value : Value) (cont : Value) (below : Array Value := #[]) : Array Value :=
  below ++ #[value, cont]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def setContCtrTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits (0xed60 >>> 8) 8) #[]

private def setContCtrTruncated15 : Cell :=
  Cell.mkOrdinary (natToBits (0xed60 >>> 1) 15) #[]

private def runSetContCtrDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContSetContCtr (setContCtrInstr idx) stack

private def runSetContCtrFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContSetContCtr instr (VM.push (intV dispatchSentinel)) stack

private def runSetContCtrRaw (stack : Array Value) (idx : Nat) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContSetContCtr (setContCtrInstr idx) (pure ())).run st0

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

private def expectDecodeSetContCtr
    (label : String)
    (code : Cell)
    (expectedIdx : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != setContCtrInstr expectedIdx then
        throw (IO.userError s!"{label}: expected {reprStr (setContCtrInstr expectedIdx)}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeNotSetContCtr (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, _) =>
      match instr with
      | .setContCtr _ =>
          throw (IO.userError s!"{label}: expected non-SETCONTCTR decode, got {reprStr instr}")
      | _ =>
          pure ()
  | .error _ =>
      pure ()

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrId
    program := program
    initStack := stack
    fuel := fuel }

private def mkIdxCase
    (name : String)
    (stack : Array Value)
    (idx : Nat)
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (#[setContCtrInstr idx] ++ tail) fuel

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrId
    codeCell? := some codeCell
    initStack := stack
    fuel := fuel }

private def progSetTwice (idx1 idx2 : Nat) : Array Instr :=
  #[setContCtrInstr idx1, setContCtrInstr idx2]

private def oracleCases : Array OracleCase := #[
  -- Success over all valid static indices.
  mkIdxCase "ok/index/idx0-basic" (stackFor q0 q0) 0,
  mkIdxCase "ok/index/idx1-basic" (stackFor q0 q0) 1,
  mkIdxCase "ok/index/idx2-basic" (stackFor q0 q0) 2,
  mkIdxCase "ok/index/idx3-basic" (stackFor q0 q0) 3,
  mkIdxCase "ok/index/idx4-basic-cell" (stackFor (.cell cellA) q0) 4,
  mkIdxCase "ok/index/idx5-basic-cell" (stackFor (.cell cellB) q0) 5,
  mkIdxCase "ok/index/idx7-basic-tuple" (stackFor (.tuple #[]) q0) 7,
  mkIdxCase "ok/index/idx0-noise-below" (stackFor q0 q0 #[.null, intV 7]) 0,
  mkIdxCase "ok/index/idx4-noise-below" (stackFor (.cell cellA) q0 #[.builder Builder.empty, .null]) 4,
  mkIdxCase "ok/index/idx7-noise-below" (stackFor (.tuple #[]) q0 #[.cell cellB, intV 11]) 7,
  mkIdxCase "ok/flow/non-jump-tail-push" (stackFor (.cell cellA) q0) 4 #[.pushInt (.num 77)],
  mkIdxCase "ok/flow/popctr0-after-set" (stackFor q0 q0) 0 #[.popCtr 0, .pushCtr 0],
  mkCase "ok/redefine/c7-second-ignored"
    #[.tuple #[], .tuple #[], q0]
    (progSetTwice 7 7),
  mkCase "ok/redefine/c7-second-ignored-noise"
    #[.null, .tuple #[], .tuple #[], q0]
    (progSetTwice 7 7),

  -- Underflow gates.
  mkIdxCase "err/underflow/empty" #[] 4,
  mkIdxCase "err/underflow/one-value" #[.cell cellA] 4,
  mkIdxCase "err/underflow/one-cont" #[q0] 4,
  mkIdxCase "err/underflow/one-null" #[.null] 0,

  -- Continuation operand type errors.
  mkIdxCase "err/cont/type-null" (stackFor (.cell cellA) .null) 4,
  mkIdxCase "err/cont/type-int" (stackFor (.cell cellA) (intV 9)) 4,
  mkIdxCase "err/cont/type-cell" (stackFor (.cell cellA) (.cell cellB)) 4,
  mkIdxCase "err/cont/type-slice" (stackFor (.cell cellA) (.slice sliceB)) 4,
  mkIdxCase "err/cont/type-builder" (stackFor (.cell cellA) (.builder Builder.empty)) 4,
  mkIdxCase "err/cont/type-tuple" (stackFor (.cell cellA) (.tuple #[])) 4,

  -- Value-type mapping errors.
  mkIdxCase "err/value/type-c0-int" (stackFor (intV 5) q0) 0,
  mkIdxCase "err/value/type-c1-cell" (stackFor (.cell cellA) q0) 1,
  mkIdxCase "err/value/type-c2-tuple" (stackFor (.tuple #[]) q0) 2,
  mkIdxCase "err/value/type-c3-null" (stackFor .null q0) 3,
  mkIdxCase "err/value/type-c4-cont" (stackFor q0 q0) 4,
  mkIdxCase "err/value/type-c5-tuple" (stackFor (.tuple #[]) q0) 5,
  mkIdxCase "err/value/type-c7-cell" (stackFor (.cell cellA) q0) 7,
  mkIdxCase "err/value/type-c7-null" (stackFor .null q0) 7,

  -- Re-define failures on non-c7 registers.
  mkCase "err/redefine/c0-second-fails"
    #[q0, q0, q0]
    (progSetTwice 0 0),
  mkCase "err/redefine/c4-second-fails"
    #[.cell cellB, .cell cellA, q0]
    (progSetTwice 4 4),
  mkCase "err/redefine/c5-second-fails"
    #[.cell cellA, .cell cellB, q0]
    (progSetTwice 5 5),
  mkCase "err/redefine/c0-second-fails-with-noise"
    #[.null, q0, q0, q0]
    (progSetTwice 0 0),

  -- Ordering-sensitive probes.
  mkIdxCase "err/order/cont-type-before-value-pop" (stackFor (intV 7) .null) 4,
  mkIdxCase "err/order/value-pop-before-define-type" (stackFor (intV 7) q0) 4,
  mkIdxCase "err/order/underflow-before-cont-type" #[.null] 4,
  mkIdxCase "err/order/underflow-before-value-type" #[intV 7] 4,

  -- Decode/raw opcode boundaries around ed60 family.
  mkCodeCase "ok/raw/opcode-ed60-idx0" (stackFor q0 q0) (rawOp16 0xed60),
  mkCodeCase "ok/raw/opcode-ed65-idx5" (stackFor (.cell cellA) q0) (rawOp16 0xed65),
  mkCodeCase "ok/raw/opcode-ed67-idx7" (stackFor (.tuple #[]) q0) (rawOp16 0xed67),
  mkCodeCase "err/raw/opcode-ed66-hole" (stackFor q0 q0) (rawOp16 0xed66),
  mkCodeCase "err/raw/opcode-ed68-neighbor-setret" (stackFor q0 q0) (rawOp16 0xed68),
  mkCodeCase "err/raw/opcode-ed6f-neighbor-setret" (stackFor q0 q0) (rawOp16 0xed6f),
  mkCodeCase "err/raw/opcode-ed70-neighbor-setret" (stackFor q0 q0) (rawOp16 0xed70),
  mkCodeCase "err/raw/opcode-truncated8" (stackFor q0 q0) setContCtrTruncated8,
  mkCodeCase "err/raw/opcode-truncated15" (stackFor q0 q0) setContCtrTruncated15,
  mkCodeCase "err/raw/opcode-near-ed5f" (stackFor q0 q0) (rawOp16 0xed5f),
  mkCodeCase "err/raw/opcode-near-ed78" (stackFor q0 q0) (rawOp16 0xed78)
]

def suite : InstrSuite where
  id := setContCtrId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runSetContCtrFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        match runSetContCtrFallback (setContCtrInstr 4) (stackFor (.cell cellA) q0) with
        | .ok st =>
            if st.size != 1 then
              throw (IO.userError s!"dispatch/matched: expected stack size 1, got {st.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"dispatch/matched: expected success, got {e}") }
    ,
    { name := "unit/errors/underflow-before-cont-type"
      run :=
        expectErr "underflow-before-cont-type"
          (runSetContCtrDirect 4 #[.null])
          .stkUnd }
    ,
    { name := "unit/order/cont-type-after-pop"
      run := do
        let st ← expectRawErr "order/cont-type-after-pop"
          (runSetContCtrRaw (stackFor (.cell cellA) .null) 4) .typeChk
        if st.stack != #[.cell cellA] then
          throw (IO.userError
            s!"order/cont-type-after-pop: expected #[cell], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/value-pop-before-define"
      run := do
        let st ← expectRawErr "order/value-pop-before-define"
          (runSetContCtrRaw (stackFor (intV 7) q0) 4) .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"order/value-pop-before-define: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/underflow-preserves-empty"
      run := do
        let st ← expectRawErr "order/underflow-preserves-empty"
          (runSetContCtrRaw #[] 4) .stkUnd
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"order/underflow-preserves-empty: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/branch/force-envelope-on-quit-cont"
      run := do
        let st ← expectRawOk "branch/force-envelope-on-quit"
          (runSetContCtrRaw (stackFor (.cell cellA) q0) 4)
        match st.stack with
        | #[.cont (.envelope ext cregs cdata)] =>
            if ext != .quit 0 then
              throw (IO.userError s!"branch/force-envelope-on-quit: expected ext quit0, got {reprStr ext}")
            else if cregs.c4 != some cellA then
              throw (IO.userError s!"branch/force-envelope-on-quit: expected c4=cellA, got {reprStr cregs.c4}")
            else if !cdata.stack.isEmpty || cdata.nargs != -1 then
              throw (IO.userError s!"branch/force-envelope-on-quit: expected empty cdata, got {reprStr cdata}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"branch/force-envelope-on-quit: unexpected stack {reprStr st.stack}") }
    ,
    { name := "unit/branch/duplicate-c0-maps-to-typeChk"
      run := do
        let preCont : Continuation :=
          .envelope (.quit 0) { OrdCregs.empty with c0 := some (.quit 0) } OrdCdata.empty
        let st ← expectRawErr "branch/duplicate-c0"
          (runSetContCtrRaw (stackFor q0 (.cont preCont)) 0) .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError s!"branch/duplicate-c0: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/branch/c7-define-keeps-existing"
      run := do
        let preCont : Continuation :=
          .envelope (.quit 0) { OrdCregs.empty with c7 := some tupleA } OrdCdata.empty
        let st ← expectRawOk "branch/c7-keep-existing"
          (runSetContCtrRaw (stackFor (.tuple tupleB) (.cont preCont)) 7)
        match st.stack with
        | #[.cont (.envelope _ cregs _)] =>
            if cregs.c7 != some tupleA then
              throw (IO.userError
                s!"branch/c7-keep-existing: expected c7={reprStr tupleA}, got {reprStr cregs.c7}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"branch/c7-keep-existing: unexpected stack {reprStr st.stack}") }
    ,
    { name := "unit/idx/mask-16-to-0"
      run := do
        match runSetContCtrDirect 16 (stackFor q0 q0) with
        | .ok st =>
            if st.size != 1 then
              throw (IO.userError s!"idx/mask-16-to-0: expected stack size 1, got {st.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"idx/mask-16-to-0: expected success, got {e}") }
    ,
    { name := "unit/decode/opcode-bounds-and-truncation"
      run := do
        expectDecodeSetContCtr "decode/opcode-ed60" (rawOp16 0xed60) 0
        expectDecodeSetContCtr "decode/opcode-ed65" (rawOp16 0xed65) 5
        expectDecodeSetContCtr "decode/opcode-ed67" (rawOp16 0xed67) 7
        expectDecodeErr "decode/opcode-ed66-hole" (rawOp16 0xed66) .invOpcode
        expectDecodeErr "decode/truncated-8" setContCtrTruncated8 .invOpcode
        expectDecodeErr "decode/truncated-15" setContCtrTruncated15 .invOpcode
        expectDecodeNotSetContCtr "decode/neighbor-ed68" (rawOp16 0xed68)
        expectDecodeNotSetContCtr "decode/neighbor-ed70" (rawOp16 0xed70) }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTCTR
