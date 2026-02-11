import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETCONTCTRX

private def setContCtrXId : InstrId := { name := "SETCONTCTRX" }
private def setContCtrXInstr : Instr := .contExt .setContCtrX

private def dispatchSentinel : Int := 49123

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def fullSliceA : Slice := Slice.ofCell cellA
private def fullSliceB : Slice := Slice.ofCell cellB

private def stackFor (value : Value) (cont : Value) (idx : Int) (below : Array Value := #[]) : Array Value :=
  below ++ #[value, cont, intV idx]

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def setContCtrXTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits (0xede2 >>> 8) 8) #[]

private def setContCtrXTruncated15 : Cell :=
  Cell.mkOrdinary (natToBits (0xede2 >>> 1) 15) #[]

private def runSetContCtrXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt setContCtrXInstr stack

private def runSetContCtrXFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSetContCtrXRaw
    (stack : Array Value)
    (instr : Instr := setContCtrXInstr) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContChangeExt instr (pure ())).run st0

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

private def expectDecodeSetContCtrX
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != setContCtrXInstr then
        throw (IO.userError s!"{label}: expected {reprStr setContCtrXInstr}, got {reprStr instr}")
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
    (program : Array Instr := #[setContCtrXInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrXId
    program := program
    initStack := stack
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrXId
    codeCell? := some codeCell
    initStack := stack
    fuel := fuel }

private def progSetContCtrX (tail : Array Instr := #[]) : Array Instr :=
  #[setContCtrXInstr] ++ tail

private def oracleCases : Array OracleCase := #[
  -- Success paths over supported control-register classes.
  mkCase "ok/index/idx0-basic" (stackFor q0 q0 0),
  mkCase "ok/index/idx1-basic" (stackFor q0 q0 1),
  mkCase "ok/index/idx2-basic" (stackFor q0 q0 2),
  mkCase "ok/index/idx3-basic" (stackFor q0 q0 3),
  mkCase "ok/index/idx4-basic-cell" (stackFor (.cell cellA) q0 4),
  mkCase "ok/index/idx5-basic-cell" (stackFor (.cell cellB) q0 5),
  mkCase "ok/index/idx7-basic-tuple" (stackFor (.tuple #[]) q0 7),
  mkCase "ok/index/idx0-noise-below" (stackFor q0 q0 0 #[.null, intV 7]),
  mkCase "ok/index/idx4-noise-below" (stackFor (.cell cellA) q0 4 #[.builder Builder.empty, .slice fullSliceA]),
  mkCase "ok/index/idx7-noise-below" (stackFor (.tuple #[]) q0 7 #[.cell cellB, intV 11]),

  -- Branch behavior: this instruction is non-jumping, so tail must execute.
  mkCase "ok/branch/non-jump-tail-push"
    (stackFor (.cell cellA) q0 4)
    (progSetContCtrX #[.pushInt (.num 77)]),
  mkCase "ok/branch/popctr0-after-setcont"
    (stackFor (.cell cellA) q0 4)
    (progSetContCtrX #[.popCtr 0, .pushCtr 0]),

  -- Entry underflow gates.
  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/one" #[intV 1],
  mkCase "err/underflow/two" #[intV 1, q0],
  mkCase "err/underflow/two-nonint-top" #[.null, .cell cellA],

  -- Index type/range errors.
  mkCase "err/index/type-null" #[.cell cellA, q0, .null],
  mkCase "err/index/type-cell" #[.cell cellA, q0, .cell cellB],
  mkCase "err/index/type-slice" #[.cell cellA, q0, .slice fullSliceA],
  mkCase "err/index/type-builder" #[.cell cellA, q0, .builder Builder.empty],
  mkCase "err/index/type-tuple" #[.cell cellA, q0, .tuple #[]],
  mkCase "err/index/range-minus1" (stackFor (.cell cellA) q0 (-1)),
  mkCase "err/index/range-hole-6" (stackFor (.cell cellA) q0 6),
  mkCase "err/index/range-8" (stackFor (.cell cellA) q0 8),
  mkCase "err/index/range-16" (stackFor (.cell cellA) q0 16),
  mkCase "err/index/range-17" (stackFor (.cell cellA) q0 17),
  mkCase "err/index/range-max-int257" (stackFor (.cell cellA) q0 maxInt257),
  mkCase "err/index/range-min-int257" (stackFor (.cell cellA) q0 minInt257),
  mkCase "err/index/range-nan-program"
    #[.cell cellA, q0]
    #[.pushInt .nan, setContCtrXInstr],

  -- Continuation operand type errors.
  mkCase "err/cont/type-null" (stackFor (.cell cellA) .null 4),
  mkCase "err/cont/type-int" (stackFor (.cell cellA) (intV 9) 4),
  mkCase "err/cont/type-cell" (stackFor (.cell cellA) (.cell cellB) 4),
  mkCase "err/cont/type-slice" (stackFor (.cell cellA) (.slice fullSliceB) 4),

  -- Value-type mapping by target register class.
  mkCase "err/value/type-c0-int" (stackFor (intV 5) q0 0),
  mkCase "err/value/type-c1-cell" (stackFor (.cell cellA) q0 1),
  mkCase "err/value/type-c4-cont" (stackFor q0 q0 4),
  mkCase "err/value/type-c5-tuple" (stackFor (.tuple #[]) q0 5),
  mkCase "err/value/type-c7-cell" (stackFor (.cell cellA) q0 7),
  mkCase "err/value/type-c7-null" (stackFor .null q0 7),

  -- Ordering probes.
  mkCase "err/order/range-before-cont-type" (stackFor (.cell cellA) .null 6),
  mkCase "err/order/range-before-value-type" (stackFor (intV 7) q0 8),
  mkCase "err/order/cont-type-before-value-type" (stackFor (intV 7) .null 4),
  mkCase "err/order/value-type-after-cont-pop" (stackFor (intV 7) q0 4),

  -- Decode/raw opcode boundaries.
  mkRawCase "ok/raw/opcode-ede2-basic" (stackFor (.cell cellA) q0 4) (rawOp16 0xede2),
  mkRawCase "ok/raw/opcode-ede2-noise" (stackFor (.cell cellA) q0 4 #[.null, intV 7]) (rawOp16 0xede2),
  mkRawCase "err/raw/truncated-8" (stackFor (.cell cellA) q0 4) setContCtrXTruncated8,
  mkRawCase "err/raw/truncated-15" (stackFor (.cell cellA) q0 4) setContCtrXTruncated15,
  mkRawCase "err/raw/neighbor-ede1" (stackFor (.cell cellA) q0 4) (rawOp16 0xede1),
  mkRawCase "err/raw/neighbor-ede3-missing-tail" (stackFor (.cell cellA) q0 4) (rawOp16 0xede3),
  mkRawCase "err/raw/neighbor-ede5" (stackFor (.cell cellA) q0 4) (rawOp16 0xede5),
  mkRawCase "err/raw/neighbor-eddf" (stackFor (.cell cellA) q0 4) (rawOp16 0xeddf),

  -- Execute branch coverage for continuation targets with saved regs.
  mkCase "ok/branch/execute-after-set-c0" (stackFor q0 q0 0) (progSetContCtrX #[.execute]),
  mkCase "ok/branch/execute-after-set-c1" (stackFor q0 q0 1) (progSetContCtrX #[.execute]),
  mkCase "ok/branch/execute-after-set-c3" (stackFor q0 q0 3) (progSetContCtrX #[.execute])
]

def suite : InstrSuite where
  id := setContCtrXId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback"
          (runSetContCtrXFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        match runSetContCtrXFallback setContCtrXInstr (stackFor (.cell cellA) q0 4) with
        | .ok st =>
            if st.size != 1 then
              throw (IO.userError s!"dispatch/matched: expected stack size 1, got {st.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"dispatch/matched: expected success, got {e}") }
    ,
    { name := "unit/errors/underflow-before-idx-type"
      run :=
        expectErr "underflow-before-idx-type"
          (runSetContCtrXDirect #[.null, .cell cellA])
          .stkUnd }
    ,
    { name := "unit/errors/nan-maps-to-rangeChk"
      run :=
        expectErr "nan-range"
          (runSetContCtrXDirect #[.cell cellA, q0, .int .nan])
          .rangeChk }
    ,
    { name := "unit/order/range-before-cont-type"
      run := do
        let st ← expectRawErr "order/range-before-cont-type"
          (runSetContCtrXRaw (stackFor (.cell cellA) .null 6)) .rangeChk
        if st.stack != #[.cell cellA, .null] then
          throw (IO.userError
            s!"order/range-before-cont-type: expected stack #[cell,null], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/cont-type-after-idx-pop"
      run := do
        let st ← expectRawErr "order/cont-type-after-idx-pop"
          (runSetContCtrXRaw (stackFor (.cell cellA) .null 4)) .typeChk
        if st.stack != #[.cell cellA] then
          throw (IO.userError
            s!"order/cont-type-after-idx-pop: expected stack #[cell], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/value-pop-before-define-type"
      run := do
        let st ← expectRawErr "order/value-pop-before-define-type"
          (runSetContCtrXRaw (stackFor (intV 7) q0 4)) .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"order/value-pop-before-define-type: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/branch/force-envelope-on-quit-cont"
      run := do
        let st ← expectRawOk "branch/force-envelope-on-quit"
          (runSetContCtrXRaw (stackFor (.cell cellA) q0 4))
        match st.stack with
        | #[.cont (.envelope ext cregs cdata)] =>
            if ext != .quit 0 then
              throw (IO.userError s!"branch/force-envelope-on-quit: expected ext quit0, got {reprStr ext}")
            else if cregs.c4.isNone then
              throw (IO.userError "branch/force-envelope-on-quit: expected c4 to be defined")
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
          (runSetContCtrXRaw (stackFor q0 (.cont preCont) 0)) .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError s!"branch/duplicate-c0: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/branch/c7-define-keeps-existing"
      run := do
        let preCont : Continuation :=
          .envelope (.quit 0) { OrdCregs.empty with c7 := some #[intV 99] } OrdCdata.empty
        let st ← expectRawOk "branch/c7-keep-existing"
          (runSetContCtrXRaw (stackFor (.tuple #[]) (.cont preCont) 7))
        match st.stack with
        | #[.cont (.envelope _ cregs _)] =>
            match cregs.c7 with
            | some t =>
                if t.size != 1 then
                  throw (IO.userError s!"branch/c7-keep-existing: expected size=1, got {t.size}")
                else
                  match t[0]? with
                  | some v =>
                      match v with
                      | .int (.num n) =>
                          if n != 99 then
                            throw (IO.userError s!"branch/c7-keep-existing: expected 99, got {n}")
                          else
                            pure ()
                      | _ =>
                          throw (IO.userError s!"branch/c7-keep-existing: unexpected c7[0] {reprStr v}")
                  | none =>
                      throw (IO.userError "branch/c7-keep-existing: c7[0] missing")
            | none =>
                throw (IO.userError "branch/c7-keep-existing: expected c7 to remain defined")
        | _ =>
            throw (IO.userError s!"branch/c7-keep-existing: unexpected stack {reprStr st.stack}") }
    ,
    { name := "unit/decode/opcode-and-truncation"
      run := do
        expectDecodeSetContCtrX "decode/opcode-ede2" (rawOp16 0xede2)
        expectDecodeErr "decode/truncated-8" setContCtrXTruncated8 .invOpcode
        expectDecodeErr "decode/truncated-15" setContCtrXTruncated15 .invOpcode
        expectDecodeErr "decode/neighbor-ede3-no-tail" (rawOp16 0xede3) .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec setContCtrXId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTCTRX
