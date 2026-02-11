import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.JMPXDATA

/-
JMPXDATA branch map (Lean vs C++):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/JmpxData.lean`
  - `TvmLean/Semantics/Exec/Common.lean` (`VM.pushCode`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.jump`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_jmpx_data`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::jump`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.h` (`push_code`)

Coverage goals in this suite:
- dispatch: `.jmpxData` match vs fallback;
- decode gates: exact `0xdb35` (16-bit) vs truncated/empty code (`invOpcode`);
- runtime order: `pop_cont` -> `push_code` -> `jump`;
- control-flow ordering: tail after `JMPXDATA` is not executed;
- jump argument plumbing after push-code side effect;
- deterministic oracle coverage with harness-compatible continuation token (`K=quit(0)`).
-/

private def jmpxdataId : InstrId := { name := "JMPXDATA" }
private def jmpxdataInstr : Instr := .jmpxData

private def dispatchSentinel : Int := 90653

private def q0 : Value := .cont (.quit 0)

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice := Slice.ofCell refCellA

private def emptySlice : Slice := Slice.ofCell Cell.empty

private def ccCodeCell : Cell :=
  Cell.mkOrdinary (natToBits 0x73db 16) #[refCellA]

private def partialCcSlice : Slice :=
  { cell := ccCodeCell, bitPos := 3, refPos := 1 }

private def opcodeBits : BitString :=
  natToBits 0xdb35 16

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def assembleNoRefBits! (label : String) (program : Array Instr) : BitString :=
  (assembleNoRefCell! label program).bits

private def mkJmpxdataCode (tail : Array Instr := #[]) : Cell :=
  Cell.mkOrdinary (opcodeBits ++ assembleNoRefBits! "jmpxdata/tail" tail) #[]

private def bareJmpxdataCode : Cell :=
  mkJmpxdataCode #[]

private def truncated8Code : Cell :=
  Cell.mkOrdinary (opcodeBits.take 8) #[]

private def truncated15Code : Cell :=
  Cell.mkOrdinary (opcodeBits.take 15) #[]

private def emptyCode : Cell :=
  Cell.empty

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def mkJmpxdataStack
    (below : Array Value)
    (cont : Continuation := .quit 0) : Array Value :=
  below ++ #[.cont cont]

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def runJmpxdataDirect
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowJmpxData jmpxdataInstr stack

private def runJmpxdataDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowJmpxData instr (VM.push (intV dispatchSentinel)) stack

private def runJmpxdataRaw
    (stack : Array Value)
    (cc : Continuation := .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty)
    (gas : GasLimits := GasLimits.default) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc, gas := gas }
  (execInstrFlowJmpxData jmpxdataInstr (pure ())).run st0

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
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectDecodeOkJmpxdata
    (label : String)
    (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (.jmpxData, bits, _) =>
      if bits = 16 then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decoded bits=16, got {bits}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected JMPXDATA, got instr={reprStr instr}, bits={bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[jmpxdataInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpxdataId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpxdataId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkJumpCase
    (name : String)
    (below : Array Value)
    (program : Array Instr := #[jmpxdataInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name (mkJmpxdataStack below) program gasLimits fuel

private def progSetNargsThenJmpxdata (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num n), .setNumVarArgs, jmpxdataInstr] ++ tail

private def jmpxdataGasExact : Int :=
  computeExactGasBudget jmpxdataInstr

private def jmpxdataGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne jmpxdataInstr

private def oracleCases : Array OracleCase := #[
  -- Success: pop continuation, push remaining code slice, jump.
  mkJumpCase "ok/basic/empty-below" #[],
  mkJumpCase "ok/basic/int-zero" #[intV 0],
  mkJumpCase "ok/basic/int-neg" #[intV (-5)],
  mkJumpCase "ok/basic/max-int257" #[intV maxInt257],
  mkJumpCase "ok/basic/min-plus1" #[intV (minInt257 + 1)],
  mkJumpCase "ok/basic/null-int" #[.null, intV 9],
  mkJumpCase "ok/basic/cell" #[.cell refCellA],
  mkJumpCase "ok/basic/slice" #[.slice fullSliceA],
  mkJumpCase "ok/basic/builder-empty" #[.builder Builder.empty],
  mkJumpCase "ok/basic/tuple-empty" #[.tuple #[]],
  mkJumpCase "ok/basic/cont-below" #[q0],
  mkJumpCase "ok/basic/deep-mixed" #[.null, .cell refCellB, .slice fullSliceA, intV 3],
  mkJumpCase "ok/basic/long-int-prefix" (intStackAsc 12),

  -- Ordering: tail must be skipped after JMPXDATA.
  mkJumpCase "order/tail/push-skipped" #[] #[jmpxdataInstr, .pushInt (.num 777)],
  mkJumpCase "order/tail/retalt-skipped" #[] #[jmpxdataInstr, .retAlt],
  mkJumpCase "order/tail/add-underflow-skipped" #[] #[jmpxdataInstr, .add],
  mkJumpCase "order/tail/two-ops-skipped" #[intV 2, intV 3]
    #[jmpxdataInstr, .pushInt (.num 11), .add],
  mkJumpCase "order/tail/deep-preserved" #[.null, .cell refCellA, intV 8]
    #[jmpxdataInstr, .pushInt (.num 19)],
  mkCase "order/prelude/push-swap-jmpxdata" #[q0]
    #[.pushInt (.num 9), .xchg0 1, jmpxdataInstr, .add],
  mkCase "order/prelude/deep-push-swap-jmpxdata" #[intV 4, q0]
    #[.pushInt (.num 7), .xchg0 1, jmpxdataInstr, .pushInt (.num 55)],
  mkCase "order/prelude/push-push-swap-jmpxdata" #[q0]
    #[.pushInt (.num 4), .pushInt (.num 5), .xchg0 1, .xchg0 1, jmpxdataInstr, .add],

  -- Push-code influences jump argument selection when nargs is forced.
  mkCase "ok/nargsm1/empty-init" #[q0] (progSetNargsThenJmpxdata (-1)),
  mkCase "ok/nargs0/empty-init" #[q0] (progSetNargsThenJmpxdata 0),
  mkCase "ok/nargs1/empty-init" #[q0] (progSetNargsThenJmpxdata 1),
  mkCase "err/nargs2/empty-underflow" #[q0] (progSetNargsThenJmpxdata 2),
  mkCase "ok/nargs1/one-int" #[intV 33, q0] (progSetNargsThenJmpxdata 1),
  mkCase "ok/nargs2/one-int" #[intV 33, q0] (progSetNargsThenJmpxdata 2),
  mkCase "err/nargs3/one-int-underflow" #[intV 33, q0] (progSetNargsThenJmpxdata 3),
  mkCase "ok/nargs2/two-int" #[intV 1, intV 2, q0] (progSetNargsThenJmpxdata 2),
  mkCase "ok/nargs3/two-int" #[intV 1, intV 2, q0] (progSetNargsThenJmpxdata 3),
  mkCase "err/nargs4/two-int-underflow" #[intV 1, intV 2, q0] (progSetNargsThenJmpxdata 4),
  mkCase "order/nargs1/trailing-skipped" #[intV 7, q0]
    (progSetNargsThenJmpxdata 1 #[.pushInt (.num 999)]),

  -- Runtime pop/type errors in JMPXDATA itself.
  mkCase "err/underflow/empty" #[],
  mkCase "err/type/top-int" #[intV 1],
  mkCase "err/type/top-null" #[.null],
  mkCase "err/type/top-cell" #[.cell refCellA],
  mkCase "err/type/top-slice" #[.slice fullSliceA],
  mkCase "err/type/top-builder" #[.builder Builder.empty],
  mkCase "err/type/top-tuple" #[.tuple #[]],
  mkCase "err/type/top-int-with-below" #[intV 9, intV 1],
  mkCase "err/type/top-cell-with-below" #[intV 9, .cell refCellA],
  mkCase "err/type/prelude-push-makes-int-top" #[q0] #[.pushInt (.num 1), jmpxdataInstr],

  -- Decode gates (cp0 exact-width/truncation).
  mkCodeCase "decode/truncated8/empty" #[] truncated8Code,
  mkCodeCase "decode/truncated15/empty" #[] truncated15Code,
  mkCodeCase "decode/empty-code/empty" #[] emptyCode,
  mkCodeCase "decode/truncated8/with-k" #[q0] truncated8Code,
  mkCodeCase "decode/truncated15/with-int" #[intV 3] truncated15Code,
  mkCodeCase "decode/empty-code/with-k" #[q0] emptyCode,
  mkCodeCase "decode/truncated15/with-mixed" #[.null, intV 5, q0] truncated15Code,

  -- Gas boundary probes for the JMPXDATA opcode itself.
  mkJumpCase "gas/exact-cost-succeeds" #[]
    #[.pushInt (.num jmpxdataGasExact), .tonEnvOp .setGasLimit, jmpxdataInstr],
  mkJumpCase "gas/exact-minus-one-out-of-gas" #[]
    #[.pushInt (.num jmpxdataGasExactMinusOne), .tonEnvOp .setGasLimit, jmpxdataInstr]
]

def suite : InstrSuite where
  id := jmpxdataId
  unit := #[
    { name := "unit/direct/pop-and-preserve-below-plus-pushed-code"
      run := do
        expectOkStack "direct/empty" (runJmpxdataDirect (mkJmpxdataStack #[] (.quit 7))) #[.slice emptySlice]
        expectOkStack "direct/deep-mixed"
          (runJmpxdataDirect (mkJmpxdataStack #[.null, intV 9, .cell refCellB, .slice fullSliceA] (.quit 7)))
          #[.null, intV 9, .cell refCellB, .slice fullSliceA, .slice emptySlice] }
    ,
    { name := "unit/raw/cc-transition-and-pushcode-before-jump"
      run := do
        let ccRest : Continuation := .ordinary partialCcSlice (.quit 0) OrdCregs.empty OrdCdata.empty
        let target : Continuation := .quit 7
        let (res, st) := runJmpxdataRaw (mkJmpxdataStack #[intV 3] target) ccRest
        match res with
        | .error e =>
            throw (IO.userError s!"raw/cc-transition: expected success, got {e}")
        | .ok _ =>
            if st.stack != #[intV 3, .slice partialCcSlice] then
              throw (IO.userError s!"raw/cc-transition: stack mismatch {reprStr st.stack}")
            else if st.cc != target then
              throw (IO.userError s!"raw/cc-transition: expected cc={reprStr target}, got {reprStr st.cc}")
            else
              pure () }
    ,
    { name := "unit/error/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runJmpxdataDirect #[]) .stkUnd
        expectErr "type/top-int" (runJmpxdataDirect #[intV 1]) .typeChk
        expectErr "type/top-null" (runJmpxdataDirect #[.null]) .typeChk

        let ccInit : Continuation := .ordinary partialCcSlice (.quit 0) OrdCregs.empty OrdCdata.empty
        let (resType, stType) := runJmpxdataRaw #[intV 77, .null] ccInit
        match resType with
        | .error .typeChk =>
            if stType.stack == #[intV 77] then
              pure ()
            else
              throw (IO.userError s!"type/pop-order: expected #[77], got {reprStr stType.stack}")
        | .error e =>
            throw (IO.userError s!"type/pop-order: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "type/pop-order: expected typeChk, got success") }
    ,
    { name := "unit/order/pushcode-happens-before-jump-error"
      run := do
        let ccRest : Continuation := .ordinary partialCcSlice (.quit 0) OrdCregs.empty OrdCdata.empty
        let need2 : Continuation := mkOrdCont 2 #[]
        let (res, st) := runJmpxdataRaw (mkJmpxdataStack #[] need2) ccRest
        match res with
        | .error .stkUnd =>
            if st.stack != #[.slice partialCcSlice] then
              throw (IO.userError s!"pushcode-before-jump-error: stack mismatch {reprStr st.stack}")
            else if st.cc != ccRest then
              throw (IO.userError s!"pushcode-before-jump-error: cc changed {reprStr st.cc}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"pushcode-before-jump-error: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "pushcode-before-jump-error: expected stkUnd, got success") }
    ,
    { name := "unit/order/nonordinary-cc-typechk-at-pushcode"
      run := do
        let (res, st) := runJmpxdataRaw (mkJmpxdataStack #[] (.quit 8)) (.quit 44)
        match res with
        | .error .typeChk =>
            if st.stack != #[] then
              throw (IO.userError s!"nonordinary-cc-typechk: expected empty stack, got {reprStr st.stack}")
            else if st.cc != .quit 44 then
              throw (IO.userError s!"nonordinary-cc-typechk: cc changed {reprStr st.cc}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"nonordinary-cc-typechk: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "nonordinary-cc-typechk: expected typeChk, got success") }
    ,
    { name := "unit/regression/captured-stack-uses-pushed-slice-as-arg"
      run := do
        let ccRest : Continuation := .ordinary partialCcSlice (.quit 0) OrdCregs.empty OrdCdata.empty
        let contCaptured : Continuation := mkOrdCont 1 #[intV 42]
        let (res, st) := runJmpxdataRaw (mkJmpxdataStack #[intV 99] contCaptured) ccRest
        match res with
        | .error e =>
            throw (IO.userError s!"captured-uses-pushed-slice: expected success, got {e}")
        | .ok _ =>
            if st.stack != #[intV 42, .slice partialCcSlice] then
              throw (IO.userError s!"captured-uses-pushed-slice: stack mismatch {reprStr st.stack}")
            else if st.cc != contCaptured then
              throw (IO.userError s!"captured-uses-pushed-slice: expected cc=contCaptured, got {reprStr st.cc}")
            else
              pure () }
    ,
    { name := "unit/decode-gates"
      run := do
        expectDecodeOkJmpxdata "decode/bare" bareJmpxdataCode
        expectDecodeOkJmpxdata "decode/with-tail" (mkJmpxdataCode #[.pushInt (.num 9)])
        expectDecodeErr "decode/truncated-8" truncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" truncated15Code .invOpcode
        expectDecodeErr "decode/empty" emptyCode .invOpcode }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runJmpxdataDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/match-jmpxdata"
          (runJmpxdataDispatchFallback jmpxdataInstr #[q0])
          #[.slice emptySlice] }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec jmpxdataId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.JMPXDATA
