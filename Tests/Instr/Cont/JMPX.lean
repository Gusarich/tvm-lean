import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.JMPX

/-
JMPX branch map (Lean vs C++):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Jmpx.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popCont`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.jump`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_jmpx`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::jump`, `adjust_jump_cont`)

Coverage goals in this suite:
- dispatch: `.jmpx` handled vs fallback to `next`;
- pre-pop gate: empty stack -> `stkUnd`;
- pop/type order: top value popped then checked as continuation (`typeChk` on non-cont);
- taken path semantics: success jumps via `VM.jump` (not `jumpTo`), including
  closure/captured-stack branches in raw unit tests;
- decode gates: cp0 `0xd9` decode success vs truncated/empty code (`invOpcode`);
- deterministic oracle-only coverage with stack-token constraints (`K=quit(0)` only).
-/

private def jmpxId : InstrId := { name := "JMPX" }
private def jmpxInstr : Instr := .jmpx

private def dispatchSentinel : Int := 90441

private def q0 : Value := .cont (.quit 0)

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice := Slice.ofCell refCellA
private def fullSliceB : Slice := Slice.ofCell refCellB

private def opcodeBits : BitString :=
  natToBits 0xd9 8

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

private def mkJmpxCode (tail : Array Instr := #[]) : Cell :=
  Cell.mkOrdinary (opcodeBits ++ assembleNoRefBits! "jmpx/tail" tail) #[]

private def bareJmpxCode : Cell :=
  mkJmpxCode #[]

private def truncated7Code : Cell :=
  Cell.mkOrdinary (opcodeBits.take 7) #[]

private def truncated1Code : Cell :=
  Cell.mkOrdinary (opcodeBits.take 1) #[]

private def emptyCode : Cell :=
  Cell.empty

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def mkEnvCont
    (ext : Continuation := .quit 0)
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .envelope ext OrdCregs.empty { stack := captured, nargs := nargs }

private def mkJmpxStack
    (below : Array Value)
    (cont : Continuation := .quit 0) : Array Value :=
  below ++ #[.cont cont]

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def runJmpxDirect
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowJmpx jmpxInstr stack

private def runJmpxDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowJmpx instr (VM.push (intV dispatchSentinel)) stack

private def runJmpxRaw
    (stack : Array Value)
    (cc : Continuation := .quit 0)
    (gas : GasLimits := GasLimits.default) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc, gas := gas }
  (execInstrFlowJmpx jmpxInstr (pure ())).run st0

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

private def expectDecodeOkJmpx
    (label : String)
    (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (.jmpx, bits, _) =>
      if bits = 8 then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decoded bits=8, got {bits}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected JMPX, got instr={reprStr instr}, bits={bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[jmpxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpxId
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
    instr := jmpxId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkJumpCase
    (name : String)
    (below : Array Value)
    (program : Array Instr := #[jmpxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name (mkJmpxStack below) program gasLimits fuel

private def jmpxGasExact : Int :=
  computeExactGasBudget jmpxInstr

private def jmpxGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne jmpxInstr

private def jmpxOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/deep/",
    "order/tail/",
    "order/prelude/",
    "err/underflow/",
    "err/type/",
    "decode/truncated7/",
    "decode/truncated1/",
    "decode/empty-code/",
    "gas/"
  ]

private def jmpxFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := jmpxOracleFamilies
    mutationModes := #[
      0, 0, 0, 0,
      1, 1, 1,
      2, 2,
      3, 3, 3,
      4
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success: unconditional jump (`JMPX`) with oracle-supported continuation token `K=quit(0)`.
  mkJumpCase "ok/basic/empty-below" #[],
  mkJumpCase "ok/basic/int-zero" #[intV 0],
  mkJumpCase "ok/basic/int-neg" #[intV (-5)],
  mkJumpCase "ok/basic/max-int257" #[intV maxInt257],
  mkJumpCase "ok/basic/min-plus1" #[intV (minInt257 + 1)],
  mkJumpCase "ok/basic/cell" #[.cell refCellA],
  mkJumpCase "ok/basic/slice" #[.slice fullSliceA],
  mkJumpCase "ok/basic/builder-empty" #[.builder Builder.empty],
  mkJumpCase "ok/basic/tuple-empty" #[.tuple #[]],
  mkJumpCase "ok/basic/cont-below" #[q0],
  mkJumpCase "ok/deep/null-int" #[.null, intV 9],
  mkJumpCase "ok/deep/cell-slice-int" #[.cell refCellB, .slice fullSliceA, intV 3],
  mkJumpCase "ok/deep/builder-tuple-int" #[.builder Builder.empty, .tuple #[], intV (-9)],
  mkJumpCase "ok/deep/long-int-prefix" (intStackAsc 12),
  mkJumpCase "ok/deep/mixed-with-cont" #[.null, q0, intV 1],

  -- Ordering: tail must be skipped after JMPX.
  mkJumpCase "order/tail/push-skipped" #[] #[jmpxInstr, .pushInt (.num 777)],
  mkJumpCase "order/tail/retalt-skipped" #[] #[jmpxInstr, .retAlt],
  mkJumpCase "order/tail/add-underflow-skipped" #[] #[jmpxInstr, .add],
  mkJumpCase "order/tail/two-ops-skipped" #[intV 2, intV 3]
    #[jmpxInstr, .pushInt (.num 11), .add],
  mkJumpCase "order/tail/deep-preserved" #[.null, .cell refCellA, intV 8]
    #[jmpxInstr, .pushInt (.num 19)],
  mkCase "order/prelude/push-swap-jmp" #[q0]
    #[.pushInt (.num 9), .xchg0 1, jmpxInstr, .add],
  mkCase "order/prelude/deep-push-swap-jmp" #[intV 4, q0]
    #[.pushInt (.num 7), .xchg0 1, jmpxInstr, .pushInt (.num 55)],
  mkCase "order/prelude/push-push-swap-jmp" #[q0]
    #[.pushInt (.num 4), .pushInt (.num 5), .xchg0 1, .xchg0 1, jmpxInstr, .add],

  -- Runtime errors at `pop_cont`.
  mkCase "err/underflow/empty" #[],
  mkCase "err/type/top-int" #[intV 1],
  mkCase "err/type/top-null" #[.null],
  mkCase "err/type/top-cell" #[.cell refCellA],
  mkCase "err/type/top-slice" #[.slice fullSliceA],
  mkCase "err/type/top-builder" #[.builder Builder.empty],
  mkCase "err/type/top-tuple" #[.tuple #[]],
  mkCase "err/type/top-int-with-below" #[intV 9, intV 1],
  mkCase "err/type/top-cell-with-below" #[intV 9, .cell refCellA],
  mkCase "err/type/prelude-push-makes-int-top" #[q0] #[.pushInt (.num 1), jmpxInstr],

  -- Decode gates (cp0 prefix/truncation).
  mkCodeCase "decode/truncated7/empty" #[] truncated7Code,
  mkCodeCase "decode/truncated1/empty" #[] truncated1Code,
  mkCodeCase "decode/empty-code/empty" #[] emptyCode,
  mkCodeCase "decode/truncated7/with-k" #[q0] truncated7Code,
  mkCodeCase "decode/truncated1/with-int" #[intV 3] truncated1Code,
  mkCodeCase "decode/empty-code/with-k" #[q0] emptyCode,
  mkCodeCase "decode/truncated7/with-mixed" #[.null, intV 5, q0] truncated7Code,
  mkCodeCase "decode/truncated1/with-mixed" #[.cell refCellB, .slice fullSliceB] truncated1Code,

  -- Gas boundary probes for the JMPX opcode itself.
  mkJumpCase "gas/exact-cost-succeeds" #[]
    #[.pushInt (.num jmpxGasExact), .tonEnvOp .setGasLimit, jmpxInstr],
  mkJumpCase "gas/exact-minus-one-out-of-gas" #[]
    #[.pushInt (.num jmpxGasExactMinusOne), .tonEnvOp .setGasLimit, jmpxInstr]
]

def suite : InstrSuite where
  id := jmpxId
  unit := #[
    { name := "unit/direct/pop-and-preserve-below"
      run := do
        expectOkStack "direct/empty" (runJmpxDirect (mkJmpxStack #[] (.quit 7))) #[]
        expectOkStack "direct/deep-mixed"
          (runJmpxDirect (mkJmpxStack #[.null, intV 9, .cell refCellB, .slice fullSliceA] (.quit 7)))
          #[.null, intV 9, .cell refCellB, .slice fullSliceA] }
    ,
    { name := "unit/raw/cc-transition-on-success"
      run := do
        let ccInit : Continuation := .quit 123
        let target : Continuation := .quit 7
        let (res, st) := runJmpxRaw (mkJmpxStack #[intV 3] target) ccInit
        match res with
        | .error e =>
            throw (IO.userError s!"raw/cc-transition: expected success, got {e}")
        | .ok _ =>
            if st.stack != #[intV 3] then
              throw (IO.userError s!"raw/cc-transition: stack mismatch {reprStr st.stack}")
            else if st.cc != target then
              throw (IO.userError s!"raw/cc-transition: expected cc={reprStr target}, got {reprStr st.cc}")
            else
              pure () }
    ,
    { name := "unit/error/underflow-and-type-pop-order"
      run := do
        expectErr "underflow/empty" (runJmpxDirect #[]) .stkUnd
        expectErr "type/top-int" (runJmpxDirect #[intV 1]) .typeChk
        expectErr "type/top-null" (runJmpxDirect #[.null]) .typeChk

        let (resType, stType) := runJmpxRaw #[intV 77, .null] (.quit 10)
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
    { name := "unit/regression/jump-enforces-nargs-underflow"
      run := do
        let ccInit : Continuation := .quit 55
        let need2 : Continuation := mkOrdCont 2 #[]
        let (res, st) := runJmpxRaw (mkJmpxStack #[intV 5] need2) ccInit
        match res with
        | .error .stkUnd =>
            if st.stack != #[intV 5] then
              throw (IO.userError s!"nargs-underflow: stack mismatch {reprStr st.stack}")
            else if st.cc != ccInit then
              throw (IO.userError s!"nargs-underflow: cc changed {reprStr st.cc}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"nargs-underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "nargs-underflow: expected stkUnd, got success") }
    ,
    { name := "unit/regression/jump-applies-captured-stack-ordinary"
      run := do
        let contCaptured : Continuation := mkOrdCont 1 #[intV 42]
        let (res, st) := runJmpxRaw (mkJmpxStack #[.null, intV 99] contCaptured) (.quit 71)
        match res with
        | .error e =>
            throw (IO.userError s!"captured-ordinary: expected success, got {e}")
        | .ok _ =>
            if st.stack != #[intV 42, intV 99] then
              throw (IO.userError s!"captured-ordinary: expected #[42,99], got {reprStr st.stack}")
            else if st.cc != contCaptured then
              throw (IO.userError s!"captured-ordinary: expected cc=contCaptured, got {reprStr st.cc}")
            else
              pure () }
    ,
    { name := "unit/regression/jump-applies-captured-stack-envelope"
      run := do
        let contCaptured : Continuation := mkEnvCont (.quit 0) 1 #[intV 55]
        let (res, st) := runJmpxRaw (mkJmpxStack #[intV 7, intV 8] contCaptured) (.quit 72)
        match res with
        | .error e =>
            throw (IO.userError s!"captured-envelope: expected success, got {e}")
        | .ok _ =>
            if st.stack != #[intV 55, intV 8] then
              throw (IO.userError s!"captured-envelope: expected #[55,8], got {reprStr st.stack}")
            else if st.cc != contCaptured then
              throw (IO.userError s!"captured-envelope: expected cc=contCaptured, got {reprStr st.cc}")
            else
              pure () }
    ,
    { name := "unit/regression/jump-nargs-zero-drops-stack"
      run := do
        let contZero : Continuation := mkOrdCont 0 #[]
        let (res, st) := runJmpxRaw (mkJmpxStack #[intV 7, intV 8] contZero) (.quit 73)
        match res with
        | .error e =>
            throw (IO.userError s!"nargs-zero: expected success, got {e}")
        | .ok _ =>
            if st.stack != #[] then
              throw (IO.userError s!"nargs-zero: expected empty stack, got {reprStr st.stack}")
            else if st.cc != contZero then
              throw (IO.userError s!"nargs-zero: expected cc=contZero, got {reprStr st.cc}")
            else
              pure () }
    ,
    { name := "unit/regression/stack-gas-for-captured-branch"
      run := do
        let captured : Array Value := intStackAsc 40
        let below : Array Value := intStackAsc 10
        let contGas : Continuation := mkOrdCont 10 captured
        let (res, st) := runJmpxRaw (mkJmpxStack below contGas) (.quit 74)
        match res with
        | .error e =>
            throw (IO.userError s!"stack-gas: expected success, got {e}")
        | .ok _ =>
            let expectedStack : Array Value := captured ++ below
            let expectedDepth : Nat := expectedStack.size
            let expectedGas : Int :=
              Int.ofNat (expectedDepth - freeStackDepth) * stackEntryGasPrice
            if st.stack != expectedStack then
              throw (IO.userError s!"stack-gas: expected stack mismatch {reprStr st.stack}")
            else if st.gas.gasConsumed != expectedGas then
              throw (IO.userError
                s!"stack-gas: expected gasConsumed={expectedGas}, got {st.gas.gasConsumed}")
            else
              pure () }
    ,
    { name := "unit/decode-gates"
      run := do
        expectDecodeOkJmpx "decode/bare" bareJmpxCode
        expectDecodeOkJmpx "decode/with-tail" (mkJmpxCode #[.pushInt (.num 9)])
        expectDecodeErr "decode/truncated-7" truncated7Code .invOpcode
        expectDecodeErr "decode/truncated-1" truncated1Code .invOpcode
        expectDecodeErr "decode/empty" emptyCode .invOpcode }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runJmpxDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/match-jmpx"
          (runJmpxDispatchFallback jmpxInstr #[q0])
          #[] }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile jmpxId jmpxFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.JMPX
