import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFNBITJMP

/-
IFNBITJMP branch map (Lean vs C++ `exec_if_bit_jmp`):
- opcode dispatch: only `.contExt (.ifnbitjmp idx)` is handled here, others fall through to `next`;
- pre-check: `check_underflow(2)` / `VM.checkUnderflow 2` before any pop;
- pop order: pop continuation first, then pop finite integer operand;
- integer checks: non-int => `typeChk`, NaN/non-finite => `intOv`;
- bit extraction: C++ uses `x->get_bit(bit)` with `bit = args & 0x1f`; cp0 decode constrains `idx` to 0..31;
- stack effect on success: `cont` consumed, `x` preserved (C++ pop+push; Lean now mirrors this);
- branch predicate: jump iff extracted bit is `false` (`val ^ negate` with `negate = true` for IFNBITJMP);
- taken path must use `VM.jump`/`VmState::jump` semantics (nargs checks + captured stack application).

Regression fixed in Lean:
- `IFNBITJMP` used `fetch` for `x` instead of `pop_int_finite` + re-push.
- This mismatched C++ stack effects on errors at int-pop site.
-/

private def ifnbitjmpId : InstrId := { name := "IFNBITJMP" }

private def ifnbitjmpInstr (idx : Nat) : Instr :=
  .contExt (.ifnbitjmp idx)

private def q0 : Value :=
  .cont (.quit 0)

private def tailMarker : Int := 777

private def dispatchSentinel : Int := 53021

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice :=
  Slice.ofCell refCellA

private def fullSliceB : Slice :=
  Slice.ofCell refCellB

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def mkIfnbitStack
    (below : Array Value)
    (x : Int)
    (cont : Continuation := .quit 0) : Array Value :=
  below ++ #[intV x, .cont cont]

private def branchProbeProgram (idx : Nat) : Array Instr :=
  #[ifnbitjmpInstr idx, .pushInt (.num tailMarker)]

private def nanOperandProgram (idx : Nat) : Array Instr :=
  #[.pushInt .nan, .xchg0 1, ifnbitjmpInstr idx]

private def popContBeforeNanProgram (idx : Nat) : Array Instr :=
  #[.pushInt .nan, ifnbitjmpInstr idx]

private def mkCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (program : Array Instr := #[ifnbitjmpInstr idx])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnbitjmpId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkProbeCase
    (name : String)
    (idx : Nat)
    (x : Int)
    (below : Array Value := #[]) : OracleCase :=
  mkCase name idx (mkIfnbitStack below x) (branchProbeProgram idx)

private def runIfnbitjmpDirect
    (idx : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfBitJmp (ifnbitjmpInstr idx) stack

private def runIfnbitjmpDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfBitJmp instr (VM.push (intV dispatchSentinel)) stack

private def runIfnbitjmpRaw
    (idx : Nat)
    (stack : Array Value)
    (cc : Continuation := .quit 0) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc }
  (execInstrFlowIfBitJmp (ifnbitjmpInstr idx) (pure ())).run st0

private def ifnbitjmpSetGasExact : Int :=
  computeExactGasBudget (ifnbitjmpInstr 0)

private def ifnbitjmpSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (ifnbitjmpInstr 0)

def suite : InstrSuite where
  id := ifnbitjmpId
  unit := #[
    { name := "unit/raw/branch-predicate-updates-cc"
      run := do
        let ccInit : Continuation := .quit 91
        let target : Continuation := .quit 13

        let (rTaken0, sTaken0) := runIfnbitjmpRaw 0 (mkIfnbitStack #[] 2 target) ccInit
        match rTaken0 with
        | .error e => throw (IO.userError s!"taken/idx0: expected success, got {e}")
        | .ok _ =>
            if sTaken0.stack != #[intV 2] then
              throw (IO.userError s!"taken/idx0: stack mismatch {reprStr sTaken0.stack}")
            else if sTaken0.cc != target then
              throw (IO.userError s!"taken/idx0: cc mismatch {reprStr sTaken0.cc}")
            else
              pure ()

        let (rNotTaken0, sNotTaken0) := runIfnbitjmpRaw 0 (mkIfnbitStack #[] 1 target) ccInit
        match rNotTaken0 with
        | .error e => throw (IO.userError s!"not-taken/idx0: expected success, got {e}")
        | .ok _ =>
            if sNotTaken0.stack != #[intV 1] then
              throw (IO.userError s!"not-taken/idx0: stack mismatch {reprStr sNotTaken0.stack}")
            else if sNotTaken0.cc != ccInit then
              throw (IO.userError s!"not-taken/idx0: cc should remain unchanged, got {reprStr sNotTaken0.cc}")
            else
              pure ()

        let (rTaken31, sTaken31) := runIfnbitjmpRaw 31 (mkIfnbitStack #[] ((pow2 31) - 1) target) ccInit
        match rTaken31 with
        | .error e => throw (IO.userError s!"taken/idx31: expected success, got {e}")
        | .ok _ =>
            if sTaken31.stack != #[intV ((pow2 31) - 1)] then
              throw (IO.userError s!"taken/idx31: stack mismatch {reprStr sTaken31.stack}")
            else if sTaken31.cc != target then
              throw (IO.userError s!"taken/idx31: cc mismatch {reprStr sTaken31.cc}")
            else
              pure ()

        let (rNotTaken31, sNotTaken31) := runIfnbitjmpRaw 31 (mkIfnbitStack #[] (pow2 31) target) ccInit
        match rNotTaken31 with
        | .error e => throw (IO.userError s!"not-taken/idx31: expected success, got {e}")
        | .ok _ =>
            if sNotTaken31.stack != #[intV (pow2 31)] then
              throw (IO.userError s!"not-taken/idx31: stack mismatch {reprStr sNotTaken31.stack}")
            else if sNotTaken31.cc != ccInit then
              throw (IO.userError s!"not-taken/idx31: cc should remain unchanged, got {reprStr sNotTaken31.cc}")
            else
              pure () }
    ,
    { name := "unit/error/underflow-before-any-pop"
      run := do
        expectErr "underflow/empty" (runIfnbitjmpDirect 0 #[]) .stkUnd
        expectErr "underflow/one-int" (runIfnbitjmpDirect 0 #[intV 0]) .stkUnd
        expectErr "underflow/one-cont" (runIfnbitjmpDirect 0 #[q0]) .stkUnd

        let singleton : Array Value := #[.null]
        let (res, st) := runIfnbitjmpRaw 0 singleton (.quit 7)
        match res with
        | .error .stkUnd =>
            if st.stack == singleton then
              pure ()
            else
              throw (IO.userError s!"underflow/singleton-mutated: got {reprStr st.stack}")
        | .error e =>
            throw (IO.userError s!"underflow/singleton: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "underflow/singleton: expected stkUnd, got success") }
    ,
    { name := "unit/error/pop-cont-site"
      run := do
        expectErr "type/top-int" (runIfnbitjmpDirect 0 #[intV 1, intV 2]) .typeChk
        expectErr "type/top-null" (runIfnbitjmpDirect 0 #[intV 1, .null]) .typeChk
        expectErr "type/top-cell" (runIfnbitjmpDirect 0 #[intV 1, .cell refCellA]) .typeChk
        expectErr "type/top-builder" (runIfnbitjmpDirect 0 #[intV 1, .builder Builder.empty]) .typeChk
        expectErr "type/top-slice" (runIfnbitjmpDirect 0 #[intV 1, .slice fullSliceA]) .typeChk

        let (resOrder, stOrder) := runIfnbitjmpRaw 0 #[.int .nan, intV 9] (.quit 77)
        match resOrder with
        | .error .typeChk =>
            if stOrder.stack == #[.int .nan] then
              pure ()
            else
              throw (IO.userError s!"popcont/order-stack-mismatch: {reprStr stOrder.stack}")
        | .error e =>
            throw (IO.userError s!"popcont/order: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "popcont/order: expected typeChk, got success") }
    ,
    { name := "unit/error/pop-int-finite-site-stack-effects"
      run := do
        let (rType, sType) := runIfnbitjmpRaw 0 #[intV 88, .null, .cont (.quit 0)] (.quit 10)
        match rType with
        | .error .typeChk =>
            if sType.stack == #[intV 88] then
              pure ()
            else
              throw (IO.userError s!"pop-int/type: stack mismatch {reprStr sType.stack}")
        | .error e =>
            throw (IO.userError s!"pop-int/type: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "pop-int/type: expected typeChk, got success")

        let (rNan, sNan) := runIfnbitjmpRaw 0 #[intV 99, .int .nan, .cont (.quit 0)] (.quit 10)
        match rNan with
        | .error .intOv =>
            if sNan.stack == #[intV 99] then
              pure ()
            else
              throw (IO.userError s!"pop-int/nan: stack mismatch {reprStr sNan.stack}")
        | .error e =>
            throw (IO.userError s!"pop-int/nan: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "pop-int/nan: expected intOv, got success") }
    ,
    { name := "unit/bit-semantics/signed-values"
      run := do
        let ccInit : Continuation := .quit 21
        let target : Continuation := .quit 22

        let (rNeg1, sNeg1) := runIfnbitjmpRaw 0 (mkIfnbitStack #[] (-1) target) ccInit
        match rNeg1 with
        | .error e => throw (IO.userError s!"neg1/idx0: expected success, got {e}")
        | .ok _ =>
            if sNeg1.cc != ccInit then
              throw (IO.userError s!"neg1/idx0: expected no jump")
            else
              pure ()

        let (rNeg2Bit0, sNeg2Bit0) := runIfnbitjmpRaw 0 (mkIfnbitStack #[] (-2) target) ccInit
        match rNeg2Bit0 with
        | .error e => throw (IO.userError s!"neg2/idx0: expected success, got {e}")
        | .ok _ =>
            if sNeg2Bit0.cc != target then
              throw (IO.userError s!"neg2/idx0: expected jump")
            else
              pure ()

        let (rNeg2Bit1, sNeg2Bit1) := runIfnbitjmpRaw 1 (mkIfnbitStack #[] (-2) target) ccInit
        match rNeg2Bit1 with
        | .error e => throw (IO.userError s!"neg2/idx1: expected success, got {e}")
        | .ok _ =>
            if sNeg2Bit1.cc != ccInit then
              throw (IO.userError s!"neg2/idx1: expected no jump")
            else
              pure ()

        let (rMin257Bit31, sMin257Bit31) :=
          runIfnbitjmpRaw 31 (mkIfnbitStack #[] minInt257 target) ccInit
        match rMin257Bit31 with
        | .error e => throw (IO.userError s!"min257/idx31: expected success, got {e}")
        | .ok _ =>
            if sMin257Bit31.cc != target then
              throw (IO.userError s!"min257/idx31: expected jump")
            else
              pure () }
    ,
    { name := "unit/regression/taken-jump-uses-vm-jump"
      run := do
        let ccInit : Continuation := .quit 123

        let contNeed2 : Continuation := mkOrdCont 2 #[]
        let (rUnd, sUnd) := runIfnbitjmpRaw 0 (mkIfnbitStack #[] 0 contNeed2) ccInit
        match rUnd with
        | .error .stkUnd =>
            if sUnd.stack != #[intV 0] then
              throw (IO.userError s!"jump/nargs-underflow: stack mismatch {reprStr sUnd.stack}")
            else if sUnd.cc != ccInit then
              throw (IO.userError s!"jump/nargs-underflow: cc mismatch {reprStr sUnd.cc}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"jump/nargs-underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "jump/nargs-underflow: expected stkUnd, got success")

        let contCaptured : Continuation := mkOrdCont 1 #[intV 42]
        let (rCap, sCap) := runIfnbitjmpRaw 0 (mkIfnbitStack #[.null, intV 9] 0 contCaptured) (.quit 55)
        match rCap with
        | .error e =>
            throw (IO.userError s!"jump/captured-stack: expected success, got {e}")
        | .ok _ =>
            if sCap.stack != #[intV 42, intV 0] then
              throw (IO.userError s!"jump/captured-stack: expected [42,0], got {reprStr sCap.stack}")
            else if sCap.cc != contCaptured then
              throw (IO.userError s!"jump/captured-stack: cc mismatch {reprStr sCap.cc}")
            else
              pure () }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfnbitjmpDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/match-ifnbitjmp"
          (runIfnbitjmpDispatchFallback (ifnbitjmpInstr 0) (mkIfnbitStack #[] 1 (.quit 0)))
          #[intV 1] }
  ]
  oracle := #[
    mkProbeCase "branch/taken/idx0/x0" 0 0,
    mkProbeCase "branch/taken/idx0/x2" 0 2,
    mkProbeCase "branch/taken/idx1/x1" 1 1,
    mkProbeCase "branch/taken/idx5/xpow4" 5 (pow2 4),
    mkProbeCase "branch/taken/idx5/x0" 5 0,
    mkProbeCase "branch/taken/idx31/xpow31minus1" 31 ((pow2 31) - 1),
    mkProbeCase "branch/taken/idx31/xmin257" 31 minInt257,
    mkProbeCase "branch/taken/deep-null-int" 0 0 #[.null, intV 9],
    mkProbeCase "branch/taken/deep-cell" 31 minInt257 #[.cell refCellA],
    mkProbeCase "branch/taken/deep-builder-tuple" 1 1 #[.builder Builder.empty, .tuple #[]],

    mkProbeCase "branch/not-taken/idx0/x1" 0 1,
    mkProbeCase "branch/not-taken/idx0/xneg1" 0 (-1),
    mkProbeCase "branch/not-taken/idx1/x2" 1 2,
    mkProbeCase "branch/not-taken/idx1/xneg2" 1 (-2),
    mkProbeCase "branch/not-taken/idx5/xpow5" 5 (pow2 5),
    mkProbeCase "branch/not-taken/idx5/xpow5plus3" 5 ((pow2 5) + 3),
    mkProbeCase "branch/not-taken/idx31/xpow31" 31 (pow2 31),
    mkProbeCase "branch/not-taken/idx31/xneg2" 31 (-2),
    mkProbeCase "branch/not-taken/deep-null-int" 0 1 #[.null, intV 9],
    mkProbeCase "branch/not-taken/deep-cell" 1 2 #[.cell refCellA],

    mkCase "ok/no-tail/taken-default" 0 (mkIfnbitStack #[] 0),
    mkCase "ok/no-tail/not-taken-default" 0 (mkIfnbitStack #[] 1),
    mkCase "ok/no-tail/deep-preserve" 31 (mkIfnbitStack #[.slice fullSliceB, .tuple #[]] (pow2 31)),

    mkCase "underflow/empty" 0 #[],
    mkCase "underflow/one-int" 0 #[intV 0],
    mkCase "underflow/one-cont" 0 #[q0],
    mkCase "underflow/one-null" 0 #[.null],

    mkCase "type/popcont/top-int" 0 #[intV 0, intV 1],
    mkCase "type/popcont/top-null" 0 #[intV 0, .null],
    mkCase "type/popcont/top-cell" 0 #[intV 0, .cell refCellA],
    mkCase "type/popcont/top-builder" 0 #[intV 0, .builder Builder.empty],
    mkCase "type/popcont/top-slice" 0 #[intV 0, .slice fullSliceA],
    mkCase "type/popcont/top-tuple" 0 #[intV 0, .tuple #[]],
    mkCase "error-order/popcont-before-popint-type" 0 #[.null, intV 9],
    mkCase "error-order/popcont-before-popint-intov" 0 #[intV 9] (popContBeforeNanProgram 0),

    mkCase "type/popint/null-after-cont" 0 #[.null, q0],
    mkCase "type/popint/cell-after-cont" 0 #[.cell refCellA, q0],
    mkCase "type/popint/builder-after-cont" 0 #[.builder Builder.empty, q0],
    mkCase "type/popint/slice-after-cont" 0 #[.slice fullSliceA, q0],
    mkCase "type/popint/tuple-after-cont" 0 #[.tuple #[], q0],
    mkCase "intov/popint/nan-after-cont" 0 #[q0] (nanOperandProgram 0),
    mkCase "intov/popint/nan-after-cont-with-below" 31 #[intV 9, q0] (nanOperandProgram 31),

    mkCase "gas/exact-cost-succeeds" 0 (mkIfnbitStack #[] 0)
      #[.pushInt (.num ifnbitjmpSetGasExact), .tonEnvOp .setGasLimit, ifnbitjmpInstr 0],
    mkCase "gas/exact-minus-one-out-of-gas" 0 (mkIfnbitStack #[] 0)
      #[.pushInt (.num ifnbitjmpSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnbitjmpInstr 0]
  ]
  fuzz := #[ mkReplayOracleFuzzSpec ifnbitjmpId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.IFNBITJMP
