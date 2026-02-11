import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFNOTRETALT

/-
IFNOTRETALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/IfretAlt.lean` (`.contExt .ifnotretAlt`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popBool`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.retAlt`, `VM.jump`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` / `TvmLean/Model/Instr/Asm/Cp0.lean` (opcode `0xe309`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_ifnotretalt`, opcode registration)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_bool`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::ret_alt`, `VmState::jump`, `adjust_jump_cont`)

Branch map covered by this suite:
- dispatch: only `.contExt .ifnotretAlt` executes here; all others fall through to `next`;
- bool parsing: top stack item must be finite integer (`0` => taken branch, non-zero => not taken);
- error ordering before branch: underflow/type/intOv from `pop_bool` happen before any `ret_alt` effect;
- taken branch: must call `ret_alt` semantics (swap `c1 := quit1`, then jump old `c1`);
- jump path parity: taken branch uses full `jump` closure semantics (including `nargs` underflow checks);
- opcode parity: assemble/decode around `IFRETALT(0xe308)` and `IFNOTRETALT(0xe309)`.
-/

private def ifnotretaltId : InstrId := { name := "IFNOTRETALT" }

private def ifnotretaltInstr : Instr := .contExt .ifnotretAlt

private def ifretaltInstr : Instr := .contExt .ifretAlt

private def dispatchSentinel : Int := 91011

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def q0 : Value := .cont (.quit 0)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def fullSliceA : Slice := Slice.ofCell refLeafA

private def fullSliceB : Slice := Slice.ofCell refLeafB

private def ordinaryCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def envelopeCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .envelope (.quit 5) OrdCregs.empty { stack := captured, nargs := nargs }

private def mkIfnotretaltCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifnotretaltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnotretaltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runIfnotretaltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfretAlt ifnotretaltInstr stack

private def runIfnotretaltDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfretAlt instr (VM.push (intV dispatchSentinel)) stack

private def runIfnotretaltRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowIfretAlt ifnotretaltInstr (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
  match res with
  | (.ok _, st) => pure st
  | (.error e, _) =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectContEq
    (label : String)
    (actual expected : Continuation) : IO Unit := do
  if actual == expected then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected continuation {reprStr expected}, got {reprStr actual}")

private def ifnotretaltSetGasExact : Int :=
  computeExactGasBudget ifnotretaltInstr

private def ifnotretaltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifnotretaltInstr

def suite : InstrSuite where
  id := ifnotretaltId
  unit := #[
    { name := "unit/direct/stack-preserved-on-taken-and-not-taken"
      run := do
        let below : Array Value :=
          #[.null, intV (-7), .cell refLeafA, .builder Builder.empty, .tuple #[], .slice fullSliceA, q0]
        expectOkStack "taken/zero"
          (runIfnotretaltDirect (below ++ #[intV 0]))
          below
        expectOkStack "not-taken/nonzero"
          (runIfnotretaltDirect (below ++ #[intV (-5)]))
          below }
    ,
    { name := "unit/raw/not-taken-keeps-cc-and-c1"
      run := do
        let c1Init : Continuation := .quit 9
        let ccInit : Continuation := .quit 77
        let checks : Array Int := #[1, -1, 2, -2, 255, -255, maxInt257, minInt257]
        for cond in checks do
          let regs := { Regs.initial with c1 := c1Init }
          let st ← expectRawOk s!"raw/not-taken/{cond}"
            (runIfnotretaltRaw #[intV 5, intV cond] regs ccInit)
          if st.stack == #[intV 5] then
            pure ()
          else
            throw (IO.userError s!"raw/not-taken/{cond}: expected stack #[5], got {reprStr st.stack}")
          expectContEq s!"raw/not-taken/{cond}/cc" st.cc ccInit
          expectContEq s!"raw/not-taken/{cond}/c1" st.regs.c1 c1Init }
    ,
    { name := "unit/raw/taken-swaps-c1-and-jumps-to-old-c1"
      run := do
        let c1Init : Continuation := .quit 9
        let ccInit : Continuation := .quit 77
        let regs := { Regs.initial with c1 := c1Init }
        let st ← expectRawOk "raw/taken" (runIfnotretaltRaw #[.null, intV 0] regs ccInit)
        if st.stack == #[.null] then
          pure ()
        else
          throw (IO.userError s!"raw/taken: expected preserved below-stack, got {reprStr st.stack}")
        expectContEq "raw/taken/cc" st.cc c1Init
        expectContEq "raw/taken/c1-swapped" st.regs.c1 (.quit 1) }
    ,
    { name := "unit/raw/taken-uses-jump-closure-semantics"
      run := do
        let ordCaptured := ordinaryCont 1 #[intV 99]
        let regsOrd := { Regs.initial with c1 := ordCaptured }
        let stOrd ← expectRawOk "raw/taken/ordinary-captured"
          (runIfnotretaltRaw #[intV 4, intV 5, intV 0] regsOrd (.quit 50))
        if stOrd.stack == #[intV 99, intV 5] then
          pure ()
        else
          throw (IO.userError
            s!"raw/taken/ordinary-captured: expected #[99,5], got {reprStr stOrd.stack}")
        expectContEq "raw/taken/ordinary-captured/cc" stOrd.cc ordCaptured
        expectContEq "raw/taken/ordinary-captured/c1" stOrd.regs.c1 (.quit 1)

        let envCaptured := envelopeCont 1 #[intV 55]
        let regsEnv := { Regs.initial with c1 := envCaptured }
        let stEnv ← expectRawOk "raw/taken/envelope-captured"
          (runIfnotretaltRaw #[intV 6, intV 7, intV 0] regsEnv (.quit 51))
        if stEnv.stack == #[intV 55, intV 7] then
          pure ()
        else
          throw (IO.userError
            s!"raw/taken/envelope-captured: expected #[55,7], got {reprStr stEnv.stack}")
        expectContEq "raw/taken/envelope-captured/cc" stEnv.cc envCaptured
        expectContEq "raw/taken/envelope-captured/c1" stEnv.regs.c1 (.quit 1) }
    ,
    { name := "unit/raw/error-order-popbool-before-retalt-effects"
      run := do
        let c1NeedArgs := ordinaryCont 2 #[]
        let regs := { Regs.initial with c1 := c1NeedArgs }
        let ccInit : Continuation := .quit 88

        let (underflowRes, underflowSt) := runIfnotretaltRaw #[] regs ccInit
        match underflowRes with
        | .error .stkUnd =>
            if underflowSt.stack == #[] then
              pure ()
            else
              throw (IO.userError s!"underflow/stack-mutated: {reprStr underflowSt.stack}")
            expectContEq "underflow/cc" underflowSt.cc ccInit
            expectContEq "underflow/c1-unchanged" underflowSt.regs.c1 c1NeedArgs
        | .error e =>
            throw (IO.userError s!"underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "underflow: expected stkUnd, got success")

        let (typeRes, typeSt) := runIfnotretaltRaw #[.null] regs ccInit
        match typeRes with
        | .error .typeChk =>
            if typeSt.stack == #[] then
              pure ()
            else
              throw (IO.userError s!"type/popbool: expected empty stack after pop, got {reprStr typeSt.stack}")
            expectContEq "type/popbool/cc" typeSt.cc ccInit
            expectContEq "type/popbool/c1-unchanged" typeSt.regs.c1 c1NeedArgs
        | .error e =>
            throw (IO.userError s!"type/popbool: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "type/popbool: expected typeChk, got success")

        let (nanRes, nanSt) := runIfnotretaltRaw #[.int .nan] regs ccInit
        match nanRes with
        | .error .intOv =>
            if nanSt.stack == #[] then
              pure ()
            else
              throw (IO.userError s!"nan/popbool: expected empty stack after pop, got {reprStr nanSt.stack}")
            expectContEq "nan/popbool/cc" nanSt.cc ccInit
            expectContEq "nan/popbool/c1-unchanged" nanSt.regs.c1 c1NeedArgs
        | .error e =>
            throw (IO.userError s!"nan/popbool: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "nan/popbool: expected intOv, got success") }
    ,
    { name := "unit/raw/taken-jump-underflow-after-pop-swaps-c1"
      run := do
        let c1NeedTwo := ordinaryCont 2 #[]
        let regs := { Regs.initial with c1 := c1NeedTwo }
        let ccInit : Continuation := .quit 123
        let (res, st) := runIfnotretaltRaw #[intV 7, intV 0] regs ccInit
        match res with
        | .error .stkUnd =>
            if st.stack == #[intV 7] then
              pure ()
            else
              throw (IO.userError s!"taken/jump-underflow: expected bool popped first, got {reprStr st.stack}")
            expectContEq "taken/jump-underflow/cc-unchanged" st.cc ccInit
            expectContEq "taken/jump-underflow/c1-swapped" st.regs.c1 (.quit 1)
        | .error e =>
            throw (IO.userError s!"taken/jump-underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "taken/jump-underflow: expected stkUnd, got success") }
    ,
    { name := "unit/dispatch/fallback-and-match-contract"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfnotretaltDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/matching-ifretalt-does-not-run-next"
          (runIfnotretaltDispatchFallback ifretaltInstr #[intV 1])
          #[]
        expectOkStack "dispatch/matching-ifnotretalt-does-not-run-next"
          (runHandlerDirectWithNext execInstrFlowIfretAlt ifnotretaltInstr (VM.push (intV dispatchSentinel)) #[intV 1])
          #[] }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let seq : Array Instr := #[ifretaltInstr, ifnotretaltInstr, .add]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ifretalt" s0 ifretaltInstr 16
        let s2 ← expectDecodeStep "decode/ifnotretalt" s1 ifnotretaltInstr 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/seq-end: expected exhausted bits, got {s3.bitsRemaining}")

        let ifnotretaltCode ←
          match assembleCp0 [ifnotretaltInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/ifnotretalt failed: {reprStr e}")
        if ifnotretaltCode.bits = natToBits 0xe309 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ifnotretalt: expected 0xe309, got {reprStr ifnotretaltCode.bits}")

        let rawBits : BitString :=
          natToBits 0xe308 16 ++
          natToBits 0xe309 16 ++
          natToBits 0xa0 8
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-ifretalt" r0 ifretaltInstr 16
        let r2 ← expectDecodeStep "decode/raw-ifnotretalt" r1 ifnotretaltInstr 16
        let r3 ← expectDecodeStep "decode/raw-tail-add" r2 .add 8
        if r3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted bits, got {r3.bitsRemaining}") }
    ,
    { name := "unit/gas/probe-budget-ordering"
      run := do
        if ifnotretaltSetGasExact > 0 then
          pure ()
        else
          throw (IO.userError s!"gas/exact: expected positive budget, got {ifnotretaltSetGasExact}")
        if ifnotretaltSetGasExactMinusOne < ifnotretaltSetGasExact then
          pure ()
        else
          throw (IO.userError
            s!"gas/exact-minus-one: expected strict decrease, got exact={ifnotretaltSetGasExact} minusOne={ifnotretaltSetGasExactMinusOne}") }
  ]
  oracle := #[
    mkIfnotretaltCase "ok/taken/zero-empty" #[intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-int-below" #[intV 7, intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-null-below" #[.null, intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-cell-below" #[.cell refLeafA, intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-builder-below" #[.builder Builder.empty, intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-tuple-below" #[.tuple #[], intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-slice-below" #[.slice fullSliceA, intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-cont-below" #[q0, intV 0],
    mkIfnotretaltCase "ok/taken/zero-with-mixed-below"
      #[.null, intV (-3), .cell refLeafB, .builder Builder.empty, .tuple #[], intV 0],

    mkIfnotretaltCase "ok/not-taken/one" #[intV 1],
    mkIfnotretaltCase "ok/not-taken/neg-one" #[intV (-1)],
    mkIfnotretaltCase "ok/not-taken/two" #[intV 2],
    mkIfnotretaltCase "ok/not-taken/neg-two" #[intV (-2)],
    mkIfnotretaltCase "ok/not-taken/large-pos" #[intV (intPow2 64)],
    mkIfnotretaltCase "ok/not-taken/large-neg" #[intV (-(intPow2 64))],
    mkIfnotretaltCase "ok/not-taken/max-int257" #[intV maxInt257],
    mkIfnotretaltCase "ok/not-taken/min-int257" #[intV minInt257],
    mkIfnotretaltCase "ok/not-taken/with-int-below" #[intV 7, intV 1],
    mkIfnotretaltCase "ok/not-taken/with-null-below" #[.null, intV 1],
    mkIfnotretaltCase "ok/not-taken/with-cell-below" #[.cell refLeafB, intV (-5)],
    mkIfnotretaltCase "ok/not-taken/with-builder-below" #[.builder Builder.empty, intV 255],
    mkIfnotretaltCase "ok/not-taken/with-tuple-below" #[.tuple #[], intV (-255)],
    mkIfnotretaltCase "ok/not-taken/with-slice-below" #[.slice fullSliceB, intV 123456],
    mkIfnotretaltCase "ok/not-taken/with-cont-below" #[q0, intV 1],
    mkIfnotretaltCase "ok/not-taken/with-mixed-below"
      #[.null, intV 99, .cell refLeafA, .builder Builder.empty, intV (-42)],

    mkIfnotretaltCase "underflow/empty" #[],

    mkIfnotretaltCase "type/top-null" #[.null],
    mkIfnotretaltCase "type/top-cell" #[.cell refLeafA],
    mkIfnotretaltCase "type/top-builder" #[.builder Builder.empty],
    mkIfnotretaltCase "type/top-tuple" #[.tuple #[]],
    mkIfnotretaltCase "type/top-slice" #[.slice fullSliceA],
    mkIfnotretaltCase "type/top-cont" #[q0],

    mkIfnotretaltCase "intov/nan-top-via-program"
      #[]
      #[.pushInt .nan, ifnotretaltInstr],
    mkIfnotretaltCase "intov/nan-over-null-via-program"
      #[.null]
      #[.pushInt .nan, ifnotretaltInstr],
    mkIfnotretaltCase "intov/nan-over-two-below-via-program"
      #[.cell refLeafA, intV 7]
      #[.pushInt .nan, ifnotretaltInstr],

    mkIfnotretaltCase "gas/exact/taken"
      #[intV 0]
      #[.pushInt (.num ifnotretaltSetGasExact), .tonEnvOp .setGasLimit, ifnotretaltInstr],

    mkIfnotretaltCase "gas/exact-minus-one/taken"
      #[intV 0]
      #[.pushInt (.num ifnotretaltSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotretaltInstr],

    mkIfnotretaltCase "gas/exact/not-taken"
      #[intV 1]
      #[.pushInt (.num ifnotretaltSetGasExact), .tonEnvOp .setGasLimit, ifnotretaltInstr],

    mkIfnotretaltCase "gas/exact-minus-one/not-taken"
      #[intV 1]
      #[.pushInt (.num ifnotretaltSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotretaltInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.IFNOTRETALT
