import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.RETBOOL

/-
RETBOOL branch mapping (Lean + C++):
- Lean:
  - `TvmLean/Semantics/Exec/Flow/RetBool.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popBool`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.ret`, `VM.retAlt`, `VM.jump`)
  - `TvmLean/Model/Instr/{Codepage,Asm}/Cp0.lean` (`0xdb32`)
- C++:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_ret_bool`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_bool`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::ret`, `VmState::ret_alt`, `VmState::jump`)

Covered branches:
1) dispatch/fallback (`.retBool` vs `next`);
2) pop_bool coercion and error order (underflow/type/intOv; top-first behavior);
3) branch split (`true -> RET`, `false -> RETALT`);
4) RET / RETALT jump subpaths (nargs underflow and reset-before-jump behavior);
5) cp0 decode/asm boundaries (`0xdb30/0xdb31/0xdb32`, truncated prefixes).
-/

private def retBoolId : InstrId := { name := "RETBOOL" }

private def retBoolInstr : Instr := .retBool

private def dispatchSentinel : Int := 92052

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def q0 : Value := .cont (.quit 0)

private def refCellA : Cell := Cell.ofUInt 8 0xa5

private def refCellB : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice := Slice.ofCell refCellA

private def fullSliceB : Slice := Slice.ofCell refCellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[q0, .cell refCellB, .null, intV (-9)]

private def withBool (below : Array Value) (cond : IntVal) : Array Value :=
  below ++ #[.int cond]

private def withRawBool (below : Array Value) (cond : Value) : Array Value :=
  below ++ #[cond]

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty
    { stack := captured, nargs := nargs }

private def runRetBoolDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowRetBool retBoolInstr stack

private def runRetBoolDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowRetBool instr (VM.push (intV dispatchSentinel)) stack

private def runRetBoolRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowRetBool retBoolInstr (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  match res with
  | (.ok _, st) => pure st
  | (.error e, _) =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  match res with
  | (.ok _, st) =>
      throw (IO.userError s!"{label}: expected error {expected}, got success with state {reprStr st}")
  | (.error e, st) =>
      if e == expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectContEq
    (label : String)
    (actual expected : Continuation) : IO Unit := do
  if actual == expected then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected continuation {reprStr expected}, got {reprStr actual}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[retBoolInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retBoolId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retBoolId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC0Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, retBoolInstr] ++ tail

private def progSetC1Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num n), .setNumVarArgs, .popCtr 1, retBoolInstr] ++ tail

private def progPushNanRetBool (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt .nan, retBoolInstr] ++ tail

private def retBoolTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def retBoolTruncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits 0xdb32 16).take 15) #[]

def suite : InstrSuite where
  id := retBoolId
  unit := #[
    { name := "unit/state/true-branch-uses-ret-c0-and-resets-c0"
      run := do
        let regs := { Regs.initial with c0 := .quit 9, c1 := .quit 17 }
        let st ← expectRawOk "state/true-branch"
          (runRetBoolRaw #[intV 1] regs)
        if st.stack != #[] then
          throw (IO.userError s!"state/true-branch: expected empty stack, got {reprStr st.stack}")
        expectContEq "state/true-branch/cc" st.cc (.quit 9)
        expectContEq "state/true-branch/c0-reset" st.regs.c0 (.quit 0)
        expectContEq "state/true-branch/c1-unchanged" st.regs.c1 (.quit 17) }
    ,
    { name := "unit/state/false-branch-uses-retalt-c1-and-resets-c1"
      run := do
        let regs := { Regs.initial with c0 := .quit 9, c1 := .quit 17 }
        let st ← expectRawOk "state/false-branch"
          (runRetBoolRaw #[intV 0] regs)
        if st.stack != #[] then
          throw (IO.userError s!"state/false-branch: expected empty stack, got {reprStr st.stack}")
        expectContEq "state/false-branch/cc" st.cc (.quit 17)
        expectContEq "state/false-branch/c0-unchanged" st.regs.c0 (.quit 9)
        expectContEq "state/false-branch/c1-reset" st.regs.c1 (.quit 1) }
    ,
    { name := "unit/state/true-branch-ret-underflow-resets-c0-after-pop"
      run := do
        let needTwo := mkOrdCont 2 #[]
        let regs := { Regs.initial with c0 := needTwo, c1 := .quit 13 }
        let st ← expectRawErr "state/true-ret-underflow"
          (runRetBoolRaw #[intV 44, intV 1] regs) .stkUnd
        if st.stack != #[intV 44] then
          throw (IO.userError
            s!"state/true-ret-underflow: expected stack #[44], got {reprStr st.stack}")
        expectContEq "state/true-ret-underflow/c0-reset" st.regs.c0 (.quit 0)
        expectContEq "state/true-ret-underflow/c1-unchanged" st.regs.c1 (.quit 13) }
    ,
    { name := "unit/state/false-branch-retalt-underflow-resets-c1-after-pop"
      run := do
        let needTwo := mkOrdCont 2 #[]
        let regs := { Regs.initial with c0 := .quit 12, c1 := needTwo }
        let st ← expectRawErr "state/false-retalt-underflow"
          (runRetBoolRaw #[intV 77, intV 0] regs) .stkUnd
        if st.stack != #[intV 77] then
          throw (IO.userError
            s!"state/false-retalt-underflow: expected stack #[77], got {reprStr st.stack}")
        expectContEq "state/false-retalt-underflow/c0-unchanged" st.regs.c0 (.quit 12)
        expectContEq "state/false-retalt-underflow/c1-reset" st.regs.c1 (.quit 1) }
    ,
    { name := "unit/state/popbool-errors-before-ret-paths"
      run := do
        let needTwo := mkOrdCont 2 #[]
        let regs := { Regs.initial with c0 := needTwo, c1 := needTwo }

        let stType ← expectRawErr "state/type-before-ret"
          (runRetBoolRaw #[intV 9, .null] regs) .typeChk
        if stType.stack != #[intV 9] then
          throw (IO.userError
            s!"state/type-before-ret: expected stack #[9], got {reprStr stType.stack}")
        expectContEq "state/type-before-ret/c0" stType.regs.c0 needTwo
        expectContEq "state/type-before-ret/c1" stType.regs.c1 needTwo

        let stNan ← expectRawErr "state/intov-before-ret"
          (runRetBoolRaw #[intV 10, .int .nan] regs) .intOv
        if stNan.stack != #[intV 10] then
          throw (IO.userError
            s!"state/intov-before-ret: expected stack #[10], got {reprStr stNan.stack}")
        expectContEq "state/intov-before-ret/c0" stNan.regs.c0 needTwo
        expectContEq "state/intov-before-ret/c1" stNan.regs.c1 needTwo }
    ,
    { name := "unit/direct/errors-underflow-type-intov-order"
      run := do
        expectErr "underflow/empty" (runRetBoolDirect #[]) .stkUnd
        expectErr "type/top-null" (runRetBoolDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runRetBoolDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice" (runRetBoolDirect #[.slice fullSliceA]) .typeChk
        expectErr "type/top-builder" (runRetBoolDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runRetBoolDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont" (runRetBoolDirect #[q0]) .typeChk
        expectErr "intov/top-nan" (runRetBoolDirect #[.int .nan]) .intOv
        expectErr "order/type-before-below-nan"
          (runRetBoolDirect #[.int .nan, .null]) .typeChk
        expectErr "order/intov-before-below-type"
          (runRetBoolDirect #[.null, .int .nan]) .intOv }
    ,
    { name := "unit/direct/deep-stack-preserved-on-both-branches"
      run := do
        let below : Array Value := #[.null, intV (-7), .cell refCellA, .builder Builder.empty, .tuple #[], q0]
        expectOkStack "deep/false"
          (runRetBoolDirect (withBool below (.num 0)))
          below
        expectOkStack "deep/true"
          (runRetBoolDirect (withBool below (.num (-3))))
          below }
    ,
    { name := "unit/dispatch/fallback-and-match-contract"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runRetBoolDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/matching-retbool-no-next"
          (runHandlerDirectWithNext execInstrFlowRetBool retBoolInstr (VM.push (intV dispatchSentinel)) #[intV 0])
          #[] }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let seq : Array Instr := #[.ret, .retAlt, .retBool, .add]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ret" s0 .ret 16
        let s2 ← expectDecodeStep "decode/retalt" s1 .retAlt 16
        let s3 ← expectDecodeStep "decode/retbool" s2 .retBool 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/seq-end: expected exhausted bits, got {s4.bitsRemaining}")

        let retBoolCode ←
          match assembleCp0 [.retBool] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/retbool failed: {reprStr e}")
        if retBoolCode.bits = natToBits 0xdb32 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/retbool: expected 0xdb32, got {reprStr retBoolCode.bits}")

        let rawBits : BitString :=
          natToBits 0xdb30 16 ++
          natToBits 0xdb31 16 ++
          natToBits 0xdb32 16 ++
          natToBits 0xa0 8
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-ret" r0 .ret 16
        let r2 ← expectDecodeStep "decode/raw-retalt" r1 .retAlt 16
        let r3 ← expectDecodeStep "decode/raw-retbool" r2 .retBool 16
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted bits, got {r4.bitsRemaining}") }
  ]
  oracle := #[
    -- Default c0/c1 branch split.
    mkCase "ok/true/one" (withBool #[] (.num 1)),
    mkCase "ok/true/neg-one" (withBool #[] (.num (-1))),
    mkCase "ok/true/two" (withBool #[] (.num 2)),
    mkCase "ok/true/neg-two" (withBool #[] (.num (-2))),
    mkCase "ok/true/max-int257" (withBool #[] (.num maxInt257)),
    mkCase "ok/true/min-int257" (withBool #[] (.num minInt257)),
    mkCase "ok/true/deep-noise-a" (withBool noiseA (.num 3)),
    mkCase "ok/true/deep-noise-b" (withBool noiseB (.num 5)),
    mkCase "ok/true/deep-noise-c" (withBool noiseC (.num (-9))),
    mkCase "ok/true/deep-mixed" (withBool #[.null, intV 7, .cell refCellB] (.num 11)),

    mkCase "ok/false/zero" (withBool #[] (.num 0)),
    mkCase "ok/false/deep-noise-a" (withBool noiseA (.num 0)),
    mkCase "ok/false/deep-noise-b" (withBool noiseB (.num 0)),
    mkCase "ok/false/deep-noise-c" (withBool noiseC (.num 0)),
    mkCase "ok/false/deep-mixed-a" (withBool #[q0, .builder Builder.empty, .tuple #[]] (.num 0)),
    mkCase "ok/false/deep-mixed-b" (withBool #[.slice fullSliceB, intV 42, .null] (.num 0)),
    mkCase "ok/false/zero-with-int-below" (withBool #[intV 6] (.num 0)),
    mkCase "ok/false/zero-with-two-below" (withBool #[intV 6, intV 7] (.num 0)),

    -- Control transfer skips tail regardless of branch.
    mkCase "branch/skip-tail/true" (withBool #[] (.num 1))
      #[retBoolInstr, .pushInt (.num 777)],
    mkCase "branch/skip-tail/false" (withBool #[] (.num 0))
      #[retBoolInstr, .pushInt (.num 777)],
    mkCase "branch/skip-add/true" (withBool #[intV 2, intV 3] (.num 1))
      #[retBoolInstr, .add],
    mkCase "branch/skip-add/false" (withBool #[intV 2, intV 3] (.num 0))
      #[retBoolInstr, .add],

    -- True-branch RET path via c0 nargs shaping.
    mkCase "c0nargs0/true/ok" (withBool #[] (.num 1)) (progSetC0Nargs 0),
    mkCase "c0nargs0/false/ok" (withBool #[] (.num 0)) (progSetC0Nargs 0),
    mkCase "c0nargs1/true/underflow" (withBool #[] (.num 1)) (progSetC0Nargs 1),
    mkCase "c0nargs1/true/ok" (withBool #[intV 55] (.num 1)) (progSetC0Nargs 1),
    mkCase "c0nargs1/false/skips-underflow" (withBool #[] (.num 0)) (progSetC0Nargs 1),
    mkCase "c0nargs2/true/underflow" (withBool #[intV 9] (.num 1)) (progSetC0Nargs 2),
    mkCase "c0nargs2/true/ok" (withBool #[intV 8, intV 9] (.num 1)) (progSetC0Nargs 2),
    mkCase "c0nargs2/false/skips-underflow" (withBool #[intV 9] (.num 0)) (progSetC0Nargs 2),

    -- False-branch RETALT path via c1 nargs shaping.
    mkCase "c1nargs0/true/ok" (withBool #[] (.num 1)) (progSetC1Nargs 0),
    mkCase "c1nargs0/false/ok" (withBool #[] (.num 0)) (progSetC1Nargs 0),
    mkCase "c1nargs1/false/underflow" (withBool #[] (.num 0)) (progSetC1Nargs 1),
    mkCase "c1nargs1/false/ok" (withBool #[intV 44] (.num 0)) (progSetC1Nargs 1),
    mkCase "c1nargs1/true/skips-underflow" (withBool #[] (.num 1)) (progSetC1Nargs 1),
    mkCase "c1nargs2/false/underflow" (withBool #[intV 9] (.num 0)) (progSetC1Nargs 2),
    mkCase "c1nargs2/false/ok" (withBool #[intV 8, intV 9] (.num 0)) (progSetC1Nargs 2),
    mkCase "c1nargs2/true/skips-underflow" (withBool #[intV 9] (.num 1)) (progSetC1Nargs 2),

    -- Deterministic bool-pop failures.
    mkCase "err/underflow/empty" #[],
    mkCase "err/type/null" (withRawBool #[] (.null : Value)),
    mkCase "err/type/cell" (withRawBool #[] (.cell refCellA)),
    mkCase "err/type/slice" (withRawBool #[] (.slice fullSliceA)),
    mkCase "err/type/builder" (withRawBool #[] (.builder Builder.empty)),
    mkCase "err/type/tuple" (withRawBool #[] (.tuple #[])),
    mkCase "err/type/cont" (withRawBool #[] q0),
    mkCase "err/order/type-before-below-int" (withRawBool #[intV 99] (.null : Value)),
    mkCase "err/intov/push-nan" #[] (progPushNanRetBool),
    mkCase "err/intov/push-nan-with-below" #[intV 5] (progPushNanRetBool),

    -- Decode failures for truncated RETBOOL prefixes.
    mkCaseCode "err/decode/truncated-8-prefix" #[] retBoolTruncated8Code,
    mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] retBoolTruncated15Code
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.RETBOOL
