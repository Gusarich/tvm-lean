import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFRET

/-
IFRET branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Ifret.lean` (`execInstrFlowIfret`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popBool`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.ret`, `VM.jump`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xdc -> .ifret`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifret -> 0xdc`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_ifret`, opcode registration)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_bool`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::ret`, `VmState::jump`)

Branch map covered by this suite:
- dispatch: `.ifret` handled vs non-`.ifret` fallback to `next`;
- bool extraction path (`pop_bool` parity):
  - underflow (`stkUnd`) on empty stack;
  - non-int top (`typeChk`);
  - NaN top (`intOv`);
  - finite int -> `false` for zero, `true` otherwise;
- branch split:
  - false => no return jump, only bool pop;
  - true => `ret()` path with c0 extraction/reset then jump;
- true-branch ret/jump subcases validated in focused unit tests:
  - jump target from current `c0`;
  - `c0` reset to `quit(0)` before jump;
  - reset persists even if jump throws (`stkUnd`);
  - closure-style jump stack shaping via captured-stack + nargs.
-/

private def ifretId : InstrId := { name := "IFRET" }

private def ifretInstr : Instr := .ifret

private def dispatchSentinel : Int := 8621

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

private def noiseD : Array Value :=
  #[intV maxInt257, intV minInt257, .slice fullSliceB]

private def withBool (below : Array Value) (cond : IntVal) : Array Value :=
  below ++ #[.int cond]

private def withRawBool (below : Array Value) (cond : Value) : Array Value :=
  below ++ #[cond]

private def ordinaryCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def mkIfretCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifretInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifretId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runIfretDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfret ifretInstr stack

private def runIfretDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfret instr (VM.push (intV dispatchSentinel)) stack

private def runIfretRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowIfret ifretInstr (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
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

private def expectContEq (label : String) (actual expected : Continuation) : IO Unit := do
  if actual == expected then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected continuation {reprStr expected}, got {reprStr actual}")

private def ifretSetGasExact : Int :=
  computeExactGasBudget ifretInstr

private def ifretSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifretInstr

def suite : InstrSuite where
  id := ifretId
  unit := #[
    { name := "unit/state/false-branch-skips-ret-and-keeps-c0"
      run := do
        let guardC0 := ordinaryCont 3 #[]
        let regs := { Regs.initial with c0 := guardC0 }
        let st ← expectRawOk "state/false-branch" (runIfretRaw #[intV 0] regs)
        if st.stack == #[] then
          pure ()
        else
          throw (IO.userError s!"state/false-branch: expected empty stack, got {reprStr st.stack}")
        expectContEq "state/false-branch/cc" st.cc defaultCc
        match st.regs.c0 with
        | .ordinary _ _ _ cdata =>
            if cdata.nargs = 3 then
              pure ()
            else
              throw (IO.userError
                s!"state/false-branch: expected c0.nargs=3, got {cdata.nargs}")
        | other =>
            throw (IO.userError
              s!"state/false-branch: expected ordinary c0, got {reprStr other}") }
    ,
    { name := "unit/state/true-branch-jumps-to-c0-and-resets-c0"
      run := do
        let regs := { Regs.initial with c0 := .quit 17 }
        let st ← expectRawOk "state/true-branch" (runIfretRaw #[intV 5] regs)
        if st.stack == #[] then
          pure ()
        else
          throw (IO.userError s!"state/true-branch: expected empty stack, got {reprStr st.stack}")
        expectContEq "state/true-branch/cc" st.cc (.quit 17)
        expectContEq "state/true-branch/c0-reset" st.regs.c0 (.quit 0) }
    ,
    { name := "unit/state/true-branch-c0-reset-persists-on-jump-error"
      run := do
        let needTwo := ordinaryCont 2 #[]
        let regs := { Regs.initial with c0 := needTwo }
        let st ← expectRawErr "state/true-branch-jump-error"
          (runIfretRaw #[intV 11, intV 1] regs) .stkUnd
        if st.stack == #[intV 11] then
          pure ()
        else
          throw (IO.userError
            s!"state/true-branch-jump-error: expected stack #[11], got {reprStr st.stack}")
        expectContEq "state/true-branch-jump-error/c0-reset" st.regs.c0 (.quit 0) }
    ,
    { name := "unit/state/true-branch-applies-jump-captured-stack"
      run := do
        let captured := ordinaryCont 1 #[intV 99]
        let regs := { Regs.initial with c0 := captured }
        let st ← expectRawOk "state/true-captured-stack"
          (runIfretRaw #[intV 7, intV 8, intV 1] regs)
        if st.stack == #[intV 99, intV 8] then
          pure ()
        else
          throw (IO.userError
            s!"state/true-captured-stack: expected #[99,8], got {reprStr st.stack}")
        expectContEq "state/true-captured-stack/c0-reset" st.regs.c0 (.quit 0) }
    ,
    { name := "unit/direct/errors-underflow-type-intov-order"
      run := do
        expectErr "underflow/empty" (runIfretDirect #[]) .stkUnd
        expectErr "type/top-null" (runIfretDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runIfretDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice" (runIfretDirect #[.slice fullSliceA]) .typeChk
        expectErr "type/top-builder" (runIfretDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runIfretDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont" (runIfretDirect #[q0]) .typeChk
        expectErr "intov/top-nan" (runIfretDirect #[.int .nan]) .intOv
        expectErr "order/type-before-below-nan"
          (runIfretDirect #[.int .nan, .null]) .typeChk
        expectErr "order/intov-before-below-type"
          (runIfretDirect #[.null, .int .nan]) .intOv }
    ,
    { name := "unit/direct/deep-stack-preserved-on-both-branches"
      run := do
        let below : Array Value := #[.null, intV (-7), .cell refCellA, .builder Builder.empty, .tuple #[], q0]
        expectOkStack "deep/false"
          (runIfretDirect (withBool below (.num 0)))
          below
        expectOkStack "deep/true"
          (runIfretDirect (withBool below (.num (-3))))
          below }
    ,
    { name := "unit/dispatch/fallback-and-match-contract"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfretDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/matching-ifret-no-next"
          (runHandlerDirectWithNext execInstrFlowIfret ifretInstr (VM.push (intV dispatchSentinel)) #[intV 0])
          #[] }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let seq : Array Instr := #[.ifret, .ifnotret, .if_, .ifnot, .ifjmp, .ifnotjmp, .ifelse, .add]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ifret" s0 .ifret 8
        let s2 ← expectDecodeStep "decode/ifnotret" s1 .ifnotret 8
        let s3 ← expectDecodeStep "decode/if" s2 .if_ 8
        let s4 ← expectDecodeStep "decode/ifnot" s3 .ifnot 8
        let s5 ← expectDecodeStep "decode/ifjmp" s4 .ifjmp 8
        let s6 ← expectDecodeStep "decode/ifnotjmp" s5 .ifnotjmp 8
        let s7 ← expectDecodeStep "decode/ifelse" s6 .ifelse 8
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/seq-end: expected exhausted bits, got {s8.bitsRemaining}")

        let ifretCode ←
          match assembleCp0 [.ifret] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/ifret failed: {reprStr e}")
        if ifretCode.bits == natToBits 0xdc 8 then
          pure ()
        else
          throw (IO.userError s!"opcode/ifret: expected 0xdc, got {reprStr ifretCode.bits}")

        let rawBits : BitString :=
          natToBits 0xdc 8 ++
          natToBits 0xdd 8 ++
          natToBits 0xde 8 ++
          natToBits 0xa0 8
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-ifret" r0 .ifret 8
        let r2 ← expectDecodeStep "decode/raw-ifnotret" r1 .ifnotret 8
        let r3 ← expectDecodeStep "decode/raw-if" r2 .if_ 8
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted bits, got {r4.bitsRemaining}") }
    ,
    { name := "unit/gas/probe-budget-ordering"
      run := do
        if ifretSetGasExact > 0 then
          pure ()
        else
          throw (IO.userError s!"gas/exact: expected positive budget, got {ifretSetGasExact}")
        if ifretSetGasExactMinusOne < ifretSetGasExact then
          pure ()
        else
          throw (IO.userError
            s!"gas/exact-minus-one: expected strict decrease, got exact={ifretSetGasExact} minusOne={ifretSetGasExactMinusOne}") }
  ]
  oracle := #[
    mkIfretCase "ok/true/one" (withBool #[] (.num 1)),
    mkIfretCase "ok/true/neg-one" (withBool #[] (.num (-1))),
    mkIfretCase "ok/true/two" (withBool #[] (.num 2)),
    mkIfretCase "ok/true/max-int257" (withBool #[] (.num maxInt257)),
    mkIfretCase "ok/true/min-int257" (withBool #[] (.num minInt257)),
    mkIfretCase "ok/true/deep-noise-a" (withBool noiseA (.num 3)),
    mkIfretCase "ok/true/deep-noise-b" (withBool noiseB (.num 5)),
    mkIfretCase "ok/true/deep-noise-c" (withBool noiseC (.num (-9))),
    mkIfretCase "ok/true/deep-noise-d" (withBool noiseD (.num 11)),
    mkIfretCase "ok/true/deep-mixed-a" (withBool #[.null, intV 7, .cell refCellB] (.num 1)),
    mkIfretCase "ok/true/deep-mixed-b" (withBool #[q0, .builder Builder.empty, .tuple #[]] (.num (-5))),
    mkIfretCase "ok/true/deep-mixed-c" (withBool #[.slice fullSliceA, intV 42, .null, q0] (.num 8)),

    mkIfretCase "ok/false/zero" (withBool #[] (.num 0)),
    mkIfretCase "ok/false/deep-noise-a" (withBool noiseA (.num 0)),
    mkIfretCase "ok/false/deep-noise-b" (withBool noiseB (.num 0)),
    mkIfretCase "ok/false/deep-noise-c" (withBool noiseC (.num 0)),
    mkIfretCase "ok/false/deep-noise-d" (withBool noiseD (.num 0)),
    mkIfretCase "ok/false/deep-mixed-a" (withBool #[.null, intV 7, .cell refCellB] (.num 0)),
    mkIfretCase "ok/false/deep-mixed-b" (withBool #[q0, .builder Builder.empty, .tuple #[]] (.num 0)),
    mkIfretCase "ok/false/deep-mixed-c" (withBool #[.slice fullSliceA, intV 42, .null, q0] (.num 0)),
    mkIfretCase "ok/false/preserve-max-noise" (withBool #[intV maxInt257] (.num 0)),
    mkIfretCase "ok/false/preserve-min-noise" (withBool #[intV minInt257] (.num 0)),
    mkIfretCase "ok/false/preserve-cont-noise" (withBool #[q0] (.num 0)),
    mkIfretCase "ok/false/preserve-slice-builder" (withBool #[.slice fullSliceB, .builder Builder.empty] (.num 0)),

    mkIfretCase "err/underflow/empty" #[],

    mkIfretCase "err/type/top-null" (withRawBool #[] (.null : Value)),
    mkIfretCase "err/type/top-cell" (withRawBool #[] (.cell refCellA)),
    mkIfretCase "err/type/top-slice" (withRawBool #[] (.slice fullSliceA)),
    mkIfretCase "err/type/top-builder" (withRawBool #[] (.builder Builder.empty)),
    mkIfretCase "err/type/top-tuple" (withRawBool #[] (.tuple #[])),
    mkIfretCase "err/type/top-cont" (withRawBool #[] q0),
    mkIfretCase "err/type/order-top-first" #[intV 19, .null],

    mkIfretCase "err/intov/pushnan" #[]
      #[.pushInt .nan, ifretInstr],
    mkIfretCase "err/intov/pushnan-with-noise" noiseA
      #[.pushInt .nan, ifretInstr],

    mkIfretCase "gas/exact-true-succeeds" (withBool #[] (.num 1))
      #[.pushInt (.num ifretSetGasExact), .tonEnvOp .setGasLimit, ifretInstr],
    mkIfretCase "gas/exact-minus-one-true-out-of-gas" (withBool #[] (.num 1))
      #[.pushInt (.num ifretSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifretInstr],
    mkIfretCase "gas/exact-false-succeeds" (withBool #[] (.num 0))
      #[.pushInt (.num ifretSetGasExact), .tonEnvOp .setGasLimit, ifretInstr],
    mkIfretCase "gas/exact-minus-one-false-out-of-gas" (withBool #[] (.num 0))
      #[.pushInt (.num ifretSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifretInstr]
  ]
  fuzz := #[ mkReplayOracleFuzzSpec ifretId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.IFRET
