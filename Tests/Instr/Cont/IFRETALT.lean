import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFRETALT

/-
IFRETALT / IFNOTRETALT branch-mapping notes (Lean + C++ reference):
- Lean audited files:
  - `TvmLean/Semantics/Exec/Flow/IfretAlt.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popBool`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.retAlt`, `VM.jump`)
- C++ audited files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_ifretalt`, `exec_ifnotretalt`, opcode registration 0xe308/0xe309)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_bool`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::ret_alt`, `VmState::jump`, `adjust_jump_cont`)

Branch map covered by this suite:
1. Dispatch branch: `.contExt .ifretAlt` / `.contExt .ifnotretAlt` handled vs fallback to `next`.
2. `pop_bool` gate (shared by both opcodes):
   - underflow (`stkUnd`);
   - non-int type (`typeChk`);
   - NaN integer (`intOv`);
   - finite integer -> boolean (`0` false, non-zero true).
3. IFRETALT branch split:
   - true -> `ret_alt`;
   - false -> no-op.
4. IFNOTRETALT branch split:
   - false -> `ret_alt`;
   - true -> no-op.
5. `ret_alt` jump-path behavior:
   - swaps `c1` to `quit(1)` before jump checks;
   - jump-time closure `nargs` underflow path;
   - captured-stack rewrite path.
-/

private def ifretAltId : InstrId := { name := "IFRETALT" }

private def ifretAltInstr : Instr := .contExt .ifretAlt

private def ifnotretAltInstr : Instr := .contExt .ifnotretAlt

private def dispatchSentinel : Int := 11937

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def refCellA : Cell := Cell.ofUInt 8 0xa5

private def refCellB : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice := Slice.ofCell refCellA

private def fullSliceB : Slice := Slice.ofCell refCellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[intV (-1), .null, intV 0, .cell Cell.empty, .builder Builder.empty]

private def withBool (below : Array Value) (cond : IntVal) : Array Value :=
  below ++ #[.int cond]

private def withRawBool (below : Array Value) (cond : Value) : Array Value :=
  below ++ #[cond]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifretAltInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifretAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkIfretAltCase
    (name : String)
    (stack : Array Value)
    (programTail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (#[ifretAltInstr] ++ programTail) gasLimits fuel

private def mkIfnotretAltCase
    (name : String)
    (stack : Array Value)
    (programTail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (#[ifnotretAltInstr] ++ programTail) gasLimits fuel

private def runIfretAltDirect
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfretAlt instr stack

private def runIfretAltDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfretAlt instr (VM.push (intV dispatchSentinel)) stack

private def runIfretAltRaw
    (instr : Instr)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowIfretAlt instr (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
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

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty
    { stack := captured, nargs := nargs }

private def ifretAltSetGasExact : Int :=
  computeExactGasBudget ifretAltInstr

private def ifretAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifretAltInstr

private def ifnotretAltSetGasExact : Int :=
  computeExactGasBudget ifnotretAltInstr

private def ifnotretAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifnotretAltInstr

private def ifretAltBoolPool : Array Int :=
  #[0, 1, -1, 2, -2, 7, -7, maxInt257, minInt257]

private def ifretAltNonIntBoolPool : Array Value :=
  #[
    .null,
    .cell refCellA,
    .cell refCellB,
    .slice fullSliceA,
    .slice fullSliceB,
    .builder Builder.empty,
    .tuple #[],
    .cont (.quit 0)
  ]

private def ifretAltBelowPool : Array Value :=
  noiseA ++ noiseB ++ noiseC

private def pickFromPool {a : Type} [Inhabited a] (pool : Array a) (rng : StdGen) : a × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genBelowStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool ifretAltBelowPool rng
    out := out.push v
    rng := rng'
  pure (out, rng)

private def genIfretAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (depth, rng2) := randNat rng1 0 4
  let (below, rng3) := genBelowStack depth rng2
  let (bRaw, rng4) := pickFromPool ifretAltBoolPool rng3
  let bNonZero := if bRaw = 0 then 1 else bRaw
  let (base, rng5) :=
    if shape = 0 then
      (mkIfretAltCase s!"fuzz/ifretalt/taken/deep-{depth}/cond-{bNonZero}"
        (withBool below (.num bNonZero)), rng4)
    else if shape = 1 then
      (mkIfretAltCase "fuzz/ifretalt/taken/basic-one"
        (withBool #[] (.num 1)), rng4)
    else if shape = 2 then
      (mkIfretAltCase "fuzz/ifretalt/taken/tail-skipped"
        (withBool #[intV 3] (.num bNonZero)) #[.pushInt (.num 777)], rng4)
    else if shape = 3 then
      (mkIfretAltCase s!"fuzz/ifretalt/not-taken/deep-{depth}"
        (withBool below (.num 0)), rng4)
    else if shape = 4 then
      (mkIfretAltCase "fuzz/ifretalt/not-taken/basic-zero"
        (withBool #[] (.num 0)), rng4)
    else if shape = 5 then
      (mkIfretAltCase "fuzz/ifretalt/not-taken/tail-push-exec"
        (withBool #[intV 3] (.num 0)) #[.pushInt (.num 777)], rng4)
    else if shape = 6 then
      (mkIfretAltCase "fuzz/ifretalt/not-taken/tail-add-exec"
        (withBool #[intV 2, intV 3] (.num 0)) #[.add], rng4)
    else if shape = 7 then
      (mkIfnotretAltCase s!"fuzz/ifnotretalt/taken/deep-{depth}"
        (withBool below (.num 0)), rng4)
    else if shape = 8 then
      (mkIfnotretAltCase "fuzz/ifnotretalt/taken/basic-zero"
        (withBool #[] (.num 0)), rng4)
    else if shape = 9 then
      (mkIfnotretAltCase "fuzz/ifnotretalt/taken/tail-skipped"
        (withBool #[intV 3] (.num 0)) #[.pushInt (.num 777)], rng4)
    else if shape = 10 then
      (mkIfnotretAltCase s!"fuzz/ifnotretalt/not-taken/deep-{depth}/cond-{bNonZero}"
        (withBool below (.num bNonZero)), rng4)
    else if shape = 11 then
      (mkIfnotretAltCase "fuzz/ifnotretalt/not-taken/basic-one"
        (withBool #[] (.num 1)), rng4)
    else if shape = 12 then
      (mkIfnotretAltCase "fuzz/ifnotretalt/not-taken/tail-push-exec"
        (withBool #[intV 3] (.num bNonZero)) #[.pushInt (.num 777)], rng4)
    else if shape = 13 then
      (mkIfnotretAltCase "fuzz/ifnotretalt/not-taken/tail-add-exec"
        (withBool #[intV 2, intV 3] (.num bNonZero)) #[.add], rng4)
    else if shape = 14 then
      (mkIfretAltCase "fuzz/err/ifretalt/underflow-empty" #[], rng4)
    else if shape = 15 then
      let (bad, rng6) := pickFromPool ifretAltNonIntBoolPool rng4
      (mkIfretAltCase s!"fuzz/err/ifretalt/type/deep-{depth}" (withRawBool below bad), rng6)
    else if shape = 16 then
      (mkCase "fuzz/err/ifretalt/intov-nan"
        #[] #[.pushInt .nan, ifretAltInstr], rng4)
    else if shape = 17 then
      (mkCase "fuzz/err/ifretalt/intov-nan-with-below"
        #[intV 9] #[.pushInt .nan, ifretAltInstr], rng4)
    else if shape = 18 then
      (mkIfnotretAltCase "fuzz/err/ifnotretalt/underflow-empty" #[], rng4)
    else if shape = 19 then
      let (bad, rng6) := pickFromPool ifretAltNonIntBoolPool rng4
      (mkIfnotretAltCase s!"fuzz/err/ifnotretalt/type/deep-{depth}" (withRawBool below bad), rng6)
    else if shape = 20 then
      (mkCase "fuzz/err/ifnotretalt/intov-nan"
        #[] #[.pushInt .nan, ifnotretAltInstr], rng4)
    else if shape = 21 then
      (mkCase "fuzz/gas/ifretalt/exact-true"
        (withBool #[] (.num 1))
        #[.pushInt (.num ifretAltSetGasExact), .tonEnvOp .setGasLimit, ifretAltInstr], rng4)
    else if shape = 22 then
      (mkCase "fuzz/gas/ifretalt/exact-minus-one-true"
        (withBool #[] (.num 1))
        #[.pushInt (.num ifretAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifretAltInstr], rng4)
    else if shape = 23 then
      (mkCase "fuzz/gas/ifretalt/exact-false"
        (withBool #[] (.num 0))
        #[.pushInt (.num ifretAltSetGasExact), .tonEnvOp .setGasLimit, ifretAltInstr], rng4)
    else if shape = 24 then
      (mkCase "fuzz/gas/ifnotretalt/exact-false"
        (withBool #[] (.num 0))
        #[.pushInt (.num ifnotretAltSetGasExact), .tonEnvOp .setGasLimit, ifnotretAltInstr], rng4)
    else if shape = 25 then
      (mkCase "fuzz/gas/ifnotretalt/exact-minus-one-false"
        (withBool #[] (.num 0))
        #[.pushInt (.num ifnotretAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotretAltInstr], rng4)
    else
      (mkCase "fuzz/gas/ifnotretalt/exact-true"
        (withBool #[] (.num 1))
        #[.pushInt (.num ifnotretAltSetGasExact), .tonEnvOp .setGasLimit, ifnotretAltInstr], rng4)
  let (tag, rng6) := randNat rng5 0 999_999
  ({ base with name := s!"{base.name}/{tag}" }, rng6)

def suite : InstrSuite where
  id := ifretAltId
  unit := #[
    { name := "unit/raw/ifretalt-branch-and-c1-swap"
      run := do
        let target : Continuation := .quit 9
        let regs : Regs := { Regs.initial with c1 := target }

        let stTaken ← expectRawOk "ifretalt/taken" (runIfretAltRaw ifretAltInstr #[intV 1] regs)
        if stTaken.stack != #[] then
          throw (IO.userError s!"ifretalt/taken: expected empty stack, got {reprStr stTaken.stack}")
        expectContEq "ifretalt/taken/cc" stTaken.cc target
        expectContEq "ifretalt/taken/c1" stTaken.regs.c1 (.quit 1)

        let stNotTaken ← expectRawOk "ifretalt/not-taken" (runIfretAltRaw ifretAltInstr #[intV 0] regs)
        if stNotTaken.stack != #[] then
          throw (IO.userError s!"ifretalt/not-taken: expected empty stack, got {reprStr stNotTaken.stack}")
        expectContEq "ifretalt/not-taken/cc" stNotTaken.cc defaultCc
        expectContEq "ifretalt/not-taken/c1" stNotTaken.regs.c1 target }
    ,
    { name := "unit/raw/ifnotretalt-branch-inversion-and-c1-swap"
      run := do
        let target : Continuation := .quit 13
        let regs : Regs := { Regs.initial with c1 := target }

        let stTaken ← expectRawOk "ifnotretalt/taken" (runIfretAltRaw ifnotretAltInstr #[intV 0] regs)
        if stTaken.stack != #[] then
          throw (IO.userError s!"ifnotretalt/taken: expected empty stack, got {reprStr stTaken.stack}")
        expectContEq "ifnotretalt/taken/cc" stTaken.cc target
        expectContEq "ifnotretalt/taken/c1" stTaken.regs.c1 (.quit 1)

        let stNotTaken ← expectRawOk "ifnotretalt/not-taken" (runIfretAltRaw ifnotretAltInstr #[intV 5] regs)
        if stNotTaken.stack != #[] then
          throw (IO.userError s!"ifnotretalt/not-taken: expected empty stack, got {reprStr stNotTaken.stack}")
        expectContEq "ifnotretalt/not-taken/cc" stNotTaken.cc defaultCc
        expectContEq "ifnotretalt/not-taken/c1" stNotTaken.regs.c1 target }
    ,
    { name := "unit/direct/errors-underflow-type-and-intov"
      run := do
        expectErr "ifretalt/underflow/empty"
          (runIfretAltDirect ifretAltInstr #[]) .stkUnd
        expectErr "ifnotretalt/underflow/empty"
          (runIfretAltDirect ifnotretAltInstr #[]) .stkUnd

        expectErr "ifretalt/type/null"
          (runIfretAltDirect ifretAltInstr #[.null]) .typeChk
        expectErr "ifretalt/type/cell"
          (runIfretAltDirect ifretAltInstr #[.cell refCellA]) .typeChk
        expectErr "ifnotretalt/type/slice"
          (runIfretAltDirect ifnotretAltInstr #[.slice fullSliceA]) .typeChk
        expectErr "ifnotretalt/type/cont"
          (runIfretAltDirect ifnotretAltInstr #[.cont (.quit 0)]) .typeChk

        expectErr "ifretalt/intov/nan"
          (runIfretAltDirect ifretAltInstr #[.int .nan]) .intOv
        expectErr "ifnotretalt/intov/nan"
          (runIfretAltDirect ifnotretAltInstr #[.int .nan]) .intOv }
    ,
    { name := "unit/raw/popbool-errors-happen-before-retalt"
      run := do
        let target : Continuation := .quit 77
        let regs : Regs := { Regs.initial with c1 := target }

        let (rType, stType) := runIfretAltRaw ifretAltInstr #[.null] regs
        match rType with
        | .error .typeChk =>
            if stType.stack != #[] then
              throw (IO.userError s!"type-order/stack: expected empty stack, got {reprStr stType.stack}")
            expectContEq "type-order/c1-unchanged" stType.regs.c1 target
            expectContEq "type-order/cc-unchanged" stType.cc defaultCc
        | .error e =>
            throw (IO.userError s!"type-order: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "type-order: expected typeChk, got success")

        let (rNan, stNan) := runIfretAltRaw ifnotretAltInstr #[.int .nan] regs
        match rNan with
        | .error .intOv =>
            if stNan.stack != #[] then
              throw (IO.userError s!"nan-order/stack: expected empty stack, got {reprStr stNan.stack}")
            expectContEq "nan-order/c1-unchanged" stNan.regs.c1 target
            expectContEq "nan-order/cc-unchanged" stNan.cc defaultCc
        | .error e =>
            throw (IO.userError s!"nan-order: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "nan-order: expected intOv, got success") }
    ,
    { name := "unit/raw/retalt-jump-underflow-resets-c1-first"
      run := do
        let needTwo : Continuation := mkOrdCont 2 #[]
        let regs : Regs := { Regs.initial with c1 := needTwo }

        let (r1, st1) := runIfretAltRaw ifretAltInstr #[intV 1] regs
        match r1 with
        | .error .stkUnd =>
            if st1.stack != #[] then
              throw (IO.userError s!"ifretalt/jump-underflow/stack: got {reprStr st1.stack}")
            expectContEq "ifretalt/jump-underflow/c1-reset" st1.regs.c1 (.quit 1)
            expectContEq "ifretalt/jump-underflow/cc-unchanged" st1.cc defaultCc
        | .error e =>
            throw (IO.userError s!"ifretalt/jump-underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "ifretalt/jump-underflow: expected stkUnd, got success")

        let (r2, st2) := runIfretAltRaw ifnotretAltInstr #[intV 0] regs
        match r2 with
        | .error .stkUnd =>
            if st2.stack != #[] then
              throw (IO.userError s!"ifnotretalt/jump-underflow/stack: got {reprStr st2.stack}")
            expectContEq "ifnotretalt/jump-underflow/c1-reset" st2.regs.c1 (.quit 1)
            expectContEq "ifnotretalt/jump-underflow/cc-unchanged" st2.cc defaultCc
        | .error e =>
            throw (IO.userError s!"ifnotretalt/jump-underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "ifnotretalt/jump-underflow: expected stkUnd, got success") }
    ,
    { name := "unit/raw/retalt-applies-captured-stack"
      run := do
        let captured : Continuation := mkOrdCont 1 #[intV 42]
        let regs : Regs := { Regs.initial with c1 := captured }

        let stIfret ← expectRawOk "captured/ifretalt"
          (runIfretAltRaw ifretAltInstr #[intV 4, intV 5, intV 1] regs)
        if stIfret.stack != #[intV 42, intV 5] then
          throw (IO.userError s!"captured/ifretalt: expected [42,5], got {reprStr stIfret.stack}")
        expectContEq "captured/ifretalt/c1-reset" stIfret.regs.c1 (.quit 1)

        let stIfnot ← expectRawOk "captured/ifnotretalt"
          (runIfretAltRaw ifnotretAltInstr #[intV 4, intV 5, intV 0] regs)
        if stIfnot.stack != #[intV 42, intV 5] then
          throw (IO.userError s!"captured/ifnotretalt: expected [42,5], got {reprStr stIfnot.stack}")
        expectContEq "captured/ifnotretalt/c1-reset" stIfnot.regs.c1 (.quit 1) }
    ,
    { name := "unit/direct/deep-stack-preserved-on-all-branches"
      run := do
        let below : Array Value :=
          #[.null, intV (-9), .cell refCellA, .builder Builder.empty, .tuple #[], .slice fullSliceA]
        expectOkStack "ifretalt/false/deep"
          (runIfretAltDirect ifretAltInstr (withBool below (.num 0)))
          below
        expectOkStack "ifretalt/true/deep"
          (runIfretAltDirect ifretAltInstr (withBool below (.num 8)))
          below
        expectOkStack "ifnotretalt/false/deep"
          (runIfretAltDirect ifnotretAltInstr (withBool below (.num 0)))
          below
        expectOkStack "ifnotretalt/true/deep"
          (runIfretAltDirect ifnotretAltInstr (withBool below (.num 8)))
          below }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback/add"
          (runIfretAltDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/match/ifretalt"
          (runIfretAltDispatchFallback ifretAltInstr #[intV 1])
          #[]
        expectOkStack "dispatch/match/ifnotretalt"
          (runIfretAltDispatchFallback ifnotretAltInstr #[intV 1])
          #[] }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let seq : Array Instr :=
          #[.contExt .condSel, .contExt .condSelChk, ifretAltInstr, ifnotretAltInstr, .add]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/condsel" s0 (.contExt .condSel) 16
        let s2 ← expectDecodeStep "decode/condselchk" s1 (.contExt .condSelChk) 16
        let s3 ← expectDecodeStep "decode/ifretalt" s2 ifretAltInstr 16
        let s4 ← expectDecodeStep "decode/ifnotretalt" s3 ifnotretAltInstr 16
        let s5 ← expectDecodeStep "decode/add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted bits, got {s5.bitsRemaining}") }
  ]
  oracle := #[
    -- IFRETALT true branch (`pop_bool != 0`) => `RETALT`.
    mkIfretAltCase "ifretalt/taken/one" (withBool #[] (.num 1)),
    mkIfretAltCase "ifretalt/taken/neg-one" (withBool #[] (.num (-1))),
    mkIfretAltCase "ifretalt/taken/two" (withBool #[] (.num 2)),
    mkIfretAltCase "ifretalt/taken/max-int257" (withBool #[] (.num maxInt257)),
    mkIfretAltCase "ifretalt/taken/min-int257" (withBool #[] (.num minInt257)),
    mkIfretAltCase "ifretalt/taken/deep-noise-a" (withBool noiseA (.num 7)),
    mkIfretAltCase "ifretalt/taken/deep-noise-b" (withBool noiseB (.num 5)),
    mkIfretAltCase "ifretalt/taken/deep-noise-c" (withBool noiseC (.num 9)),
    mkIfretAltCase "ifretalt/taken/trailing-push-skipped"
      (withBool #[intV 3] (.num 1)) #[.pushInt (.num 777)],

    -- IFRETALT false branch (`pop_bool == 0`) => no RETALT.
    mkIfretAltCase "ifretalt/not-taken/zero" (withBool #[] (.num 0)),
    mkIfretAltCase "ifretalt/not-taken/deep-noise-a" (withBool noiseA (.num 0)),
    mkIfretAltCase "ifretalt/not-taken/deep-noise-b" (withBool noiseB (.num 0)),
    mkIfretAltCase "ifretalt/not-taken/deep-noise-c" (withBool noiseC (.num 0)),
    mkIfretAltCase "ifretalt/not-taken/preserve-max-noise"
      (withBool #[intV maxInt257] (.num 0)),
    mkIfretAltCase "ifretalt/not-taken/preserve-min-noise"
      (withBool #[intV minInt257] (.num 0)),
    mkIfretAltCase "ifretalt/not-taken/slice-builder-noise"
      (withBool #[.slice fullSliceA, .builder Builder.empty] (.num 0)),
    mkIfretAltCase "ifretalt/not-taken/trailing-push-exec"
      (withBool #[intV 3] (.num 0)) #[.pushInt (.num 777)],
    mkIfretAltCase "ifretalt/not-taken/trailing-add-exec"
      (withBool #[intV 2, intV 3] (.num 0)) #[.add],

    -- IFNOTRETALT true/false inversion.
    mkIfnotretAltCase "ifnotretalt/taken/zero" (withBool #[] (.num 0)),
    mkIfnotretAltCase "ifnotretalt/taken/deep-noise-a" (withBool noiseA (.num 0)),
    mkIfnotretAltCase "ifnotretalt/taken/deep-noise-b" (withBool noiseB (.num 0)),
    mkIfnotretAltCase "ifnotretalt/taken/trailing-push-skipped"
      (withBool #[intV 3] (.num 0)) #[.pushInt (.num 777)],

    mkIfnotretAltCase "ifnotretalt/not-taken/one" (withBool #[] (.num 1)),
    mkIfnotretAltCase "ifnotretalt/not-taken/neg-one" (withBool #[] (.num (-1))),
    mkIfnotretAltCase "ifnotretalt/not-taken/two" (withBool #[] (.num 2)),
    mkIfnotretAltCase "ifnotretalt/not-taken/max-int257" (withBool #[] (.num maxInt257)),
    mkIfnotretAltCase "ifnotretalt/not-taken/min-int257" (withBool #[] (.num minInt257)),
    mkIfnotretAltCase "ifnotretalt/not-taken/deep-noise-a" (withBool noiseA (.num 8)),
    mkIfnotretAltCase "ifnotretalt/not-taken/trailing-push-exec"
      (withBool #[intV 3] (.num 5)) #[.pushInt (.num 777)],
    mkIfnotretAltCase "ifnotretalt/not-taken/trailing-add-exec"
      (withBool #[intV 2, intV 3] (.num 5)) #[.add],

    -- Underflow.
    mkIfretAltCase "err/ifretalt/underflow-empty" #[],
    mkIfnotretAltCase "err/ifnotretalt/underflow-empty" #[],

    -- Type-check failures at `pop_bool` (non-int on top).
    mkIfretAltCase "err/ifretalt/type-null" (withRawBool #[] (.null : Value)),
    mkIfretAltCase "err/ifretalt/type-cell" (withRawBool #[] (.cell refCellA)),
    mkIfretAltCase "err/ifretalt/type-slice" (withRawBool #[] (.slice fullSliceB)),
    mkIfretAltCase "err/ifretalt/type-builder" (withRawBool #[] (.builder Builder.empty)),
    mkIfretAltCase "err/ifretalt/type-tuple" (withRawBool #[] (.tuple #[])),
    mkIfretAltCase "err/ifretalt/type-cont" (withRawBool #[] (.cont (.quit 0))),
    mkIfnotretAltCase "err/ifnotretalt/type-null" (withRawBool #[] (.null : Value)),
    mkIfnotretAltCase "err/ifnotretalt/type-cell" (withRawBool #[] (.cell refCellB)),
    mkIfnotretAltCase "err/ifnotretalt/type-slice" (withRawBool #[] (.slice fullSliceA)),
    mkIfnotretAltCase "err/ifnotretalt/type-builder" (withRawBool #[] (.builder Builder.empty)),
    mkIfnotretAltCase "err/ifnotretalt/type-tuple" (withRawBool #[] (.tuple #[])),
    mkIfnotretAltCase "err/ifnotretalt/type-cont" (withRawBool #[] (.cont (.quit 0))),

    -- Int overflow from NaN bool.
    mkCase "err/ifretalt/intov-nan"
      #[] #[.pushInt .nan, ifretAltInstr],
    mkCase "err/ifretalt/intov-nan-with-below"
      #[intV 9] #[.pushInt .nan, ifretAltInstr],
    mkCase "err/ifnotretalt/intov-nan"
      #[] #[.pushInt .nan, ifnotretAltInstr],
    mkCase "err/ifnotretalt/intov-nan-with-below"
      #[intV 9] #[.pushInt .nan, ifnotretAltInstr],

    -- Deterministic gas cliffs (exact budget vs exact-minus-one).
    mkCase "gas/ifretalt/exact-true-succeeds"
      (withBool #[] (.num 1))
      #[.pushInt (.num ifretAltSetGasExact), .tonEnvOp .setGasLimit, ifretAltInstr],
    mkCase "gas/ifretalt/exact-minus-one-true-out-of-gas"
      (withBool #[] (.num 1))
      #[.pushInt (.num ifretAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifretAltInstr],
    mkCase "gas/ifretalt/exact-false-succeeds"
      (withBool #[] (.num 0))
      #[.pushInt (.num ifretAltSetGasExact), .tonEnvOp .setGasLimit, ifretAltInstr],
    mkCase "gas/ifnotretalt/exact-false-succeeds"
      (withBool #[] (.num 0))
      #[.pushInt (.num ifnotretAltSetGasExact), .tonEnvOp .setGasLimit, ifnotretAltInstr],
    mkCase "gas/ifnotretalt/exact-minus-one-false-out-of-gas"
      (withBool #[] (.num 0))
      #[.pushInt (.num ifnotretAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotretAltInstr],
    mkCase "gas/ifnotretalt/exact-true-succeeds"
      (withBool #[] (.num 1))
      #[.pushInt (.num ifnotretAltSetGasExact), .tonEnvOp .setGasLimit, ifnotretAltInstr]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr ifretAltId
      count := 500
      gen := genIfretAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.IFRETALT
