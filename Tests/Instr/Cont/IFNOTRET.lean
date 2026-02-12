import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFNOTRET

/-
IFNOTRET branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Ifnotret.lean` (`execInstrFlowIfnotret`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popBool`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.ret`, `VM.jump`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xdd -> .ifnotret`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifnotret -> 0xdd`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_ifnotret`, registration in `register_continuation_cond_loop_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::pop_bool`, `pop_int_finite`, error order)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp`
    (`VmState::ret`, `VmState::jump`).

Branch map covered by this suite:
- dispatch: only `.ifnotret` is handled; non-matching opcodes must fall through to `next`;
- handled path:
  1. pop bool (`pop_bool` / `VM.popBool`): underflow, type, intov behavior;
  2. branch inversion: `RET` only when popped bool is false (`0`);
  3. `RET` path uses c0 and may fail in `jump`; true branch must skip this path;
- opcode/decode parity for cp0 neighborhood (`0xdc/0xdd/0xde`).
-/

private def ifnotretId : InstrId := { name := "IFNOTRET" }

private def ifnotretInstr : Instr := .ifnotret

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def q0 : Value :=
  .cont (.quit 0)

private def refCellA : Cell :=
  Cell.ofUInt 8 0xa5

private def fullSliceA : Slice :=
  Slice.ofCell refCellA

private def tailMarker : Int :=
  7331

private def dispatchSentinel : Int :=
  9012

private def branchObservableProgram : Array Instr :=
  #[ifnotretInstr, .pushInt (.num tailMarker)]

private def nanProgram : Array Instr :=
  #[.pushInt .nan, ifnotretInstr]

private def withCond (below : Array Value) (cond : IntVal) : Array Value :=
  below ++ #[.int cond]

private def withCondRaw (below : Array Value) (cond : Value) : Array Value :=
  below ++ #[cond]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifnotretInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnotretId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runIfnotretDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfnotret ifnotretInstr stack

private def runIfnotretDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfnotret instr (VM.push (intV dispatchSentinel)) stack

private def runIfnotretState
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno VmState := do
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  let (res, st1) := (execInstrFlowIfnotret ifnotretInstr (pure ())).run st0
  match res with
  | .ok _ => .ok st1
  | .error e => .error e

private def expectStateOk (label : String) (res : Except Excno VmState) : IO VmState := do
  match res with
  | .ok st => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectStateErr (label : String) (res : Except Excno VmState) (expected : Excno) : IO Unit := do
  match res with
  | .ok st =>
      throw (IO.userError s!"{label}: expected error {expected}, got state {reprStr st}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def ifnotretSetGasExact : Int :=
  computeExactGasBudget ifnotretInstr

private def ifnotretSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifnotretInstr

private def ifnotretOracleFamilies : Array String :=
  #[
    "branch/observable/",
    "ok/no-tail/",
    "err/underflow/",
    "err/type/",
    "err/intov/",
    "gas/"
  ]

private def ifnotretFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := ifnotretOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def ifnotretBoolPool : Array Int :=
  #[
    0, 1, -1, 2, -2, 3, -3,
    pow2 200, -(pow2 200),
    maxInt257, minInt257
  ]

private def ifnotretBadCondNonIntPool : Array Value :=
  #[.null, .cell refCellA, .slice fullSliceA, .builder Builder.empty, .tuple #[], q0]

private def noiseA : Array Value :=
  #[.null, intV 9, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[intV (-1), .null, .cell Cell.empty, .builder Builder.empty]

private def pickFromPool {a : Type} [Inhabited a] (pool : Array a) (rng : StdGen) : a × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genBelowStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  let pool : Array Value := noiseA ++ noiseB ++ noiseC
  for _ in [0:count] do
    let (v, rng') := pickFromPool pool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def genIfnotretFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (depth, rng2) := randNat rng1 0 4
  let (below, rng3) := genBelowStack depth rng2
  let (bRaw, rng4) := pickFromPool ifnotretBoolPool rng3
  let b := if bRaw = 0 then 0 else bRaw
  let (base, rng5) :=
    if shape = 0 then
      (mkCase s!"fuzz/branch/observable/deep-{depth}/cond-{b}"
        (withCond below (.num b)) branchObservableProgram, rng4)
    else if shape = 1 then
      (mkCase "fuzz/ok/no-tail/zero" (withCond #[] (.num 0)), rng4)
    else if shape = 2 then
      (mkCase "fuzz/ok/no-tail/nonzero" (withCond #[] (.num 1)), rng4)
    else if shape = 3 then
      (mkCase s!"fuzz/ok/no-tail/deep-{depth}" (withCond below (.num b)), rng4)
    else if shape = 4 then
      (mkCase "fuzz/err/underflow/empty" #[], rng4)
    else if shape = 5 then
      let (bad, rng6) := pickFromPool ifnotretBadCondNonIntPool rng4
      (mkCase s!"fuzz/type/top-non-int/deep-{depth}" (withCondRaw below bad), rng6)
    else if shape = 6 then
      (mkCase "fuzz/intov/nan-via-program" #[] nanProgram, rng4)
    else if shape = 7 then
      (mkCase "fuzz/intov/nan-via-program-deep" noiseA nanProgram, rng4)
    else if shape = 8 then
      (mkCase "fuzz/gas/exact/nonzero-succeeds"
        (withCond #[] (.num 1))
        #[.pushInt (.num ifnotretSetGasExact), .tonEnvOp .setGasLimit, ifnotretInstr], rng4)
    else if shape = 9 then
      (mkCase "fuzz/gas/exact-minus-one/nonzero-out-of-gas"
        (withCond #[] (.num 1))
        #[.pushInt (.num ifnotretSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotretInstr], rng4)
    else if shape = 10 then
      (mkCase "fuzz/gas/exact/zero-succeeds"
        (withCond #[] (.num 0))
        #[.pushInt (.num ifnotretSetGasExact), .tonEnvOp .setGasLimit, ifnotretInstr], rng4)
    else if shape = 11 then
      -- Non-ret branch should execute tail.
      (mkCase "fuzz/order/tail-exec-on-nonzero"
        (withCond #[] (.num (-5))) branchObservableProgram, rng4)
    else if shape = 12 then
      -- Ret-on-zero should skip tail (observable by absence of marker).
      (mkCase "fuzz/order/tail-skipped-on-zero"
        (withCond #[] (.num 0)) branchObservableProgram, rng4)
    else if shape = 13 then
      let (bad, rng6) := pickFromPool ifnotretBadCondNonIntPool rng4
      (mkCase s!"fuzz/type/deep-order-top-first"
        (below ++ #[intV 19, bad]) #[ifnotretInstr], rng6)
    else if shape = 14 then
      -- dispatch fallback exercise: different opcode must fall through.
      (mkCase "fuzz/dispatch/fallback-add" #[intV 1] #[.add], rng4)
    else
      (mkCase "fuzz/gas/exact-minus-one/zero-out-of-gas"
        (withCond #[] (.num 0))
        #[.pushInt (.num ifnotretSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotretInstr], rng4)
  let (tag, rng6) := randNat rng5 0 999_999
  ({ base with name := s!"{base.name}/{tag}" }, rng6)

private def needOneArgCont : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := #[], nargs := 1 }

private def regsC0Quit9 : Regs :=
  { Regs.initial with c0 := .quit 9 }

private def regsC0NeedOne : Regs :=
  { Regs.initial with c0 := needOneArgCont }

def suite : InstrSuite where
  id := ifnotretId
  unit := #[
    { name := "unit/state/false-branch-invokes-ret-and-resets-c0"
      run := do
        let st ← expectStateOk "state/false-branch"
          (runIfnotretState (withCond #[intV 17] (.num 0)) regsC0Quit9 (.quit 71))
        if st.stack != #[intV 17] then
          throw (IO.userError s!"state/false-branch: expected stack #[17], got {reprStr st.stack}")
        if st.cc != .quit 9 then
          throw (IO.userError s!"state/false-branch: expected cc=quit9, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"state/false-branch: expected c0=quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/true-branch-skips-ret-and-preserves-c0-and-cc"
      run := do
        let st ← expectStateOk "state/true-branch"
          (runIfnotretState (withCond #[intV 17] (.num 5)) regsC0Quit9 (.quit 71))
        if st.stack != #[intV 17] then
          throw (IO.userError s!"state/true-branch: expected stack #[17], got {reprStr st.stack}")
        if st.cc != .quit 71 then
          throw (IO.userError s!"state/true-branch: expected cc=quit71, got {reprStr st.cc}")
        if st.regs.c0 != .quit 9 then
          throw (IO.userError s!"state/true-branch: expected c0 unchanged quit9, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/state/false-branch-ret-propagates-jump-underflow"
      run := do
        expectStateErr "state/false-ret-underflow"
          (runIfnotretState (withCond #[] (.num 0)) regsC0NeedOne (.quit 44))
          .stkUnd }
    ,
    { name := "unit/state/true-branch-avoids-ret-error-path"
      run := do
        let st ← expectStateOk "state/true-skips-ret-underflow"
          (runIfnotretState (withCond #[] (.num 3)) regsC0NeedOne (.quit 44))
        if st.cc != .quit 44 then
          throw (IO.userError s!"state/true-skips-ret-underflow: expected cc unchanged, got {reprStr st.cc}")
        if st.regs.c0 != needOneArgCont then
          throw (IO.userError s!"state/true-skips-ret-underflow: expected c0 unchanged, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/error-order/popbool-before-ret"
      run := do
        expectStateErr "order/type-before-ret-underflow"
          (runIfnotretState (withCondRaw #[] (.null : Value)) regsC0NeedOne (.quit 12))
          .typeChk
        expectStateErr "order/intov-before-ret-underflow"
          (runIfnotretState (withCond #[] .nan) regsC0NeedOne (.quit 12))
          .intOv
        expectStateErr "order/ret-underflow-when-bool-false"
          (runIfnotretState (withCond #[] (.num 0)) regsC0NeedOne (.quit 12))
          .stkUnd }
    ,
    { name := "unit/direct/underflow-type-intov"
      run := do
        expectErr "underflow/empty" (runIfnotretDirect #[]) .stkUnd
        expectErr "type/null" (runIfnotretDirect #[.null]) .typeChk
        expectErr "type/cell" (runIfnotretDirect #[.cell refCellA]) .typeChk
        expectErr "type/slice" (runIfnotretDirect #[.slice fullSliceA]) .typeChk
        expectErr "type/builder" (runIfnotretDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/tuple" (runIfnotretDirect #[.tuple #[]]) .typeChk
        expectErr "type/cont" (runIfnotretDirect #[q0]) .typeChk
        expectErr "intov/nan" (runIfnotretDirect #[.int .nan]) .intOv }
    ,
    { name := "unit/direct/deep-stack-preserved-on-both-branches"
      run := do
        let below : Array Value := #[.null, intV (-9), .cell refCellA, .builder Builder.empty, .tuple #[]]
        expectOkStack "deep/false"
          (runIfnotretDirect (withCond below (.num 0)))
          below
        expectOkStack "deep/true"
          (runIfnotretDirect (withCond below (.num 5)))
          below }
    ,
    { name := "unit/direct/boolean-coercion-zero-vs-nonzero"
      run := do
        let checks : Array (Int × Bool) :=
          #[(0, true), (1, false), (-1, false), (17, false), (-255, false)]
        for (cond, shouldRet) in checks do
          let st ← expectStateOk s!"coercion/{cond}"
            (runIfnotretState (withCond #[] (.num cond)) regsC0Quit9 (.quit 66))
          if shouldRet then
            if st.cc != .quit 9 then
              throw (IO.userError s!"coercion/{cond}: expected RET to c0 target, got {reprStr st.cc}")
          else
            if st.cc != .quit 66 then
              throw (IO.userError s!"coercion/{cond}: expected no RET, got {reprStr st.cc}") }
    ,
    { name := "unit/dispatch/fallback-and-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfnotretDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]

        expectOkStack "dispatch/matched-ifnotret-no-next"
          (runHandlerDirectWithNext execInstrFlowIfnotret ifnotretInstr (VM.push (intV dispatchSentinel)) #[intV 1])
          #[] }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let seq : Array Instr := #[.ifret, .ifnotret, .if_, .ifnot, .add]
        let code ←
          match assembleCp0 seq.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {reprStr e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ifret" s0 .ifret 8
        let s2 ← expectDecodeStep "decode/ifnotret" s1 .ifnotret 8
        let s3 ← expectDecodeStep "decode/if" s2 .if_ 8
        let s4 ← expectDecodeStep "decode/ifnot" s3 .ifnot 8
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/seq-end: expected exhausted bits, got {s5.bitsRemaining}")

        let ifnotretCode ←
          match assembleCp0 [.ifnotret] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/ifnotret failed: {reprStr e}")
        if ifnotretCode.bits = natToBits 0xdd 8 then
          pure ()
        else
          throw (IO.userError s!"opcode/ifnotret: expected 0xdd, got {reprStr ifnotretCode.bits}")

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
          throw (IO.userError s!"decode/raw-end: expected exhausted bits, got {r4.bitsRemaining}") }
  ]
  oracle := #[
    -- Branch observability with a tail instruction: RET-on-false skips the tail.
    mkCase "branch/observable/ret-on-zero" (withCond #[] (.num 0)) branchObservableProgram,
    mkCase "branch/observable/no-ret-on-one" (withCond #[] (.num 1)) branchObservableProgram,
    mkCase "branch/observable/no-ret-on-neg-one" (withCond #[] (.num (-1))) branchObservableProgram,
    mkCase "branch/observable/no-ret-on-two" (withCond #[] (.num 2)) branchObservableProgram,
    mkCase "branch/observable/no-ret-on-neg-two" (withCond #[] (.num (-2))) branchObservableProgram,
    mkCase "branch/observable/no-ret-big-pos" (withCond #[] (.num (pow2 200))) branchObservableProgram,
    mkCase "branch/observable/no-ret-big-neg" (withCond #[] (.num (-(pow2 200)))) branchObservableProgram,
    mkCase "branch/observable/no-ret-max-int257" (withCond #[] (.num maxInt257)) branchObservableProgram,
    mkCase "branch/observable/no-ret-min-int257" (withCond #[] (.num minInt257)) branchObservableProgram,
    mkCase "branch/observable/deep-ret-zero-noise-a" (withCond noiseA (.num 0)) branchObservableProgram,
    mkCase "branch/observable/deep-no-ret-one-noise-a" (withCond noiseA (.num 1)) branchObservableProgram,
    mkCase "branch/observable/deep-no-ret-neg-seven-noise-b" (withCond noiseB (.num (-7))) branchObservableProgram,
    mkCase "branch/observable/deep-ret-zero-noise-c" (withCond noiseC (.num 0)) branchObservableProgram,
    mkCase "branch/observable/deep-no-ret-max-noise-c" (withCond noiseC (.num maxInt257)) branchObservableProgram,

    -- No-tail baseline success cases.
    mkCase "ok/no-tail/zero" (withCond #[] (.num 0)),
    mkCase "ok/no-tail/one" (withCond #[] (.num 1)),
    mkCase "ok/no-tail/neg-one" (withCond #[] (.num (-1))),
    mkCase "ok/no-tail/max-int257" (withCond #[] (.num maxInt257)),
    mkCase "ok/no-tail/min-int257" (withCond #[] (.num minInt257)),
    mkCase "ok/no-tail/deep-zero-a" (withCond noiseA (.num 0)),
    mkCase "ok/no-tail/deep-nonzero-a" (withCond noiseA (.num 11)),
    mkCase "ok/no-tail/deep-zero-b" (withCond noiseB (.num 0)),
    mkCase "ok/no-tail/deep-nonzero-b" (withCond noiseB (.num (-5))),
    mkCase "ok/no-tail/deep-zero-c" (withCond noiseC (.num 0)),
    mkCase "ok/no-tail/deep-nonzero-c" (withCond noiseC (.num 4)),

    -- Deterministic underflow/type/intov failures at bool-pop site.
    mkCase "err/underflow/empty" #[],
    mkCase "err/type/null" (withCondRaw #[] (.null : Value)),
    mkCase "err/type/cell" (withCondRaw #[] (.cell refCellA)),
    mkCase "err/type/slice" (withCondRaw #[] (.slice fullSliceA)),
    mkCase "err/type/builder" (withCondRaw #[] (.builder Builder.empty)),
    mkCase "err/type/tuple" (withCondRaw #[] (.tuple #[])),
    mkCase "err/type/cont" (withCondRaw #[] q0),
    mkCase "err/type/deep-null" (withCondRaw noiseA (.null : Value)),
    mkCase "err/type/deep-cont" (withCondRaw noiseC q0),
    mkCase "err/intov/nan-via-program" #[] nanProgram,
    mkCase "err/intov/nan-via-program-deep" noiseA nanProgram,

    -- Deterministic gas cliff (nonzero branch includes implicit RET).
    mkCase "gas/exact/nonzero-succeeds" (withCond #[] (.num 1))
      #[.pushInt (.num ifnotretSetGasExact), .tonEnvOp .setGasLimit, ifnotretInstr],
    mkCase "gas/exact-minus-one/nonzero-out-of-gas" (withCond #[] (.num 1))
      #[.pushInt (.num ifnotretSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotretInstr],
    mkCase "gas/exact/zero-succeeds" (withCond #[] (.num 0))
      #[.pushInt (.num ifnotretSetGasExact), .tonEnvOp .setGasLimit, ifnotretInstr]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr ifnotretId
      count := 500
      gen := genIfnotretFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.IFNOTRET
