import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.IFNOT

/-
IFNOT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Ifnot.lean`
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.call` contract used by false branch)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xdf -> .ifnot`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ifnot -> 0xdf`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_ifnot`, registration in `register_continuation_cond_loop_ops`).

Branch map covered by this suite:
- dispatch: only `.ifnot` executes; all other opcodes must fall through to `next`;
- pre-check: `checkUnderflow(2)` must fire before any pop/type logic;
- pop order: top is continuation (`popCont`) then condition (`popBool`);
- condition branch inversion: `0` calls continuation, non-zero skips call;
- false-branch call semantics parity: `call(cont)` stack/closure behavior (including
  `nargs`/captured-stack underflow) must match C++;
- cp0 registration parity around opcode neighborhood `0xde/0xdf/0xe0`.
-/

private def ifnotId : InstrId := { name := "IFNOT" }

private def ifnotInstr : Instr := .ifnot

private def dispatchSentinel : Int := 7402

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def q0 : Value :=
  .cont (.quit 0)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def sliceNoiseA : Slice :=
  mkSliceWithBitsRefs (natToBits 0x5a 8) #[]

private def sliceNoiseB : Slice :=
  mkSliceWithBitsRefs (natToBits 0x1ace 13) #[refLeafA]

private def ordinaryCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def envelopeCont (nargs : Int := -1) (captured : Array Value := #[]) : Continuation :=
  .envelope (.quit 5) OrdCregs.empty { stack := captured, nargs := nargs }

private def mkIfnotCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ifnotInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnotId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runIfnotDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfnot ifnotInstr stack

private def runIfnotDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfnot instr (VM.push (intV dispatchSentinel)) stack

private def runIfnotRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowIfnot ifnotInstr (pure ())).run st0

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

private def expectTopC0Ordinary (label : String) (st : VmState) : IO Unit := do
  match st.regs.c0 with
  | .ordinary _ _ _ _ => pure ()
  | other =>
      throw (IO.userError s!"{label}: expected regs.c0 to be ordinary return cont, got {reprStr other}")

private def ifnotSetGasExact : Int :=
  computeExactGasBudget ifnotInstr

private def ifnotSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ifnotInstr

private def boolPool : Array Int :=
  #[0, 1, -1, 2, -2, 7, -7, 255, -255, maxInt257, minInt257]

private def noisePool : Array Value :=
  #[
    .null,
    intV 0,
    intV 7,
    intV (-9),
    .cell refLeafA,
    .cell refLeafB,
    .builder Builder.empty,
    .tuple #[],
    .cont (.quit 0),
    .slice sliceNoiseA,
    .slice sliceNoiseB
  ]

private def badTopNonContPool : Array Value :=
  #[.null, intV 1, .cell refLeafA, .builder Builder.empty, .tuple #[], .slice sliceNoiseA]

private def badBoolNonIntPool : Array Value :=
  #[.null, .cell refLeafB, .builder Builder.empty, .tuple #[], .slice sliceNoiseB, .cont (.quit 0)]

private def pickFromPool {a : Type} [Inhabited a] (pool : Array a) (rng : StdGen) : a × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickBoolVal (rng : StdGen) : Int × StdGen :=
  pickFromPool boolPool rng

private def genBelowStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool noisePool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def genIfnotFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (base, rng2) :=
    if shape = 0 then
      (mkIfnotCase "fuzz/ok/false-basic" #[intV 0, q0], rng1)
    else if shape = 1 then
      (mkIfnotCase "fuzz/ok/true-basic" #[intV 1, q0], rng1)
    else if shape = 2 then
      let (b, rng3) := pickBoolVal rng1
      let b' := if b = 0 then 1 else b
      (mkIfnotCase s!"fuzz/ok/true-random-{b'}" #[intV b', q0], rng3)
    else if shape = 3 then
      let (depth, rng3) := randNat rng1 1 4
      let (below, rng4) := genBelowStack depth rng3
      (mkIfnotCase s!"fuzz/ok/deep-false-depth-{depth}" (below ++ #[intV 0, q0]), rng4)
    else if shape = 4 then
      let (depth, rng3) := randNat rng1 1 4
      let (below, rng4) := genBelowStack depth rng3
      let (b, rng5) := pickBoolVal rng4
      let b' := if b = 0 then -1 else b
      (mkIfnotCase s!"fuzz/ok/deep-true-depth-{depth}" (below ++ #[intV b', q0]), rng5)
    else if shape = 5 then
      (mkIfnotCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 6 then
      let (single, rng3) := pickFromPool noisePool rng1
      (mkIfnotCase "fuzz/underflow/one" #[single], rng3)
    else if shape = 7 then
      let (bad, rng3) := pickFromPool badTopNonContPool rng1
      (mkIfnotCase "fuzz/type/popcont" #[intV 1, bad], rng3)
    else if shape = 8 then
      let (bad, rng3) := pickFromPool badBoolNonIntPool rng1
      (mkIfnotCase "fuzz/type/popbool" #[bad, q0], rng3)
    else if shape = 9 then
      let (depth, rng3) := randNat rng1 1 3
      let (below, rng4) := genBelowStack depth rng3
      let (bad, rng5) := pickFromPool badTopNonContPool rng4
      (mkIfnotCase s!"fuzz/type/deep-popcont-depth-{depth}" (below ++ #[intV 0, bad]), rng5)
    else if shape = 10 then
      let (depth, rng3) := randNat rng1 1 3
      let (below, rng4) := genBelowStack depth rng3
      let (bad, rng5) := pickFromPool badBoolNonIntPool rng4
      (mkIfnotCase s!"fuzz/type/deep-popbool-depth-{depth}" (below ++ #[bad, q0]), rng5)
    else if shape = 11 then
      (mkIfnotCase "fuzz/gas/exact/true"
        #[intV 1, q0]
        #[.pushInt (.num ifnotSetGasExact), .tonEnvOp .setGasLimit, ifnotInstr],
        rng1)
    else if shape = 12 then
      (mkIfnotCase "fuzz/gas/exact-minus-one/true"
        #[intV 1, q0]
        #[.pushInt (.num ifnotSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotInstr],
        rng1)
    else
      (mkIfnotCase "fuzz/gas/exact/false"
        #[intV 0, q0]
        #[.pushInt (.num ifnotSetGasExact), .tonEnvOp .setGasLimit, ifnotInstr],
        rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ base with name := s!"{base.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := ifnotId
  unit := #[
    { name := "unit/direct/branch-inversion-and-bool-coercion"
      run := do
        let target : Continuation := .quit 9
        let checks : Array (Int × Bool) :=
          #[(0, true), (1, false), (-1, false), (17, false), (-255, false)]
        for (cond, shouldCall) in checks do
          let st ← expectRawOk s!"raw/cond-{cond}" (runIfnotRaw #[intV cond, .cont target])
          if st.stack == #[] then
            pure ()
          else
            throw (IO.userError s!"raw/cond-{cond}: expected empty stack, got {reprStr st.stack}")
          if shouldCall then
            expectContEq s!"raw/cond-{cond}/cc-called" st.cc target
            expectTopC0Ordinary s!"raw/cond-{cond}/c0-called" st
          else
            expectContEq s!"raw/cond-{cond}/cc-not-called" st.cc defaultCc
            expectContEq s!"raw/cond-{cond}/c0-unchanged" st.regs.c0 Regs.initial.c0 }
    ,
    { name := "unit/direct/false-branch-uses-vm-call-semantics"
      run := do
        let needOne := ordinaryCont 1 #[]
        expectErr "call/ordinary/nargs-underflow"
          (runIfnotDirect #[intV 0, .cont needOne]) .stkUnd

        expectOkStack "call/ordinary/nargs-select-top"
          (runIfnotDirect #[intV 7, intV 8, intV 0, .cont needOne])
          #[intV 8]

        let capturedAll := ordinaryCont (-1) #[intV 41]
        expectOkStack "call/ordinary/captured-plus-all-args"
          (runIfnotDirect #[intV 7, intV 0, .cont capturedAll])
          #[intV 41, intV 7]

        let capturedOne := ordinaryCont 1 #[intV 99]
        expectOkStack "call/ordinary/captured-plus-top1"
          (runIfnotDirect #[intV 4, intV 5, intV 0, .cont capturedOne])
          #[intV 99, intV 5]

        let envNeedTwo := envelopeCont 2 #[]
        expectErr "call/envelope/nargs-underflow"
          (runIfnotDirect #[intV 11, intV 0, .cont envNeedTwo]) .stkUnd

        let envCaptured := envelopeCont 1 #[intV 55]
        expectOkStack "call/envelope/captured-plus-top1"
          (runIfnotDirect #[intV 4, intV 5, intV 0, .cont envCaptured])
          #[intV 55, intV 5] }
    ,
    { name := "unit/direct/errors-underflow-type-and-intov"
      run := do
        expectErr "underflow/empty" (runIfnotDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runIfnotDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-noncont" (runIfnotDirect #[.null]) .stkUnd

        expectErr "type/popcont-null" (runIfnotDirect #[intV 1, .null]) .typeChk
        expectErr "type/popcont-int" (runIfnotDirect #[intV 1, intV 2]) .typeChk
        expectErr "type/popcont-cell" (runIfnotDirect #[intV 1, .cell refLeafA]) .typeChk
        expectErr "type/popcont-builder" (runIfnotDirect #[intV 1, .builder Builder.empty]) .typeChk
        expectErr "type/popcont-tuple" (runIfnotDirect #[intV 1, .tuple #[]]) .typeChk
        expectErr "type/popcont-slice" (runIfnotDirect #[intV 1, .slice sliceNoiseA]) .typeChk

        expectErr "type/popbool-null" (runIfnotDirect #[.null, q0]) .typeChk
        expectErr "type/popbool-cell" (runIfnotDirect #[.cell refLeafA, q0]) .typeChk
        expectErr "type/popbool-builder" (runIfnotDirect #[.builder Builder.empty, q0]) .typeChk
        expectErr "type/popbool-tuple" (runIfnotDirect #[.tuple #[], q0]) .typeChk
        expectErr "type/popbool-slice" (runIfnotDirect #[.slice sliceNoiseB, q0]) .typeChk
        expectErr "type/popbool-cont" (runIfnotDirect #[q0, q0]) .typeChk

        expectErr "intov/popbool-nan" (runIfnotDirect #[.int .nan, q0]) .intOv }
    ,
    { name := "unit/direct/deep-stack-preserved-on-both-branches"
      run := do
        let below : Array Value :=
          #[.null, intV (-7), .cell refLeafA, .builder Builder.empty, .tuple #[], .slice sliceNoiseA]
        expectOkStack "deep/false"
          (runIfnotDirect (below ++ #[intV 0, q0]))
          below
        expectOkStack "deep/true"
          (runIfnotDirect (below ++ #[intV (-5), q0]))
          below }
    ,
    { name := "unit/dispatch/fallback-and-match-contract"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfnotDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]

        expectOkStack "dispatch/fallback-if"
          (runIfnotDispatchFallback .if_ #[intV 1, q0])
          #[intV 1, q0, intV dispatchSentinel]

        expectOkStack "dispatch/matching-ifnot-does-not-run-next"
          (runHandlerDirectWithNext execInstrFlowIfnot ifnotInstr (VM.push (intV dispatchSentinel)) #[intV 1, q0])
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
          throw (IO.userError s!"decode/seq-end: expected exhausted bits, got {s8.bitsRemaining}")

        let ifnotCode ←
          match assembleCp0 [.ifnot] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/ifnot failed: {reprStr e}")
        if ifnotCode.bits = natToBits 0xdf 8 then
          pure ()
        else
          throw (IO.userError s!"opcode/ifnot: expected 0xdf, got {reprStr ifnotCode.bits}")

        let rawBits : BitString :=
          natToBits 0xde 8 ++
          natToBits 0xdf 8 ++
          natToBits 0xe0 8 ++
          natToBits 0xa0 8
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-if" r0 .if_ 8
        let r2 ← expectDecodeStep "decode/raw-ifnot" r1 .ifnot 8
        let r3 ← expectDecodeStep "decode/raw-ifjmp" r2 .ifjmp 8
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted bits, got {r4.bitsRemaining}") }
    ,
    { name := "unit/gas/probe-budget-ordering"
      run := do
        if ifnotSetGasExact > 0 then
          pure ()
        else
          throw (IO.userError s!"gas/exact: expected positive budget, got {ifnotSetGasExact}")
        if ifnotSetGasExactMinusOne < ifnotSetGasExact then
          pure ()
        else
          throw (IO.userError
            s!"gas/exact-minus-one: expected strict decrease, got exact={ifnotSetGasExact} minusOne={ifnotSetGasExactMinusOne}") }
  ]
  oracle := #[
    mkIfnotCase "ok/false/basic-zero" #[intV 0, q0],
    mkIfnotCase "ok/false/deep-int" #[intV 7, intV 0, q0],
    mkIfnotCase "ok/false/deep-null" #[.null, intV 0, q0],
    mkIfnotCase "ok/false/deep-cell" #[.cell refLeafA, intV 0, q0],
    mkIfnotCase "ok/false/deep-builder" #[.builder Builder.empty, intV 0, q0],
    mkIfnotCase "ok/false/deep-tuple" #[.tuple #[], intV 0, q0],
    mkIfnotCase "ok/false/deep-slice" #[.slice sliceNoiseA, intV 0, q0],
    mkIfnotCase "ok/false/deep-mixed" #[.null, intV 7, .cell refLeafB, intV 0, q0],

    mkIfnotCase "ok/true/basic-one" #[intV 1, q0],
    mkIfnotCase "ok/true/basic-neg-one" #[intV (-1), q0],
    mkIfnotCase "ok/true/basic-large-pos" #[intV (intPow2 32), q0],
    mkIfnotCase "ok/true/basic-large-neg" #[intV (-(intPow2 32)), q0],
    mkIfnotCase "ok/true/deep-int" #[intV 7, intV 1, q0],
    mkIfnotCase "ok/true/deep-null" #[.null, intV 1, q0],
    mkIfnotCase "ok/true/deep-cell" #[.cell refLeafA, intV 1, q0],
    mkIfnotCase "ok/true/deep-builder" #[.builder Builder.empty, intV 1, q0],
    mkIfnotCase "ok/true/deep-tuple" #[.tuple #[], intV 1, q0],
    mkIfnotCase "ok/true/deep-slice" #[.slice sliceNoiseB, intV (-5), q0],
    mkIfnotCase "ok/true/deep-mixed" #[.cell refLeafB, .null, intV 123, q0],

    mkIfnotCase "underflow/empty" #[],
    mkIfnotCase "underflow/one-int" #[intV 0],
    mkIfnotCase "underflow/one-cont" #[q0],
    mkIfnotCase "underflow/one-null" #[.null],

    mkIfnotCase "type/popcont-null" #[intV 1, .null],
    mkIfnotCase "type/popcont-int" #[intV 1, intV 2],
    mkIfnotCase "type/popcont-cell" #[intV 1, .cell refLeafA],
    mkIfnotCase "type/popcont-builder" #[intV 1, .builder Builder.empty],
    mkIfnotCase "type/popcont-tuple" #[intV 1, .tuple #[]],
    mkIfnotCase "type/popcont-slice" #[intV 1, .slice sliceNoiseA],

    mkIfnotCase "type/popbool-null" #[.null, q0],
    mkIfnotCase "type/popbool-cell" #[.cell refLeafA, q0],
    mkIfnotCase "type/popbool-builder" #[.builder Builder.empty, q0],
    mkIfnotCase "type/popbool-tuple" #[.tuple #[], q0],
    mkIfnotCase "type/popbool-slice" #[.slice sliceNoiseB, q0],
    mkIfnotCase "type/popbool-cont" #[q0, q0],

    mkIfnotCase "gas/exact-cost-succeeds/true"
      #[intV 1, q0]
      #[.pushInt (.num ifnotSetGasExact), .tonEnvOp .setGasLimit, ifnotInstr],

    mkIfnotCase "gas/exact-minus-one-out-of-gas/true"
      #[intV 1, q0]
      #[.pushInt (.num ifnotSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotInstr],

    mkIfnotCase "gas/exact-cost-succeeds/false"
      #[intV 0, q0]
      #[.pushInt (.num ifnotSetGasExact), .tonEnvOp .setGasLimit, ifnotInstr],

    mkIfnotCase "gas/exact-minus-one-out-of-gas/false"
      #[intV 0, q0]
      #[.pushInt (.num ifnotSetGasExactMinusOne), .tonEnvOp .setGasLimit, ifnotInstr]
  ]
  fuzz := #[
    { seed := 2026021102
      count := 500
      gen := genIfnotFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.IFNOT
