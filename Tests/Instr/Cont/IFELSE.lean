import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFELSE

/-
IFELSE branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Flow/Ifelse.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_if_else`)

Branch map and terminal outcomes:
- Dispatch branch:
  - `.ifelse` executes handler body;
  - all other opcodes fall through to `next`.
- `.ifelse` execution branch points:
  - `checkUnderflow 3` success vs `stkUnd`;
  - first `popCont` (top, logical `cont0`) success vs `typeChk`;
  - second `popCont` (next, logical `cont1`) success vs `typeChk`;
  - `popBool` success vs `typeChk`/`intOv`;
  - boolean split: false selects `cont0`, true selects `cont1`.

Lean/C++ semantic alignment for branch mapping:
- C++ pops `cont0`, then `cont1`, then bool; if bool=true it swaps, then calls `cont0`.
- Lean pops `cont0`, then `cont1`, then bool; if bool=true it calls `cont1`, else `cont0`.
- These are equivalent: false -> top continuation (`cont0`), true -> second continuation (`cont1`).

No branch-selection mismatch was found.
-/

private def ifelseId : InstrId := { name := "IFELSE" }

private def q0 : Continuation := .quit 0
private def qa : Continuation := .quit 41
private def qb : Continuation := .quit 42

private def mkIfelseStack
    (flag : Value)
    (cont1 cont0 : Continuation)
    (below : Array Value := #[]) : Array Value :=
  below ++ #[flag, .cont cont1, .cont cont0]

private def runIfelseRaw
    (instr : Instr := .ifelse)
    (stack : Array Value := #[])
    (next : VM Unit := pure ()) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrFlowIfelse instr next).run st0

private def runIfelseDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfelse .ifelse stack

private def expectSelectedCc
    (label : String)
    (stack : Array Value)
    (expectedCc : Continuation)
    (expectedStack : Array Value := #[]) : IO Unit := do
  let (res, st1) := runIfelseRaw .ifelse stack
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok _ =>
      if st1.cc != expectedCc then
        throw (IO.userError
          s!"{label}: expected cc {reprStr expectedCc}, got {reprStr st1.cc}")
      else if st1.stack != expectedStack then
        throw (IO.userError
          s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st1.stack}")
      else
        pure ()

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.ifelse])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifelseId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def progPushC0C1Ifelse : Array Instr :=
  #[.pushCtr 0, .pushCtr 1, .ifelse]

private def progPushC1C0Ifelse : Array Instr :=
  #[.pushCtr 1, .pushCtr 0, .ifelse]

private def progNanC0C1Ifelse : Array Instr :=
  #[.pushInt .nan, .pushCtr 0, .pushCtr 1, .ifelse]

private def progNanC1C0Ifelse : Array Instr :=
  #[.pushInt .nan, .pushCtr 1, .pushCtr 0, .ifelse]

private def oracleCases : Array OracleCase :=
  #[
    -- Branch behavior via register continuations (C0=quit0, C1=quit1).
    mkCase "branch/c0c1/false/zero" #[intV 0] progPushC0C1Ifelse,
    mkCase "branch/c0c1/true/one" #[intV 1] progPushC0C1Ifelse,
    mkCase "branch/c0c1/true/minus-one" #[intV (-1)] progPushC0C1Ifelse,
    mkCase "branch/c0c1/true/large" #[intV ((2 : Int) ^ (64 : Nat))] progPushC0C1Ifelse,
    mkCase "branch/c0c1/deep/false" #[.null, intV 9, intV 0] progPushC0C1Ifelse,
    mkCase "branch/c0c1/deep/true" #[.null, intV 9, intV 3] progPushC0C1Ifelse,
    mkCase "branch/c0c1/deep/cell-below/false" #[.cell Cell.empty, intV 0] progPushC0C1Ifelse,
    mkCase "branch/c0c1/deep/cell-below/true" #[.cell Cell.empty, intV 8] progPushC0C1Ifelse,
    mkCase "branch/c0c1/deep/builder-below/false" #[.builder Builder.empty, intV 0] progPushC0C1Ifelse,
    mkCase "branch/c0c1/deep/builder-below/true" #[.builder Builder.empty, intV (-8)] progPushC0C1Ifelse,

    mkCase "branch/c1c0/false/zero" #[intV 0] progPushC1C0Ifelse,
    mkCase "branch/c1c0/true/one" #[intV 1] progPushC1C0Ifelse,
    mkCase "branch/c1c0/true/minus-one" #[intV (-1)] progPushC1C0Ifelse,
    mkCase "branch/c1c0/true/large" #[intV ((2 : Int) ^ (32 : Nat))] progPushC1C0Ifelse,
    mkCase "branch/c1c0/deep/false" #[.null, intV 11, intV 0] progPushC1C0Ifelse,
    mkCase "branch/c1c0/deep/true" #[.null, intV 11, intV 5] progPushC1C0Ifelse,
    mkCase "branch/c1c0/deep/cell-below/false" #[.cell Cell.empty, intV 0] progPushC1C0Ifelse,
    mkCase "branch/c1c0/deep/cell-below/true" #[.cell Cell.empty, intV (-2)] progPushC1C0Ifelse,
    mkCase "branch/c1c0/deep/builder-below/false" #[.builder Builder.empty, intV 0] progPushC1C0Ifelse,
    mkCase "branch/c1c0/deep/builder-below/true" #[.builder Builder.empty, intV 2] progPushC1C0Ifelse,

    -- Direct IFELSE with identical continuations (oracle stack token supports only quit(0) continuations).
    mkCase "direct/identical/false" (mkIfelseStack (intV 0) q0 q0),
    mkCase "direct/identical/true" (mkIfelseStack (intV 1) q0 q0),
    mkCase "direct/identical/true-negative" (mkIfelseStack (intV (-5)) q0 q0),
    mkCase "direct/identical/deep/false" (mkIfelseStack (intV 0) q0 q0 #[.null, intV 7]),
    mkCase "direct/identical/deep/true" (mkIfelseStack (intV 1) q0 q0 #[.null, intV 7]),
    mkCase "direct/identical/deep/cell" (mkIfelseStack (intV 0) q0 q0 #[.cell Cell.empty]),

    -- Underflow and type/intOv paths.
    mkCase "underflow/empty" #[],
    mkCase "underflow/one/int" #[intV 0],
    mkCase "underflow/two/int-cont" #[intV 0, .cont q0],
    mkCase "underflow/two/int-null" #[intV 0, .null],

    mkCase "type/top-not-cont/null" #[intV 0, .cont q0, .null],
    mkCase "type/top-not-cont/int" #[intV 0, .cont q0, intV 1],
    mkCase "type/second-not-cont/null" #[intV 0, .null, .cont q0],
    mkCase "type/second-not-cont/cell" #[intV 0, .cell Cell.empty, .cont q0],

    mkCase "type/bool-null" #[.null, .cont q0, .cont q0],
    mkCase "type/bool-cell" #[.cell Cell.empty, .cont q0, .cont q0],
    mkCase "type/bool-builder" #[.builder Builder.empty, .cont q0, .cont q0],

    mkCase "intov/bool-nan/c0c1" #[] progNanC0C1Ifelse,
    mkCase "intov/bool-nan/c1c0" #[] progNanC1C0Ifelse
  ]

private def randFlagInt (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 5
  if mode = 0 then
    (0, rng1)
  else
    let (neg, rng2) := randBool rng1
    let magnitude : Int := Int.ofNat (mode + 1)
    (if neg then -magnitude else magnitude, rng2)

private def randSmallInt (rng0 : StdGen) : Int × StdGen :=
  let (u, rng1) := randNat rng0 0 40
  (Int.ofNat u - 20, rng1)

private def genIfelseFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  if shape = 0 then
    let (flag, rng2) := randFlagInt rng1
    (mkCase s!"fuzz/branch/c0c1/{flag}" #[intV flag] progPushC0C1Ifelse, rng2)
  else if shape = 1 then
    let (flag, rng2) := randFlagInt rng1
    (mkCase s!"fuzz/branch/c1c0/{flag}" #[intV flag] progPushC1C0Ifelse, rng2)
  else if shape = 2 then
    let (flag, rng2) := randFlagInt rng1
    let (n, rng3) := randSmallInt rng2
    (mkCase s!"fuzz/deep/c0c1/{flag}" #[.null, intV n, intV flag] progPushC0C1Ifelse, rng3)
  else if shape = 3 then
    let (flag, rng2) := randFlagInt rng1
    let (n, rng3) := randSmallInt rng2
    (mkCase s!"fuzz/deep/c1c0/{flag}" #[.cell Cell.empty, intV n, intV flag] progPushC1C0Ifelse, rng3)
  else if shape = 4 then
    let (flag, rng2) := randFlagInt rng1
    (mkCase s!"fuzz/direct/identical/{flag}" (mkIfelseStack (intV flag) q0 q0), rng2)
  else if shape = 5 then
    let (flag, rng2) := randFlagInt rng1
    let (n, rng3) := randSmallInt rng2
    (mkCase s!"fuzz/direct/deep/{flag}" (mkIfelseStack (intV flag) q0 q0 #[.null, intV n]), rng3)
  else if shape = 6 then
    (mkCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkCase "fuzz/underflow/two" #[intV 0, .cont q0], rng1)
  else if shape = 8 then
    (mkCase "fuzz/type/top-not-cont" #[intV 0, .cont q0, .null], rng1)
  else if shape = 9 then
    (mkCase "fuzz/type/second-not-cont" #[intV 0, .null, .cont q0], rng1)
  else if shape = 10 then
    (mkCase "fuzz/type/bool-null" #[.null, .cont q0, .cont q0], rng1)
  else if shape = 11 then
    (mkCase "fuzz/intov/nan-c0c1" #[] progNanC0C1Ifelse, rng1)
  else
    (mkCase "fuzz/intov/nan-c1c0" #[] progNanC1C0Ifelse, rng1)

def suite : InstrSuite where
  id := ifelseId
  unit := #[
    { name := "unit/branch/cont-order-and-bool-selection"
      run := do
        expectSelectedCc "false-selects-top-cont0"
          (mkIfelseStack (intV 0) qb qa)
          qa
        expectSelectedCc "true-selects-second-cont1"
          (mkIfelseStack (intV 1) qb qa)
          qb
        expectSelectedCc "true-nonzero-selects-second-cont1"
          (mkIfelseStack (intV (-9)) qb qa)
          qb }
    ,
    { name := "unit/branch/deep-stack-preserved"
      run := do
        let below : Array Value := #[.null, intV 17, .cell Cell.empty]
        expectSelectedCc "deep-false"
          (mkIfelseStack (intV 0) qb qa below)
          qa
          below
        expectSelectedCc "deep-true"
          (mkIfelseStack (intV 3) qb qa below)
          qb
          below }
    ,
    { name := "unit/errors/underflow-type-intov"
      run := do
        expectErr "underflow-empty" (runIfelseDirect #[]) .stkUnd
        expectErr "underflow-one" (runIfelseDirect #[intV 0]) .stkUnd
        expectErr "underflow-two" (runIfelseDirect #[intV 0, .cont qa]) .stkUnd

        expectErr "type-top-not-cont" (runIfelseDirect #[intV 0, .cont q0, .null]) .typeChk
        expectErr "type-second-not-cont" (runIfelseDirect #[intV 0, .null, .cont q0]) .typeChk
        expectErr "type-bool-null" (runIfelseDirect #[.null, .cont q0, .cont q0]) .typeChk
        expectErr "type-bool-cell" (runIfelseDirect #[.cell Cell.empty, .cont q0, .cont q0]) .typeChk
        expectErr "intov-bool-nan" (runIfelseDirect #[.int .nan, .cont q0, .cont q0]) .intOv }
    ,
    { name := "unit/dispatch/non-ifelse-falls-through"
      run := do
        expectOkStack "fallback-empty"
          (runHandlerDirectWithNext execInstrFlowIfelse .if_ (VM.push (intV 777)) #[])
          #[intV 777]
        expectOkStack "fallback-preserve-stack"
          (runHandlerDirectWithNext execInstrFlowIfelse .if_ (VM.push (intV 888)) #[.null, intV 1])
          #[.null, intV 1, intV 888] }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := 2026021105
      count := 300
      gen := genIfelseFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.IFELSE
