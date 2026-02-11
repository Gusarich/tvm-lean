import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CONDSEL

/-
CONDSEL branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Cont/CondSel.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
  (`exec_condsel`, `exec_condsel_chk`).

Branch map used for this suite:
- dispatch: `.contExt .condSel` executes, all other opcodes fall through to `next`.
- underflow guard: both paths require 3 stack items before any pop.
- value pop order: `y` (top), then `x`, then bool (`cond`, third from top).
- bool parsing outcomes: finite zero => false, finite non-zero => true,
  non-int => `typeChk`, NaN => `intOv`.
- selection semantics: true selects `x`; false selects `y`; deeper stack prefix is preserved.

Mismatch audit result:
- C++ does `check_underflow(3)` before pops.
- Lean originally popped first and only failed later; this suite assumes the patched Lean semantics
  now matches C++ with upfront `VM.checkUnderflow 3`.
-/

private def condSelId : InstrId := { name := "CONDSEL" }

private def condSelInstr : Instr := .contExt .condSel

private def dispatchSentinel : Int := 606

private def cellA : Cell := Cell.mkOrdinary #[true, false, true] #[]
private def cellB : Cell := Cell.mkOrdinary #[] #[Cell.empty]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def builderA : Builder := Builder.empty
private def builderB : Builder := Builder.empty.storeBits #[true, false, true]

private def tupleEmpty : Value := .tuple #[]
private def contQuit0 : Value := .cont (.quit 0)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[condSelInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := condSelId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runCondSelDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContCondSel condSelInstr stack

private def runCondSelDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContCondSel instr (VM.push (intV dispatchSentinel)) stack

private def runCondSelRaw (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrContCondSel condSelInstr (pure ())).run st0
  (res, st1.stack)

private def expectRawErrStack
    (label : String)
    (stack : Array Value)
    (expectedErr : Excno)
    (expectedStack : Array Value) : IO Unit := do
  let (res, stOut) := runCondSelRaw stack
  match res with
  | .error e =>
      if e != expectedErr then
        throw (IO.userError s!"{label}: expected error {expectedErr}, got {e}")
      else if stOut != expectedStack then
        throw (IO.userError s!"{label}: expected stack {reprStr expectedStack}, got {reprStr stOut}")
      else
        pure ()
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expectedErr}, got success")

private def condTruePool : Array Int := #[1, -1, 2, -9, maxInt257, minInt257]

private def noisePool : Array Value :=
  #[.null, intV 0, intV 17, .cell cellA, .slice sliceA, .builder builderA, tupleEmpty, contQuit0]

private def pickFromPool {a : Type} [Inhabited a] (pool : Array a) (rng : StdGen) : a × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genCondSelFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (x, rng2) := pickSigned257ish rng1
  let (y, rng3) := pickSigned257ish rng2
  let (condTrue, rng4) := pickFromPool condTruePool rng3
  let (noise1, rng5) := pickFromPool noisePool rng4
  let (noise2, rng6) := pickFromPool noisePool rng5
  let case0 :=
    if shape = 0 then
      mkCase s!"fuzz/ok/false/int-int" #[intV 0, intV x, intV y]
    else if shape = 1 then
      mkCase s!"fuzz/ok/true/int-int" #[intV condTrue, intV x, intV y]
    else if shape = 2 then
      mkCase s!"fuzz/ok/true/null-cell" #[intV condTrue, .null, .cell cellA]
    else if shape = 3 then
      mkCase s!"fuzz/ok/false/null-cell" #[intV 0, .null, .cell cellA]
    else if shape = 4 then
      mkCase s!"fuzz/ok/deep/true" #[noise1, noise2, intV condTrue, intV x, .slice sliceA]
    else if shape = 5 then
      mkCase s!"fuzz/ok/deep/false" #[noise1, noise2, intV 0, intV x, .slice sliceA]
    else if shape = 6 then
      mkCase s!"fuzz/underflow/empty" #[]
    else if shape = 7 then
      mkCase s!"fuzz/underflow/one" #[noise1]
    else if shape = 8 then
      mkCase s!"fuzz/underflow/two" #[noise1, noise2]
    else if shape = 9 then
      mkCase s!"fuzz/type/bool-null" #[.null, intV x, intV y]
    else if shape = 10 then
      mkCase s!"fuzz/type/bool-cell" #[.cell cellA, intV x, intV y]
    else if shape = 11 then
      mkCase s!"fuzz/type/bool-slice" #[.slice sliceA, intV x, intV y]
    else if shape = 12 then
      mkCase s!"fuzz/type/bool-builder" #[.builder builderA, intV x, intV y]
    else if shape = 13 then
      mkCase s!"fuzz/type/bool-cont" #[contQuit0, intV x, intV y]
    else
      mkCase s!"fuzz/intov/bool-nan-program" #[]
        #[.pushInt .nan, .pushInt (.num x), .pushInt (.num y), condSelInstr]
  let (tag, rng7) := randNat rng6 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng7)

def suite : InstrSuite where
  id := condSelId
  unit := #[
    { name := "unit/selection/false-selects-y-and-preserves-prefix"
      run := do
        expectOkStack "false/int-int" (runCondSelDirect #[intV 0, intV 11, intV 22]) #[intV 22]
        expectOkStack "false/prefix" (runCondSelDirect #[.null, intV 0, intV 11, intV 22]) #[.null, intV 22]
        expectOkStack "false/mixed" (runCondSelDirect #[intV 0, .cell cellA, .slice sliceA]) #[.slice sliceA]
        expectOkStack "false/deep-mixed"
          (runCondSelDirect #[tupleEmpty, contQuit0, intV 0, .builder builderA, .cell cellA])
          #[tupleEmpty, contQuit0, .cell cellA] }
    ,
    { name := "unit/selection/true-selects-x-and-accepts-any-nonzero"
      run := do
        expectOkStack "true/one" (runCondSelDirect #[intV 1, intV 11, intV 22]) #[intV 11]
        expectOkStack "true/minus-one" (runCondSelDirect #[intV (-1), intV 11, intV 22]) #[intV 11]
        expectOkStack "true/two" (runCondSelDirect #[intV 2, intV 11, intV 22]) #[intV 11]
        expectOkStack "true/max257" (runCondSelDirect #[intV maxInt257, intV 11, intV 22]) #[intV 11]
        expectOkStack "true/min257" (runCondSelDirect #[intV minInt257, intV 11, intV 22]) #[intV 11]
        expectOkStack "true/deep"
          (runCondSelDirect #[.null, .cell cellB, intV (-7), .builder builderB, .slice sliceB])
          #[.null, .cell cellB, .builder builderB] }
    ,
    { name := "unit/pop-order/bool-parse-happens-after-x-y-pops"
      run := do
        -- With three items, x and y are consumed before bool parsing; on bool parse error only deep prefix remains.
        expectRawErrStack "typechk/three-items-null-bool" #[.null, intV 11, intV 22] .typeChk #[]
        expectRawErrStack "intov/three-items-nan-bool" #[.int .nan, intV 11, intV 22] .intOv #[]
        expectRawErrStack "typechk/deep-prefix-preserved" #[.cell cellA, .null, intV 11, intV 22] .typeChk #[.cell cellA] }
    ,
    { name := "unit/underflow/upfront-guard-preserves-stack"
      run := do
        expectRawErrStack "underflow/empty" #[] .stkUnd #[]
        expectRawErrStack "underflow/one-int" #[intV 7] .stkUnd #[intV 7]
        expectRawErrStack "underflow/one-non-int" #[.null] .stkUnd #[.null]
        expectRawErrStack "underflow/two-ints" #[intV 7, intV 8] .stkUnd #[intV 7, intV 8]
        expectRawErrStack "underflow/two-mixed" #[.cell cellA, .null] .stkUnd #[.cell cellA, .null] }
    ,
    { name := "unit/error/bool-parsing-typechk-and-intov"
      run := do
        expectErr "bool-null" (runCondSelDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "bool-cell" (runCondSelDirect #[.cell cellA, intV 1, intV 2]) .typeChk
        expectErr "bool-slice" (runCondSelDirect #[.slice sliceA, intV 1, intV 2]) .typeChk
        expectErr "bool-builder" (runCondSelDirect #[.builder builderA, intV 1, intV 2]) .typeChk
        expectErr "bool-tuple-empty" (runCondSelDirect #[tupleEmpty, intV 1, intV 2]) .typeChk
        expectErr "bool-cont-quit0" (runCondSelDirect #[contQuit0, intV 1, intV 2]) .typeChk
        expectErr "bool-nan" (runCondSelDirect #[.int .nan, intV 1, intV 2]) .intOv }
    ,
    { name := "unit/dispatch/non-condsel-falls-through"
      run := do
        expectOkStack "dispatch/non-contExt" (runCondSelDispatchFallback .add #[]) #[intV dispatchSentinel]
        expectOkStack "dispatch/other-contExt" (runCondSelDispatchFallback (.contExt .booleval) #[])
          #[intV dispatchSentinel] }
  ]
  oracle := #[
    mkCase "ok/int/false-select-y" #[intV 0, intV 11, intV 22],
    mkCase "ok/int/true-select-x-one" #[intV 1, intV 11, intV 22],
    mkCase "ok/int/true-select-x-minus-one" #[intV (-1), intV 11, intV 22],
    mkCase "ok/int/true-select-x-two" #[intV 2, intV 11, intV 22],
    mkCase "ok/int/true-select-x-large-negative" #[intV (-987654321), intV 11, intV 22],
    mkCase "ok/int/true-select-x-max257" #[intV maxInt257, intV 11, intV 22],
    mkCase "ok/int/true-select-x-min257" #[intV minInt257, intV 11, intV 22],

    mkCase "ok/null-vs-int/true" #[intV 1, .null, intV 9],
    mkCase "ok/null-vs-int/false" #[intV 0, .null, intV 9],
    mkCase "ok/cell-vs-null/true" #[intV 1, .cell cellA, .null],
    mkCase "ok/cell-vs-null/false" #[intV 0, .cell cellA, .null],
    mkCase "ok/slice-vs-cell/true" #[intV 1, .slice sliceA, .cell cellB],
    mkCase "ok/slice-vs-cell/false" #[intV 0, .slice sliceA, .cell cellB],
    mkCase "ok/builder-empty-vs-tuple-empty/true" #[intV 1, .builder builderA, tupleEmpty],
    mkCase "ok/builder-empty-vs-tuple-empty/false" #[intV 0, .builder builderA, tupleEmpty],
    mkCase "ok/builder-nonempty-vs-slice/true" #[intV (-3), .builder builderB, .slice sliceB],
    mkCase "ok/builder-nonempty-vs-slice/false" #[intV 0, .builder builderB, .slice sliceB],
    mkCase "ok/cont-vs-int/true" #[intV 1, contQuit0, intV 5],
    mkCase "ok/cont-vs-int/false" #[intV 0, contQuit0, intV 5],

    mkCase "ok/deep/true/prefix-mixed" #[.null, .cell cellA, intV 1, intV 5, .slice sliceA],
    mkCase "ok/deep/false/prefix-mixed" #[.null, .cell cellA, intV 0, intV 5, .slice sliceA],
    mkCase "ok/deep/true/prefix-slice-builder" #[.slice sliceB, .builder builderA, intV (-1), .cell cellA, tupleEmpty],
    mkCase "ok/deep/false/prefix-tuple-cont" #[tupleEmpty, contQuit0, intV 0, .builder builderB, .null],

    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "underflow/one-non-int" #[.null],
    mkCase "underflow/two-ints" #[intV 1, intV 2],
    mkCase "underflow/two-mixed" #[.cell cellA, .null],

    mkCase "type/bool-null" #[.null, intV 1, intV 2],
    mkCase "type/bool-cell" #[.cell cellA, intV 1, intV 2],
    mkCase "type/bool-slice" #[.slice sliceA, intV 1, intV 2],
    mkCase "type/bool-builder-empty" #[.builder builderA, intV 1, intV 2],
    mkCase "type/bool-tuple-empty" #[tupleEmpty, intV 1, intV 2],
    mkCase "type/bool-cont-quit0" #[contQuit0, intV 1, intV 2],

    mkCase "intov/bool-nan-via-program" #[]
      #[.pushInt .nan, .pushInt (.num 17), .pushInt (.num 23), condSelInstr],
    mkCase "intov/bool-nan-via-program-prefix" #[.null, .cell cellA]
      #[.pushInt .nan, .pushInt (.num 17), .pushInt (.num 23), condSelInstr]
  ]
  fuzz := #[
    { seed := 2026021106
      count := 450
      gen := genCondSelFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.CONDSEL
