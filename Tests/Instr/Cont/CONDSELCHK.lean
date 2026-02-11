import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CONDSELCHK

/-
CONDSELCHK branch-mapping notes (Lean + C++ reference):
- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Cont/CondSel.lean` (`.contExt .condSelChk` branch)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_condsel_chk`, opcode `0xe305`).

Branch map used for this suite:
- Shared handler dispatch:
  - `.contExt .condSel` path,
  - `.contExt .condSelChk` path,
  - fallback `next` passthrough.
- CONDSELCHK path (after alignment to C++):
  - `checkUnderflow 3` first (must raise `stkUnd` before any type checks/pops);
  - pop order is `y` (top), then `x`, then `bool`;
  - type gate compares runtime tags of `x` and `y` only;
  - bool decode happens strictly after successful type equality;
  - selection is `x` on true, `y` on false.

Key risk areas covered here:
- underflow vs type-check precedence for 0/1/2-element stacks;
- mixed-type rejection before bool pop (including bool=`NaN` to prove ordering);
- bool decoding errors after same-type validation (`intOv` for NaN, `typeChk` for non-int);
- deep-stack stability and true/false selection with all TVM value kinds.
-/

private def condSelChkId : InstrId := { name := "CONDSELCHK" }

private def condSelChkInstr : Instr :=
  .contExt .condSelChk

private def condSelInstr : Instr :=
  .contExt .condSel

private def dispatchSentinel : Int := 7007

private def boolTrue : Value := intV (-1)
private def boolTruePos : Value := intV 5
private def boolFalse : Value := intV 0
private def boolNaN : Value := .int .nan

private def cellA : Cell := Cell.mkOrdinary (natToBits 0xa 4) #[]
private def cellB : Cell := Cell.mkOrdinary (natToBits 0x15 5) #[]

private def sliceA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x2d 6) #[cellA])

private def sliceB : Slice :=
  { cell := Cell.mkOrdinary (natToBits 0x1b 7) #[cellB]
    bitPos := 1
    refPos := 0 }

private def builderA : Builder :=
  { bits := natToBits 0x5 3
    refs := #[] }

private def builderB : Builder :=
  { bits := natToBits 0x12 5
    refs := #[cellA] }

private def intX : Value := intV 11
private def intY : Value := intV (-22)

private def cellX : Value := .cell cellA
private def cellY : Value := .cell cellB

private def sliceX : Value := .slice sliceA
private def sliceY : Value := .slice sliceB

private def builderX : Value := .builder builderA
private def builderY : Value := .builder builderB

private def tupleX : Value := .tuple #[intV 1, .null]
private def tupleY : Value := .tuple #[.cell cellA, intV 2]

private def contX : Value := .cont (.quit 0)
private def contY : Value := .cont (.quit 17)

private def nullX : Value := .null
private def nullY : Value := .null

private def noiseA : Value := .null
private def noiseB : Value := intV 404
private def noiseC : Value := .tuple #[intV (-3)]
private def sliceYOracle : Value := .slice (Slice.ofCell cellB)
private def tupleOracle : Value := .tuple #[]
private def contYOracle : Value := .cont (.quit 0)

private def mkCondSelChkInput (b x y : Value) (below : Array Value := #[]) : Array Value :=
  below ++ #[b, x, y]

private def mkCondSelChkExpected (selected : Value) (below : Array Value := #[]) : Array Value :=
  below.push selected

private def mkCondSelChkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[condSelChkInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := condSelChkId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runCondSelChkDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContCondSel condSelChkInstr stack

private def runCondSelDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContCondSel condSelInstr stack

private def runCondSelChkDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContCondSel instr (VM.push (intV dispatchSentinel)) stack

private def condSelChkSetGasExact : Int :=
  computeExactGasBudget condSelChkInstr

private def condSelChkSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne condSelChkInstr

private structure TypedPair where
  tag : String
  x : Value
  y : Value
  deriving Inhabited

private structure MixedPair where
  tag : String
  x : Value
  y : Value
  deriving Inhabited

private def typedPairs : Array TypedPair :=
  #[
    { tag := "int", x := intX, y := intY },
    { tag := "cell", x := cellX, y := cellY },
    { tag := "slice", x := sliceX, y := sliceY },
    { tag := "builder", x := builderX, y := builderY },
    { tag := "tuple", x := tupleX, y := tupleY },
    { tag := "cont", x := contX, y := contY },
    { tag := "null", x := nullX, y := nullY }
  ]

private def mixedPairs : Array MixedPair :=
  #[
    { tag := "int-cell", x := intX, y := cellX },
    { tag := "cell-slice", x := cellX, y := sliceX },
    { tag := "tuple-cont", x := tupleX, y := contX },
    { tag := "builder-null", x := builderX, y := nullX },
    { tag := "slice-int", x := sliceY, y := intY }
  ]

private def noisePool : Array Value :=
  #[noiseA, noiseB, noiseC, .cell cellA, .cont (.quit 9)]

private def pickTypedPair (rng : StdGen) : TypedPair × StdGen :=
  let (idx, rng') := randNat rng 0 (typedPairs.size - 1)
  (typedPairs[idx]!, rng')

private def pickMixedPair (rng : StdGen) : MixedPair × StdGen :=
  let (idx, rng') := randNat rng 0 (mixedPairs.size - 1)
  (mixedPairs[idx]!, rng')

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (idx, rng') := randNat rng 0 (noisePool.size - 1)
  (noisePool[idx]!, rng')

private def genCondSelChkFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (tp, rng2) := pickTypedPair rng1
    (mkCondSelChkCase s!"fuzz/ok/{tp.tag}/true" (mkCondSelChkInput boolTrue tp.x tp.y), rng2)
  else if shape = 1 then
    let (tp, rng2) := pickTypedPair rng1
    (mkCondSelChkCase s!"fuzz/ok/{tp.tag}/false" (mkCondSelChkInput boolFalse tp.x tp.y), rng2)
  else if shape = 2 then
    let (tp, rng2) := pickTypedPair rng1
    let (noise, rng3) := pickNoise rng2
    (mkCondSelChkCase s!"fuzz/ok/{tp.tag}/deep-true" (mkCondSelChkInput boolTruePos tp.x tp.y #[noise]), rng3)
  else if shape = 3 then
    let (mp, rng2) := pickMixedPair rng1
    (mkCondSelChkCase s!"fuzz/type/{mp.tag}/mismatch" (mkCondSelChkInput boolTrue mp.x mp.y), rng2)
  else if shape = 4 then
    let (mp, rng2) := pickMixedPair rng1
    (mkCondSelChkCase s!"fuzz/type-order/{mp.tag}/before-bool-type-cell" (mkCondSelChkInput (.cell cellA) mp.x mp.y), rng2)
  else if shape = 5 then
    let (tp, rng2) := pickTypedPair rng1
    (mkCondSelChkCase s!"fuzz/bool/type-cell/{tp.tag}" (mkCondSelChkInput (.cell cellA) tp.x tp.y), rng2)
  else if shape = 6 then
    let (tp, rng2) := pickTypedPair rng1
    (mkCondSelChkCase s!"fuzz/bool/type/{tp.tag}" (mkCondSelChkInput .null tp.x tp.y), rng2)
  else if shape = 7 then
    (mkCondSelChkCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 8 then
    let (tp, rng2) := pickTypedPair rng1
    (mkCondSelChkCase s!"fuzz/underflow/one/{tp.tag}" #[tp.y], rng2)
  else if shape = 9 then
    let (mp, rng2) := pickMixedPair rng1
    (mkCondSelChkCase s!"fuzz/underflow/two-mixed/{mp.tag}" #[mp.x, mp.y], rng2)
  else if shape = 10 then
    let (tp, rng2) := pickTypedPair rng1
    let (n1, rng3) := pickNoise rng2
    let (n2, rng4) := pickNoise rng3
    (mkCondSelChkCase s!"fuzz/ok/{tp.tag}/deep-false" (mkCondSelChkInput boolFalse tp.x tp.y #[n1, n2]), rng4)
  else
    let (mp, rng2) := pickMixedPair rng1
    let (noise, rng3) := pickNoise rng2
    (mkCondSelChkCase s!"fuzz/type/{mp.tag}/deep-mismatch" (mkCondSelChkInput boolFalse mp.x mp.y #[noise]), rng3)

def suite : InstrSuite where
  id := condSelChkId
  unit := #[
    { name := "unit/same-type-success-selection"
      run := do
        for tp in typedPairs do
          expectOkStack s!"ok/{tp.tag}/true"
            (runCondSelChkDirect (mkCondSelChkInput boolTrue tp.x tp.y))
            (mkCondSelChkExpected tp.x)
          expectOkStack s!"ok/{tp.tag}/false"
            (runCondSelChkDirect (mkCondSelChkInput boolFalse tp.x tp.y))
            (mkCondSelChkExpected tp.y)
          expectOkStack s!"ok/{tp.tag}/positive-true"
            (runCondSelChkDirect (mkCondSelChkInput boolTruePos tp.x tp.y))
            (mkCondSelChkExpected tp.x) }
    ,
    { name := "unit/type-equality-and-bool-pop-order"
      run := do
        for mp in mixedPairs do
          expectErr s!"type/{mp.tag}/true"
            (runCondSelChkDirect (mkCondSelChkInput boolTrue mp.x mp.y)) .typeChk
          expectErr s!"type/{mp.tag}/false"
            (runCondSelChkDirect (mkCondSelChkInput boolFalse mp.x mp.y)) .typeChk
          expectErr s!"order/{mp.tag}/mismatch-before-bool-nan"
            (runCondSelChkDirect (mkCondSelChkInput boolNaN mp.x mp.y)) .typeChk
          expectErr s!"order/{mp.tag}/mismatch-before-bool-type"
            (runCondSelChkDirect (mkCondSelChkInput (.cell cellA) mp.x mp.y)) .typeChk }
    ,
    { name := "unit/underflow-ordering"
      run := do
        expectErr "underflow/empty"
          (runCondSelChkDirect #[]) .stkUnd
        expectErr "underflow/one-int"
          (runCondSelChkDirect #[intX]) .stkUnd
        expectErr "underflow/one-cell"
          (runCondSelChkDirect #[cellX]) .stkUnd
        expectErr "underflow/two-same-type"
          (runCondSelChkDirect #[intX, intY]) .stkUnd
        expectErr "underflow/two-mixed-int-cell"
          (runCondSelChkDirect #[intX, cellX]) .stkUnd
        expectErr "underflow/two-mixed-cell-int"
          (runCondSelChkDirect #[cellX, intX]) .stkUnd
        expectErr "underflow/two-mixed-tuple-cont"
          (runCondSelChkDirect #[tupleX, contX]) .stkUnd }
    ,
    { name := "unit/bool-errors-after-type-pass-and-deep-stack"
      run := do
        expectErr "bool/intov/nan-after-same-type-int"
          (runCondSelChkDirect (mkCondSelChkInput boolNaN intX intY)) .intOv
        expectErr "bool/intov/nan-after-same-type-cell"
          (runCondSelChkDirect (mkCondSelChkInput boolNaN cellX cellY)) .intOv
        expectErr "bool/type/null-after-same-type-int"
          (runCondSelChkDirect (mkCondSelChkInput .null intX intY)) .typeChk
        expectErr "bool/type/cell-after-same-type-tuple"
          (runCondSelChkDirect (mkCondSelChkInput (.cell cellA) tupleX tupleY)) .typeChk

        expectOkStack "deep/select-x"
          (runCondSelChkDirect (mkCondSelChkInput boolTrue intX intY #[noiseA, noiseB]))
          (mkCondSelChkExpected intX #[noiseA, noiseB])
        expectOkStack "deep/select-y"
          (runCondSelChkDirect (mkCondSelChkInput boolFalse cellX cellY #[noiseC]))
          (mkCondSelChkExpected cellY #[noiseC]) }
    ,
    { name := "unit/dispatch-and-shared-handler-branches"
      run := do
        expectOkStack "dispatch/non-cont-fallback"
          (runCondSelChkDispatchFallback .add #[])
          #[intV dispatchSentinel]
        expectOkStack "dispatch/other-cont-fallback"
          (runCondSelChkDispatchFallback .boolAnd #[])
          #[intV dispatchSentinel]

        expectOkStack "shared-handler/condsel-true"
          (runCondSelDirect (mkCondSelChkInput boolTrue intX intY))
          (mkCondSelChkExpected intX)
        expectOkStack "shared-handler/condsel-false"
          (runCondSelDirect (mkCondSelChkInput boolFalse intX intY #[noiseA]))
          (mkCondSelChkExpected intY #[noiseA]) }
  ]
  oracle := #[
    mkCondSelChkCase "ok/int/true" (mkCondSelChkInput boolTrue intX intY),
    mkCondSelChkCase "ok/int/false" (mkCondSelChkInput boolFalse intX intY),
    mkCondSelChkCase "ok/int/positive-true" (mkCondSelChkInput boolTruePos intX intY),

    mkCondSelChkCase "ok/cell/true" (mkCondSelChkInput boolTrue cellX cellY),
    mkCondSelChkCase "ok/cell/false" (mkCondSelChkInput boolFalse cellX cellY),

    mkCondSelChkCase "ok/slice/true" (mkCondSelChkInput boolTrue sliceX sliceYOracle),
    mkCondSelChkCase "ok/slice/false" (mkCondSelChkInput boolFalse sliceX sliceYOracle),

    mkCondSelChkCase "ok/builder/true" (mkCondSelChkInput boolTrue builderX builderY),
    mkCondSelChkCase "ok/builder/false" (mkCondSelChkInput boolFalse builderX builderY),

    mkCondSelChkCase "ok/tuple/true" (mkCondSelChkInput boolTrue tupleOracle tupleOracle),
    mkCondSelChkCase "ok/tuple/false" (mkCondSelChkInput boolFalse tupleOracle tupleOracle),

    mkCondSelChkCase "ok/cont/true" (mkCondSelChkInput boolTrue contX contYOracle),
    mkCondSelChkCase "ok/cont/false" (mkCondSelChkInput boolFalse contX contYOracle),

    mkCondSelChkCase "ok/null/true" (mkCondSelChkInput boolTrue nullX nullY),
    mkCondSelChkCase "ok/null/false" (mkCondSelChkInput boolFalse nullX nullY),

    mkCondSelChkCase "ok/deep/int/true" (mkCondSelChkInput boolTrue intX intY #[noiseA, noiseB]),
    mkCondSelChkCase "ok/deep/int/false" (mkCondSelChkInput boolFalse intX intY #[noiseA, noiseB]),
    mkCondSelChkCase "ok/deep/cell/false" (mkCondSelChkInput boolFalse cellX cellY #[noiseA]),
    mkCondSelChkCase "ok/deep/tuple/true" (mkCondSelChkInput boolTrue tupleOracle tupleOracle #[noiseB, noiseA]),

    mkCondSelChkCase "type/mismatch/int-cell" (mkCondSelChkInput boolTrue intX cellX),
    mkCondSelChkCase "type/mismatch/cell-slice" (mkCondSelChkInput boolFalse cellX sliceX),
    mkCondSelChkCase "type/mismatch/tuple-cont" (mkCondSelChkInput boolTrue tupleOracle contX),
    mkCondSelChkCase "type/mismatch/builder-null" (mkCondSelChkInput boolFalse builderX nullX),

    mkCondSelChkCase "type/order/mismatch-before-bool-type" (mkCondSelChkInput (.cell cellA) tupleOracle contX),

    mkCondSelChkCase "underflow/empty" #[],
    mkCondSelChkCase "underflow/one-item" #[intX],
    mkCondSelChkCase "underflow/two-items-same-type" #[intX, intY],
    mkCondSelChkCase "underflow/two-items-mixed-int-cell" #[intX, cellX],
    mkCondSelChkCase "underflow/two-items-mixed-cell-int" #[cellX, intX],

    mkCondSelChkCase "bool/type/null-after-same-type-int" (mkCondSelChkInput .null intX intY),
    mkCondSelChkCase "bool/type/cell-after-same-type-tuple" (mkCondSelChkInput (.cell cellA) tupleOracle tupleOracle),

    mkCondSelChkCase "gas/exact-cost-succeeds"
      (mkCondSelChkInput boolTrue intX intY)
      #[.pushInt (.num condSelChkSetGasExact), .tonEnvOp .setGasLimit, condSelChkInstr],
    mkCondSelChkCase "gas/exact-minus-one-out-of-gas"
      (mkCondSelChkInput boolTrue intX intY)
      #[.pushInt (.num condSelChkSetGasExactMinusOne), .tonEnvOp .setGasLimit, condSelChkInstr]
  ]
  fuzz := #[ mkReplayOracleFuzzSpec condSelChkId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.CONDSELCHK
