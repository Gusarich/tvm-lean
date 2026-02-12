import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.POPCTRX

private def popCtrXId : InstrId := { name := "POPCTRX" }

private def popCtrXInstr : Instr := .contExt .popCtrX

private def dispatchSentinel : Int := 49081

private def intV (n : Int) : Value := .int (.num n)

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def fullSliceA : Slice := Slice.ofCell cellA

private def fullSliceB : Slice := Slice.ofCell cellB

private def noiseA : Array Value :=
  #[.null, intV 7]

private def noiseB : Array Value :=
  #[.cell cellA, .slice fullSliceB, .builder Builder.empty]

private def withValueIdx (stackPrefix : Array Value) (v : Value) (idx : Int) : Array Value :=
  stackPrefix ++ #[v, intV idx]

private def withValueTop (stackPrefix : Array Value) (v top : Value) : Array Value :=
  stackPrefix ++ #[v, top]

private def progPopX (tail : Array Instr := #[]) : Array Instr :=
  #[popCtrXInstr] ++ tail

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr) : OracleCase :=
  { name := name
    instr := popCtrXId
    program := program
    initStack := stack }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell) : OracleCase :=
  { name := name
    instr := popCtrXId
    codeCell? := some codeCell
    initStack := stack }

private def runPopCtrXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt popCtrXInstr stack

private def runPopCtrXFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runPopCtrXRaw
    (stack : Array Value)
    (instr : Instr := popCtrXInstr) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContChangeExt instr (pure ())).run st0

private def expectRawErr
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (res, st) := out
  match res with
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def popCtrXOracleFamilies : Array String :=
  #[
    "ok/index/",
    "ok/roundtrip/",
    "err/type-probe/",
    "err/value-type/",
    "err/index-validity/",
    "err/index-pop/",
    "ok/raw-opcode/",
    "err/raw-opcode/"
  ]

private def popCtrXFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := popCtrXOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def fuzzValidIdxPool : Array Int := #[0, 1, 2, 3, 4, 5, 7]

private def fuzzInvalidIdxPool : Array Int := #[6, 8, 16, -1]

private def fuzzNoisePool : Array (Array Value) := #[#[], noiseA, noiseB]

private def valueForIdx (idx : Int) : Value :=
  if idx ≤ 3 then q0
  else if idx = 4 then .cell cellA
  else if idx = 5 then .cell cellB
  else .tuple #[]

private def badValueForIdx (idx : Int) : Array Value :=
  if idx ≤ 3 then #[intV 11, .cell cellA, .null]
  else if idx = 4 then #[intV 12, .builder Builder.empty, q0]
  else if idx = 5 then #[.null, q0, .builder Builder.empty]
  else #[intV 13, .cell cellA, q0, .slice fullSliceA]

private def genPopCtrXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let (idx, rng2) := pickFromPool fuzzValidIdxPool rng1
  let (badIdx, rng3) := pickFromPool fuzzInvalidIdxPool rng2
  let (noise, rng4) := pickFromPool fuzzNoisePool rng3
  let okValue := valueForIdx idx
  let (case0, rngTag) :=
    if shape = 0 then
      (mkCase s!"fuzz/ok/index/idx{idx}" (withValueIdx noise okValue idx) (progPopX), rng4)
    else if shape = 1 then
      (mkCase s!"fuzz/ok/roundtrip/idx{idx}"
        (withValueIdx #[] okValue idx) (progPopX #[.pushCtr (Int.toNat idx), .popCtr (Int.toNat idx)]), rng4)
    else if shape = 2 then
      let (badV, rng5) := pickFromPool (badValueForIdx idx) rng4
      (mkCase s!"fuzz/err/value-type/idx{idx}" (withValueIdx #[] badV idx) (progPopX), rng5)
    else if shape = 3 then
      (mkCase s!"fuzz/err/index/range-{badIdx}" (withValueIdx #[] okValue badIdx) (progPopX), rng4)
    else if shape = 4 then
      let (badTop, rng5) := pickFromPool
        #[.null, .cell cellA, .slice fullSliceA, .builder Builder.empty, .tuple #[]] rng4
      (mkCase "fuzz/err/index/type" (withValueTop #[] okValue badTop) (progPopX), rng5)
    else if shape = 5 then
      let (underflowStack, rng5) := pickFromPool #[#[], #[q0]] rng4
      (mkCase "fuzz/err/underflow/entry" underflowStack (progPopX), rng5)
    else if shape = 6 then
      let (rawCode, rng5) := pickFromPool #[rawOp16 0xede1] rng4
      (mkRawCase "fuzz/ok/raw-opcode" (withValueIdx noise okValue idx) rawCode, rng5)
    else if shape = 7 then
      let (rawCode, rng5) := pickFromPool #[rawOp16 0xeddf, rawOp16 0xede5, rawOp16 0xede3] rng4
      (mkRawCase "fuzz/err/raw-opcode" (withValueIdx #[] okValue idx) rawCode, rng5)
    else
      (mkCase "fuzz/err/type-probe/add-after-set-c4"
        (withValueIdx #[intV 21] (.cell cellA) 4) (progPopX #[.pushCtr 4, .add]), rng4)
  let (tag, rng5) := randNat rngTag 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

private def oracleCases : Array OracleCase := #[
  -- Valid index/type matrix.
  mkCase "ok/index/idx0-cont-q0" (withValueIdx #[] q0 0) (progPopX),
  mkCase "ok/index/idx1-cont-q0-push" (withValueIdx #[] q0 1) (progPopX #[.pushCtr 1]),
  mkCase "ok/index/idx2-cont-q0-push" (withValueIdx #[] q0 2) (progPopX #[.pushCtr 2]),
  mkCase "ok/index/idx3-cont-q0-push" (withValueIdx #[] q0 3) (progPopX #[.pushCtr 3]),
  mkCase "ok/index/idx4-cellA-push" (withValueIdx #[] (.cell cellA) 4) (progPopX #[.pushCtr 4]),
  mkCase "ok/index/idx5-cellB-push" (withValueIdx #[] (.cell cellB) 5) (progPopX #[.pushCtr 5]),
  mkCase "ok/index/idx7-tuple-empty-push" (withValueIdx #[] (.tuple #[]) 7) (progPopX #[.pushCtr 7]),
  mkCase "ok/index/idx1-noise-a" (withValueIdx noiseA q0 1) (progPopX),
  mkCase "ok/index/idx4-noise-b" (withValueIdx noiseB (.cell cellA) 4) (progPopX),
  mkCase "ok/index/idx7-noise-a" (withValueIdx noiseA (.tuple #[]) 7) (progPopX),

  -- Valid-path roundtrips and follow-up probes.
  mkCase "ok/roundtrip/idx4-push-popctr5"
    (withValueIdx #[] (.cell cellB) 4) (progPopX #[.pushCtr 4, .popCtr 5]),
  mkCase "ok/roundtrip/idx7-push-popctr7"
    (withValueIdx #[] (.tuple #[]) 7) (progPopX #[.pushCtr 7, .popCtr 7]),
  mkCase "err/type-probe/add-after-set-c4"
    (withValueIdx #[intV 21] (.cell cellA) 4) (progPopX #[.pushCtr 4, .add]),
  mkCase "err/type-probe/popctr4-after-set-c1"
    (withValueIdx #[] q0 1) (progPopX #[.pushCtr 1, .popCtr 4]),
  mkCase "err/type-probe/execute-after-set-c4"
    (withValueIdx #[] (.cell cellA) 4) (progPopX #[.pushCtr 4, .execute]),

  -- Valid index but invalid value type.
  mkCase "err/value-type/idx0-int" (withValueIdx #[] (intV 11) 0) (progPopX),
  mkCase "err/value-type/idx1-cell" (withValueIdx #[] (.cell cellA) 1) (progPopX),
  mkCase "err/value-type/idx2-null" (withValueIdx #[] .null 2) (progPopX),
  mkCase "err/value-type/idx3-tuple-empty" (withValueIdx #[] (.tuple #[]) 3) (progPopX),
  mkCase "err/value-type/idx4-int" (withValueIdx #[] (intV 12) 4) (progPopX),
  mkCase "err/value-type/idx4-builder" (withValueIdx #[] (.builder Builder.empty) 4) (progPopX),
  mkCase "err/value-type/idx5-cont" (withValueIdx #[] q0 5) (progPopX),
  mkCase "err/value-type/idx5-null" (withValueIdx #[] .null 5) (progPopX),
  mkCase "err/value-type/idx7-int" (withValueIdx #[] (intV 13) 7) (progPopX),
  mkCase "err/value-type/idx7-cell" (withValueIdx #[] (.cell cellA) 7) (progPopX),
  mkCase "err/value-type/idx7-cont" (withValueIdx #[] q0 7) (progPopX),
  mkCase "err/value-type/idx7-slice" (withValueIdx #[] (.slice fullSliceA) 7) (progPopX),

  -- Index validity check (after successful `popNatUpTo 16`).
  mkCase "err/index-validity/hole-6-int-value" (withValueIdx #[] (intV 30) 6) (progPopX),
  mkCase "err/index-validity/hole-6-cell-value" (withValueIdx #[] (.cell cellA) 6) (progPopX),
  mkCase "err/index-validity/outside-8" (withValueIdx #[] (intV 31) 8) (progPopX),
  mkCase "err/index-validity/outside-16" (withValueIdx #[] (intV 32) 16) (progPopX),
  mkCase "err/index-validity/outside-16-noise" (withValueIdx noiseA (intV 33) 16) (progPopX),
  mkCase "err/index-validity/outside-8-noise" (withValueIdx noiseB (.cell cellB) 8) (progPopX),

  -- Index pop (type/range/underflow) coverage.
  mkCase "err/index-pop/underflow-empty" #[] (progPopX),
  mkCase "err/index-pop/underflow-one" #[q0] (progPopX),
  mkCase "err/index-pop/type-null" (withValueTop #[] q0 .null) (progPopX),
  mkCase "err/index-pop/type-cell" (withValueTop #[] q0 (.cell cellA)) (progPopX),
  mkCase "err/index-pop/type-slice" (withValueTop #[] q0 (.slice fullSliceA)) (progPopX),
  mkCase "err/index-pop/type-builder" (withValueTop #[] q0 (.builder Builder.empty)) (progPopX),
  mkCase "err/index-pop/type-tuple-empty" (withValueTop #[] q0 (.tuple #[])) (progPopX),
  mkCase "err/index-pop/type-cont-quit0" (withValueTop #[] q0 q0) (progPopX),
  mkCase "err/index-pop/range-minus1" (withValueIdx #[] q0 (-1)) (progPopX),
  mkCase "err/index-pop/range-17" (withValueIdx #[] q0 17) (progPopX),
  mkCase "err/index-pop/range-nan-via-program"
    #[q0] #[.pushInt .nan, popCtrXInstr],
  mkCase "err/index-pop/range-nan-via-program-noise"
    #[intV 9, q0] #[.pushInt .nan, popCtrXInstr],

  -- Raw opcode coverage and nearby decode boundaries.
  mkRawCase "ok/raw-opcode/ede1-valid-idx4" (withValueIdx #[] (.cell cellA) 4) (rawOp16 0xede1),
  mkRawCase "err/raw-opcode/ede1-underflow" #[] (rawOp16 0xede1),
  mkRawCase "err/raw-opcode/prefix-near-eddf" (withValueIdx #[] q0 1) (rawOp16 0xeddf),
  mkRawCase "err/raw-opcode/prefix-near-ede5" (withValueIdx #[] q0 1) (rawOp16 0xede5),
  mkRawCase "err/raw-opcode/missing-tail-ede3" (withValueIdx #[] q0 1) (rawOp16 0xede3),
  mkRawCase "err/raw-opcode/prefix-ede2-setcontctrx-underflow"
    (withValueIdx #[] q0 1) (rawOp16 0xede2)
]

def suite : InstrSuite where
  id := popCtrXId
  unit := #[
    { name := "unit/dispatch/popctrx-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-next-only"
          (runPopCtrXFallback .add (withValueIdx #[] q0 1))
          #[q0, intV 1, intV dispatchSentinel]
        expectErr "dispatch/matched-popctrx"
          (runPopCtrXDirect (withValueIdx #[] q0 6))
          .rangeChk }
    ,
    { name := "unit/order/underflow-before-index-pop"
      run := do
        let st ← expectRawErr "underflow-before-index-pop" (runPopCtrXRaw #[intV 6]) .stkUnd
        if st.stack != #[intV 6] then
          throw (IO.userError s!"underflow-before-index-pop: expected stack #[6], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/idx-invalid-before-value-pop"
      run := do
        let st ← expectRawErr "idx-invalid-before-value-pop"
          (runPopCtrXRaw (withValueIdx #[intV 55] (intV 777) 6)) .rangeChk
        if st.stack != #[intV 55, intV 777] then
          throw (IO.userError
            s!"idx-invalid-before-value-pop: expected #[55,777], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/idx-type-error-pops-only-index"
      run := do
        let st ← expectRawErr "idx-type-error-pops-only-index"
          (runPopCtrXRaw (withValueTop #[intV 55] (intV 777) .null)) .typeChk
        if st.stack != #[intV 55, intV 777] then
          throw (IO.userError
            s!"idx-type-error-pops-only-index: expected #[55,777], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/valid-idx-type-error-pops-value"
      run := do
        let st ← expectRawErr "valid-idx-type-error-pops-value"
          (runPopCtrXRaw (withValueIdx #[intV 55] (intV 777) 4)) .typeChk
        if st.stack != #[intV 55] then
          throw (IO.userError
            s!"valid-idx-type-error-pops-value: expected #[55], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr popCtrXId
      count := 500
      gen := genPopCtrXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.POPCTRX
