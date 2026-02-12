import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.POPCTR

private def popCtrId : InstrId := { name := "POPCTR" }
private def popCtrInstr (idx : Nat) : Instr := .popCtr idx

private def dispatchSentinel : Int := 49080

private def intV (n : Int) : Value := .int (.num n)

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2c 8) #[cellA]

private def fullSliceA : Slice := Slice.ofCell cellA

private def tupleEmpty : Value := .tuple #[]

private def noiseA : Array Value :=
  #[.null, intV 7]

private def noiseB : Array Value :=
  #[.cell cellA, .slice fullSliceA, .builder Builder.empty]

private def withValue (stackPrefix : Array Value) (v : Value) : Array Value :=
  stackPrefix.push v

private def progPop (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[popCtrInstr idx] ++ tail

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def popCtrTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits (0xed50 >>> 8) 8) #[]

private def popCtrTruncated15 : Cell :=
  Cell.mkOrdinary (natToBits (0xed50 >>> 1) 15) #[]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr) : OracleCase :=
  { name := name
    instr := popCtrId
    program := program
    initStack := stack }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell) : OracleCase :=
  { name := name
    instr := popCtrId
    codeCell? := some codeCell
    initStack := stack }

private def runPopCtrDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContPopCtr (popCtrInstr idx) stack

private def runPopCtrFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContPopCtr instr (VM.push (intV dispatchSentinel)) stack

private def runPopCtrRaw (stack : Array Value) (idx : Nat) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContPopCtr (popCtrInstr idx) (pure ())).run st0

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

private def popCtrOracleFamilies : Array String :=
  #[
    "ok/index/",
    "ok/roundtrip/",
    "err/type-probe/",
    "err/value-type/",
    "err/underflow/",
    "err/order/",
    "ok/raw-opcode/",
    "err/raw-opcode/"
  ]

private def popCtrFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := popCtrOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def fuzzValidIdxPool : Array Nat := #[0, 1, 2, 3, 4, 5, 7]

private def fuzzNoisePool : Array (Array Value) := #[#[], noiseA, noiseB]

private def valueForIdx (idx : Nat) : Value :=
  if idx ≤ 3 then q0
  else if idx = 4 then .cell cellA
  else if idx = 5 then .cell cellB
  else .tuple #[]

private def badValueForIdx (idx : Nat) : Array Value :=
  if idx ≤ 3 then #[intV 11, .cell cellA, .null]
  else if idx = 4 then #[intV 12, .builder Builder.empty, q0]
  else if idx = 5 then #[.null, q0, .builder Builder.empty]
  else #[intV 14, .cell cellA, q0, .slice fullSliceA]

private def genPopCtrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  let (idx, rng2) := pickFromPool fuzzValidIdxPool rng1
  let (noise, rng3) := pickFromPool fuzzNoisePool rng2
  let okValue := valueForIdx idx
  let (case0, rngTag) :=
    if shape = 0 then
      (mkCase s!"fuzz/ok/index/idx{idx}" (withValue noise okValue) (progPop idx #[.pushCtr idx]), rng3)
    else if shape = 1 then
      (mkCase s!"fuzz/ok/roundtrip/idx{idx}" (withValue #[] okValue) (progPop idx #[.pushCtr idx]), rng3)
    else if shape = 2 then
      let (badV, rng4) := pickFromPool (badValueForIdx idx) rng3
      (mkCase s!"fuzz/err/value-type/idx{idx}" (withValue #[] badV) (progPop idx), rng4)
    else if shape = 3 then
      let (underflowStack, rng4) := pickFromPool #[#[], #[intV 1]] rng3
      (mkCase "fuzz/err/underflow/empty-or-one" underflowStack (progPop idx), rng4)
    else if shape = 4 then
      (mkCase "fuzz/err/order/type-after-pop"
        (withValue #[intV 55] q0) (progPop 4), rng3)
    else if shape = 5 then
      let (rawCode, rng4) := pickFromPool #[rawOp16 0xed50, rawOp16 0xed55, rawOp16 0xed57] rng3
      (mkRawCase "fuzz/ok/raw-opcode" (withValue noise okValue) rawCode, rng4)
    else if shape = 6 then
      let (rawCode, rng4) := pickFromPool
        #[rawOp16 0xed56, rawOp16 0xed4f, rawOp16 0xed58, popCtrTruncated8, popCtrTruncated15] rng3
      (mkRawCase "fuzz/err/raw-opcode" (withValue #[] okValue) rawCode, rng4)
    else
      (mkCase "fuzz/err/value-type/idx7-slice"
        (withValue #[] (.slice fullSliceA)) (progPop 7), rng3)
  let (tag, rng4) := randNat rngTag 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

private def oracleCases : Array OracleCase := #[
  -- Success matrix over valid static indices and value classes.
  mkCase "ok/index/idx0-cont-q0" (withValue #[] q0) (progPop 0 #[.pushCtr 0]),
  mkCase "ok/index/idx1-cont-q0" (withValue #[] q0) (progPop 1 #[.pushCtr 1]),
  mkCase "ok/index/idx2-cont-q0" (withValue #[] q0) (progPop 2 #[.pushCtr 2]),
  mkCase "ok/index/idx3-cont-q0" (withValue #[] q0) (progPop 3 #[.pushCtr 3]),
  mkCase "ok/index/idx4-cellA" (withValue #[] (.cell cellA)) (progPop 4 #[.pushCtr 4]),
  mkCase "ok/index/idx5-cellB" (withValue #[] (.cell cellB)) (progPop 5 #[.pushCtr 5]),
  mkCase "ok/index/idx7-tuple-empty" (withValue #[] tupleEmpty) (progPop 7 #[.pushCtr 7]),
  mkCase "ok/index/idx0-noise-a" (withValue noiseA q0) (progPop 0 #[.pushCtr 0]),
  mkCase "ok/index/idx1-noise-b" (withValue noiseB q0) (progPop 1 #[.pushCtr 1]),
  mkCase "ok/index/idx4-noise-b" (withValue noiseB (.cell cellA)) (progPop 4 #[.pushCtr 4]),
  mkCase "ok/index/idx5-noise-a" (withValue noiseA (.cell cellB)) (progPop 5 #[.pushCtr 5]),
  mkCase "ok/index/idx7-noise-a" (withValue noiseA tupleEmpty) (progPop 7 #[.pushCtr 7]),

  -- Successful cross-register follow-up probes.
  mkCase "ok/roundtrip/idx4-push-popctr5"
    (withValue #[] (.cell cellB)) (progPop 4 #[.pushCtr 4, .popCtr 5, .pushCtr 5]),
  mkCase "ok/roundtrip/idx5-push-popctr4"
    (withValue #[] (.cell cellA)) (progPop 5 #[.pushCtr 5, .popCtr 4, .pushCtr 4]),
  mkCase "ok/roundtrip/idx7-push-popctr7"
    (withValue #[] tupleEmpty) (progPop 7 #[.pushCtr 7, .popCtr 7, .pushCtr 7]),
  mkCase "ok/roundtrip/idx2-push-popctr0"
    (withValue #[] q0) (progPop 2 #[.pushCtr 2, .popCtr 0, .pushCtr 0]),

  -- Type probes after successful set.
  mkCase "err/type-probe/add-after-set-c4"
    (withValue #[intV 21] (.cell cellA)) (progPop 4 #[.pushCtr 4, .add]),
  mkCase "err/type-probe/execute-after-set-c4"
    (withValue #[] (.cell cellA)) (progPop 4 #[.pushCtr 4, .execute]),
  mkCase "err/type-probe/popctr4-after-set-c1"
    (withValue #[] q0) (progPop 1 #[.pushCtr 1, .popCtr 4]),
  mkCase "err/type-probe/popctr0-after-set-c4"
    (withValue #[] (.cell cellA)) (progPop 4 #[.pushCtr 4, .popCtr 0]),

  -- Invalid value type mapping per index class.
  mkCase "err/value-type/idx0-int" (withValue #[] (intV 11)) (progPop 0),
  mkCase "err/value-type/idx0-cell" (withValue #[] (.cell cellA)) (progPop 0),
  mkCase "err/value-type/idx1-cell" (withValue #[] (.cell cellA)) (progPop 1),
  mkCase "err/value-type/idx1-null" (withValue #[] .null) (progPop 1),
  mkCase "err/value-type/idx2-int" (withValue #[] (intV 12)) (progPop 2),
  mkCase "err/value-type/idx2-tuple" (withValue #[] tupleEmpty) (progPop 2),
  mkCase "err/value-type/idx3-cell" (withValue #[] (.cell cellA)) (progPop 3),
  mkCase "err/value-type/idx3-null" (withValue #[] .null) (progPop 3),
  mkCase "err/value-type/idx4-int" (withValue #[] (intV 13)) (progPop 4),
  mkCase "err/value-type/idx4-builder" (withValue #[] (.builder Builder.empty)) (progPop 4),
  mkCase "err/value-type/idx4-cont" (withValue #[] q0) (progPop 4),
  mkCase "err/value-type/idx5-cont" (withValue #[] q0) (progPop 5),
  mkCase "err/value-type/idx5-null" (withValue #[] .null) (progPop 5),
  mkCase "err/value-type/idx5-builder" (withValue #[] (.builder Builder.empty)) (progPop 5),
  mkCase "err/value-type/idx7-int" (withValue #[] (intV 14)) (progPop 7),
  mkCase "err/value-type/idx7-cell" (withValue #[] (.cell cellA)) (progPop 7),
  mkCase "err/value-type/idx7-cont" (withValue #[] q0) (progPop 7),
  mkCase "err/value-type/idx7-slice" (withValue #[] (.slice fullSliceA)) (progPop 7),
  mkCase "err/value-type/idx7-null" (withValue #[] .null) (progPop 7),
  mkCase "err/value-type/idx7-builder" (withValue #[] (.builder Builder.empty)) (progPop 7),

  -- Error precedence probes on stack effects.
  mkCase "err/underflow/empty" #[] (progPop 4),
  mkCase "err/order/type-after-pop-idx4-noise"
    (withValue #[intV 55] q0) (progPop 4),
  mkCase "err/order/type-after-pop-idx0-noise"
    (withValue #[intV 56] (.cell cellA)) (progPop 0),

  -- Raw opcode coverage and decode boundaries around ed50 family.
  mkRawCase "ok/raw-opcode/ed50-idx0" (withValue #[] q0) (rawOp16 0xed50),
  mkRawCase "ok/raw-opcode/ed55-idx5" (withValue noiseA (.cell cellB)) (rawOp16 0xed55),
  mkRawCase "ok/raw-opcode/ed57-idx7" (withValue noiseB tupleEmpty) (rawOp16 0xed57),
  mkRawCase "err/raw-opcode/ed50-underflow" #[] (rawOp16 0xed50),
  mkRawCase "err/raw-opcode/hole-ed56" (withValue #[] q0) (rawOp16 0xed56),
  mkRawCase "err/raw-opcode/prefix-near-ed4f" (withValue #[] q0) (rawOp16 0xed4f),
  mkRawCase "err/raw-opcode/prefix-near-ed58" (withValue #[] q0) (rawOp16 0xed58),
  mkRawCase "err/raw-opcode/prefix-near-ed60" (withValue #[] q0) (rawOp16 0xed60),
  mkRawCase "err/raw-opcode/truncated8" (withValue #[] q0) popCtrTruncated8,
  mkRawCase "err/raw-opcode/truncated15" (withValue #[] q0) popCtrTruncated15
]

def suite : InstrSuite where
  id := popCtrId
  unit := #[
    { name := "unit/dispatch/popctr-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-next-only"
          (runPopCtrFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-popctr"
          (runPopCtrFallback (popCtrInstr 0) #[q0])
          #[] }
    ,
    { name := "unit/order/underflow-before-set"
      run := do
        let st ← expectRawErr "underflow-before-set" (runPopCtrRaw #[] 6) .stkUnd
        if !st.stack.isEmpty then
          throw (IO.userError s!"underflow-before-set: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/invalid-idx-pops-before-error"
      run := do
        let st ← expectRawErr "invalid-idx-pops-before-error"
          (runPopCtrRaw #[intV 55, q0] 6) .typeChk
        if st.stack != #[intV 55] then
          throw (IO.userError
            s!"invalid-idx-pops-before-error: expected #[55], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/valid-idx-type-error-pops-value"
      run := do
        let st ← expectRawErr "valid-idx-type-error-pops-value"
          (runPopCtrRaw #[intV 56, q0] 4) .typeChk
        if st.stack != #[intV 56] then
          throw (IO.userError
            s!"valid-idx-type-error-pops-value: expected #[56], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/mapping/invalid-idx-maps-typeChk"
      run :=
        expectErr "invalid-idx-maps-typeChk"
          (runPopCtrDirect 6 #[q0])
          .typeChk }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr popCtrId
      count := 500
      gen := genPopCtrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.POPCTR
