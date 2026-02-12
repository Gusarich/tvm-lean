import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.PUSHCTRX

private def pushCtrXId : InstrId := { name := "PUSHCTRX" }

private def intV (n : Int) : Value := .int (.num n)

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

private def withIdx (stackPrefix : Array Value) (idx : Int) : Array Value :=
  stackPrefix.push (intV idx)

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr) : OracleCase :=
  { name := name
    instr := pushCtrXId
    program := program
    initStack := stack }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell) : OracleCase :=
  { name := name
    instr := pushCtrXId
    codeCell? := some codeCell
    initStack := stack }

private def progPushX (tail : Array Instr := #[]) : Array Instr :=
  #[.contExt .pushCtrX] ++ tail

private def pushCtrXOracleFamilies : Array String :=
  #[
    "ok/index/",
    "err/index/",
    "ok/raw-opcode/",
    "err/raw-opcode/",
    "err/type/",
    "err/order/",
    "ok/edge/",
    "err/edge/",
    "err/underflow/"
  ]

private def pushCtrXFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := pushCtrXOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := pushCtrXId
  unit := #[]
  oracle := #[
    -- Stack-index decode matrix (valid supported indices).
    mkCase "ok/index/idx0/empty" (withIdx #[] 0) (progPushX),
    mkCase "ok/index/idx1/empty" (withIdx #[] 1) (progPushX),
    mkCase "ok/index/idx2/empty" (withIdx #[] 2) (progPushX),
    mkCase "ok/index/idx3/empty" (withIdx #[] 3) (progPushX),
    mkCase "ok/index/idx4/empty" (withIdx #[] 4) (progPushX),
    mkCase "ok/index/idx5/empty" (withIdx #[] 5) (progPushX),
    mkCase "ok/index/idx7/empty" (withIdx #[] 7) (progPushX),
    mkCase "ok/index/idx0/noise-a" (withIdx noiseA 0) (progPushX),
    mkCase "ok/index/idx1/noise-b" (withIdx noiseB 1) (progPushX),
    mkCase "ok/index/idx4/noise-int" (withIdx #[intV 11] 4) (progPushX),
    mkCase "ok/index/idx5/noise-cell-slice" (withIdx #[.cell cellA, .slice fullSliceA] 5) (progPushX),
    mkCase "ok/index/idx7/noise-builder-tuple" (withIdx #[.builder Builder.empty, .tuple #[]] 7) (progPushX),

    -- Stack-index range/type rejection.
    mkCase "err/index/hole-6-empty" (withIdx #[] 6) (progPushX),
    mkCase "err/index/hole-6-noise" (withIdx noiseA 6) (progPushX),
    mkCase "err/index/outside-8" (withIdx #[] 8) (progPushX),
    mkCase "err/index/outside-16" (withIdx #[] 16) (progPushX),
    mkCase "err/index/outside-17" (withIdx #[] 17) (progPushX),
    mkCase "err/index/negative-minus1" (withIdx #[] (-1)) (progPushX),
    mkCase "err/index/type-null" #[.null] (progPushX),
    mkCase "err/index/type-cell" #[.cell cellA] (progPushX),
    mkCase "err/index/type-slice" #[.slice fullSliceA] (progPushX),
    mkCase "err/index/type-builder" #[.builder Builder.empty] (progPushX),
    mkCase "err/index/type-tuple-empty" #[.tuple #[]] (progPushX),
    mkCase "err/index/type-nan" #[] #[.pushInt .nan, .contExt .pushCtrX],

    -- Raw opcode coverage for decode boundaries.
    mkRawCase "ok/raw-opcode/ede0-idx0" (withIdx #[] 0) (rawOp16 0xede0),
    mkRawCase "ok/raw-opcode/ede0-idx5-noise" (withIdx noiseA 5) (rawOp16 0xede0),
    mkRawCase "ok/raw-opcode/ede0-idx7-noise" (withIdx noiseB 7) (rawOp16 0xede0),
    mkRawCase "err/raw-opcode/ede0-underflow" #[] (rawOp16 0xede0),
    mkRawCase "err/raw-opcode/prefix-near-eddf" (withIdx #[] 0) (rawOp16 0xeddf),
    mkRawCase "err/raw-opcode/prefix-near-ede5" (withIdx #[] 0) (rawOp16 0xede5),
    mkRawCase "err/raw-opcode/missing-tail-ede3" (withIdx #[] 0) (rawOp16 0xede3),

    -- Type/order probes via follow-up operations.
    mkCase "err/type/add/from-c4-with-below-int" (withIdx #[intV 21] 4) (progPushX #[.add]),
    mkCase "err/type/add/from-c7-with-below-int" (withIdx #[intV 22] 7) (progPushX #[.add]),
    mkCase "err/type/execute/from-c4" (withIdx #[] 4) (progPushX #[.execute]),
    mkCase "err/type/execute/from-c5" (withIdx #[] 5) (progPushX #[.execute]),
    mkCase "err/type/execute/from-c7" (withIdx #[] 7) (progPushX #[.execute]),
    mkCase "err/type/popctr0/from-c4" (withIdx #[] 4) (progPushX #[.popCtr 0]),
    mkCase "err/type/popctr4/from-c0" (withIdx #[] 0) (progPushX #[.popCtr 4]),
    mkCase "err/order/top-first-popctr4/from-c0-with-below-cell"
      (withIdx #[.cell cellB] 0) (progPushX #[.popCtr 4]),

    -- Edge continuation behavior and stack-order roundtrips.
    mkCase "ok/edge/popctr0-roundtrip" (withIdx #[intV 9] 0) (progPushX #[.popCtr 0]),
    mkCase "ok/edge/popctr4-roundtrip" (withIdx #[] 4) (progPushX #[.popCtr 4]),
    mkCase "ok/edge/popctr5-roundtrip" (withIdx #[] 5) (progPushX #[.popCtr 5]),
    mkCase "ok/edge/popctr7-roundtrip" (withIdx #[.null] 7) (progPushX #[.popCtr 7]),
    mkCase "ok/edge/execute-c0" (withIdx #[] 0) (progPushX #[.execute]),
    mkCase "ok/edge/execute-c1" (withIdx #[] 1) (progPushX #[.execute]),
    mkCase "ok/edge/execute-c3" (withIdx #[] 3) (progPushX #[.execute]),
    mkCase "ok/edge/execute-c2-with-arg" (withIdx #[intV 17] 2) (progPushX #[.execute]),
    mkCase "err/edge/execute-c2-no-arg" (withIdx #[] 2) (progPushX #[.execute]),
    mkCase "err/underflow/after-roundtrip-add-empty" (withIdx #[] 0) (progPushX #[.popCtr 0, .add]),
    mkCase "err/underflow/after-roundtrip-add-one-int" (withIdx #[intV 1] 0) (progPushX #[.popCtr 0, .add]),
    mkCase "ok/edge/after-roundtrip-add-two-ints" (withIdx #[intV 2, intV 3] 0) (progPushX #[.popCtr 0, .add])
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile pushCtrXId pushCtrXFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.PUSHCTRX
