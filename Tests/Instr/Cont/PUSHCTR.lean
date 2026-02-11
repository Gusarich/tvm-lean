import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.PUSHCTR

private def pushCtrId : InstrId := { name := "PUSHCTR" }

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

private def rawOp16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr) : OracleCase :=
  { name := name
    instr := pushCtrId
    program := program
    initStack := stack }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell) : OracleCase :=
  { name := name
    instr := pushCtrId
    codeCell? := some codeCell
    initStack := stack }

private def progPush (idx : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr idx] ++ tail

def suite : InstrSuite where
  id := pushCtrId
  unit := #[]
  oracle := #[
    -- Valid index decode paths (0..5,7) via normal assembler route.
    mkCase "ok/decode/idx0/empty" #[] (progPush 0),
    mkCase "ok/decode/idx1/empty" #[] (progPush 1),
    mkCase "ok/decode/idx2/empty" #[] (progPush 2),
    mkCase "ok/decode/idx3/empty" #[] (progPush 3),
    mkCase "ok/decode/idx4/empty" #[] (progPush 4),
    mkCase "ok/decode/idx5/empty" #[] (progPush 5),
    mkCase "ok/decode/idx7/empty" #[] (progPush 7),
    mkCase "ok/decode/idx0/noise-a" noiseA (progPush 0),
    mkCase "ok/decode/idx1/noise-b" noiseB (progPush 1),
    mkCase "ok/decode/idx4/noise-int" #[intV 11] (progPush 4),
    mkCase "ok/decode/idx5/noise-cell-slice" #[.cell cellA, .slice fullSliceA] (progPush 5),
    mkCase "ok/decode/idx7/noise-builder-tuple" #[.builder Builder.empty, .tuple #[]] (progPush 7),

    -- Raw opcode coverage for decode-hole and boundary behavior.
    mkRawCase "ok/raw-opcode/ed40-idx0" #[] (rawOp16 0xed40),
    mkRawCase "ok/raw-opcode/ed45-idx5" noiseA (rawOp16 0xed45),
    mkRawCase "ok/raw-opcode/ed47-idx7" noiseB (rawOp16 0xed47),
    mkRawCase "err/raw-opcode/hole-ed46-empty" #[] (rawOp16 0xed46),
    mkRawCase "err/raw-opcode/hole-ed46-noise" noiseA (rawOp16 0xed46),
    mkRawCase "err/raw-opcode/outside-ed48" #[] (rawOp16 0xed48),
    mkRawCase "err/raw-opcode/prefix-near-ed3f" #[] (rawOp16 0xed3f),

    -- Type/order probes via follow-up operations.
    mkCase "err/type/add/from-c4-with-below-int" #[intV 21] (progPush 4 #[.add]),
    mkCase "err/type/add/from-c7-with-below-int" #[intV 22] (progPush 7 #[.add]),
    mkCase "err/type/execute/from-c4" #[] (progPush 4 #[.execute]),
    mkCase "err/type/execute/from-c5" #[intV 5] (progPush 5 #[.execute]),
    mkCase "err/type/execute/from-c7" #[.null] (progPush 7 #[.execute]),
    mkCase "err/type/popctr0/from-c4" #[] (progPush 4 #[.popCtr 0]),
    mkCase "err/type/popctr4/from-c0" #[] (progPush 0 #[.popCtr 4]),
    mkCase "err/order/top-first-popctr4/from-c0-with-below-cell"
      #[.cell cellB] (progPush 0 #[.popCtr 4]),

    -- Edge continuation behavior and roundtrip interactions.
    mkCase "ok/edge/popctr0-roundtrip" #[intV 9] (progPush 0 #[.popCtr 0]),
    mkCase "ok/edge/popctr4-roundtrip" #[] (progPush 4 #[.popCtr 4]),
    mkCase "ok/edge/popctr5-roundtrip" #[] (progPush 5 #[.popCtr 5]),
    mkCase "ok/edge/popctr7-roundtrip" #[.null] (progPush 7 #[.popCtr 7]),
    mkCase "ok/edge/execute-c0" #[] (progPush 0 #[.execute]),
    mkCase "ok/edge/execute-c1" #[] (progPush 1 #[.execute]),
    mkCase "ok/edge/execute-c3" #[] (progPush 3 #[.execute]),
    mkCase "ok/edge/execute-c2-with-arg" #[intV 17] (progPush 2 #[.execute]),
    mkCase "err/edge/execute-c2-no-arg" #[] (progPush 2 #[.execute]),
    mkCase "err/underflow/after-roundtrip-add-empty" #[] (progPush 0 #[.popCtr 0, .add]),
    mkCase "err/underflow/after-roundtrip-add-one-int" #[intV 1] (progPush 0 #[.popCtr 0, .add]),
    mkCase "ok/edge/after-roundtrip-add-two-ints" #[intV 2, intV 3] (progPush 0 #[.popCtr 0, .add])
  ]
  fuzz := #[ mkReplayOracleFuzzSpec pushCtrId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.PUSHCTR
