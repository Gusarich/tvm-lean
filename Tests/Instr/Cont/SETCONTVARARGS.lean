import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETCONTVARARGS

private def setContVarArgsId : InstrId := { name := "SETCONTVARARGS" }

private def setContVarArgsInstr : Instr := .setContVarArgs

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def sliceA : Slice := Slice.ofCell cellA

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[setContVarArgsInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContVarArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def intStackAsc (n : Nat) : Array Value :=
  (Array.range n).map (fun i => intV (Int.ofNat i))

private def args254 : Array Value := intStackAsc 254

private def args255 : Array Value := intStackAsc 255

private def progSetThenJmp (tail : Array Instr := #[]) : Array Instr :=
  #[setContVarArgsInstr, .jmpx] ++ tail

private def progSetNumThenSetCont (nargs copy more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num nargs), .setNumVarArgs,
    .pushInt (.num copy), .pushInt (.num more), setContVarArgsInstr] ++ tail

private def progDoubleCaptureAppend : Array Instr :=
  #[.pushCtr 0, .pushInt (.num 1), .pushInt (.num (-1)), setContVarArgsInstr,
    .pushInt (.num 1), .pushInt (.num (-1)), setContVarArgsInstr,
    .jmpx]

private def setContVarArgsCopyPool : Array Int :=
  #[0, 1, 2, 3, 7, 31, 254, 255]

private def setContVarArgsMorePool : Array Int :=
  #[-1, 0, 1, 2, 7, 31, 254, 255]

private def setContVarArgsBadCopyPool : Array Int :=
  #[-1, 256, maxInt257, minInt257]

private def setContVarArgsBadMorePool : Array Int :=
  #[-2, 256, maxInt257, minInt257]

private def setContVarArgsTypePool : Array Value :=
  #[.null, .cell cellA, .slice sliceA, .builder Builder.empty, .tuple #[]]

private def setContVarArgsNoisePool : Array (Array Value) :=
  #[#[], #[intV 7], #[.null], #[.cell cellA], #[.slice sliceA], #[.builder Builder.empty], #[.tuple #[]]]

private def setContVarArgsJumpMorePool : Array Int :=
  #[-1, 0, 1, 2]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genSetContVarArgsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (copy, rng2) := pickFromPool setContVarArgsCopyPool rng1
  let (more, rng3) := pickFromPool setContVarArgsMorePool rng2
  let (badCopy, rng4) := pickFromPool setContVarArgsBadCopyPool rng3
  let (badMore, rng5) := pickFromPool setContVarArgsBadMorePool rng4
  let (ty, rng6) := pickFromPool setContVarArgsTypePool rng5
  let (noise, rng7) := pickFromPool setContVarArgsNoisePool rng6
  let (jumpMore, rng8) := pickFromPool setContVarArgsJumpMorePool rng7
  let (extraDepth, rng9) := randNat rng8 0 2
  let needCopy : Int := if copy = 0 then 1 else copy
  let jumpNeed : Nat := if jumpMore < 0 then 0 else jumpMore.toNat
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/direct/copy-more-random"
        (intStackAsc (copy.toNat + extraDepth) ++ #[q0, intV copy, intV more])
    else if shape = 1 then
      mkCase "fuzz/ok/direct/copy0-more-neg1-with-noise"
        (noise ++ #[q0, intV 0, intV (-1)])
    else if shape = 2 then
      mkCase "fuzz/err/underflow/empty" #[]
    else if shape = 3 then
      mkCase "fuzz/err/underflow/copy-requirement"
        (intStackAsc (needCopy.toNat - 1) ++ #[q0, intV needCopy, intV 0])
    else if shape = 4 then
      mkCase "fuzz/err/range/more-outside-smallint"
        #[q0, intV 0, intV badMore]
    else if shape = 5 then
      mkCase "fuzz/err/range/copy-outside-smallint"
        #[q0, intV badCopy, intV 0]
    else if shape = 6 then
      mkCase "fuzz/err/type/more-nonint"
        #[q0, intV 0, ty]
    else if shape = 7 then
      mkCase "fuzz/err/type/copy-nonint"
        #[q0, ty, intV 0]
    else if shape = 8 then
      mkCase "fuzz/err/type/cont-noncont"
        #[ty, intV 0, intV (-1)]
    else if shape = 9 then
      mkCase "fuzz/err/order/more-range-before-copy-type"
        #[q0, ty, intV 256]
    else if shape = 10 then
      mkCase "fuzz/err/order/more-type-before-copy-range"
        #[q0, intV 256, ty]
    else if shape = 11 then
      mkCase "fuzz/err/order/copy-range-before-cont-type"
        #[ty, intV 256, intV 0]
    else if shape = 12 then
      mkCase "fuzz/err/order/secondary-underflow-before-cont-type"
        #[ty, intV 2, intV 0]
    else if shape = 13 then
      mkCase "fuzz/err/rangemap/more-nan-rangechk" #[]
        #[.pushCtr 0, .pushInt (.num 0), .pushInt .nan, setContVarArgsInstr]
    else if shape = 14 then
      mkCase "fuzz/err/rangemap/copy-nan-rangechk" #[]
        #[.pushCtr 0, .pushInt .nan, .pushInt (.num 0), setContVarArgsInstr]
    else if shape = 15 then
      mkCase "fuzz/ok/jump/setthenjmp"
        (intStackAsc jumpNeed ++ #[q0, intV 0, intV jumpMore])
        (progSetThenJmp)
    else if shape = 16 then
      mkCase "fuzz/err/jump/underflow-after-jmp"
        #[q0, intV 0, intV 1]
        (progSetThenJmp)
    else if shape = 17 then
      mkCase "fuzz/ok/jump/setnum1-copy1"
        #[intV 9]
        (progSetNumThenSetCont 1 1 (-1) #[.jmpx])
    else if shape = 18 then
      mkCase "fuzz/err/stkov/setnum1-copy2"
        #[intV 9, intV 8]
        (progSetNumThenSetCont 1 2 0)
    else
      mkCase "fuzz/ok/order/jump-tail-skipped"
        #[q0, intV 0, intV (-1)]
        (progSetThenJmp #[.pushInt (.num 999)])
  let (tag, rng10) := randNat rng9 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng10)

def suite : InstrSuite where
  id := setContVarArgsId
  unit := #[]
  oracle := #[
    -- Direct success paths and copy/more boundaries.
    mkCase "ok/direct/copy0-more-neg1-keep-quit-empty"
      #[q0, intV 0, intV (-1)],
    mkCase "ok/direct/copy0-more-neg1-preserve-below"
      #[intV 7, q0, intV 0, intV (-1)],
    mkCase "ok/direct/copy0-more0-force-envelope"
      #[q0, intV 0, intV 0],
    mkCase "ok/direct/copy0-more255-force-envelope"
      #[q0, intV 0, intV 255],
    mkCase "ok/direct/copy1-more-neg1-capture-one"
      #[intV 7, q0, intV 1, intV (-1)],
    mkCase "ok/direct/copy2-more1-capture-two"
      #[intV 7, intV 8, q0, intV 2, intV 1],
    mkCase "ok/direct/copy255-more-neg1-exact-depth"
      (args255 ++ #[q0, intV 255, intV (-1)]),
    mkCase "ok/direct/copy255-more255-exact-depth"
      (args255 ++ #[q0, intV 255, intV 255]),

    -- Underflow and finite-range bounds.
    mkCase "err/underflow/empty"
      #[],
    mkCase "err/underflow/one-item"
      #[q0],
    mkCase "err/underflow/copy-plus-cont-requirement-2"
      #[q0, intV 1, intV 0],
    mkCase "err/underflow/copy-plus-cont-requirement-4"
      #[intV 7, q0, intV 3, intV 0],
    mkCase "err/range/more-low"
      #[q0, intV 0, intV (-2)],
    mkCase "err/range/more-high"
      #[q0, intV 0, intV 256],
    mkCase "err/range/more-max-int257"
      #[q0, intV 0, intV maxInt257],
    mkCase "err/range/more-min-int257"
      #[q0, intV 0, intV minInt257],
    mkCase "err/range/copy-low"
      #[q0, intV (-1), intV 0],
    mkCase "err/range/copy-high"
      #[q0, intV 256, intV 0],
    mkCase "err/range/copy-max-int257"
      #[q0, intV maxInt257, intV 0],
    mkCase "err/range/copy-min-int257"
      #[q0, intV minInt257, intV 0],
    mkCase "err/underflow/copy255-with-254-args"
      (args254 ++ #[q0, intV 255, intV (-1)]),

    -- Type checks on each operand position.
    mkCase "err/type/more-null"
      #[q0, intV 0, .null],
    mkCase "err/type/more-cell"
      #[q0, intV 0, .cell cellA],
    mkCase "err/type/more-slice"
      #[q0, intV 0, .slice sliceA],
    mkCase "err/type/more-builder"
      #[q0, intV 0, .builder Builder.empty],
    mkCase "err/type/more-tuple"
      #[q0, intV 0, .tuple #[]],
    mkCase "err/type/copy-null"
      #[q0, .null, intV 0],
    mkCase "err/type/copy-cell"
      #[q0, .cell cellA, intV 0],
    mkCase "err/type/copy-slice"
      #[q0, .slice sliceA, intV 0],
    mkCase "err/type/cont-null"
      #[.null, intV 0, intV (-1)],
    mkCase "err/type/cont-cell"
      #[.cell cellA, intV 0, intV 0],
    mkCase "err/type/cont-slice"
      #[.slice sliceA, intV 0, intV 0],
    mkCase "err/type/cont-builder"
      #[.builder Builder.empty, intV 0, intV 0],
    mkCase "err/type/cont-tuple"
      #[.tuple #[], intV 0, intV 0],

    -- Error-order checks around `more`, `copy`, and secondary underflow gate.
    mkCase "err/order/more-range-before-copy-type"
      #[q0, .null, intV 256],
    mkCase "err/order/more-type-before-copy-range"
      #[q0, intV 256, .null],
    mkCase "err/order/copy-range-before-cont-type"
      #[.null, intV 256, intV 0],
    mkCase "err/order/secondary-underflow-before-cont-type"
      #[.null, intV 2, intV 0],

    -- NaN parity with C++ `pop_smallint_range` (`range_chk`).
    mkCase "err/rangemap/more-nan-rangechk"
      #[]
      #[.pushCtr 0, .pushInt (.num 0), .pushInt .nan, setContVarArgsInstr],
    mkCase "err/rangemap/copy-nan-rangechk"
      #[]
      #[.pushCtr 0, .pushInt .nan, .pushInt (.num 0), setContVarArgsInstr],
    mkCase "err/order/more-nan-before-copy-range"
      #[]
      #[.pushCtr 0, .pushInt (.num 256), .pushInt .nan, setContVarArgsInstr],
    mkCase "err/order/copy-nan-before-cont-type"
      #[.null]
      #[.pushInt .nan, .pushInt (.num 0), setContVarArgsInstr],

    -- Observable copy/more semantics through jump to modified continuation.
    mkCase "ok/jump/copy0-more-neg1-empty"
      #[q0, intV 0, intV (-1)]
      (progSetThenJmp),
    mkCase "err/jump/copy0-more1-empty-underflow"
      #[q0, intV 0, intV 1]
      (progSetThenJmp),
    mkCase "ok/jump/copy0-more1-onearg"
      #[intV 5, q0, intV 0, intV 1]
      (progSetThenJmp),
    mkCase "ok/jump/copy1-more-neg1-captured-one"
      #[intV 6, q0, intV 1, intV (-1)]
      (progSetThenJmp),
    mkCase "ok/jump/copy2-more-neg1-order-preserved"
      #[intV 1, intV 2, q0, intV 2, intV (-1)]
      (progSetThenJmp),
    mkCase "ok/jump/double-capture-append-order"
      #[intV 10, intV 11]
      progDoubleCaptureAppend,
    mkCase "err/stkov/setnum1-copy2"
      #[intV 9, intV 8]
      (progSetNumThenSetCont 1 2 0),
    mkCase "ok/jump/setnum1-copy1-nargs-decrement"
      #[intV 9]
      (progSetNumThenSetCont 1 1 (-1) #[.jmpx]),
    mkCase "err/jump/setnum2-copy0-more1-sentinel"
      #[intV 7]
      (progSetNumThenSetCont 2 0 1 #[.jmpx]),
    mkCase "ok/order/jump-tail-skipped"
      #[q0, intV 0, intV (-1)]
      (progSetThenJmp #[.pushInt (.num 999)])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr setContVarArgsId
      count := 500
      gen := genSetContVarArgsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTVARARGS
