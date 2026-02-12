import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CALLXVARARGS

private def callxVarArgsId : InstrId := { name := "CALLXVARARGS" }

private def callxVarArgsInstr : Instr := .callxVarArgs

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def fullSliceA : Slice := Slice.ofCell cellA

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[callxVarArgsInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callxVarArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def progSetNumCallxVarArgs (nargs params retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num nargs), .setNumVarArgs,
    .pushInt (.num params), .pushInt (.num retVals), callxVarArgsInstr]

private def progSetContVarCallxVarArgs (copy more params retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num copy), .pushInt (.num more), .setContVarArgs,
    .pushInt (.num params), .pushInt (.num retVals), callxVarArgsInstr]

private def callxVarArgsFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/basic/",
      "ok/call/",
      "err/underflow/",
      "err/bounds/",
      "err/call/",
      "err/order/",
      "err/type/",
      "err/rangemap/"
    ]
    -- Bias toward argument/order perturbations while still covering all mutation families.
    mutationModes := #[0, 0, 0, 0, 2, 2, 2, 4, 4, 1, 1, 3]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def callxVarArgsParamPool : Array Int := #[-1, 0, 1, 2, 3, 254]
private def callxVarArgsRetPool : Array Int := #[-1, 0, 1, 254]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def mkOkStack (params retVals : Int) : Array Value :=
  let need : Nat :=
    if params < 0 then
      3
    else
      params.toNat + 1
  let below := intStackAsc need
  below ++ #[q0, intV params, intV retVals]

private def genCallxVarArgsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (params, rng2) := pickFromPool callxVarArgsParamPool rng1
  let (retVals, rng3) := pickFromPool callxVarArgsRetPool rng2
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/basic" (mkOkStack params retVals)
    else if shape = 1 then
      mkCase "fuzz/ok/order/tail-skipped" #[intV 11, q0, intV 1, intV 0]
        #[callxVarArgsInstr, .pushInt (.num 999)]
    else if shape = 2 then
      mkCase "fuzz/err/underflow/empty" #[]
    else if shape = 3 then
      mkCase "fuzz/err/underflow/need-after-pop" #[q0, intV 1, intV 0]
    else if shape = 4 then
      mkCase "fuzz/err/bounds/params-255" #[q0, intV 255, intV 0]
    else if shape = 5 then
      mkCase "fuzz/err/bounds/retvals-255" #[q0, intV 0, intV 255]
    else if shape = 6 then
      mkCase "fuzz/err/type/retvals-null" #[q0, intV 0, .null]
    else if shape = 7 then
      mkCase "fuzz/err/order/params-range-before-cont-type" #[.null, intV 255, intV 0]
    else if shape = 8 then
      mkCase "fuzz/err/rangemap/params-nan" #[]
        #[.pushCtr 0, .pushInt .nan, .pushInt (.num 0), callxVarArgsInstr]
    else if shape = 9 then
      mkCase "fuzz/ok/call/setnum-nargs1" #[intV 9] (progSetNumCallxVarArgs 1 1 0)
    else
      mkCase "fuzz/err/call/setnum-nargs2" #[intV 9] (progSetNumCallxVarArgs 2 0 0)
  let (tag, rng4) := randNat rng3 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

def suite : InstrSuite where
  id := callxVarArgsId
  unit := #[]
  oracle := #[
    -- Success: direct CALLXVARARGS with default `quit(0)` continuation.
    mkCase "ok/basic/empty-pass-all-ret-all"
      #[q0, intV (-1), intV (-1)],
    mkCase "ok/basic/empty-pass0-ret0"
      #[q0, intV 0, intV 0],
    mkCase "ok/basic/empty-pass0-ret254"
      #[q0, intV 0, intV 254],
    mkCase "ok/basic/one-arg-pass1-ret0"
      #[intV 7, q0, intV 1, intV 0],
    mkCase "ok/basic/two-args-pass1-ret0"
      #[intV 7, intV 8, q0, intV 1, intV 0],
    mkCase "ok/basic/two-args-pass2-ret1"
      #[intV 7, intV 8, q0, intV 2, intV 1],
    mkCase "ok/basic/three-args-pass-all-ret0"
      #[intV 1, intV 2, intV 3, q0, intV (-1), intV 0],
    mkCase "ok/basic/three-args-pass0-ret-all"
      #[intV 1, intV 2, intV 3, q0, intV 0, intV (-1)],
    mkCase "ok/basic/four-args-pass3-ret254"
      #[intV 1, intV 2, intV 3, intV 4, q0, intV 3, intV 254],
    mkCase "ok/basic/mixed-values-pass2-ret0"
      #[.null, .cell cellA, .builder Builder.empty, q0, intV 2, intV 0],
    mkCase "ok/basic/mixed-values-pass-all-ret1"
      #[.slice fullSliceA, .tuple #[], intV 9, q0, intV (-1), intV 1],
    mkCase "ok/basic/trailing-push-skipped"
      #[intV 11, q0, intV 1, intV 0]
      #[callxVarArgsInstr, .pushInt (.num 999)],

    -- Underflow and bounds.
    mkCase "err/underflow/empty"
      #[],
    mkCase "err/underflow/one-item"
      #[q0],
    mkCase "err/underflow/two-items"
      #[q0, intV 0],
    mkCase "err/bounds/retvals-low"
      #[q0, intV 0, intV (-2)],
    mkCase "err/bounds/retvals-high"
      #[q0, intV 0, intV 255],
    mkCase "err/bounds/params-low"
      #[q0, intV (-2), intV 0],
    mkCase "err/bounds/params-high"
      #[q0, intV 255, intV 0],
    mkCase "err/call/pass1-no-args"
      #[q0, intV 1, intV 0],
    mkCase "err/call/pass2-one-arg"
      #[intV 7, q0, intV 2, intV 0],
    mkCase "err/call/pass254-no-args"
      #[q0, intV 254, intV 0],

    -- Error order around range/type checks.
    mkCase "err/order/retvals-range-before-params-type"
      #[.null, .null, intV 255],
    mkCase "err/order/params-range-before-cont-type"
      #[.null, intV 255, intV 0],
    mkCase "err/order/params-type-before-cont-type"
      #[.null, .null, intV 0],

    -- Type mapping on each operand position.
    mkCase "err/type/retvals-null"
      #[q0, intV 0, .null],
    mkCase "err/type/retvals-cell"
      #[q0, intV 0, .cell cellA],
    mkCase "err/type/retvals-slice"
      #[q0, intV 0, .slice fullSliceA],
    mkCase "err/type/retvals-builder"
      #[q0, intV 0, .builder Builder.empty],
    mkCase "err/type/retvals-tuple"
      #[q0, intV 0, .tuple #[]],
    mkCase "err/type/retvals-cont"
      #[q0, intV 0, q0],
    mkCase "err/type/params-null"
      #[q0, .null, intV 0],
    mkCase "err/type/params-cell"
      #[q0, .cell cellA, intV 0],
    mkCase "err/type/params-slice"
      #[q0, .slice fullSliceA, intV 0],
    mkCase "err/type/params-builder"
      #[q0, .builder Builder.empty, intV 0],
    mkCase "err/type/cont-null"
      #[.null, intV 0, intV 0],
    mkCase "err/type/cont-cell"
      #[.cell cellA, intV 0, intV 0],
    mkCase "err/type/cont-slice"
      #[.slice fullSliceA, intV 0, intV 0],
    mkCase "err/type/cont-builder"
      #[.builder Builder.empty, intV 0, intV 0],
    mkCase "err/type/cont-tuple"
      #[.tuple #[], intV 0, intV 0],

    -- NaN mapping parity: C++ `pop_smallint_range` reports `range_chk`.
    mkCase "err/rangemap/retvals-nan-rangechk"
      #[]
      #[.pushCtr 0, .pushInt (.num 0), .pushInt .nan, callxVarArgsInstr],
    mkCase "err/rangemap/params-nan-rangechk"
      #[]
      #[.pushCtr 0, .pushInt .nan, .pushInt (.num 0), callxVarArgsInstr],
    mkCase "err/order/retvals-nan-before-params-range"
      #[]
      #[.pushCtr 0, .pushInt (.num 255), .pushInt .nan, callxVarArgsInstr],
    mkCase "err/order/params-nan-before-cont-type"
      #[.null]
      #[.pushInt .nan, .pushInt (.num 0), callxVarArgsInstr],

    -- Call behavior through constructed continuations (nargs/captured stack paths).
    mkCase "ok/call/setnum/nargs1-pass1"
      #[intV 9]
      (progSetNumCallxVarArgs 1 1 0),
    mkCase "err/call/setnum/nargs1-pass0"
      #[intV 9]
      (progSetNumCallxVarArgs 1 0 0),
    mkCase "ok/call/setnum/nargs2-pass2"
      #[intV 1, intV 2]
      (progSetNumCallxVarArgs 2 2 0),
    mkCase "err/call/setnum/nargs2-pass1"
      #[intV 1, intV 2]
      (progSetNumCallxVarArgs 2 1 0),
    mkCase "ok/call/setcont/copy1-more1-pass1"
      #[intV 10, intV 20]
      (progSetContVarCallxVarArgs 1 1 1 0),
    mkCase "err/call/setcont/copy1-more2-pass1"
      #[intV 10, intV 20]
      (progSetContVarCallxVarArgs 1 2 1 0),
    mkCase "ok/call/setcont/copy1-more-neg1-pass0"
      #[intV 10]
      (progSetContVarCallxVarArgs 1 (-1) 0 0),
    mkCase "ok/call/setcont/copy1-more-neg1-pass-all"
      #[intV 10, intV 11]
      (progSetContVarCallxVarArgs 1 (-1) (-1) 0)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr callxVarArgsId
      count := 500
      gen := genCallxVarArgsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.CALLXVARARGS
