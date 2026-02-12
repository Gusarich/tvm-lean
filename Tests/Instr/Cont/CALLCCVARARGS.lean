import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.CALLCCVARARGS

private def callccVarArgsId : InstrId := { name := "CALLCCVARARGS" }

private def callccVarArgsInstr : Instr := .callccVarArgs

private def dispatchSentinel : Int := 43123

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell := Cell.ofUInt 8 0xa5

private def fullSliceA : Slice := Slice.ofCell cellA

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def mkStack (below : Array Value) (params retVals : Int) (cont : Value := q0) : Array Value :=
  below ++ #[cont, intV params, intV retVals]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[callccVarArgsInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := callccVarArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowCallcc callccVarArgsInstr stack

private def runFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowCallcc instr (VM.push (intV dispatchSentinel)) stack

private def progSetNumCallccVarArgs (nargs params retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num nargs), .setNumVarArgs, .pushInt (.num params), .pushInt (.num retVals), callccVarArgsInstr]

private def progSetContVarCallccVarArgs (copy more params retVals : Int) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num copy), .pushInt (.num more), .setContVarArgs,
    .pushInt (.num params), .pushInt (.num retVals), callccVarArgsInstr]

private def callccVarArgsFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/basic/",
      "ok/order/",
      "err/underflow/",
      "err/range/",
      "err/type/",
      "err/order/",
      "err/rangemap/",
      "ok/jump/",
      "err/jump/"
    ]
    -- Bias toward argument/order perturbations while still covering all mutation families.
    mutationModes := #[0, 0, 0, 0, 2, 2, 2, 4, 4, 1, 1, 3]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def callccVarArgsParamPool : Array Int := #[-1, 0, 1, 2, 3, 254]
private def callccVarArgsRetPool : Array Int := #[-1, 0, 1, 254]
private def callccVarArgsNoisePool : Array (Array Value) :=
  #[#[], #[intV 1], #[.null], #[.cell cellA], #[.slice fullSliceA], #[.builder Builder.empty]]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def mkOkStack (params : Int) (noise : Array Value) : Array Value :=
  let need : Nat :=
    if params < 0 then
      noise.size + 1
    else
      (params.toNat + 1)
  mkStack (intStackAsc need ++ noise) params 0

private def genCallccVarArgsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (params, rng2) := pickFromPool callccVarArgsParamPool rng1
  let (retVals, rng3) := pickFromPool callccVarArgsRetPool rng2
  let (noise, rng4) := pickFromPool callccVarArgsNoisePool rng3
  let okBelow :=
    if params < 0 then
      intStackAsc 3
    else
      intStackAsc (params.toNat + 1)
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/basic" (mkStack okBelow params retVals)
    else if shape = 1 then
      mkCase "fuzz/ok/order/mixed-stack" (mkOkStack params noise)
    else if shape = 2 then
      mkCase "fuzz/err/underflow/empty" #[]
    else if shape = 3 then
      mkCase "fuzz/err/underflow/need-after-pop" (mkStack #[] 2 0)
    else if shape = 4 then
      mkCase "fuzz/err/range/params-255" (mkStack #[] 255 0)
    else if shape = 5 then
      mkCase "fuzz/err/range/retvals-255" (mkStack #[] 0 255)
    else if shape = 6 then
      mkCase "fuzz/err/type/retvals-null" #[q0, intV 0, .null]
    else if shape = 7 then
      mkCase "fuzz/err/order/params-range-before-cont-type" #[.null, intV 255, intV 0]
    else if shape = 8 then
      mkCase "fuzz/err/rangemap/params-nan-rangechk"
        #[]
        #[.pushCtr 0, .pushInt .nan, .pushInt (.num 0), callccVarArgsInstr]
    else if shape = 9 then
      mkCase "fuzz/ok/jump/setnum-nargs1" #[intV 9] (progSetNumCallccVarArgs 1 1 0)
    else
      mkCase "fuzz/err/jump/setnum-nargs2" #[intV 9] (progSetNumCallccVarArgs 2 0 0)
  let (tag, rng5) := randNat rng4 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

private def oracleCases : Array OracleCase := #[
  -- Success: params/retvals bounds and extraction stack-copy paths.
  mkCase "ok/basic/pass-minus1-ret-minus1-empty" (mkStack #[] (-1) (-1)),
  mkCase "ok/basic/pass-minus1-ret0-empty" (mkStack #[] (-1) 0),
  mkCase "ok/basic/pass0-ret0-empty" (mkStack #[] 0 0),
  mkCase "ok/basic/pass0-ret254-empty" (mkStack #[] 0 254),
  mkCase "ok/basic/pass1-ret0-one-arg" (mkStack #[intV 7] 1 0),
  mkCase "ok/basic/pass1-ret1-two-args" (mkStack #[intV 7, intV 8] 1 1),
  mkCase "ok/basic/pass2-ret0-two-args" (mkStack #[intV 7, intV 8] 2 0),
  mkCase "ok/basic/pass2-ret254-three-args" (mkStack #[intV 1, intV 2, intV 3] 2 254),
  mkCase "ok/basic/pass-minus1-ret0-mixed" (mkStack #[.null, .cell cellA, .builder Builder.empty] (-1) 0),
  mkCase "ok/basic/pass0-ret-minus1-mixed" (mkStack #[.slice fullSliceA, .tuple #[], intV 9] 0 (-1)),
  mkCase "ok/basic/pass254-exact-depth" (mkStack (intStackAsc 254) 254 0),
  mkCase "ok/basic/pass254-drop-bottom" (mkStack (intStackAsc 255) 254 0),

  -- Jump behavior / control-flow ordering.
  mkCase "ok/order/tail-skipped-push" (mkStack #[] 0 0)
    #[callccVarArgsInstr, .pushInt (.num 77)],
  mkCase "ok/order/tail-skipped-add-underflow" (mkStack #[] 0 0)
    #[callccVarArgsInstr, .add],
  mkCase "ok/order/program-push-minus1" #[q0]
    #[.pushInt (.num (-1)), .pushInt (.num 0), callccVarArgsInstr],
  mkCase "ok/order/program-push-one" #[intV 5, q0]
    #[.pushInt (.num 1), .pushInt (.num 0), callccVarArgsInstr],
  mkCase "ok/order/program-push-zero" #[intV 5, q0]
    #[.pushInt (.num 0), .pushInt (.num 0), callccVarArgsInstr],
  mkCase "ok/order/pass2-preserves-top-order" (mkStack #[intV 1, intV 2, intV 3, intV 4] 2 0),
  mkCase "ok/order/pass2-mixed-types" (mkStack #[.cell cellA, .slice fullSliceA, .builder Builder.empty] 2 0),

  -- Error behavior: entry underflow, secondary underflow, bounds.
  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/one-item" #[q0],
  mkCase "err/underflow/two-items" #[q0, intV 0],
  mkCase "err/underflow/need-after-pop-1" (mkStack #[] 1 0),
  mkCase "err/underflow/need-after-pop-254" (mkStack #[] 254 0),
  mkCase "err/range/retvals-minus2" (mkStack #[] 0 (-2)),
  mkCase "err/range/retvals-255" (mkStack #[] 0 255),
  mkCase "err/range/params-minus2" (mkStack #[] (-2) 0),
  mkCase "err/range/params-255" (mkStack #[] 255 0),
  mkCase "err/range/retvals-max-int257" (mkStack #[] 0 maxInt257),
  mkCase "err/range/retvals-min-int257" (mkStack #[] 0 minInt257),
  mkCase "err/range/params-max-int257" (mkStack #[] maxInt257 0),
  mkCase "err/range/params-min-int257" (mkStack #[] minInt257 0),

  -- Type and ordering around stack operand positions.
  mkCase "err/type/retvals-null" #[q0, intV 0, .null],
  mkCase "err/type/retvals-cell" #[q0, intV 0, .cell cellA],
  mkCase "err/type/retvals-slice" #[q0, intV 0, .slice fullSliceA],
  mkCase "err/type/retvals-builder" #[q0, intV 0, .builder Builder.empty],
  mkCase "err/type/retvals-tuple" #[q0, intV 0, .tuple #[]],
  mkCase "err/type/retvals-cont" #[q0, intV 0, q0],
  mkCase "err/type/params-null" #[q0, .null, intV 0],
  mkCase "err/type/params-cell" #[q0, .cell cellA, intV 0],
  mkCase "err/type/params-slice" #[q0, .slice fullSliceA, intV 0],
  mkCase "err/type/params-builder" #[q0, .builder Builder.empty, intV 0],
  mkCase "err/type/cont-null" #[.null, intV 0, intV 0],
  mkCase "err/type/cont-cell" #[.cell cellA, intV 0, intV 0],
  mkCase "err/type/cont-slice" #[.slice fullSliceA, intV 0, intV 0],
  mkCase "err/type/cont-builder" #[.builder Builder.empty, intV 0, intV 0],
  mkCase "err/type/cont-tuple" #[.tuple #[], intV 0, intV 0],
  mkCase "err/order/retvals-range-before-params-type" #[.null, .null, intV 255],
  mkCase "err/order/params-range-before-cont-type" #[.null, intV 255, intV 0],
  mkCase "err/order/params-type-before-cont-type" #[.null, .null, intV 0],
  mkCase "err/order/underflow-before-cont-type" #[intV 8, intV 1, intV 0],
  mkCase "err/order/cont-type-after-need-check" #[intV 7, intV 8, intV 1, intV 0],

  -- NaN mapping parity with C++ `pop_smallint_range(254, -1)`.
  mkCase "err/rangemap/retvals-nan-rangechk"
    #[]
    #[.pushCtr 0, .pushInt (.num 0), .pushInt .nan, callccVarArgsInstr],
  mkCase "err/rangemap/params-nan-rangechk"
    #[]
    #[.pushCtr 0, .pushInt .nan, .pushInt (.num 0), callccVarArgsInstr],
  mkCase "err/order/retvals-nan-before-params-range"
    #[]
    #[.pushCtr 0, .pushInt (.num 255), .pushInt .nan, callccVarArgsInstr],
  mkCase "err/order/params-nan-before-cont-type"
    #[.null]
    #[.pushInt .nan, .pushInt (.num 0), callccVarArgsInstr],

  -- Delegation to full jump behavior through continuations created in-program.
  mkCase "ok/jump/setnum/nargs1-params1" #[intV 9] (progSetNumCallccVarArgs 1 1 0),
  mkCase "err/jump/setnum/nargs2-params0" #[intV 9] (progSetNumCallccVarArgs 2 0 0),
  mkCase "ok/jump/setnum/nargs2-params1" #[intV 9] (progSetNumCallccVarArgs 2 1 0),
  mkCase "ok/jump/setcont/copy1-more1-params1" #[intV 10, intV 20] (progSetContVarCallccVarArgs 1 1 1 0),
  mkCase "err/jump/setcont/copy1-more2-params1" #[intV 10, intV 20] (progSetContVarCallccVarArgs 1 2 1 0),
  mkCase "ok/jump/setcont/copy1-more-neg1-params0" #[intV 10] (progSetContVarCallccVarArgs 1 (-1) 0 0),
  mkCase "ok/jump/setcont/copy1-more-neg1-params-minus1" #[intV 10, intV 11]
    (progSetContVarCallccVarArgs 1 (-1) (-1) 0)
]

def suite : InstrSuite where
  id := callccVarArgsId
  unit := #[
    { name := "unit/direct/dispatch-fallback"
      run :=
        expectOkStack "direct/fallback"
          (runFallback .ret #[])
          #[intV dispatchSentinel] }
    ,
    { name := "unit/direct/nan-maps-to-rangeChk"
      run := do
        expectErr "direct/retvals-nan"
          (runDirect #[q0, intV 0, .int .nan])
          .rangeChk
        expectErr "direct/params-nan"
          (runDirect #[q0, .int .nan, intV 0])
          .rangeChk }
    ,
    { name := "unit/direct/order-underflow-before-cont-type"
      run :=
        expectErr "direct/underflow-before-type"
          (runDirect #[intV 8, intV 1, intV 0])
          .stkUnd }
    ,
    { name := "unit/direct/order-cont-type-after-need-check"
      run :=
        expectErr "direct/type-after-need"
          (runDirect #[intV 7, intV 8, intV 1, intV 0])
          .typeChk }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr callccVarArgsId
      count := 500
      gen := genCallccVarArgsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.CALLCCVARARGS
