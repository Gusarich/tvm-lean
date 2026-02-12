import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.JMPXVARARGS

private def jmpxVarArgsId : InstrId := { name := "JMPXVARARGS" }
private def jmpxVarArgsInstr : Instr := .jmpxVarArgs

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def mkStack (below : Array Value) (params : Int) (cont : Value := q0) : Array Value :=
  below ++ #[cont, intV params]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[jmpxVarArgsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpxVarArgsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowJmpxVarArgs jmpxVarArgsInstr stack

private def jmpxVarArgsOracleFamilies : Array String :=
  #[
    "ok/pass-minus1/",
    "ok/pass0/",
    "ok/pass1/",
    "ok/pass2/",
    "ok/pass3/",
    "ok/pass254/",
    "order/",
    "err/underflow/",
    "err/type/",
    "err/range/",
    "err/order/"
  ]

private def jmpxVarArgsFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := jmpxVarArgsOracleFamilies
    -- Bias toward parameter/order perturbations while still covering all mutation families.
    mutationModes := #[
      0, 0, 0, 0,
      2, 2, 2,
      4, 4,
      1, 1,
      3
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success and pass-args behavior.
  mkCase "ok/pass-minus1/empty" (mkStack #[] (-1)),
  mkCase "ok/pass-minus1/one-int" (mkStack #[intV 7] (-1)),
  mkCase "ok/pass-minus1/mixed-keep-all"
    (mkStack #[.null, .cell cellA, .slice sliceA, .builder Builder.empty, .tuple #[]] (-1)),
  mkCase "ok/pass0/empty" (mkStack #[] 0),
  mkCase "ok/pass0/drop-one" (mkStack #[intV 7] 0),
  mkCase "ok/pass0/drop-mixed" (mkStack #[.null, .cell cellA, .slice sliceB] 0),
  mkCase "ok/pass1/exact-one" (mkStack #[intV 7] 1),
  mkCase "ok/pass1/keep-top-of-two" (mkStack #[intV 7, intV 8] 1),
  mkCase "ok/pass2/exact-two" (mkStack #[intV 7, intV 8] 2),
  mkCase "ok/pass2/drop-bottom-of-three" (mkStack #[intV 7, intV 8, intV 9] 2),
  mkCase "ok/pass3/keep-top-three-mixed"
    (mkStack #[intV 1, .null, .cell cellA, .slice sliceA] 3),
  mkCase "ok/pass254/exact-depth" (mkStack (intStackAsc 254) 254),
  mkCase "ok/pass254/drop-bottom" (mkStack (intStackAsc 255) 254),

  -- Jump ordering (tail must be skipped after jump) and program-supplied params.
  mkCase "order/tail-skipped-push"
    (mkStack #[] 0)
    #[jmpxVarArgsInstr, .pushInt (.num 77)],
  mkCase "order/tail-skipped-add-underflow"
    (mkStack #[] 0)
    #[jmpxVarArgsInstr, .add],
  mkCase "order/program-push-minus1"
    #[q0]
    #[.pushInt (.num (-1)), jmpxVarArgsInstr],
  mkCase "order/program-push-one"
    #[intV 5, q0]
    #[.pushInt (.num 1), jmpxVarArgsInstr],
  mkCase "order/program-push-zero"
    #[intV 5, q0]
    #[.pushInt (.num 0), jmpxVarArgsInstr],
  mkCase "order/pass2-preserves-top-order"
    (mkStack #[intV 1, intV 2, intV 3, intV 4] 2),
  mkCase "order/pass2-mixed-types"
    (mkStack #[.cell cellA, .slice sliceA, .builder Builder.empty] 2),

  -- Error behavior: underflow/type/range and error ordering.
  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/one-int" #[intV 1],
  mkCase "err/underflow/one-cont" #[q0],
  mkCase "err/underflow/need-after-pop-1" (mkStack #[] 1),
  mkCase "err/underflow/need-after-pop-254" (mkStack #[] 254),

  mkCase "err/type/params-null" #[q0, .null],
  mkCase "err/type/params-cell" #[q0, .cell cellA],
  mkCase "err/type/params-slice" #[q0, .slice sliceA],
  mkCase "err/type/params-builder" #[q0, .builder Builder.empty],
  mkCase "err/type/params-tuple" #[q0, .tuple #[]],
  mkCase "err/type/cont-after-need-pass1" #[intV 7, intV 8, intV 1],
  mkCase "err/type/cont-after-need-pass0" #[intV 8, intV 0],
  mkCase "err/type/cont-after-need-pass-minus1" #[intV 8, intV (-1)],

  mkCase "err/range/params-minus2" (mkStack #[] (-2)),
  mkCase "err/range/params-255" (mkStack #[] 255),
  mkCase "err/range/params-max-int257" (mkStack #[] maxInt257),
  mkCase "err/range/params-min-int257" (mkStack #[] minInt257),
  mkCase "err/range/params-nan-via-program"
    #[q0]
    #[.pushInt .nan, jmpxVarArgsInstr],

  mkCase "err/order/range-before-cont-type"
    #[.null]
    #[.pushInt (.num 255), jmpxVarArgsInstr],
  mkCase "err/order/underflow-before-cont-type" #[intV 8, intV 1]
]

def suite : InstrSuite where
  id := jmpxVarArgsId
  unit := #[
    { name := "unit/direct/nan-maps-to-rangeChk"
      run :=
        expectErr "direct/nan-range"
          (runDirect #[q0, .int .nan])
          .rangeChk }
    ,
    { name := "unit/direct/order-underflow-before-cont-type"
      run :=
        expectErr "direct/underflow-before-type"
          (runDirect #[intV 8, intV 1])
          .stkUnd }
    ,
    { name := "unit/direct/order-cont-type-after-need-check"
      run :=
        expectErr "direct/type-after-need"
          (runDirect #[intV 7, intV 8, intV 1])
          .typeChk }
    ,
    { name := "unit/direct/pass2-keeps-top-two"
      run :=
        expectOkStack "direct/pass2"
          (runDirect (mkStack #[intV 1, intV 2, intV 3] 2))
          #[intV 2, intV 3] }
    ,
    { name := "unit/direct/pass-minus1-keeps-all"
      run :=
        expectOkStack "direct/pass-minus1"
          (runDirect (mkStack #[.null, intV 7, .cell cellA] (-1)))
          #[.null, intV 7, .cell cellA] }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile jmpxVarArgsId jmpxVarArgsFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.JMPXVARARGS
