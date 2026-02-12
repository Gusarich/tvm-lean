import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.BLESSVARARGS

private def blessVarArgsId : InstrId := { name := "BLESSVARARGS" }
private def blessVarArgsInstr : Instr := .blessVarArgs

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def cellC : Cell :=
  Cell.mkOrdinary (natToBits 0x33 6) #[cellA, cellB]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB
private def sliceC : Slice := Slice.ofCell cellC

private def prefixMixedA : Array Value :=
  #[.null, .cell cellA, .builder Builder.empty]

private def prefixMixedB : Array Value :=
  #[intV 7, .tuple #[], .cell cellB, .null]

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def mkStack (stackPrefix : Array Value) (sliceVal : Value) (copy more : Int) : Array Value :=
  stackPrefix ++ #[sliceVal, intV copy, intV more]

private def mkStackRaw
    (stackPrefix : Array Value)
    (sliceVal copyVal moreVal : Value) : Array Value :=
  stackPrefix ++ #[sliceVal, copyVal, moreVal]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[blessVarArgsInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blessVarArgsId
    program := program
    initStack := stack
    fuel := fuel }

private instance : Inhabited OracleCase := ⟨mkCase "fuzz/fallback" #[]⟩

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContBless blessVarArgsInstr stack

private def runRaw (stack : Array Value) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContBless blessVarArgsInstr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def oracleCases : Array OracleCase := #[
  -- Success coverage for copy/more bounds.
  mkCase "ok/copy0/more-minus1/empty"
    (mkStack #[] (.slice sliceA) 0 (-1)),
  mkCase "ok/copy0/more0/prefix-int"
    (mkStack #[intV 5] (.slice sliceA) 0 0),
  mkCase "ok/copy0/more255/prefix-mixed"
    (mkStack prefixMixedA (.slice sliceB) 0 255),
  mkCase "ok/copy1/more-minus1/exact"
    (mkStack #[intV 11] (.slice sliceA) 1 (-1)),
  mkCase "ok/copy1/more0/drop-lower"
    (mkStack #[intV 11, intV 22] (.slice sliceA) 1 0),
  mkCase "ok/copy2/more1/exact-two"
    (mkStack #[intV 11, intV 22] (.slice sliceB) 2 1),
  mkCase "ok/copy2/more255/drop-bottom"
    (mkStack #[intV 1, intV 2, intV 3] (.slice sliceB) 2 255),
  mkCase "ok/copy3/more2/mixed"
    (mkStack #[.null, intV 7, .cell cellA, .tuple #[]] (.slice sliceC) 3 2),
  mkCase "ok/copy4/more0/five-values"
    (mkStack #[intV 1, intV 2, intV 3, intV 4, intV 5] (.slice sliceC) 4 0),
  mkCase "ok/copy254/more255/exact-depth"
    (mkStack (intStackAsc 254) (.slice sliceA) 254 255),
  mkCase "ok/copy254/more0/drop-bottom"
    (mkStack (intStackAsc 255) (.slice sliceA) 254 0),
  mkCase "ok/copy255/more255/exact-depth"
    (mkStack (intStackAsc 255) (.slice sliceB) 255 255),

  -- Program/order coverage (params pushed by program; no jump after BLESSVARARGS).
  mkCase "order/program-push-copy-more/basic"
    #[intV 1, intV 2, .slice sliceA]
    #[.pushInt (.num 2), .pushInt (.num 1), blessVarArgsInstr],
  mkCase "order/program-tail-continues-after-bless"
    (mkStack #[intV 9] (.slice sliceA) 1 0)
    #[blessVarArgsInstr, .pushInt (.num 777)],
  mkCase "order/program-large-copy255"
    ((intStackAsc 255) ++ #[.slice sliceC])
    #[.pushInt (.num 255), .pushInt (.num 255), blessVarArgsInstr],
  mkCase "order/program-copy0-more-minus1"
    (prefixMixedB ++ #[.slice sliceC])
    #[.pushInt (.num 0), .pushInt (.num (-1)), blessVarArgsInstr],

  -- Underflow behavior.
  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/one-int" #[intV 1],
  mkCase "err/underflow/one-slice" #[.slice sliceA],
  mkCase "err/underflow/copy1-no-prefix"
    (mkStack #[] (.slice sliceA) 1 0),
  mkCase "err/underflow/copy255-prefix254"
    (mkStack (intStackAsc 254) (.slice sliceA) 255 0),

  -- `more` type/range checks (popped first).
  mkCase "err/type/more-null"
    (mkStackRaw #[] (.slice sliceA) (intV 0) .null),
  mkCase "err/type/more-cell"
    (mkStackRaw #[] (.slice sliceA) (intV 0) (.cell cellA)),
  mkCase "err/type/more-builder"
    (mkStackRaw #[] (.slice sliceA) (intV 0) (.builder Builder.empty)),
  mkCase "err/type/more-tuple"
    (mkStackRaw #[] (.slice sliceA) (intV 0) (.tuple #[])),
  mkCase "err/type/more-cont"
    (mkStackRaw #[] (.slice sliceA) (intV 0) q0),
  mkCase "err/range/more-minus2"
    (mkStack #[] (.slice sliceA) 0 (-2)),
  mkCase "err/range/more-256"
    (mkStack #[] (.slice sliceA) 0 256),
  mkCase "err/range/more-max-int257"
    (mkStack #[] (.slice sliceA) 0 maxInt257),
  mkCase "err/range/more-min-int257"
    (mkStack #[] (.slice sliceA) 0 minInt257),
  mkCase "err/range/more-nan-via-program"
    #[.slice sliceA, intV 0]
    #[.pushInt .nan, blessVarArgsInstr],

  -- Error-order checks between `more` and `copy`.
  mkCase "order/more-range-before-copy-type"
    (mkStackRaw #[] (.slice sliceA) .null (intV 256)),
  mkCase "order/more-type-before-copy-range"
    (mkStackRaw #[] (.slice sliceA) (intV (-1)) .null),

  -- `copy` type/range checks (after valid `more`).
  mkCase "err/type/copy-null"
    (mkStackRaw #[] (.slice sliceA) .null (intV 0)),
  mkCase "err/type/copy-cell"
    (mkStackRaw #[] (.slice sliceA) (.cell cellB) (intV 0)),
  mkCase "err/type/copy-slice"
    (mkStackRaw #[] (.slice sliceA) (.slice sliceB) (intV 0)),
  mkCase "err/type/copy-builder"
    (mkStackRaw #[] (.slice sliceA) (.builder Builder.empty) (intV 0)),
  mkCase "err/type/copy-tuple"
    (mkStackRaw #[] (.slice sliceA) (.tuple #[]) (intV 0)),
  mkCase "err/type/copy-cont"
    (mkStackRaw #[] (.slice sliceA) q0 (intV 0)),
  mkCase "err/range/copy-minus1"
    (mkStack #[] (.slice sliceA) (-1) 0),
  mkCase "err/range/copy-256"
    (mkStack #[] (.slice sliceA) 256 0),
  mkCase "err/range/copy-max-int257"
    (mkStack #[] (.slice sliceA) maxInt257 0),
  mkCase "err/range/copy-min-int257"
    (mkStack #[] (.slice sliceA) minInt257 0),
  mkCase "err/range/copy-nan-via-program"
    #[.slice sliceA]
    #[.pushInt .nan, .pushInt (.num 0), blessVarArgsInstr],

  -- Slice/type checks after params are accepted.
  mkCase "err/type/slice-null"
    (mkStackRaw #[] .null (intV 0) (intV 0)),
  mkCase "err/type/slice-cell"
    (mkStackRaw #[] (.cell cellA) (intV 0) (intV 0)),
  mkCase "err/type/slice-builder"
    (mkStackRaw #[] (.builder Builder.empty) (intV 0) (intV 0)),
  mkCase "err/type/slice-cont"
    (mkStackRaw #[] q0 (intV 0) (intV 0)),
  mkCase "err/type/slice-int"
    (mkStackRaw #[] (intV 99) (intV 0) (intV 0)),

  -- Additional ordering: copy underflow must happen before slice type-check.
  mkCase "order/copy-underflow-before-slice-type"
    (mkStackRaw #[] .null (intV 1) (intV 0)),
  mkCase "order/copy-type-after-more-pop-with-prefix"
    (mkStackRaw #[intV 42] (.slice sliceA) .null (intV 0))
]

private def blessVarArgsOkFuzzPool : Array OracleCase := #[
  mkCase "fuzz/ok/copy0-more-minus1"
    (mkStack #[] (.slice sliceA) 0 (-1)),
  mkCase "fuzz/ok/copy2-more1-mixed"
    (mkStack #[intV 11, intV 22] (.slice sliceB) 2 1),
  mkCase "fuzz/ok/copy255-more255-exact-depth"
    (mkStack (intStackAsc 255) (.slice sliceB) 255 255),
  mkCase "fuzz/ok/program-tail-continues-after-bless"
    (mkStack #[intV 9] (.slice sliceA) 1 0)
    #[blessVarArgsInstr, .pushInt (.num 777)]
]

private def blessVarArgsUnderflowFuzzPool : Array OracleCase := #[
  mkCase "fuzz/err/underflow-empty" #[],
  mkCase "fuzz/err/underflow-copy1-no-prefix"
    (mkStack #[] (.slice sliceA) 1 0),
  mkCase "fuzz/err/underflow-copy255-prefix254"
    (mkStack (intStackAsc 254) (.slice sliceA) 255 0)
]

private def blessVarArgsMoreTypeFuzzPool : Array OracleCase := #[
  mkCase "fuzz/err/type/more-null"
    (mkStackRaw #[] (.slice sliceA) (intV 0) .null),
  mkCase "fuzz/err/type/more-cell"
    (mkStackRaw #[] (.slice sliceA) (intV 0) (.cell cellA)),
  mkCase "fuzz/err/type/more-cont"
    (mkStackRaw #[] (.slice sliceA) (intV 0) q0)
]

private def blessVarArgsMoreRangeFuzzPool : Array OracleCase := #[
  mkCase "fuzz/err/range/more-minus2"
    (mkStack #[] (.slice sliceA) 0 (-2)),
  mkCase "fuzz/err/range/more-256"
    (mkStack #[] (.slice sliceA) 0 256),
  mkCase "fuzz/err/range/more-nan-via-program"
    #[.slice sliceA, intV 0]
    #[.pushInt .nan, blessVarArgsInstr]
]

private def blessVarArgsMoreOrderFuzzPool : Array OracleCase := #[
  mkCase "fuzz/order/more-range-before-copy-type"
    (mkStackRaw #[] (.slice sliceA) .null (intV 256)),
  mkCase "fuzz/order/more-type-before-copy-range"
    (mkStackRaw #[] (.slice sliceA) (intV (-1)) .null)
]

private def blessVarArgsCopyTypeFuzzPool : Array OracleCase := #[
  mkCase "fuzz/err/type/copy-null"
    (mkStackRaw #[] (.slice sliceA) .null (intV 0)),
  mkCase "fuzz/err/type/copy-slice"
    (mkStackRaw #[] (.slice sliceA) (.slice sliceB) (intV 0)),
  mkCase "fuzz/err/type/copy-cont"
    (mkStackRaw #[] (.slice sliceA) q0 (intV 0))
]

private def blessVarArgsCopyRangeFuzzPool : Array OracleCase := #[
  mkCase "fuzz/err/range/copy-minus1"
    (mkStack #[] (.slice sliceA) (-1) 0),
  mkCase "fuzz/err/range/copy-256"
    (mkStack #[] (.slice sliceA) 256 0),
  mkCase "fuzz/err/range/copy-nan-via-program"
    #[.slice sliceA]
    #[.pushInt .nan, .pushInt (.num 0), blessVarArgsInstr]
]

private def blessVarArgsSliceTypeFuzzPool : Array OracleCase := #[
  mkCase "fuzz/err/type/slice-null"
    (mkStackRaw #[] .null (intV 0) (intV 0)),
  mkCase "fuzz/err/type/slice-cell"
    (mkStackRaw #[] (.cell cellA) (intV 0) (intV 0)),
  mkCase "fuzz/err/type/slice-int"
    (mkStackRaw #[] (intV 99) (intV 0) (intV 0))
]

private def blessVarArgsCopyOrderFuzzPool : Array OracleCase := #[
  mkCase "fuzz/order/copy-underflow-before-slice-type"
    (mkStackRaw #[] .null (intV 1) (intV 0)),
  mkCase "fuzz/order/copy-type-after-more-pop-with-prefix"
    (mkStackRaw #[intV 42] (.slice sliceA) .null (intV 0))
]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genBlessVarArgsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  let pool :=
    if shape = 0 then
      blessVarArgsOkFuzzPool
    else if shape = 1 then
      blessVarArgsUnderflowFuzzPool
    else if shape = 2 then
      blessVarArgsMoreTypeFuzzPool
    else if shape = 3 then
      blessVarArgsMoreRangeFuzzPool
    else if shape = 4 then
      blessVarArgsMoreOrderFuzzPool
    else if shape = 5 then
      blessVarArgsCopyTypeFuzzPool
    else if shape = 6 then
      blessVarArgsCopyRangeFuzzPool
    else if shape = 7 then
      blessVarArgsSliceTypeFuzzPool
    else
      blessVarArgsCopyOrderFuzzPool
  let (case0, rng2) := pickFromPool pool rng1
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := blessVarArgsId
  unit := #[
    { name := "unit/direct/nan-more-maps-to-rangeChk"
      run :=
        expectErr "nan-more-range"
          (runDirect (mkStackRaw #[] (.slice sliceA) (intV 0) (.int .nan)))
          .rangeChk }
    ,
    { name := "unit/direct/more-range-before-copy-type"
      run :=
        expectErr "more-range-before-copy-type"
          (runDirect (mkStackRaw #[] (.slice sliceA) .null (intV 256)))
          .rangeChk }
    ,
    { name := "unit/direct/copy-type-after-more"
      run :=
        expectErr "copy-type-after-more"
          (runDirect (mkStackRaw #[] (.slice sliceA) .null (intV 0)))
          .typeChk }
    ,
    { name := "unit/direct/copy-underflow-before-slice-type"
      run :=
        expectErr "copy-underflow-before-slice-type"
          (runDirect (mkStackRaw #[] .null (intV 1) (intV 0)))
          .stkUnd }
    ,
    { name := "unit/direct/success-captures-top-copy-order"
      run := do
        let st ← expectRawOk "success-captures-top-copy-order"
          (runRaw (mkStack #[intV 1, intV 2, intV 3] (.slice sliceA) 2 5))
        match st.stack with
        | #[v0, .cont (.ordinary code _ _ cdata)] =>
            if v0 != intV 1 then
              throw (IO.userError
                s!"success-captures-top-copy-order: expected bottom int 1, got {reprStr v0}")
            else if code != sliceA then
              throw (IO.userError
                s!"success-captures-top-copy-order: expected code sliceA, got {reprStr code}")
            else if cdata.stack != #[intV 2, intV 3] then
              throw (IO.userError
                s!"success-captures-top-copy-order: expected captured #[2,3], got {reprStr cdata.stack}")
            else if cdata.nargs != 5 then
              throw (IO.userError
                s!"success-captures-top-copy-order: expected nargs=5, got {cdata.nargs}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"success-captures-top-copy-order: unexpected final stack {reprStr st.stack}") }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr blessVarArgsId
      count := 500
      gen := genBlessVarArgsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.BLESSVARARGS
