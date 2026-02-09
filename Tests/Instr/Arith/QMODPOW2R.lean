import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMODPOW2R

/-
QMODPOW2R branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod` with
     `mulMode=false`, `addMode=false`, `d=2`, `roundMode=0`, `quiet=true`, `zOpt=none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popNatUpTo`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean` (`modPow2Round`, nearest ties toward `+∞`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `register_div_ops`, quiet opcode family `0xb7a92`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean specialization: 5 branch sites / 6 terminal outcomes
  (dispatch arm; stack underflow precheck; shift-pop `typeChk`/`rangeChk`/ok;
   x-pop `typeChk`; finite-vs-NaN x split with quiet NaN funnel).
- C++ specialization: 4 branch sites / 6 aligned terminal outcomes
  (underflow check; `pop_smallint_range(256)` type/range split;
   second-pop type check; quiet `push_int_quiet` finite-vs-NaN success paths).

Key risk areas covered:
- nearest rounding-mode (`R`) remainder behavior, including half ties and sign combos;
- runtime shift strictness (`0..256`) even in quiet mode, with shift popped before x;
- quiet NaN behavior (`x=NaN` yields pushed NaN, not `intOv`);
- oracle serialization safety for NaN/out-of-range via program prefixes;
- exact gas threshold (`PUSHINT n; SETGASLIMIT; QMODPOW2R`) at exact vs exact-minus-one.
-/

private def qmodPow2RId : InstrId := { name := "QMODPOW2R" }

private def qmodPow2RInstr : Instr :=
  .arithExt (.shrMod false false 2 0 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmodPow2RInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmodPow2RId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmodPow2RInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQmodPow2RDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmodPow2RInstr stack

private def runQmodPow2RDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 938)) stack

private def qmodPow2RSetGasExact : Int :=
  computeExactGasBudget qmodPow2RInstr

private def qmodPow2RSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmodPow2RInstr

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieCasePool : Array (Int × Nat) :=
  #[
    (1, 1), (-1, 1),
    (2, 2), (-2, 2),
    (6, 2), (-6, 2),
    (12, 3), (-12, 3),
    (pow2 255, 256), (-(pow2 255), 256)
  ]

private def outOfRangeHighPool : Array Int :=
  #[maxInt257 + 1, maxInt257 + 2, pow2 257]

private def outOfRangeLowPool : Array Int :=
  #[minInt257 - 1, minInt257 - 2, -(pow2 257)]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftUniform rng1

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQmodPow2RFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let ((kind, stack, program), rng2) :
      (String × Array Value × Array Instr) × StdGen :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (shift0, r3) := pickShiftBoundary r2
      (("ok-boundary", #[intV x0, intV (Int.ofNat shift0)], #[qmodPow2RInstr]), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (shift0, r3) := pickShiftBoundary r2
      (("ok-random-x-boundary-shift", #[intV x0, intV (Int.ofNat shift0)], #[qmodPow2RInstr]), r3)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (shift0, r3) := pickShiftUniform r2
      (("ok-boundary-x-random-shift", #[intV x0, intV (Int.ofNat shift0)], #[qmodPow2RInstr]), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (shift0, r3) := pickShiftMixed r2
      (("ok-random", #[intV x0, intV (Int.ofNat shift0)], #[qmodPow2RInstr]), r3)
    else if shape = 4 then
      let ((x0, shift0), r2) := pickFromPool tieCasePool rng1
      (("ok-half-tie", #[intV x0, intV (Int.ofNat shift0)], #[qmodPow2RInstr]), r2)
    else if shape = 5 then
      let (x0, r2) := pickSigned257ish rng1
      (("ok-shift-zero", #[intV x0, intV 0], #[qmodPow2RInstr]), r2)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let x0 := if useMax then maxInt257 else minInt257
      let (shift0, r3) := pickShiftBoundary r2
      (("ok-extreme-x", #[intV x0, intV (Int.ofNat shift0)], #[qmodPow2RInstr]), r3)
    else if shape = 7 then
      (("underflow-empty", #[], #[qmodPow2RInstr]), rng1)
    else if shape = 8 then
      let (x0, r2) := pickSigned257ish rng1
      (("underflow-one-int", #[intV x0], #[qmodPow2RInstr]), r2)
    else if shape = 9 then
      (("underflow-one-non-int", #[.null], #[qmodPow2RInstr]), rng1)
    else if shape = 10 then
      let (x0, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (("type-shift-pop-first", #[intV x0, nonInt], #[qmodPow2RInstr]), r3)
    else if shape = 11 then
      let (shift0, r2) := pickShiftMixed rng1
      let (nonInt, r3) := pickNonInt r2
      (("type-x-pop-second", #[nonInt, intV (Int.ofNat shift0)], #[qmodPow2RInstr]), r3)
    else if shape = 12 then
      let (xLike, r2) := pickNonInt rng1
      let (shiftLike, r3) := pickNonInt r2
      (("error-order-both-non-int-shift-first", #[xLike, shiftLike], #[qmodPow2RInstr]), r3)
    else if shape = 13 then
      let (x0, r2) := pickSigned257ish rng1
      (("range-shift-negative", #[intV x0, intV (-1)], #[qmodPow2RInstr]), r2)
    else if shape = 14 then
      let (x0, r2) := pickSigned257ish rng1
      (("range-shift-over256", #[intV x0, intV 257], #[qmodPow2RInstr]), r2)
    else if shape = 15 then
      let (x0, r2) := pickSigned257ish rng1
      let case0 := mkCaseFromIntVals "tmp" #[.num x0, .nan]
      (("range-shift-nan-via-program", case0.initStack, case0.program), r2)
    else if shape = 16 then
      let (shift0, r2) := pickShiftMixed rng1
      let case0 := mkCaseFromIntVals "tmp" #[.nan, .num (Int.ofNat shift0)]
      (("quiet-nan-x-via-program", case0.initStack, case0.program), r2)
    else if shape = 17 then
      (("error-order-range-before-x-type-via-program", #[.null], #[.pushInt (.num (-1)), qmodPow2RInstr]), rng1)
    else if shape = 18 then
      let (x0, r2) := pickFromPool outOfRangeHighPool rng1
      let case0 := mkCaseFromIntVals "tmp" #[.num x0, .num 7]
      (("error-order-pushint-range-high-before-op", case0.initStack, case0.program), r2)
    else
      let (y0, r2) := pickFromPool outOfRangeLowPool rng1
      let case0 := mkCaseFromIntVals "tmp" #[.num 7, .num y0]
      (("error-order-pushint-range-low-before-op", case0.initStack, case0.program), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" stack program, rng3)

def suite : InstrSuite where
  id := qmodPow2RId
  unit := #[
    { name := "unit/round/nearest-sign-and-half-tie-behavior"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (1, 1, -1),
            (-1, 1, -1),
            (3, 1, -1),
            (-3, 1, -1),
            (5, 2, 1),
            (-5, 2, -1),
            (6, 2, -2),
            (-6, 2, -2),
            (7, 2, -1),
            (-7, 2, 1),
            (11, 3, 3),
            (-11, 3, -3),
            (12, 3, -4),
            (-12, 3, -4),
            (pow2 255, 256, -(pow2 255)),
            (-(pow2 255), 256, -(pow2 255)),
            (maxInt257, 256, -1),
            (minInt257, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} qmodPow2R {shift}"
            (runQmodPow2RDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/round/shift-zero-and-boundary-edges"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (123, 0, 0),
            (-123, 0, 0),
            (maxInt257, 0, 0),
            (minInt257, 0, 0),
            (pow2 255, 255, 0),
            (-(pow2 255), 255, 0),
            (maxInt257, 255, -1),
            (maxInt257 - 1, 256, -2),
            (minInt257, 255, 0),
            (minInt257 + 1, 256, 1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} qmodPow2R {shift}"
            (runQmodPow2RDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/quiet-and-error-ordering"
      run := do
        expectOkStack "quiet/x-nan" (runQmodPow2RDirect #[.int .nan, intV 5]) #[.int .nan]
        expectErr "underflow/empty" (runQmodPow2RDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQmodPow2RDirect #[intV 7]) .stkUnd
        expectErr "underflow/one-non-int" (runQmodPow2RDirect #[.null]) .stkUnd
        expectErr "type/shift-pop-first" (runQmodPow2RDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-pop-second" (runQmodPow2RDirect #[.null, intV 7]) .typeChk
        expectErr "type/both-non-int-shift-first"
          (runQmodPow2RDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "range/shift-negative" (runQmodPow2RDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runQmodPow2RDirect #[intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runQmodPow2RDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "error-order/range-before-x-type"
          (runQmodPow2RDirect #[.null, intV (-1)]) .rangeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmodPow2RDispatchFallback #[]) #[intV 938] }
  ]
  oracle := #[
    mkCase "ok/shift0/zero" #[intV 0, intV 0],
    mkCase "ok/shift0/positive" #[intV 123, intV 0],
    mkCase "ok/shift0/negative" #[intV (-123), intV 0],
    mkCase "ok/round/odd-pos-shift1" #[intV 3, intV 1],
    mkCase "ok/round/odd-neg-shift1" #[intV (-3), intV 1],
    mkCase "ok/round/non-tie-pos-shift2" #[intV 5, intV 2],
    mkCase "ok/round/non-tie-neg-shift2" #[intV (-5), intV 2],
    mkCase "ok/round/tie-pos-shift2" #[intV 6, intV 2],
    mkCase "ok/round/tie-neg-shift2" #[intV (-6), intV 2],
    mkCase "ok/round/non-tie-pos-shift3" #[intV 11, intV 3],
    mkCase "ok/round/non-tie-neg-shift3" #[intV (-11), intV 3],
    mkCase "ok/round/tie-pos-shift3" #[intV 12, intV 3],
    mkCase "ok/round/tie-neg-shift3" #[intV (-12), intV 3],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 256],
    mkCase "ok/boundary/max-shift255" #[intV maxInt257, intV 255],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/min-shift255" #[intV minInt257, intV 255],
    mkCase "ok/boundary/pow255-shift256" #[intV (pow2 255), intV 256],
    mkCase "ok/boundary/negpow255-shift256" #[intV (-(pow2 255)), intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 1],
    mkCase "error-order/single-item-underflow-before-type" #[.null],
    mkCase "type/shift-pop-first-null" #[intV 7, .null],
    mkCase "type/shift-pop-first-cell" #[intV 7, .cell Cell.empty],
    mkCase "type/x-pop-second-null" #[.null, intV 7],
    mkCase "type/x-pop-second-cell" #[.cell Cell.empty, intV 7],
    mkCase "error-order/both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative" #[intV 7, intV (-1)],
    mkCase "range/shift-over-256" #[intV 7, intV 257],
    mkCase "error-order/range-before-x-type" #[.null, intV (-1)],
    mkCaseFromIntVals "range/shift-nan-via-program" #[.num 7, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 5],
    mkCaseFromIntVals "quiet/nan/x-via-program-shift0" #[.nan, .num 0],
    mkCaseFromIntVals "error-order/pushint-range-high-before-qmodpow2r"
      #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-range-low-before-qmodpow2r"
      #[.num 7, .num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qmodPow2RSetGasExact), .tonEnvOp .setGasLimit, qmodPow2RInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qmodPow2RSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmodPow2RInstr]
  ]
  fuzz := #[
    { seed := 2026020827
      count := 700
      gen := genQmodPow2RFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMODPOW2R
