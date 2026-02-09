import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTADDDIVMODR

/-
LSHIFTADDDIVMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 0 true false none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/range behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, nearest ties toward `+∞`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (non-quiet decode family `0xa9c0..0xa9c2`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite (`d=3`, `roundMode=0`,
`add=true`, `quiet=false`, runtime shift):
- Lean specialization: ~10 branch sites / ~18 terminal outcomes
  (dispatch/fallback, pre-underflow gate, shift pop/range gate, pop order
   `shift→y→w→x`, numeric-vs-invalid split, `y=0` funnel, round-mode gate,
   `d=3` push ordering with non-quiet overflow behavior).
- C++ specialization: ~8 branch sites / ~15 aligned terminal outcomes
  (`check_underflow`, runtime-shift parse/range gate, operand validity split,
   divisor-zero funnel, `mod_div` path, `q/r` push order with `push_int_quiet`).

Key risk areas covered:
- nearest rounding ties toward `+∞` for `((x << shift) + w) / y`;
- pop/error order (`shift`, `y`, `w`, `x`) and explicit underflow precedence;
- non-quiet funnels (`divzero`, NaN operands, quotient/remainder overflow) → `intOv`;
- strict non-quiet range gate (`shift < 0` or `shift > 256`) → `rangeChk`
  before popping `y/w/x`;
- oracle-safe NaN/out-of-range injection via program prelude (`PUSHINT`) only;
- exact gas boundary oracle (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def lshiftAddDivModrId : InstrId := { name := "LSHIFTADDDIVMODR" }

private def lshiftAddDivModrInstr : Instr :=
  .arithExt (.shlDivMod 3 0 true false none)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftAddDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftAddDivModrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[lshiftAddDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runLshiftAddDivModrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftAddDivModrInstr stack

private def expectLshiftAddDivModr
    (label : String)
    (x w y shift q r : Int) : IO Unit :=
  expectOkStack label
    (runLshiftAddDivModrDirect #[intV x, intV w, intV y, intV shift])
    #[intV q, intV r]

private def lshiftAddDivModrSetGasExact : Int :=
  computeExactGasBudget lshiftAddDivModrInstr

private def lshiftAddDivModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftAddDivModrInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieNumeratorPool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieDivisorPool : Array Int :=
  #[-2, 2]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyLshiftAddDivModr (x w y shift : Int) : String :=
  if shift < 0 || shift > Int.ofNat 256 then
    "range"
  else if y = 0 then
    "divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat + w
    let (q, r) := divModRound tmp y 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genLshiftAddDivModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      let shiftI := Int.ofNat shift
      let kind := classifyLshiftAddDivModr x w y shiftI
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-valid"
        #[intV x, intV w, intV y, intV shiftI], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      let shiftI := Int.ofNat shift
      let kind := classifyLshiftAddDivModr x w y shiftI
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-boundary-shift"
        #[intV x, intV w, intV y, intV shiftI], r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftUniform r4
      let shiftI := Int.ofNat shift
      let kind := classifyLshiftAddDivModr x w y shiftI
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-uniform-shift"
        #[intV x, intV w, intV y, intV shiftI], r5)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyLshiftAddDivModr x w 0 (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/divzero"
        #[intV x, intV w, intV 0, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyLshiftAddDivModr x 0 y 0
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-shift0-add0"
        #[intV x, intV 0, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyLshiftAddDivModr x 1 (y * 2) 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-shift1-add1"
        #[intV x, intV 1, intV (y * 2), intV 1], r3)
    else if shape = 6 then
      let kind := classifyLshiftAddDivModr maxInt257 0 1 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/overflow-max-shift1-div1"
        #[intV maxInt257, intV 0, intV 1, intV 1], rng1)
    else if shape = 7 then
      let kind := classifyLshiftAddDivModr minInt257 0 (-1) 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/overflow-min-shift1-div-neg1"
        #[intV minInt257, intV 0, intV (-1), intV 1], rng1)
    else if shape = 8 then
      let kind := classifyLshiftAddDivModr maxInt257 1 1 0
      (mkCase s!"/fuzz/shape-{shape}/{kind}/overflow-add-overmax"
        #[intV maxInt257, intV 1, intV 1, intV 0], rng1)
    else if shape = 9 then
      let kind := classifyLshiftAddDivModr minInt257 (-1) 1 0
      (mkCase s!"/fuzz/shape-{shape}/{kind}/overflow-add-undermin"
        #[intV minInt257, intV (-1), intV 1, intV 0], rng1)
    else if shape = 10 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyLshiftAddDivModr 0 w y (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-x"
        #[intV 0, intV w, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyLshiftAddDivModr x 0 y (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-w"
        #[intV x, intV 0, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyLshiftAddDivModr x w 1 (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/div-by-one"
        #[intV x, intV w, intV 1, intV (Int.ofNat shift)], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyLshiftAddDivModr x w (-1) (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/div-by-neg-one"
        #[intV x, intV w, intV (-1), intV (Int.ofNat shift)], r4)
    else if shape = 14 then
      (mkCase s!"/fuzz/shape-{shape}/range/shift-neg-one"
        #[intV 7, intV 3, intV 5, intV (-1)], rng1)
    else if shape = 15 then
      (mkCase s!"/fuzz/shape-{shape}/range/shift-257"
        #[intV 7, intV 3, intV 5, intV 257], rng1)
    else if shape = 16 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg"
        #[intV x], r2)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args"
        #[intV x, intV w], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/underflow/three-args"
        #[intV x, intV w, intV y], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (badShift, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV w, intV y, badShift], r5)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let (yBad, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second"
        #[intV x, intV w, yBad, intV (Int.ofNat shift)], r5)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (wBad, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-w-third"
        #[intV x, wBad, intV y, intV (Int.ofNat shift)], r5)
    else if shape = 23 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (xBad, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-fourth"
        #[xBad, intV w, intV y, intV (Int.ofNat shift)], r5)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-y-type"
        #[intV x, intV w, yBad, intV 257], r4)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (wBad, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-w-type"
        #[intV x, wBad, intV y, intV (-1)], r4)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-shift"
        #[IntVal.num x, IntVal.num w, IntVal.num y, IntVal.nan], r4)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-y"
        #[IntVal.num x, IntVal.num w, IntVal.nan, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-w"
        #[IntVal.num x, IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 29 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-x"
        #[IntVal.nan, IntVal.num w, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 30 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-both-x-y"
        #[IntVal.nan, IntVal.num w, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 31 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num y, IntVal.num huge], r5)
    else if shape = 32 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num huge, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 33 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        #[IntVal.num x, IntVal.num huge, IntVal.num y, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 34 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num huge, IntVal.num w, IntVal.num y, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 35 then
      let (hugeX, r2) := pickInt257OutOfRange rng1
      let (hugeW, r3) := pickInt257OutOfRange r2
      let (hugeY, r4) := pickInt257OutOfRange r3
      let (hugeShift, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        #[IntVal.num hugeX, IntVal.num hugeW, IntVal.num hugeY, IntVal.num hugeShift], r5)
    else if shape = 36 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-y-type-via-program"
        #[intV 7, intV 3, .null] #[.pushInt (.num (-1)), lshiftAddDivModrInstr], rng1)
    else if shape = 37 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-w-type-via-program"
        #[intV 7, .null, intV 5] #[.pushInt (.num 257), lshiftAddDivModrInstr], rng1)
    else if shape = 38 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num (-1)), lshiftAddDivModrInstr], rng1)
    else
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftUniform r4
      let kind := classifyLshiftAddDivModr x w y (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/pop-order/lower-stack-preserved"
        #[.cell Cell.empty, intV x, intV w, intV y, intV (Int.ofNat shift)], r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftAddDivModrId
  unit := #[
    { name := "/unit/ok/nearest-rounding-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 5, 1, 3, 2),
            (-7, 3, 5, 1, -2, -1),
            (7, -3, 5, 1, 2, 1),
            (-7, -3, 5, 1, -3, -2),
            (7, 3, -5, 1, -3, 2),
            (-7, 3, -5, 1, 2, -1),
            (5, 0, 2, 0, 3, -1),
            (-5, 0, 2, 0, -2, -1),
            (5, 0, -2, 0, -2, 1),
            (-5, 0, -2, 0, 3, 1),
            (1, 0, 2, 0, 1, -1),
            (-1, 0, 2, 0, 0, -1),
            (1, 0, -2, 0, 0, 1),
            (-1, 0, -2, 0, 1, 1),
            (7, 5, 2, 2, 17, -1),
            (-7, 5, 2, 2, -11, -1),
            (7, -5, 2, 2, 12, -1),
            (-7, -5, 2, 2, -16, -1),
            (42, 0, 7, 3, 48, 0),
            (0, 9, 5, 8, 2, -1),
            (0, -9, 5, 8, -2, 1),
            (3, 1, 5, 0, 1, -1)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectLshiftAddDivModr s!"/check/({x}<<{shift})+{w}/{y}" x w y shift q r }
    ,
    { name := "/unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 1, 0, maxInt257, 0),
            (maxInt257, -1, 1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 1, 0, minInt257 + 1, 0),
            (minInt257 + 1, 0, -1, 0, maxInt257, 0),
            (maxInt257, 0, 2, 0, pow2 255, -1),
            (minInt257, 0, 2, 0, -(pow2 255), 0),
            (minInt257, 0, -2, 0, pow2 255, 0),
            (1, 0, maxInt257, 256, 1, 1),
            (-1, 0, maxInt257, 256, -1, -1),
            (1, 0, minInt257, 256, -1, 0),
            (-1, 0, minInt257, 256, 1, 0),
            (0, maxInt257, maxInt257, 0, 1, 0),
            (0, minInt257, minInt257, 0, 1, 0),
            (1, -1, maxInt257, 256, 1, 0)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectLshiftAddDivModr s!"/boundary/({x}<<{shift})+{w}/{y}" x w y shift q r }
    ,
    { name := "/unit/error/divzero-overflow-and-range-gates"
      run := do
        expectErr "/divzero/nonzero-over-zero"
          (runLshiftAddDivModrDirect #[intV 5, intV 1, intV 0, intV 3]) .intOv
        expectErr "/divzero/zero-over-zero"
          (runLshiftAddDivModrDirect #[intV 0, intV 0, intV 0, intV 8]) .intOv
        expectErr "/overflow/max-shift1-div1"
          (runLshiftAddDivModrDirect #[intV maxInt257, intV 0, intV 1, intV 1]) .intOv
        expectErr "/overflow/min-shift1-div-neg1"
          (runLshiftAddDivModrDirect #[intV minInt257, intV 0, intV (-1), intV 1]) .intOv
        expectErr "/overflow/add-overmax-shift0-div1"
          (runLshiftAddDivModrDirect #[intV maxInt257, intV 1, intV 1, intV 0]) .intOv
        expectErr "/overflow/add-undermin-shift0-div1"
          (runLshiftAddDivModrDirect #[intV minInt257, intV (-1), intV 1, intV 0]) .intOv
        expectErr "/range/shift-negative-before-y-pop"
          (runLshiftAddDivModrDirect #[intV 1, intV 2, .null, intV (-1)]) .rangeChk
        expectErr "/range/shift-257-before-w-pop"
          (runLshiftAddDivModrDirect #[intV 1, .null, intV 2, intV 257]) .rangeChk }
    ,
    { name := "/unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "/underflow/empty" (runLshiftAddDivModrDirect #[]) .stkUnd
        expectErr "/underflow/one-arg" (runLshiftAddDivModrDirect #[intV 1]) .stkUnd
        expectErr "/underflow/two-args" (runLshiftAddDivModrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/underflow/three-args" (runLshiftAddDivModrDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/error-order/underflow-before-type-with-three-items"
          (runLshiftAddDivModrDirect #[.null, .cell Cell.empty, intV 1]) .stkUnd
        expectErr "/type/pop-shift-first-null"
          (runLshiftAddDivModrDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/type/pop-shift-first-cell"
          (runLshiftAddDivModrDirect #[intV 1, intV 2, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/type/pop-y-second-null"
          (runLshiftAddDivModrDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/type/pop-y-second-cell"
          (runLshiftAddDivModrDirect #[intV 1, intV 2, .cell Cell.empty, intV 3]) .typeChk
        expectErr "/type/pop-w-third-null"
          (runLshiftAddDivModrDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "/type/pop-w-third-cell"
          (runLshiftAddDivModrDirect #[intV 1, .cell Cell.empty, intV 2, intV 3]) .typeChk
        expectErr "/type/pop-x-fourth-null"
          (runLshiftAddDivModrDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/type/pop-x-fourth-cell"
          (runLshiftAddDivModrDirect #[.cell Cell.empty, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/error-order/pop-y-before-w-when-both-non-int"
          (runLshiftAddDivModrDirect #[intV 1, .cell Cell.empty, .null, intV 3]) .typeChk
        expectErr "/error-order/pop-w-before-x-when-y-int"
          (runLshiftAddDivModrDirect #[.null, .cell Cell.empty, intV 2, intV 3]) .typeChk }
    ,
    { name := "/unit/opcode/decode-lshiftadddivmodr"
      run := do
        let code ←
          match assembleCp0 [lshiftAddDivModrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/decode/assemble-failed: {e}")
        match decodeCp0WithBits (Slice.ofCell code) with
        | .error e =>
            throw (IO.userError s!"/decode/decode-failed: {e}")
        | .ok (instr, bits, _) =>
            if instr != lshiftAddDivModrInstr then
              throw (IO.userError s!"/decode/expected-{reprStr lshiftAddDivModrInstr}-got-{reprStr instr}")
            else if bits != 16 then
              throw (IO.userError s!"/decode/expected-16-bits-got-{bits}")
            else
              pure () }
    ,
    { name := "/unit/pop-order/lower-stack-preserved"
      run := do
        expectOkStack "/pop-order/lower-cell-preserved"
          (runLshiftAddDivModrDirect #[.cell Cell.empty, intV 7, intV 3, intV 5, intV 1])
          #[.cell Cell.empty, intV 3, intV 2] }
  ]
  oracle := #[
    mkCase "/ok/round/inexact-pos-pos" #[intV 7, intV 3, intV 5, intV 1],
    mkCase "/ok/round/inexact-neg-pos" #[intV (-7), intV 3, intV 5, intV 1],
    mkCase "/ok/round/inexact-pos-neg" #[intV 7, intV 3, intV (-5), intV 1],
    mkCase "/ok/round/inexact-neg-neg" #[intV (-7), intV 3, intV (-5), intV 1],
    mkCase "/ok/tie/pos-over-pos-two-shift0" #[intV 5, intV 0, intV 2, intV 0],
    mkCase "/ok/tie/neg-over-pos-two-shift0" #[intV (-5), intV 0, intV 2, intV 0],
    mkCase "/ok/tie/pos-over-neg-two-shift0" #[intV 5, intV 0, intV (-2), intV 0],
    mkCase "/ok/tie/neg-over-neg-two-shift0" #[intV (-5), intV 0, intV (-2), intV 0],
    mkCase "/ok/tie/near-zero-pos-over-pos-two" #[intV 1, intV 0, intV 2, intV 0],
    mkCase "/ok/tie/near-zero-neg-over-pos-two" #[intV (-1), intV 0, intV 2, intV 0],
    mkCase "/ok/tie/near-zero-pos-over-neg-two" #[intV 1, intV 0, intV (-2), intV 0],
    mkCase "/ok/tie/near-zero-neg-over-neg-two" #[intV (-1), intV 0, intV (-2), intV 0],
    mkCase "/ok/exact/shifted-divisible" #[intV 42, intV 0, intV 7, intV 3],
    mkCase "/ok/exact/addend-only-positive" #[intV 0, intV 9, intV 5, intV 8],
    mkCase "/ok/exact/addend-only-negative" #[intV 0, intV (-9), intV 5, intV 8],
    mkCase "/ok/exact/addend-cancels-to-divisible" #[intV 1, intV (-1), intV maxInt257, intV 256],
    mkCase "/ok/boundary/max-shift0-div1" #[intV maxInt257, intV 0, intV 1, intV 0],
    mkCase "/ok/boundary/max-plus-negone-shift0-div1" #[intV maxInt257, intV (-1), intV 1, intV 0],
    mkCase "/ok/boundary/min-plus-one-shift0-div1" #[intV minInt257, intV 1, intV 1, intV 0],
    mkCase "/ok/boundary/min-plus-one-shift0-div-neg1" #[intV (minInt257 + 1), intV 0, intV (-1), intV 0],
    mkCase "/ok/boundary/max-shift0-div2" #[intV maxInt257, intV 0, intV 2, intV 0],
    mkCase "/ok/boundary/min-shift0-div2" #[intV minInt257, intV 0, intV 2, intV 0],
    mkCase "/ok/boundary/min-shift0-div-neg2" #[intV minInt257, intV 0, intV (-2), intV 0],
    mkCase "/ok/boundary/one-shift256-div-max" #[intV 1, intV 0, intV maxInt257, intV 256],
    mkCase "/ok/boundary/neg-one-shift256-div-max" #[intV (-1), intV 0, intV maxInt257, intV 256],
    mkCase "/ok/boundary/one-shift256-div-min" #[intV 1, intV 0, intV minInt257, intV 256],
    mkCase "/ok/boundary/neg-one-shift256-div-min" #[intV (-1), intV 0, intV minInt257, intV 256],
    mkCase "/ok/boundary/w-max-over-max" #[intV 0, intV maxInt257, intV maxInt257, intV 0],
    mkCase "/ok/boundary/w-min-over-min" #[intV 0, intV minInt257, intV minInt257, intV 0],
    mkCase "/intov/divzero/nonzero-over-zero" #[intV 5, intV 1, intV 0, intV 3],
    mkCase "/intov/divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 8],
    mkCase "/intov/overflow/max-shift1-div1" #[intV maxInt257, intV 0, intV 1, intV 1],
    mkCase "/intov/overflow/min-shift1-div-neg1" #[intV minInt257, intV 0, intV (-1), intV 1],
    mkCase "/intov/overflow/add-overmax" #[intV maxInt257, intV 1, intV 1, intV 0],
    mkCase "/intov/overflow/add-undermin" #[intV minInt257, intV (-1), intV 1, intV 0],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/type/pop-shift-first" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/pop-y-second" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/pop-w-third" #[intV 1, .null, intV 2, intV 3],
    mkCase "/type/pop-x-fourth" #[.null, intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-type-with-three-items" #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/pop-y-before-w-when-both-non-int" #[intV 1, .cell Cell.empty, .null, intV 3],
    mkCase "/error-order/pop-w-before-x-when-y-int" #[.null, .cell Cell.empty, intV 2, intV 3],
    mkCase "/range/shift-negative" #[intV 7, intV 3, intV 5, intV (-1)],
    mkCase "/range/shift-257" #[intV 7, intV 3, intV 5, intV 257],
    mkCase "/error-order/range-before-y-type" #[intV 7, intV 3, .null, intV (-1)],
    mkCase "/error-order/range-before-w-type" #[intV 7, .null, intV 5, intV 257],
    mkInputCase "/nan/program-shift" #[IntVal.num 5, IntVal.num 3, IntVal.num 7, IntVal.nan],
    mkInputCase "/nan/program-y" #[IntVal.num 5, IntVal.num 3, IntVal.nan, IntVal.num 1],
    mkInputCase "/nan/program-w" #[IntVal.num 5, IntVal.nan, IntVal.num 7, IntVal.num 1],
    mkInputCase "/nan/program-x" #[IntVal.nan, IntVal.num 3, IntVal.num 7, IntVal.num 1],
    mkInputCase "/nan/program-both-x-y" #[IntVal.nan, IntVal.num 3, IntVal.nan, IntVal.num 1],
    mkInputCase "/error-order/pushint-overflow-shift-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkInputCase "/error-order/pushint-underflow-shift-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkInputCase "/error-order/pushint-overflow-y-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkInputCase "/error-order/pushint-underflow-y-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkInputCase "/error-order/pushint-overflow-w-before-op"
      #[IntVal.num 5, IntVal.num (pow2 257), IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-underflow-w-before-op"
      #[IntVal.num 5, IntVal.num (-(pow2 257)), IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-overflow-x-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-underflow-x-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 3, IntVal.num 7, IntVal.num 1],
    mkCase "/error-order/range-before-y-type-via-program"
      #[intV 7, intV 3, .null] #[.pushInt (.num (-1)), lshiftAddDivModrInstr],
    mkCase "/error-order/range-before-w-type-via-program"
      #[intV 7, .null, intV 5] #[.pushInt (.num 257), lshiftAddDivModrInstr],
    mkCase "/error-order/underflow-before-range-via-program"
      #[] #[.pushInt (.num (-1)), lshiftAddDivModrInstr],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 5, intV 1]
      #[.pushInt (.num lshiftAddDivModrSetGasExact), .tonEnvOp .setGasLimit, lshiftAddDivModrInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 5, intV 1]
      #[.pushInt (.num lshiftAddDivModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftAddDivModrInstr]
  ]
  fuzz := #[
    { seed := 2026020864
      count := 700
      gen := genLshiftAddDivModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTADDDIVMODR
