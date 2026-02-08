import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTDIVMODR

/-
LSHIFTDIVMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shlDivMod` path)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest/ties-to-+∞ mode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa9cc..0xa9ce` decode family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite (LSHIFTDIVMODR specialization):
- Lean specialization (`.arithExt (.shlDivMod 3 0 false false none)`):
  ~8 branch sites / ~15 terminal outcomes
  (dispatch arm; shift pop/range gate; `y` pop/type split; `x` pop/type split;
   numeric-vs-invalid split; divisor-zero split; fixed round-mode validity split;
   `d` switch with double-push path).
- C++ specialization (`exec_shldivmod`, runtime shift, `d=3`, non-quiet):
  ~7 branch sites / ~13 aligned terminal outcomes
  (global-version add-remap gate; invalid-opcode guard; underflow guard;
   runtime shift range gate; operand validity split; `d`-selected push sequence).

Key risk areas covered:
- pop order must be `shift` then `y` then `x`;
- nearest rounding ties must go toward `+∞`;
- out-of-range runtime shift must throw `rangeChk` before popping divisor/numerator;
- non-quiet invalid-result funnels (div-by-zero / NaN / overflow) must throw `intOv`;
- signed-257 boundary behavior around `±2^256` with large shifts;
- exact gas threshold (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def lshiftDivModrId : InstrId := { name := "LSHIFTDIVMODR" }

private def lshiftDivModrInstr : Instr := .arithExt (.shlDivMod 3 0 false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftDivModrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[lshiftDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runLshiftDivModrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftDivModrInstr stack

private def runLshiftDivModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 2601)) stack

private def expectLshiftDivModr
    (label : String)
    (x y shift q r : Int) : IO Unit :=
  expectOkStack label
    (runLshiftDivModrDirect #[intV x, intV y, intV shift])
    #[intV q, intV r]

private def lshiftDivModrSetGasExact : Int :=
  computeExactGasBudget lshiftDivModrInstr

private def lshiftDivModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftDivModrInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieNumeratorPool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieDivisorPool : Array Int :=
  #[-2, 2]

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1]

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

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  pickFromPool outOfRangeProgramPool rng

private def classifyLshiftDivModr (x y shift : Int) : String :=
  if shift < 0 || shift > Int.ofNat 256 then
    "range"
  else if y = 0 then
    "divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat
    let (q, r) := divModRound tmp y 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genLshiftDivModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let shiftI := Int.ofNat shift
      let kind := classifyLshiftDivModr x y shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-valid"
        #[intV x, intV y, intV shiftI], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let shiftI := Int.ofNat shift
      let kind := classifyLshiftDivModr x y shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-valid"
        #[intV x, intV y, intV shiftI], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let shiftI := Int.ofNat shift
      let kind := classifyLshiftDivModr x y shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-uniform-shift"
        #[intV x, intV y, intV shiftI], r4)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftUniform r2
      let shiftI := Int.ofNat shift
      let kind := classifyLshiftDivModr x 0 shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/divzero"
        #[intV x, intV 0, intV shiftI], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyLshiftDivModr x y 0
      (mkCase s!"fuzz/shape-{shape}/{kind}/tie-shift0"
        #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyLshiftDivModr x (y * 2) 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/tie-shift1"
        #[intV x, intV (y * 2), intV 1], r3)
    else if shape = 6 then
      let kind := classifyLshiftDivModr maxInt257 1 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/overflow-max-shift1"
        #[intV maxInt257, intV 1, intV 1], rng1)
    else if shape = 7 then
      let kind := classifyLshiftDivModr minInt257 (-2) 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/overflow-min-shift1-neg2"
        #[intV minInt257, intV (-2), intV 1], rng1)
    else if shape = 8 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      (mkCase s!"fuzz/shape-{shape}/zero/x-zero"
        #[intV 0, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      let kind := classifyLshiftDivModr x 1 (Int.ofNat shift)
      (mkCase s!"fuzz/shape-{shape}/{kind}/div-by-one"
        #[intV x, intV 1, intV (Int.ofNat shift)], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      let kind := classifyLshiftDivModr x (-1) (Int.ofNat shift)
      (mkCase s!"fuzz/shape-{shape}/{kind}/div-by-neg-one"
        #[intV x, intV (-1), intV (Int.ofNat shift)], r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/range/shift-neg-one"
        #[intV 7, intV 5, intV (-1)], rng1)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/range/shift-257"
        #[intV 7, intV 5, intV 257], rng1)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-arg"
        #[intV x], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (_, r3) := pickShiftUniform r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV 1, .null], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-second"
        #[intV x, .cell Cell.empty, intV (Int.ofNat shift)], r3)
    else if shape = 17 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-third"
        #[.null, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-shift"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-y"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 20 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-x"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num huge], r4)
    else if shape = 22 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-x"
        #[IntVal.num huge, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/out-of-range/program-y"
        #[IntVal.num x, IntVal.num huge, IntVal.num (Int.ofNat shift)], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftDivModrId
  unit := #[
    { name := "unit/ok/nearest-rounding-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 5, -1),
            (-7, 3, 1, -5, 1),
            (7, -3, 1, -5, -1),
            (-7, -3, 1, 5, 1),
            (5, 2, 0, 3, -1),
            (-5, 2, 0, -2, -1),
            (5, -2, 0, -2, 1),
            (-5, -2, 0, 3, 1),
            (1, 2, 0, 1, -1),
            (-1, 2, 0, 0, -1),
            (1, -2, 0, 0, 1),
            (-1, -2, 0, 1, 1),
            (7, 5, 2, 6, -2),
            (-7, 5, 2, -6, 2),
            (7, -5, 2, -6, -2),
            (-7, -5, 2, 6, 2),
            (42, 7, 3, 48, 0),
            (0, 5, 8, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectLshiftDivModr s!"({x}<<{shift})/{y}" x y shift q r }
    ,
    { name := "unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257, 0),
            (maxInt257, -1, 0, -maxInt257, 0),
            (minInt257, 1, 0, minInt257, 0),
            (minInt257 + 1, -1, 0, maxInt257, 0),
            (maxInt257, 2, 0, pow2 255, -1),
            (minInt257, 2, 0, -(pow2 255), 0),
            (minInt257, -2, 0, pow2 255, 0),
            (maxInt257, 2, 1, maxInt257, 0),
            (minInt257, 2, 1, minInt257, 0),
            (1, maxInt257, 256, 1, 1),
            (-1, maxInt257, 256, -1, -1),
            (1, minInt257, 256, -1, 0),
            (-1, minInt257, 256, 1, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectLshiftDivModr s!"boundary/({x}<<{shift})/{y}" x y shift q r }
    ,
    { name := "unit/error/divzero-overflow-and-range-gates"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runLshiftDivModrDirect #[intV 5, intV 0, intV 3]) .intOv
        expectErr "divzero/zero-over-zero"
          (runLshiftDivModrDirect #[intV 0, intV 0, intV 8]) .intOv
        expectErr "overflow/max-shift1-div1"
          (runLshiftDivModrDirect #[intV maxInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-shift1-div-neg2"
          (runLshiftDivModrDirect #[intV minInt257, intV (-2), intV 1]) .intOv
        expectErr "overflow/min-shift256-div-neg1"
          (runLshiftDivModrDirect #[intV minInt257, intV (-1), intV 256]) .intOv
        expectErr "range/shift-neg-before-y-pop"
          (runLshiftDivModrDirect #[.null, .cell Cell.empty, intV (-1)]) .rangeChk
        expectErr "range/shift-257-before-x-pop"
          (runLshiftDivModrDirect #[.null, intV 3, intV 257]) .rangeChk }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runLshiftDivModrDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runLshiftDivModrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runLshiftDivModrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "type/pop-shift-first"
          (runLshiftDivModrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second"
          (runLshiftDivModrDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third"
          (runLshiftDivModrDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-shift-before-y-when-both-non-int"
          (runLshiftDivModrDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/pop-y-before-x-after-shift-int"
          (runLshiftDivModrDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLshiftDivModrDispatchFallback #[]) #[intV 2601] }
  ]
  oracle := #[
    mkCase "ok/round/inexact-pos-pos" #[intV 7, intV 3, intV 1],
    mkCase "ok/round/inexact-neg-pos" #[intV (-7), intV 3, intV 1],
    mkCase "ok/round/inexact-pos-neg" #[intV 7, intV (-3), intV 1],
    mkCase "ok/round/inexact-neg-neg" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/tie/pos-over-pos-two-shift0" #[intV 5, intV 2, intV 0],
    mkCase "ok/tie/neg-over-pos-two-shift0" #[intV (-5), intV 2, intV 0],
    mkCase "ok/tie/pos-over-neg-two-shift0" #[intV 5, intV (-2), intV 0],
    mkCase "ok/tie/neg-over-neg-two-shift0" #[intV (-5), intV (-2), intV 0],
    mkCase "ok/tie/pos-over-pos-two-shift1" #[intV 1, intV 4, intV 1],
    mkCase "ok/tie/neg-over-pos-two-shift1" #[intV (-1), intV 4, intV 1],
    mkCase "ok/tie/pos-over-neg-two-shift1" #[intV 1, intV (-4), intV 1],
    mkCase "ok/tie/neg-over-neg-two-shift1" #[intV (-1), intV (-4), intV 1],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 7, intV 3],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 7, intV 3],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-7), intV 3],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-7), intV 3],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 5, intV 8],
    mkCase "ok/boundary/max-shift0-div1" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/max-shift0-div-neg1" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/boundary/min-shift0-div1" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-plus-one-shift0-div-neg1" #[intV (minInt257 + 1), intV (-1), intV 0],
    mkCase "ok/boundary/max-shift0-div2" #[intV maxInt257, intV 2, intV 0],
    mkCase "ok/boundary/min-shift0-div2" #[intV minInt257, intV 2, intV 0],
    mkCase "ok/boundary/min-shift0-div-neg2" #[intV minInt257, intV (-2), intV 0],
    mkCase "ok/boundary/max-shift1-div2" #[intV maxInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-shift1-div2" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/boundary/one-shift256-div-max" #[intV 1, intV maxInt257, intV 256],
    mkCase "ok/boundary/neg-one-shift256-div-max" #[intV (-1), intV maxInt257, intV 256],
    mkCase "ok/boundary/one-shift256-div-min" #[intV 1, intV minInt257, intV 256],
    mkCase "ok/boundary/neg-one-shift256-div-min" #[intV (-1), intV minInt257, intV 256],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0, intV 3],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 8],
    mkCase "overflow/max-shift1-div1" #[intV maxInt257, intV 1, intV 1],
    mkCase "overflow/min-shift1-div-neg2" #[intV minInt257, intV (-2), intV 1],
    mkCase "overflow/min-shift256-div-neg1" #[intV minInt257, intV (-1), intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "type/pop-shift-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-shift-before-y-when-both-non-int" #[intV 1, .null, .cell Cell.empty],
    mkCase "error-order/pop-y-before-x-after-shift-int" #[.null, .cell Cell.empty, intV 1],
    mkCase "range/shift-negative" #[intV 5, intV 7, intV (-1)],
    mkCase "range/shift-257" #[intV 5, intV 7, intV 257],
    mkCase "error-order/range-before-y-type" #[intV 5, .null, intV (-1)],
    mkCase "error-order/range-before-x-type" #[.null, intV 5, intV 257],
    mkInputCase "nan/program-shift" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInputCase "nan/program-y" #[IntVal.num 5, IntVal.nan, IntVal.num 3],
    mkInputCase "nan/program-x" #[IntVal.nan, IntVal.num 5, IntVal.num 3],
    mkInputCase "overflow/program-shift-out-of-range-pos" #[IntVal.num 5, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkInputCase "overflow/program-shift-out-of-range-neg" #[IntVal.num 5, IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkInputCase "overflow/program-y-out-of-range" #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 3],
    mkInputCase "overflow/program-x-out-of-range" #[IntVal.num (minInt257 - 1), IntVal.num 5, IntVal.num 3],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 2]
      #[.pushInt (.num lshiftDivModrSetGasExact), .tonEnvOp .setGasLimit, lshiftDivModrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 2]
      #[.pushInt (.num lshiftDivModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftDivModrInstr]
  ]
  fuzz := #[
    { seed := 2026020810
      count := 700
      gen := genLshiftDivModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTDIVMODR
