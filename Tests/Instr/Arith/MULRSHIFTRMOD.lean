import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTRMOD

/-
MULRSHIFTRMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, opcode registration in `register_add_mul_ops`)

Branch counts used for this suite:
- Lean generic `.shrMod` helper: 11 branch sites / 25 terminal outcomes
  (mul-vs-non-mul split; stack precheck; runtime-vs-immediate shift source;
   range gate; add-mode arity; operand-shape split; shift-zero round remap;
   round validity; `d` switch; NaN fallback arity).
- Lean specialization (`mul=true`, `add=false`, `d=3`, `round=0`, `quiet=false`):
  8 reachable terminal outcomes (`ok`, `stkUnd`, `typeChk` on `z`/`y`/`x`,
  `rangeChk`, `intOv` from NaN funnel, `intOv` from quotient overflow).
- C++ `exec_mulshrmod`: 8 branch sites / 17 aligned terminal outcomes
  (mode/immediate gate, add remap gate, invalid-opcode guard, underflow guard,
   runtime range gate, zero-shift remap, global-version invalid-input guard,
   `d` switch).

Key risk areas covered:
- pop/error order is `z` (shift), then `y`, then `x`;
- `rangeChk` precedence over later operand type checks when `z` is invalid;
- nearest rounding (`roundMode=0`) tie behavior and `q`/`r` output order;
- shift boundary behavior at `0` and `256`;
- non-quiet NaN/out-of-range input injection via program (`PUSHINT`) only;
- signed-257 overflow behavior for large products and shift-0 quotient;
- deterministic gas boundary (`PUSHINT n; SETGASLIMIT; MULRSHIFTRMOD`).
-/

private def mulrshiftrmodId : InstrId := { name := "MULRSHIFTRMOD" }

private def mulrshiftrmodInstr : Instr :=
  .arithExt (.shrMod true false 3 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftrmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulrshiftrmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[mulrshiftrmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runMulrshiftrmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftrmodInstr stack

private def runMulrshiftrmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 3321)) stack

private def mulrshiftrmodSetGasExact : Int :=
  computeExactGasBudget mulrshiftrmodInstr

private def mulrshiftrmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftrmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 7, 8, 15, 31, 32, 63, 64, 127, 128, 255, 256]

private def outOfRangeInputPool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def classifyMulrshiftrmod (x y : Int) (shift : Nat) : String :=
  let t : Int := x * y
  let roundMode : Int := if shift = 0 then -1 else 0
  let q := rshiftPow2Round t shift roundMode
  let r := modPow2Round t shift roundMode
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "overflow"
  else if t = 0 then
    "zero"
  else if r = 0 then
    "exact"
  else
    "inexact"

private def genMulrshiftrmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickShiftBoundary r3
      let kind := classifyMulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/{kind}/boundary-boundary-boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickShiftBoundary r3
      let kind := classifyMulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/{kind}/random-random-boundary-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickShiftMixed r3
      let kind := classifyMulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/{kind}/boundary-random-random-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickShiftMixed r3
      let kind := classifyMulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/{kind}/random-boundary-random-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/shift-negative"
        #[IntVal.num x, IntVal.num y, IntVal.num (-1)], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/shift-gt-256"
        #[IntVal.num x, IntVal.num y, IntVal.num 257], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-ints" #[intV x, intV y], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, .null], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-second" #[intV x, .cell Cell.empty, intV (Int.ofNat z)], r3)
    else if shape = 11 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-third" #[.null, intV y, intV (Int.ofNat z)], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/shift-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat z)], r3)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat z)], r3)
    else if shape = 15 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/overflow/min-neg1-shift0"
        #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0], rng1)
    else if shape = 16 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/overflow/max-max-shift1"
        #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1], rng1)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/zero/left-factor"
        #[IntVal.num 0, IntVal.num y, IntVal.num (Int.ofNat z)], r3)
    else if shape = 18 then
      let (oor, r2) := pickFromPool outOfRangeInputPool rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/program-x"
        #[IntVal.num oor, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (oor, r3) := pickFromPool outOfRangeInputPool r2
      let (z, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/program-y"
        #[IntVal.num x, IntVal.num oor, IntVal.num (Int.ofNat z)], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftrmodId
  unit := #[
    { name := "unit/direct/round-nearest-sign-ties-and-output-order"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 11, -1),
            (-7, 3, 1, -10, -1),
            (7, -3, 1, -10, -1),
            (-7, -3, 1, 11, -1),
            (5, 5, 1, 13, -1),
            (-5, 5, 1, -12, -1),
            (5, -5, 1, -12, -1),
            (-5, -5, 1, 13, -1),
            (1, 1, 1, 1, -1),
            (-1, 1, 1, 0, -1),
            (1, -1, 1, 0, -1),
            (-1, -1, 1, 1, -1),
            (42, 6, 3, 32, -4),
            (-42, 6, 3, -31, -4),
            (42, -6, 3, -31, -4),
            (-42, -6, 3, 32, -4),
            (0, 9, 7, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})>>{shift}"
            (runMulrshiftrmodDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/direct/shift-boundary-successes"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257, 0),
            (minInt257, 1, 0, minInt257, 0),
            (maxInt257, 1, 256, 1, -1),
            (maxInt257, -1, 256, -1, 1),
            (minInt257, 1, 256, -1, 0),
            (minInt257 + 1, 1, 256, -1, 1),
            (pow2 255, 1, 256, 1, -(pow2 255)),
            (-(pow2 255), 1, 256, 0, -(pow2 255))
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})>>{shift}"
            (runMulrshiftrmodDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/error/range-underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runMulrshiftrmodDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runMulrshiftrmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-ints" (runMulrshiftrmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "type/pop-z-first" (runMulrshiftrmodDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulrshiftrmodDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMulrshiftrmodDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "range/shift-negative" (runMulrshiftrmodDirect #[intV 7, intV 3, intV (-1)]) .rangeChk
        expectErr "range/shift-too-large" (runMulrshiftrmodDirect #[intV 7, intV 3, intV 257]) .rangeChk
        expectErr "error-order/shift-range-before-y-type"
          (runMulrshiftrmodDirect #[intV 7, .null, intV 257]) .rangeChk }
    ,
    { name := "unit/error/intov-from-overflow"
      run := do
        expectErr "overflow/min-neg1-shift0"
          (runMulrshiftrmodDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "overflow/max-max-shift1"
          (runMulrshiftrmodDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-min-shift1"
          (runMulrshiftrmodDirect #[intV minInt257, intV minInt257, intV 1]) .intOv }
    ,
    { name := "unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulrshiftrmodDispatchFallback #[]) #[intV 3321] }
  ]
  oracle := #[
    mkCaseFromIntVals "ok/round/sign/pos-pos-inexact" #[IntVal.num 7, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "ok/round/sign/neg-pos-inexact" #[IntVal.num (-7), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "ok/round/sign/pos-neg-inexact" #[IntVal.num 7, IntVal.num (-3), IntVal.num 1],
    mkCaseFromIntVals "ok/round/sign/neg-neg-inexact" #[IntVal.num (-7), IntVal.num (-3), IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/pos-pos-half" #[IntVal.num 5, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/neg-pos-half" #[IntVal.num (-5), IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/pos-neg-half" #[IntVal.num 5, IntVal.num (-5), IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/neg-neg-half" #[IntVal.num (-5), IntVal.num (-5), IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/neg-pos-near-zero" #[IntVal.num (-1), IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/pos-neg-near-zero" #[IntVal.num 1, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "ok/round/tie/neg-neg-near-zero" #[IntVal.num (-1), IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "ok/exact/shift-zero-floor-remap" #[IntVal.num 42, IntVal.num 6, IntVal.num 0],
    mkCaseFromIntVals "ok/exact/zero-left-factor" #[IntVal.num 0, IntVal.num 17, IntVal.num 9],
    mkCaseFromIntVals "ok/exact/zero-right-factor" #[IntVal.num 17, IntVal.num 0, IntVal.num 9],
    mkCaseFromIntVals "ok/boundary/max-times-one-shift-zero" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 0],
    mkCaseFromIntVals "ok/boundary/min-times-one-shift-zero" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 0],
    mkCaseFromIntVals "ok/boundary/max-times-one-shift-256" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/max-times-neg-one-shift-256" #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/min-times-one-shift-256" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/min-plus-one-times-one-shift-256"
      #[IntVal.num (minInt257 + 1), IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/pow2-255-times-one-shift-256"
      #[IntVal.num (pow2 255), IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "ok/boundary/neg-pow2-255-times-one-shift-256"
      #[IntVal.num (-(pow2 255)), IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "overflow/min-neg1-shift0" #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0],
    mkCaseFromIntVals "overflow/max-max-shift1" #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1],
    mkCaseFromIntVals "overflow/min-min-shift1" #[IntVal.num minInt257, IntVal.num minInt257, IntVal.num 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "underflow/two-ints" #[intV 1, intV 2],
    mkCase "type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/shift-range-before-y-type" #[intV 7, .null, intV 257],
    mkCaseFromIntVals "range/shift-negative" #[IntVal.num 7, IntVal.num 3, IntVal.num (-1)],
    mkCaseFromIntVals "range/shift-gt-256" #[IntVal.num 7, IntVal.num 3, IntVal.num 257],
    mkCaseFromIntVals "nan/shift-via-program" #[IntVal.num 7, IntVal.num 3, IntVal.nan],
    mkCaseFromIntVals "nan/y-via-program" #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "nan/x-via-program" #[IntVal.nan, IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "range/program/x-out-of-range"
      #[IntVal.num (maxInt257 + 1), IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "range/program/y-out-of-range"
      #[IntVal.num 7, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulrshiftrmodSetGasExact), .tonEnvOp .setGasLimit, mulrshiftrmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulrshiftrmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftrmodInstr]
  ]
  fuzz := #[
    { seed := 2026020818
      count := 700
      gen := genMulrshiftrmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTRMOD
