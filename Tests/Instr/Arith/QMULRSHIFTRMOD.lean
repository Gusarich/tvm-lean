import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULRSHIFTRMOD

/-
QMULRSHIFTRMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 3 0 true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, shift-zero floor rewrite)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, opcode wiring in `register_add_mul_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (QMULRSHIFTRMOD specialization):
- Lean: ~9 branch sites / ~13 terminal outcomes
  (dispatch/fallback; depth precheck; runtime shift pop type/ok; y-pop type/ok;
   x-pop type/ok; shift range gate to quiet-NaN pair; shift=0 round rewrite;
   numeric-vs-NaN arithmetic path; dual quiet pushes with finite-vs-overflow split).
- C++: ~9 branch sites / ~15 aligned terminal outcomes
  (`check_underflow`; runtime `pop_long`; global-version/range gate;
   `z==0` round rewrite; `pop_int` order y->x; invalid-input quiet funnel;
   `d==3` quotient+remainder push with independent quiet-overflow handling).

Key risk areas covered:
- pop/error precedence: shift pops first, then y, then x (including with bad shift);
- quiet range handling (`z<0 || z>256` and `z=NaN`) must return NaN-pair, not `rangeChk`;
- shift-zero rewrite to floor mode (`roundMode := -1`) before q/r computation;
- nearest rounding (`R`) tie direction and q/r output ordering (`q` then `r`);
- quiet overflow funnel: q may become NaN while r stays finite (e.g., `min* -1, z=0`);
- boundary shifts (`0`, `256`) and signed-257 edge factors (`±2^256`, `2^255`);
- oracle safety: NaN and signed-257-out-of-range values injected via program prelude only.
-/

private def qmulrshiftrmodId : InstrId := { name := "QMULRSHIFTRMOD" }

private def qmulrshiftrmodInstr : Instr :=
  .arithExt (.shrMod true false 3 0 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulrshiftrmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmulrshiftrmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulrshiftrmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQmulrshiftrmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulrshiftrmodInstr stack

private def runQmulrshiftrmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 3417)) stack

private def qmulrshiftrmodSetGasExact : Int :=
  computeExactGasBudget qmulrshiftrmodInstr

private def qmulrshiftrmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulrshiftrmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 7, 8, 15, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def classifyQmulrshiftrmod (x y : Int) (shift : Nat) : String :=
  let t : Int := x * y
  let roundMode : Int := if shift = 0 then -1 else 0
  let q := rshiftPow2Round t shift roundMode
  let r := modPow2Round t shift roundMode
  if !intFitsSigned257 q then
    "q-overflow"
  else if t = 0 then
    "zero"
  else if r = 0 then
    "exact"
  else
    "inexact"

private def genQmulrshiftrmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickShiftBoundary r3
      let kind := classifyQmulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/{kind}/boundary-boundary-boundary"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickShiftBoundary r3
      let kind := classifyQmulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/{kind}/signed-signed-boundary-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickShiftMixed r3
      let kind := classifyQmulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/{kind}/boundary-signed-random-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickShiftMixed r3
      let kind := classifyQmulrshiftrmod x y z
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/{kind}/signed-boundary-random-shift"
        #[IntVal.num x, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQmulrshiftrmod x y 0
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/shift-zero-floor-rewrite"
        #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/quiet/range/shift-negative-via-program"
        #[intV x, intV y] #[.pushInt (.num (-1)), qmulrshiftrmodInstr], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/quiet/range/shift-over256-via-program"
        #[intV x, intV y] #[.pushInt (.num 257), qmulrshiftrmodInstr], r3)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-ints" #[intV x, intV y], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV y, .null], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-second"
        #[intV x, .cell Cell.empty, intV (Int.ofNat z)], r3)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-third"
        #[.null, intV y, intV (Int.ofNat z)], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/shift-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat z)], r3)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat z)], r3)
    else if shape = 16 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/overflow/min-neg1-shift0"
        #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0], rng1)
    else if shape = 17 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/overflow/max-max-shift1"
        #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1], rng1)
    else if shape = 18 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/zero/left-factor"
        #[IntVal.num 0, IntVal.num y, IntVal.num (Int.ofNat z)], r3)
    else if shape = 19 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num (Int.ofNat z)], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num (Int.ofNat z)], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-invalid-before-y-type-via-program"
        #[intV x, .null] #[.pushInt (.num (-1)), qmulrshiftrmodInstr], r2)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-invalid-before-x-type-via-program"
        #[.null, intV y] #[.pushInt (.num 257), qmulrshiftrmodInstr], r2)
    else
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num (-1)), qmulrshiftrmodInstr], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulrshiftrmodId
  unit := #[
    { name := "unit/ok/nearest-rounding-sign-ties-and-output-order"
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
            (42, 6, 3, 32, -4),
            (-42, 6, 3, -31, -4),
            (42, -6, 3, -31, -4),
            (-42, -6, 3, 32, -4),
            (42, 6, 0, 252, 0),
            (-42, 6, 0, -252, 0),
            (0, 9, 7, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})>>{shift}"
            (runQmulrshiftrmodDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/ok/shift-boundary-and-stack-shape"
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
          expectOkStack s!"boundary/({x}*{y})>>{shift}"
            (runQmulrshiftrmodDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r]
        expectOkStack "ok/order/below-null-preserved"
          (runQmulrshiftrmodDirect #[.null, intV 7, intV 3, intV 1])
          #[.null, intV 11, intV (-1)]
        expectOkStack "ok/order/below-cell-preserved"
          (runQmulrshiftrmodDirect #[.cell Cell.empty, intV (-7), intV 3, intV 1])
          #[.cell Cell.empty, intV (-10), intV (-1)] }
    ,
    { name := "unit/quiet/range-and-nan-funnel-to-nan-pair"
      run := do
        expectOkStack "quiet/range/shift-negative"
          (runQmulrshiftrmodDirect #[intV 7, intV 3, intV (-1)]) #[.int .nan, .int .nan]
        expectOkStack "quiet/range/shift-over256"
          (runQmulrshiftrmodDirect #[intV 7, intV 3, intV 257]) #[.int .nan, .int .nan]
        expectOkStack "quiet/range/shift-nan"
          (runQmulrshiftrmodDirect #[intV 7, intV 3, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/y"
          (runQmulrshiftrmodDirect #[intV 7, .int .nan, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/x"
          (runQmulrshiftrmodDirect #[.int .nan, intV 7, intV 1]) #[.int .nan, .int .nan] }
    ,
    { name := "unit/quiet/overflow-q-to-nan-r-preserved"
      run := do
        expectOkStack "quiet/overflow/min-neg1-shift0"
          (runQmulrshiftrmodDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/max-max-shift1"
          (runQmulrshiftrmodDirect #[intV maxInt257, intV maxInt257, intV 1]) #[.int .nan, intV (-1)]
        expectOkStack "quiet/overflow/min-min-shift1"
          (runQmulrshiftrmodDirect #[intV minInt257, intV minInt257, intV 1]) #[.int .nan, intV 0] }
    ,
    { name := "unit/error-order/underflow-and-pop-precedence"
      run := do
        expectErr "underflow/empty" (runQmulrshiftrmodDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQmulrshiftrmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-ints" (runQmulrshiftrmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "type/pop-shift-first" (runQmulrshiftrmodDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runQmulrshiftrmodDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runQmulrshiftrmodDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/shift-invalid-before-y-type"
          (runQmulrshiftrmodDirect #[intV 7, .null, intV (-1)]) .typeChk
        expectErr "error-order/shift-invalid-before-x-type"
          (runQmulrshiftrmodDirect #[.null, intV 7, intV 257]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmulrshiftrmodDispatchFallback #[]) #[intV 3417] }
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
    mkCase "ok/order/below-null-preserved" #[.null, intV 7, intV 3, intV 1],
    mkCase "ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-7), intV 3, intV 1],
    mkCaseFromIntVals "quiet/overflow/min-neg1-shift0" #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 0],
    mkCaseFromIntVals "quiet/overflow/max-max-shift1" #[IntVal.num maxInt257, IntVal.num maxInt257, IntVal.num 1],
    mkCaseFromIntVals "quiet/overflow/min-min-shift1" #[IntVal.num minInt257, IntVal.num minInt257, IntVal.num 1],
    mkCase "quiet/range/shift-negative-via-program" #[intV 7, intV 3]
      #[.pushInt (.num (-1)), qmulrshiftrmodInstr],
    mkCase "quiet/range/shift-over256-via-program" #[intV 7, intV 3]
      #[.pushInt (.num 257), qmulrshiftrmodInstr],
    mkCaseFromIntVals "quiet/range/shift-nan-via-program" #[IntVal.num 7, IntVal.num 3, IntVal.nan],
    mkCaseFromIntVals "quiet/nan/shift-via-program" #[IntVal.num 7, IntVal.num 3, IntVal.nan],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[IntVal.nan, IntVal.num 7, IntVal.num 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "underflow/two-ints" #[intV 1, intV 2],
    mkCase "type/pop-shift-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/shift-invalid-before-y-type-via-program" #[intV 7, .null]
      #[.pushInt (.num (-1)), qmulrshiftrmodInstr],
    mkCase "error-order/shift-invalid-before-x-type-via-program" #[.null, intV 7]
      #[.pushInt (.num 257), qmulrshiftrmodInstr],
    mkCaseFromIntVals "error-order/pushint-range-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-range-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-range-y-high-before-op"
      #[IntVal.num 7, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-range-y-low-before-op"
      #[IntVal.num 7, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-range-both-before-op"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num 1],
    mkCase "error-order/underflow-before-range-via-program" #[]
      #[.pushInt (.num (-1)), qmulrshiftrmodInstr],
    mkCase "gas/exact/cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulrshiftrmodSetGasExact), .tonEnvOp .setGasLimit, qmulrshiftrmodInstr],
    mkCase "gas/exact-minus-one/out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulrshiftrmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulrshiftrmodInstr]
  ]
  fuzz := #[
    { seed := 2026020850
      count := 700
      gen := genQmulrshiftrmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTRMOD
