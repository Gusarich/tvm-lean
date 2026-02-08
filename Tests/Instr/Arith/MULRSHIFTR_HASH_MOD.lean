import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTR_HASH_MOD

/-
MULRSHIFTR#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulShrModConst.lean`
    (`execInstrArithMulShrModConst`, target hash-immediate execution path)
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, executable oracle/fuzz bridge via runtime-shift equivalent)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, nearest-round q/r invariants)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (decode family for `MUL{RSHIFT,MODPOW2,RSHIFTMOD}#`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, rounding and q/r output behavior)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (underflow/type pop discipline in arithmetic handlers)

Branch/terminal counts used in this suite:
- Target hash-immediate handler (`.mulShrModConst 3 0 z`):
  ~7 branch sites / ~12 terminal outcomes
  (dispatch/fallback, y-pop underflow/type split, x-pop underflow/type split,
   numeric-vs-invalid operand split, `d` switch, invalid-operand NaN fallback split,
   non-quiet signed-257 push overflow funnels on q/r).
- Executable oracle/fuzz bridge (`.shrMod true false 3 0 false none`, `MULRSHIFTRMOD`):
  ~8 branch sites / ~13 terminal outcomes
  (stack precheck, runtime-shift parse/range split, pop-order `z→y→x`,
   `shift=0` round remap gate, numeric-vs-invalid funnel, q/r push overflow).

Shared helper usage:
- `Tests.Harness.Gen.Arith` for signed-257 generators/pools,
  prelude-only NaN/out-of-range injection (`oracleIntInputsToStackOrProgram`),
  and exact gas-budget helpers.

Key risk areas covered:
- hash-immediate semantics and pop-order for the target (`y` then `x`, no runtime shift pop);
- nearest rounding tie behavior and signed-variation matrix for q/r results;
- immediate boundary shifts (`1`, `256`) and signed-257 extremes;
- deterministic non-quiet overflow (`intOv`) from large products;
- exact gas cliff (`exact` vs `exact-minus-one`) in oracle path;
- NaN/out-of-range injection only via prelude program prefixes.
-/

private def mulrshiftrHashModId : InstrId := { name := "MULRSHIFTR#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulrshiftrHashModInstr (shift : Nat) : Instr :=
  .mulShrModConst 3 0 shift

private def mulrshiftrmodOracleInstr : Instr :=
  .arithExt (.shrMod true false 3 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftrmodOracleInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulrshiftrHashModId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[mulrshiftrmodOracleInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runMulrshiftrHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulShrModConst (mkMulrshiftrHashModInstr shift) stack

private def runMulrshiftrHashModDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulShrModConst .add (VM.push (intV 9013)) stack

private def mulrshiftrHashModGasProbeInstr : Instr :=
  mulrshiftrmodOracleInstr

private def mulrshiftrHashModSetGasExact : Int :=
  computeExactGasBudget mulrshiftrHashModGasProbeInstr

private def mulrshiftrHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftrHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def nearTiePool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def outOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftInRange rng1

private def pickNearTie (rng : StdGen) : Int × StdGen :=
  pickFromPool nearTiePool rng

private def pickOutOfRange (rng : StdGen) : Int × StdGen :=
  pickFromPool outOfRangePool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (useCell, rng') := randBool rng
  ((if useCell then .cell Cell.empty else .null), rng')

private def classifyMulrshiftrHashMod (x y : Int) (shift : Nat) : String :=
  let t : Int := x * y
  let q := rshiftPow2Round t shift 0
  let r := modPow2Round t shift 0
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "overflow"
  else if t = 0 then
    "zero"
  else if r = 0 then
    "exact"
  else
    "inexact"

private def genMulrshiftrHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulrshiftrHashMod x y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-boundary-shift-boundary"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulrshiftrHashMod x y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/random-random-shift-boundary"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyMulrshiftrHashMod x y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-random-shift-random"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyMulrshiftrHashMod x y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/random-boundary-shift-random"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      let (x, r2) := pickNearTie rng1
      let (y, r3) := pickNearTie r2
      let kind := classifyMulrshiftrHashMod x y 1
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/sign-variation-shift1"
        #[intV x, intV y, intV 1], r3)
    else if shape = 5 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyMulrshiftrHashMod 0 y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/zero-left-factor"
        #[intV 0, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyMulrshiftrHashMod x 0 shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/zero-right-factor"
        #[intV x, intV 0, intV (Int.ofNat shift)], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/ok/pop-order/lower-null-preserved"
        #[.null, intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"/fuzz/shape-{shape}/ok/pop-order/lower-cell-preserved"
        #[.cell Cell.empty, intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 9 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-item" #[intV x], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (badY, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-first-non-int"
        #[intV x, badY, intV (Int.ofNat shift)], r4)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (badX, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-second-non-int"
        #[badX, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 13 then
      let (shift, r2) := pickShiftBoundary rng1
      let (badX, r3) := pickNonInt r2
      let (badY, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        #[badX, badY, intV (Int.ofNat shift)], r4)
    else if shape = 14 then
      (mkCase s!"/fuzz/shape-{shape}/intov/overflow-max-max-shift1"
        #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 15 then
      (mkCase s!"/fuzz/shape-{shape}/intov/overflow-min-min-shift1"
        #[intV minInt257, intV minInt257, intV 1], rng1)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-nan-x-via-prelude"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-nan-y-via-prelude"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 18 then
      let (xo, r2) := pickOutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-via-prelude"
        #[IntVal.num xo, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickOutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-via-prelude"
        #[IntVal.num x, IntVal.num yo, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 20 then
      let (useMax, r2) := randBool rng1
      let (useNeg, r3) := randBool r2
      let x := if useMax then maxInt257 else minInt257
      let y := if useNeg then -1 else 1
      let kind := classifyMulrshiftrHashMod x y 256
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/extreme-factor-shift256"
        #[intV x, intV y, intV 256], r3)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyMulrshiftrHashMod x y 1
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/random-sign-variation-shift1"
        #[intV x, intV y, intV 1], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftrHashModId
  unit := #[
    { name := "/unit/ok/round-nearest-sign-variation-and-remainder"
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
          expectOkStack s!"/unit/ok/x={x}/y={y}/shift={shift}"
            (runMulrshiftrHashModDirect shift #[intV x, intV y])
            #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-shifts-and-signed257-extremes"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 1, 1, pow2 255, -1),
            (minInt257, 1, 1, -(pow2 255), 0),
            (maxInt257, -1, 1, 1 - (pow2 255), -1),
            (minInt257, -1, 1, pow2 255, 0),
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
          expectOkStack s!"/unit/boundary/x={x}/y={y}/shift={shift}"
            (runMulrshiftrHashModDirect shift #[intV x, intV y])
            #[intV q, intV r] }
    ,
    { name := "/unit/pop-order/hash-immediate-preserves-below-stack"
      run := do
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMulrshiftrHashModDirect 1 #[.null, intV 7, intV 3])
          #[.null, intV 11, intV (-1)]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMulrshiftrHashModDirect 2 #[.cell Cell.empty, intV (-7), intV 3])
          #[.cell Cell.empty, intV (-5), intV (-1)] }
    ,
    { name := "/unit/error/underflow-type-and-pop-ordering"
      run := do
        expectErr "/unit/underflow/empty-stack"
          (runMulrshiftrHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int"
          (runMulrshiftrHashModDirect 1 #[intV 5]) .stkUnd
        expectErr "/unit/error-order/type-before-underflow-on-single-non-int"
          (runMulrshiftrHashModDirect 1 #[.null]) .typeChk
        expectErr "/unit/type/pop-y-first-null"
          (runMulrshiftrHashModDirect 1 #[intV 5, .null]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runMulrshiftrHashModDirect 1 #[.null, intV 5]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runMulrshiftrHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/intov-overflow-from-large-products"
      run := do
        expectErr "/unit/intov/max-max-shift1"
          (runMulrshiftrHashModDirect 1 #[intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/intov/min-min-shift1"
          (runMulrshiftrHashModDirect 1 #[intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/intov/max-min-shift1"
          (runMulrshiftrHashModDirect 1 #[intV maxInt257, intV minInt257]) .intOv }
    ,
    { name := "/unit/dispatch/non-mulrshiftr-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulrshiftrHashModDispatchFallback #[]) #[intV 9013] }
  ]
  oracle := #[
    mkCaseFromIntVals "/ok/round/sign/pos-pos-shift1"
      #[IntVal.num 7, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/ok/round/sign/neg-pos-shift1"
      #[IntVal.num (-7), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/ok/round/sign/pos-neg-shift1"
      #[IntVal.num 7, IntVal.num (-3), IntVal.num 1],
    mkCaseFromIntVals "/ok/round/sign/neg-neg-shift1"
      #[IntVal.num (-7), IntVal.num (-3), IntVal.num 1],
    mkCaseFromIntVals "/ok/round/tie/plus-half"
      #[IntVal.num 1, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/round/tie/minus-half-to-plus-inf"
      #[IntVal.num (-1), IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/round/tie/plus-three-halves"
      #[IntVal.num 3, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/round/tie/minus-three-halves"
      #[IntVal.num (-3), IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/exact/zero-left-factor"
      #[IntVal.num 0, IntVal.num 7, IntVal.num 9],
    mkCaseFromIntVals "/ok/exact/zero-right-factor"
      #[IntVal.num 7, IntVal.num 0, IntVal.num 9],
    mkCaseFromIntVals "/ok/boundary/max-times-one-shift1"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/boundary/min-times-one-shift1"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "/ok/boundary/max-times-neg-one-shift1"
      #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "/ok/boundary/min-times-neg-one-shift1"
      #[IntVal.num minInt257, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "/ok/boundary/max-times-one-shift256"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "/ok/boundary/min-times-one-shift256"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "/ok/boundary/min-plus-one-times-one-shift256"
      #[IntVal.num (minInt257 + 1), IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "/ok/boundary/pow2-255-times-one-shift256"
      #[IntVal.num (pow2 255), IntVal.num 1, IntVal.num 256],
    mkCaseFromIntVals "/ok/boundary/neg-pow2-255-times-one-shift256"
      #[IntVal.num (-(pow2 255)), IntVal.num 1, IntVal.num 256],
    mkCase "/ok/pop-order/lower-null-preserved"
      #[.null, intV 7, intV 3, intV 1],
    mkCase "/ok/pop-order/lower-cell-preserved"
      #[.cell Cell.empty, intV (-7), intV 3, intV 2],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-item" #[intV 7],
    mkCase "/type/pop-y-first-null"
      #[intV 7, .null, intV 1],
    mkCase "/type/pop-x-second-null"
      #[.null, intV 7, intV 1],
    mkCase "/error-order/pop-y-before-x-when-both-non-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "/intov/overflow-max-max-shift1"
      #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "/intov/overflow-min-min-shift1"
      #[intV minInt257, intV minInt257, intV 1],
    mkCaseFromIntVals "/error-order/pushint-nan-x-via-prelude"
      #[IntVal.nan, IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-nan-y-via-prelude"
      #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-via-prelude"
      #[IntVal.num (maxInt257 + 1), IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-via-prelude"
      #[IntVal.num (minInt257 - 1), IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-via-prelude"
      #[IntVal.num 7, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-low-via-prelude"
      #[IntVal.num 7, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCase "/gas/exact-cost-succeeds"
      #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftrHashModSetGasExact), .tonEnvOp .setGasLimit, mulrshiftrHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas"
      #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftrHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftrHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020831
      count := 700
      gen := genMulrshiftrHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTR_HASH_MOD
