import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULADDRSHIFTCMOD

/-
QMULADDRSHIFTCMOD branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true true 3 1 true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type ordering)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, runtime `shift=0` rewrite to floor)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-prefixed `0xb7a9a0..0xb7a9a2` decode arm wiring)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, add-path + `d=3` result pair in quiet mode)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, quiet push behavior)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`, `AnyIntView::mod_pow2_any`)

Branch counts used for this suite (QMULADDRSHIFTCMOD specialization):
- Lean specialization (`mul=true`, `add=true`, `d=3`, `round=1`, `quiet=true`):
  ~10 branch sites / ~18 terminal outcomes
  (dispatch/fallback; arity gate; runtime shift pop/type/range; `w→y→x` pop ordering;
   runtime `shift=0` round rewrite; numeric-vs-NaN split; quiet NaN pair funnels;
   quiet quotient-overflow funnel, remainder push path).
- C++ specialization (`exec_mulshrmod`, quiet runtime-shift arm):
  ~9 branch sites / ~16 aligned outcomes
  (underflow gate; runtime shift parse/range split; add-operand path;
   operand pop/type gates; `y==0` not applicable in mul-shift path; quiet output funnels).

Key risk areas covered:
- ceil quotient/remainder behavior for mixed signs with additive term (`x*y + w`);
- runtime `shift=0` rewrite to floor mode despite `...C...` mnemonic;
- quiet handling for bad shifts (`<0`, `>256`, `NaN`) vs non-int pop failures after shift;
- pop/error precedence (`shift` before `w`, `w` before `y`, `y` before `x`);
- NaN / out-of-range oracle serialization hygiene via program prelude injection only;
- exact gas boundary for `PUSHINT n; SETGASLIMIT; QMULADDRSHIFTCMOD`.
-/

private def qmuladdrshiftcmodId : InstrId := { name := "QMULADDRSHIFTCMOD" }

private def qmuladdrshiftcmodInstr : Instr :=
  .arithExt (.shrMod true true 3 1 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuladdrshiftcmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmuladdrshiftcmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x y w shift : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x, y, w, shift]
  mkCase name (below ++ stack) (programPrefix.push qmuladdrshiftcmodInstr) gasLimits fuel

private def mkShiftInjectedCase
    (name : String)
    (x y w : Value)
    (shift : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[x, y, w] #[.pushInt shift, qmuladdrshiftcmodInstr] gasLimits fuel

private def runQmuladdrshiftcmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmuladdrshiftcmodInstr stack

private def runQmuladdrshiftcmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 8642)) stack

private def qmuladdrshiftcmodSetGasExact : Int :=
  computeExactGasBudget qmuladdrshiftcmodInstr

private def qmuladdrshiftcmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuladdrshiftcmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidNegPool : Array Int :=
  #[-9, -5, -3, -1]

private def shiftInvalidOverPool : Array Int :=
  #[257, 258, 300, 511]

private def smallSignPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -1, 0, 1, 5, 7, 9, 13, 17, 33]

private def smallShiftPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8]

private def tinySignPool : Array Int :=
  #[-1, 0, 1]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 7
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def pickShiftInvalidNeg (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftInvalidNegPool rng

private def pickShiftInvalidOver (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftInvalidOverPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQmuladdrshiftcmod (x y w : Int) (shift : Nat) : String :=
  let roundMode : Int := if shift = 0 then (-1) else 1
  let tmp := x * y + w
  let q := rshiftPow2Round tmp shift roundMode
  let r := modPow2Round tmp shift roundMode
  if !intFitsSigned257 q || !intFitsSigned257 r then
    if shift = 0 then "overflow-shift0" else "overflow"
  else if tmp = 0 then
    "zero"
  else if shift = 0 then
    "shift0"
  else if r = 0 then
    "exact"
  else if
    x = maxInt257 || x = minInt257 ||
      y = maxInt257 || y = minInt257 ||
      w = maxInt257 || w = minInt257 then
    "boundary"
  else
    "inexact"

private def genQmuladdrshiftcmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 36
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftBoundary r4
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-xyz-boundary-shift"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftBoundary r4
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/signed-xyz-boundary-shift"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInRange r4
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-x-random-yw"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInRange r4
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-y-random-xw"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftInRange r4
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-w-random-xy"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyQmuladdrshiftcmod x 0 w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/y-zero"
        #[intV x, intV 0, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 6 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyQmuladdrshiftcmod 0 y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/x-zero"
        #[intV 0, intV y, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyQmuladdrshiftcmod x y 0 shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/w-zero"
        #[intV x, intV y, intV 0, intV (Int.ofNat shift)], r4)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-shift0-max-times-one-plus-one"
        #[intV maxInt257, intV 1, intV 1, intV 0], rng1)
    else if shape = 9 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-shift0-min-times-one-minus-one"
        #[intV minInt257, intV 1, intV (-1), intV 0], rng1)
    else if shape = 10 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromPool tinySignPool r2
      let y := if y = 0 then 1 else y
      let (w, r4) := pickFromPool tinySignPool r3
      let shift := 256
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/shift256-boundary"
        #[intV x, intV y, intV w, intV 256], r4)
    else if shape = 11 then
      let (x, r2) := pickFromPool smallSignPool rng1
      let (y, r3) := pickFromPool smallSignPool r2
      let (w, r4) := pickFromPool smallSignPool r3
      let (shift, r5) := pickFromPool smallShiftPool r4
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/small-sign-space"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 12 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"/fuzz/shape-{shape}/underflow/three-args" #[intV x, intV y, intV w], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shiftLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV y, intV w, shiftLike], r5)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (wLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-w-second"
        #[intV x, intV y, wLike, intV (Int.ofNat shift)], r5)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (yLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-third"
        #[intV x, yLike, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 19 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (xLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-fourth"
        #[xLike, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wLike, r4) := pickNonInt r3
      let (shiftLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-shift-before-w"
        #[intV x, intV y, wLike, shiftLike], r5)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (yLike, r4) := pickNonInt r3
      let (wLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-y"
        #[intV x, yLike, wLike, intV (Int.ofNat shift)], r5)
    else if shape = 22 then
      let (shift, r2) := pickShiftInRange rng1
      let (xLike, r3) := pickNonInt r2
      let (yLike, r4) := pickNonInt r3
      let (w, r5) := pickSigned257ish r4
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x"
        #[xLike, yLike, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInvalidNeg r4
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/range/shift-negative-via-program"
        (intV x) (intV y) (intV w) (.num shift), r5)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInvalidOver r4
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/range/shift-overmax-via-program"
        (intV x) (intV y) (intV w) (.num shift), r5)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/range/shift-nan-via-program"
        (intV x) (intV y) (intV w) .nan, r4)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yLike, r4) := pickNonInt r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/error-order/bad-shift-before-y-type-via-program"
        (intV x) yLike (intV w) (.num 257), r4)
    else if shape = 27 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (xLike, r4) := pickNonInt r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/error-order/bad-shift-before-x-type-via-program"
        xLike (intV y) (intV w) (.num (-1)), r4)
    else if shape = 28 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        .nan (.num y) (.num w) (.num (Int.ofNat shift)), r4)
    else if shape = 29 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        (.num x) .nan (.num w) (.num (Int.ofNat shift)), r4)
    else if shape = 30 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-w-via-program"
        (.num x) (.num y) .nan (.num (Int.ofNat shift)), r4)
    else if shape = 31 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num y) (.num w) (.num (Int.ofNat shift)), r5)
    else if shape = 32 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        (.num x) (.num yOut) (.num w) (.num (Int.ofNat shift)), r5)
    else if shape = 33 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wOut, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftInRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        (.num x) (.num y) (.num wOut) (.num (Int.ofNat shift)), r5)
    else if shape = 34 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shiftOut, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        (.num x) (.num y) (.num w) (.num shiftOut), r5)
    else if shape = 35 then
      let xOut : Int := maxInt257 + 1
      let yOut : Int := minInt257 - 1
      let wOut : Int := 1
      let shiftOut : Int := -1
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-multi-before-op"
        (.num xOut) (.num yOut) (.num wOut) (.num shiftOut), rng1)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInRange r4
      let (below, r6) := pickNonInt r5
      let kind := classifyQmuladdrshiftcmod x y w shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/pop-order/below-preserved"
        #[below, intV x, intV y, intV w, intV (Int.ofNat shift)], r6)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuladdrshiftcmodId
  unit := #[
    { name := "/unit/ok/ceil-rounding-mul-add-invariants"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 1, 11, 0),
            (7, 3, 2, 1, 12, -1),
            (-7, 3, 0, 1, -10, -1),
            (7, -3, 0, 1, -10, -1),
            (-7, -3, 1, 1, 11, 0),
            (5, 5, -2, 2, 6, -1),
            (-5, 5, 2, 2, -5, -3),
            (5, -5, 2, 2, -5, -3),
            (-5, -5, -1, 2, 6, 0),
            (0, 13, 9, 3, 2, -7),
            (13, 0, -9, 3, -1, -1),
            (7, 3, 2, 0, 23, 0),
            (-7, 3, 2, 0, -19, 0),
            (maxInt257, 1, 0, 256, 1, -1),
            (minInt257, 1, 0, 256, -1, 0),
            (minInt257 + 1, 1, 0, 256, 0, minInt257 + 1),
            (maxInt257, -1, 0, 1, 1 - (pow2 255), -1),
            (minInt257, -1, 0, 1, pow2 255, 0)
          ]
        for c in checks do
          let (x, y, w, shift, q, r) := c
          expectOkStack s!"/unit/ok/x={x}/y={y}/w={w}/shift={shift}"
            (runQmuladdrshiftcmodDirect #[intV x, intV y, intV w, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "/unit/ok/pop-order-and-below-preservation"
      run := do
        expectOkStack "/unit/ok/pop-order/below-null"
          (runQmuladdrshiftcmodDirect #[.null, intV 7, intV 3, intV 1, intV 1])
          #[.null, intV 11, intV 0]
        expectOkStack "/unit/ok/pop-order/below-cell"
          (runQmuladdrshiftcmodDirect #[.cell Cell.empty, intV (-7), intV 3, intV 0, intV 1])
          #[.cell Cell.empty, intV (-10), intV (-1)] }
    ,
    { name := "/unit/quiet/nan-bad-shift-and-overflow-funnels"
      run := do
        expectOkStack "/unit/quiet/nan/x"
          (runQmuladdrshiftcmodDirect #[.int .nan, intV 5, intV 3, intV 1])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan/y"
          (runQmuladdrshiftcmodDirect #[intV 5, .int .nan, intV 3, intV 1])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan/w"
          (runQmuladdrshiftcmodDirect #[intV 5, intV 3, .int .nan, intV 1])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/range/shift-negative"
          (runQmuladdrshiftcmodDirect #[intV 9, intV 7, intV 5, intV (-1)])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/range/shift-overmax"
          (runQmuladdrshiftcmodDirect #[intV 9, intV 7, intV 5, intV 257])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/range/shift-nan"
          (runQmuladdrshiftcmodDirect #[intV 9, intV 7, intV 5, .int .nan])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow/shift0-max-times-one-plus-one"
          (runQmuladdrshiftcmodDirect #[intV maxInt257, intV 1, intV 1, intV 0])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/shift0-min-times-one-minus-one"
          (runQmuladdrshiftcmodDirect #[intV minInt257, intV 1, intV (-1), intV 0])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/shift1-max-times-max"
          (runQmuladdrshiftcmodDirect #[intV maxInt257, intV maxInt257, intV 0, intV 1])
          #[.int .nan, intV (-1)] }
    ,
    { name := "/unit/error-order/underflow-type-and-precedence"
      run := do
        expectErr "/unit/error-order/underflow/empty" (runQmuladdrshiftcmodDirect #[]) .stkUnd
        expectErr "/unit/error-order/underflow/one-arg"
          (runQmuladdrshiftcmodDirect #[intV 1]) .stkUnd
        expectErr "/unit/error-order/underflow/two-args"
          (runQmuladdrshiftcmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow/three-args"
          (runQmuladdrshiftcmodDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/unit/error-order/underflow/before-type-two-non-int"
          (runQmuladdrshiftcmodDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/error-order/type/pop-shift-first"
          (runQmuladdrshiftcmodDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/unit/error-order/type/pop-w-second"
          (runQmuladdrshiftcmodDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/unit/error-order/type/pop-y-third"
          (runQmuladdrshiftcmodDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "/unit/error-order/type/pop-x-fourth"
          (runQmuladdrshiftcmodDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/unit/error-order/pop-shift-before-w-when-both-non-int"
          (runQmuladdrshiftcmodDirect #[intV 1, intV 2, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-w-before-y-when-shift-valid"
          (runQmuladdrshiftcmodDirect #[intV 1, .cell Cell.empty, .null, intV 1]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-shift-valid"
          (runQmuladdrshiftcmodDirect #[.null, .cell Cell.empty, intV 2, intV 1]) .typeChk
        expectErr "/unit/error-order/bad-shift-before-y-type"
          (runQmuladdrshiftcmodDirect #[intV 9, .null, intV 7, intV 257]) .typeChk
        expectErr "/unit/error-order/bad-shift-before-x-type"
          (runQmuladdrshiftcmodDirect #[.null, intV 9, intV 7, intV (-1)]) .typeChk
        expectErr "/unit/error-order/bad-shift-nan-before-w-type"
          (runQmuladdrshiftcmodDirect #[intV 9, intV 7, .null, .int .nan]) .typeChk }
    ,
    { name := "/unit/dispatch/non-qmuladdrshiftcmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmuladdrshiftcmodDispatchFallback #[]) #[intV 8642] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign/pos-pos-plus-inexact" #[intV 7, intV 3, intV 2, intV 1],
    mkCase "/ok/ceil/sign/neg-pos-plus-inexact" #[intV (-7), intV 3, intV 0, intV 1],
    mkCase "/ok/ceil/sign/pos-neg-plus-inexact" #[intV 7, intV (-3), intV 0, intV 1],
    mkCase "/ok/ceil/sign/neg-neg-plus-inexact" #[intV (-7), intV (-3), intV 1, intV 1],
    mkCase "/ok/ceil/small/pos-shift2" #[intV 5, intV 5, intV (-2), intV 2],
    mkCase "/ok/ceil/small/neg-shift2" #[intV (-5), intV 5, intV 2, intV 2],
    mkCase "/ok/ceil/small/mixed-shift2" #[intV 5, intV (-5), intV 2, intV 2],
    mkCase "/ok/exact/zero-from-add-cancel" #[intV 5, intV 5, intV (-25), intV 3],
    mkCase "/ok/exact/x-zero" #[intV 0, intV 13, intV 9, intV 3],
    mkCase "/ok/exact/y-zero" #[intV 13, intV 0, intV (-9), intV 3],
    mkCase "/ok/shift0/rewrite-positive" #[intV 7, intV 3, intV 2, intV 0],
    mkCase "/ok/shift0/rewrite-negative" #[intV (-7), intV 3, intV 2, intV 0],
    mkCase "/ok/boundary/max-shift256" #[intV maxInt257, intV 1, intV 0, intV 256],
    mkCase "/ok/boundary/min-shift256" #[intV minInt257, intV 1, intV 0, intV 256],
    mkCase "/ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 1, intV 0, intV 256],
    mkCase "/ok/boundary/max-times-negone-shift1" #[intV maxInt257, intV (-1), intV 0, intV 1],
    mkCase "/ok/boundary/min-times-negone-shift1" #[intV minInt257, intV (-1), intV 0, intV 1],
    mkCase "/ok/boundary/max-plus-min-cancel-shift1" #[intV maxInt257, intV 1, intV minInt257, intV 1],
    mkCase "/ok/boundary/min-plus-max-cancel-shift1" #[intV minInt257, intV 1, intV maxInt257, intV 1],
    mkCase "/ok/pop-order/below-null-preserved" #[.null, intV 7, intV 3, intV 1, intV 1],
    mkCase "/ok/pop-order/below-cell-preserved" #[.cell Cell.empty, intV (-7), intV 3, intV 0, intV 1],
    mkInputCase "/quiet/nan/x-via-program" .nan (.num 5) (.num 3) (.num 1),
    mkInputCase "/quiet/nan/y-via-program" (.num 5) .nan (.num 3) (.num 1),
    mkInputCase "/quiet/nan/w-via-program" (.num 5) (.num 3) .nan (.num 1),
    mkInputCase "/quiet/nan/all-via-program" .nan .nan .nan (.num 1),
    mkCase "/quiet/overflow/shift0-max-times-one-plus-one" #[intV maxInt257, intV 1, intV 1, intV 0],
    mkCase "/quiet/overflow/shift0-min-times-one-minus-one" #[intV minInt257, intV 1, intV (-1), intV 0],
    mkCase "/quiet/overflow/shift1-max-times-max" #[intV maxInt257, intV maxInt257, intV 0, intV 1],
    mkShiftInjectedCase "/quiet/range/shift-negative-via-program" (intV 9) (intV 7) (intV 5) (.num (-1)),
    mkShiftInjectedCase "/quiet/range/shift-overmax-via-program" (intV 9) (intV 7) (intV 5) (.num 257),
    mkShiftInjectedCase "/quiet/range/shift-nan-via-program" (intV 9) (intV 7) (intV 5) .nan,
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-type-with-two-non-int" #[.null, .cell Cell.empty],
    mkCase "/type/pop-shift-first-null" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 1, intV 2, intV 3, .cell Cell.empty],
    mkCase "/type/pop-w-second-null" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/pop-y-third-null" #[intV 1, .null, intV 2, intV 3],
    mkCase "/type/pop-x-fourth-null" #[.null, intV 1, intV 2, intV 3],
    mkCase "/error-order/pop-shift-before-w-when-both-non-int"
      #[intV 1, intV 2, .cell Cell.empty, .null],
    mkCase "/error-order/pop-w-before-y-when-shift-valid"
      #[intV 1, .cell Cell.empty, .null, intV 1],
    mkCase "/error-order/pop-y-before-x-when-shift-valid"
      #[.null, .cell Cell.empty, intV 2, intV 1],
    mkShiftInjectedCase "/error-order/bad-shift-before-y-type-via-program" (intV 9) .null (intV 7) (.num 257),
    mkShiftInjectedCase "/error-order/bad-shift-before-x-type-via-program" .null (intV 9) (intV 7) (.num (-1)),
    mkShiftInjectedCase "/error-order/bad-shift-nan-before-w-type-via-program"
      (intV 9) (intV 7) .null .nan,
    mkInputCase "/error-order/pushint-overflow-x-high-before-op"
      (.num (maxInt257 + 1)) (.num 7) (.num 9) (.num 1),
    mkInputCase "/error-order/pushint-overflow-x-low-before-op"
      (.num (minInt257 - 1)) (.num 7) (.num 9) (.num 1),
    mkInputCase "/error-order/pushint-overflow-y-high-before-op"
      (.num 5) (.num (maxInt257 + 1)) (.num 9) (.num 1),
    mkInputCase "/error-order/pushint-overflow-y-low-before-op"
      (.num 5) (.num (minInt257 - 1)) (.num 9) (.num 1),
    mkInputCase "/error-order/pushint-overflow-w-high-before-op"
      (.num 5) (.num 7) (.num (maxInt257 + 1)) (.num 1),
    mkInputCase "/error-order/pushint-overflow-w-low-before-op"
      (.num 5) (.num 7) (.num (minInt257 - 1)) (.num 1),
    mkInputCase "/error-order/pushint-overflow-shift-high-before-op"
      (.num 5) (.num 7) (.num 9) (.num (pow2 257)),
    mkInputCase "/error-order/pushint-overflow-shift-low-before-op"
      (.num 5) (.num 7) (.num 9) (.num (-(pow2 257))),
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1, intV 1]
      #[.pushInt (.num qmuladdrshiftcmodSetGasExact), .tonEnvOp .setGasLimit, qmuladdrshiftcmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1, intV 1]
      #[.pushInt (.num qmuladdrshiftcmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuladdrshiftcmodInstr]
  ]
  fuzz := #[
    { seed := 2026020849
      count := 700
      gen := genQmuladdrshiftcmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULADDRSHIFTCMOD
