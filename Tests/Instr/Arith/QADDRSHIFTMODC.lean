import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADDRSHIFTMODC

/-
QADDRSHIFTMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false true 3 1 true none)`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popNatUpTo 256`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, `modPow2Round`, ceil-mode behavior plus runtime `shift=0` rewrite)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, add-path (`d==3`), runtime `y==0` rewrite)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`BigInt256::DoubleInt::rshift`, `mod_pow2`)

Branch counts used for this suite (QADDRSHIFTMODC specialization):
- Lean: ~9 branch sites / ~15 terminal outcomes
  (dispatch/fallback; arity precheck; shift pop type/range/ok; `w` pop type/ok;
   `x` pop type/ok; runtime `shift=0` floor rewrite; numeric-vs-NaN operand split;
   fixed `d=3` quiet push funnels including out-of-range-to-NaN conversion).
- C++: ~8 branch sites / ~14 aligned outcomes
  (`check_underflow(add?3:2)`; `pop_smallint_range(256)` type/range checks;
   `y==0` rewrite; `pop_int` for `w` then `x`; add-path double-int rshift/mod_pow2;
   two `push_int_quiet` terminals under quiet mode).

Key risk areas covered:
- ceil quotient/remainder semantics with addend across mixed signs;
- runtime `shift=0` forcing floor mode even for `...C` opcode family;
- strict runtime shift range (`0..256`) remains `rangeChk` in quiet mode;
- pop/error ordering (`shift` before `w`, `w` before `x`, underflow before type);
- quiet handling for NaN operands and overflowed quotient push (`NaN` materialization);
- exact gas cliff around `PUSHINT n; SETGASLIMIT; QADDRSHIFTMODC`.
-/

private def qaddrshiftmodcId : InstrId := { name := "QADDRSHIFTMODC" }

private def qaddrshiftmodcInstr : Instr :=
  .arithExt (.shrMod false true 3 1 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qaddrshiftmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qaddrshiftmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x w shift : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x, w, shift]
  mkCase name (below ++ stack) (programPrefix.push qaddrshiftmodcInstr) gasLimits fuel

private def mkShiftInjectedCase
    (name : String)
    (x w : Value)
    (shift : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[x, w] #[.pushInt shift, qaddrshiftmodcInstr] gasLimits fuel

private def runQaddrshiftmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qaddrshiftmodcInstr stack

private def runQaddrshiftmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 7419)) stack

private def qaddrshiftmodcSetGasExact : Int :=
  computeExactGasBudget qaddrshiftmodcInstr

private def qaddrshiftmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qaddrshiftmodcInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidNegPool : Array Int :=
  #[-7, -3, -2, -1]

private def shiftInvalidOverPool : Array Int :=
  #[257, 258, 300, 511]

private def smallSignPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -1, 0, 1, 5, 7, 9, 13, 17, 33]

private def smallShiftPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8]

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

private def classifyQaddrshiftmodc (x w : Int) (shift : Nat) : String :=
  let sum := x + w
  if shift = 0 then
    if intFitsSigned257 sum then "shift0" else "overflow-shift0"
  else
    let (_, r) := divModRound sum (pow2 shift) 1
    if r = 0 then
      "exact"
    else if
      x = maxInt257 || x = minInt257 || w = maxInt257 || w = minInt257 then
      "boundary"
    else
      "inexact"

private def genQaddrshiftmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyQaddrshiftmodc x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-xw-boundary-shift"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyQaddrshiftmodc x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-xw-boundary-shift"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyQaddrshiftmodc x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-x-random-w"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyQaddrshiftmodc x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/random-x-boundary-w"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyQaddrshiftmodc x 0 shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/w-zero"
        #[intV x, intV 0, intV (Int.ofNat shift)], r3)
    else if shape = 5 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyQaddrshiftmodc 0 w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/x-zero"
        #[intV 0, intV w, intV (Int.ofNat shift)], r3)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-shift0-max-plus-one"
        #[intV maxInt257, intV 1, intV 0], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-shift0-min-minus-one"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 8 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let (w, r3) := pickFromPool #[-1, 0, 1] r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary/shift256"
        #[intV x, intV w, intV 256], r3)
    else if shape = 9 then
      let (x, r2) := pickFromPool smallSignPool rng1
      let (w, r3) := pickFromPool smallSignPool r2
      let (shift, r4) := pickFromPool smallShiftPool r3
      let kind := classifyQaddrshiftmodc x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/small-sign-space"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-args" #[intV x, intV w], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV w, shiftLike], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (wLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-w-second"
        #[intV x, wLike, intV (Int.ofNat shift)], r4)
    else if shape = 15 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-third"
        #[xLike, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (wLike, r3) := pickNonInt r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/pop-shift-before-w"
        #[intV x, wLike, shiftLike], r4)
    else if shape = 17 then
      let (shift, r2) := pickShiftInRange rng1
      let (xLike, r3) := pickNonInt r2
      let (wLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/pop-w-before-x"
        #[xLike, wLike, intV (Int.ofNat shift)], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInvalidNeg r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range/shift-negative-via-program"
        (intV x) (intV w) (.num shift), r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInvalidOver r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range/shift-overmax-via-program"
        (intV x) (intV w) (.num shift), r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range/shift-nan-via-program"
        (intV x) (intV w) .nan, r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (wLike, r3) := pickNonInt r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order/range-before-w-type-via-program"
        (intV x) wLike (.num 257), r3)
    else if shape = 22 then
      let (w, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-via-program"
        xLike (intV w) (.num (-1)), r3)
    else if shape = 23 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        .nan (.num w) (.num (Int.ofNat shift)), r3)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-w-via-program"
        (.num x) .nan (.num (Int.ofNat shift)), r3)
    else if shape = 25 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num w) (.num (Int.ofNat shift)), r4)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftInRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        (.num x) (.num wOut) (.num (Int.ofNat shift)), r4)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        (.num x) (.num w) (.num shiftOut), r4)
    else if shape = 28 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shiftOut, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        (.num xOut) (.num w) (.num shiftOut), r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (below, r5) := pickNonInt r4
      (mkCase s!"fuzz/shape-{shape}/ok/pop-order/below-preserved"
        #[below, intV x, intV w, intV (Int.ofNat shift)], r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qaddrshiftmodcId
  unit := #[
    { name := "unit/ok/ceil-rounding-sign-and-cancel-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 0, 1, 4, -1),
            (7, 1, 1, 4, 0),
            (-7, 0, 1, -3, -1),
            (-7, -1, 1, -4, 0),
            (5, -7, 1, -1, 0),
            (-5, 7, 1, 1, 0),
            (5, 1, 2, 2, -2),
            (-5, -1, 2, -1, -2),
            (1, 0, 2, 1, -3),
            (-1, 0, 2, 0, -1),
            (0, 0, 3, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"(x={x},w={w},shift={shift})"
            (runQaddrshiftmodcDirect #[intV x, intV w, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/ok/shift-zero-rewrite-and-boundary-widths"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 0, maxInt257, 0),
            (minInt257, 0, 0, minInt257, 0),
            (maxInt257, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 0, minInt257 + 1, 0),
            (maxInt257, 0, 256, 1, -1),
            (minInt257, 0, 256, -1, 0),
            (-1, 0, 256, 0, -1),
            (1, 0, 256, 1, minInt257 + 1),
            (maxInt257, minInt257, 1, 0, -1)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"boundary/(x={x},w={w},shift={shift})"
            (runQaddrshiftmodcDirect #[intV x, intV w, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/quiet/nan-and-overflow-pairs"
      run := do
        expectOkStack "quiet/nan-x"
          (runQaddrshiftmodcDirect #[.int .nan, intV 5, intV 1]) #[intV 0, .int .nan]
        expectOkStack "quiet/nan-w"
          (runQaddrshiftmodcDirect #[intV 5, .int .nan, intV 1]) #[intV 0, .int .nan]
        expectOkStack "quiet/overflow-max-plus-one-shift0"
          (runQaddrshiftmodcDirect #[intV maxInt257, intV 1, intV 0]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow-min-minus-one-shift0"
          (runQaddrshiftmodcDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan, intV 0] }
    ,
    { name := "unit/error-order/underflow-type-range-and-precedence"
      run := do
        expectErr "underflow/empty" (runQaddrshiftmodcDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runQaddrshiftmodcDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runQaddrshiftmodcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/two-non-int-underflow-before-type"
          (runQaddrshiftmodcDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-shift-first" (runQaddrshiftmodcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-w-second" (runQaddrshiftmodcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runQaddrshiftmodcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-shift-before-w-when-both-non-int"
          (runQaddrshiftmodcDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-w-before-x-when-shift-valid"
          (runQaddrshiftmodcDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "range/shift-negative"
          (runQaddrshiftmodcDirect #[intV 9, intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax"
          (runQaddrshiftmodcDirect #[intV 9, intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan"
          (runQaddrshiftmodcDirect #[intV 9, intV 7, .int .nan]) .rangeChk
        expectErr "error-order/range-before-w-type"
          (runQaddrshiftmodcDirect #[intV 9, .null, intV 257]) .rangeChk
        expectErr "error-order/range-before-x-type"
          (runQaddrshiftmodcDirect #[.null, intV 7, intV (-1)]) .rangeChk }
    ,
    { name := "unit/dispatch/non-qaddrshiftmodc-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQaddrshiftmodcDispatchFallback #[]) #[intV 7419] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 0, intV 1],
    mkCase "ok/ceil/sign/pos-pos-exact" #[intV 7, intV 1, intV 1],
    mkCase "ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 0, intV 1],
    mkCase "ok/ceil/sign/neg-pos-exact" #[intV (-7), intV (-1), intV 1],
    mkCase "ok/ceil/cancel/pos-neg" #[intV 5, intV (-7), intV 1],
    mkCase "ok/ceil/cancel/neg-pos" #[intV (-5), intV 7, intV 1],
    mkCase "ok/ceil/small/pos-shift2" #[intV 5, intV 1, intV 2],
    mkCase "ok/ceil/small/neg-shift2" #[intV (-5), intV (-1), intV 2],
    mkCase "ok/shift0/max-plus-zero" #[intV maxInt257, intV 0, intV 0],
    mkCase "ok/shift0/min-plus-zero" #[intV minInt257, intV 0, intV 0],
    mkCase "ok/shift0/max-minus-one" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/shift0/min-plus-one" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/shift256/max" #[intV maxInt257, intV 0, intV 256],
    mkCase "ok/shift256/min" #[intV minInt257, intV 0, intV 256],
    mkCase "ok/shift256/neg-one" #[intV (-1), intV 0, intV 256],
    mkCase "ok/shift256/pos-one" #[intV 1, intV 0, intV 256],
    mkCase "ok/boundary/max-plus-min-shift1" #[intV maxInt257, intV minInt257, intV 1],
    mkCase "ok/boundary/min-plus-max-shift256" #[intV minInt257, intV maxInt257, intV 256],
    mkCase "ok/pop-order/below-null-preserved" #[.null, intV 13, intV 0, intV 2],
    mkCase "ok/pop-order/below-cell-preserved" #[.cell Cell.empty, intV (-13), intV 0, intV 2],
    mkInputCase "quiet/nan/x-via-program" .nan (.num 5) (.num 1),
    mkInputCase "quiet/nan/w-via-program" (.num 5) .nan (.num 1),
    mkInputCase "quiet/nan/both-via-program" .nan .nan (.num 1),
    mkCase "quiet/overflow/shift0-max-plus-one" #[intV maxInt257, intV 1, intV 0],
    mkCase "quiet/overflow/shift0-min-minus-one" #[intV minInt257, intV (-1), intV 0],
    mkCase "quiet/overflow/shift0-max-plus-max" #[intV maxInt257, intV maxInt257, intV 0],
    mkShiftInjectedCase "range/shift-negative-via-program" (intV 7) (intV 5) (.num (-1)),
    mkShiftInjectedCase "range/shift-overmax-via-program" (intV 7) (intV 5) (.num 257),
    mkShiftInjectedCase "range/shift-nan-via-program" (intV 7) (intV 5) .nan,
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/two-non-int-underflow-before-type" #[.null, .cell Cell.empty],
    mkCase "type/pop-shift-first-null" #[intV 1, intV 2, .null],
    mkCase "type/pop-shift-first-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/pop-w-second-null" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-shift-before-w-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-x-when-shift-valid" #[.null, .cell Cell.empty, intV 1],
    mkShiftInjectedCase "error-order/range-before-w-type-negative-via-program" (intV 9) .null (.num (-1)),
    mkShiftInjectedCase "error-order/range-before-w-type-overmax-via-program" (intV 9) (.cell Cell.empty) (.num 257),
    mkShiftInjectedCase "error-order/range-before-x-type-negative-via-program" .null (intV 7) (.num (-1)),
    mkShiftInjectedCase "error-order/range-before-x-type-overmax-via-program" (.cell Cell.empty) (intV 7) (.num 257),
    mkShiftInjectedCase "error-order/range-before-type-shift-nan-via-program" .null (intV 7) .nan,
    mkInputCase "error-order/pushint-overflow-x-high-before-op" (.num (maxInt257 + 1)) (.num 5) (.num 1),
    mkInputCase "error-order/pushint-overflow-x-low-before-op" (.num (minInt257 - 1)) (.num 5) (.num 1),
    mkInputCase "error-order/pushint-overflow-w-high-before-op" (.num 5) (.num (maxInt257 + 1)) (.num 1),
    mkInputCase "error-order/pushint-overflow-w-low-before-op" (.num 5) (.num (minInt257 - 1)) (.num 1),
    mkInputCase "error-order/pushint-overflow-shift-high-before-op" (.num 5) (.num 7) (.num (pow2 257)),
    mkInputCase "error-order/pushint-overflow-shift-low-before-op" (.num 5) (.num 7) (.num (-(pow2 257))),
    mkInputCase "error-order/pushint-overflow-both-before-op" (.num (pow2 257)) (.num (-(pow2 257))) (.num (pow2 257)),
    mkCase "gas/exact-cost-succeeds" #[intV 13, intV 2, intV 1]
      #[.pushInt (.num qaddrshiftmodcSetGasExact), .tonEnvOp .setGasLimit, qaddrshiftmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 13, intV 2, intV 1]
      #[.pushInt (.num qaddrshiftmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qaddrshiftmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020842
      count := 700
      gen := genQaddrshiftmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADDRSHIFTMODC
