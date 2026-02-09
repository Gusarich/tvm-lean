import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADDRSHIFTMODR

/-
QADDRSHIFTMODR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false true 3 0 true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popNatUpTo 256`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, nearest ties toward `+∞`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`, `AnyIntView::mod_pow2_any`)

Branch counts used for this suite (QADDRSHIFTMODR specialization):
- Lean: ~9 branch sites / ~12 terminal outcomes
  (dispatch/fallback; depth precheck; shift pop type/range/ok; `w` pop type/ok;
   `x` pop type/ok; `shift=0` round rewrite; numeric-vs-NaN (`x`,`w`) split;
   fixed `d=3` dual push with quiet overflow funnel on quotient).
- C++: ~8 branch sites / ~11 aligned terminal outcomes
  (`check_underflow(3)`; `pop_smallint_range(256)` type/range split;
   `y==0` mode rewrite; `w` then `x` `pop_int`; add-path `tmp+=w`;
   `rshift`/`mod_pow2` pair with quiet `push_int_quiet`).

Key risk areas covered:
- nearest rounding (`R`) with ties toward `+∞` on `x + w`;
- runtime shift strictness (`0..256`) even for quiet opcodes;
- pop/error order: underflow first, then shift checks, then `w`, then `x`;
- quiet NaN funnel (`x`/`w` NaN -> NaN pair) and quiet overflow funnel
  (`shift=0`, out-of-range sum -> `q=NaN`, `r=0`);
- signed-257 boundary behavior at `±2^256` with shift `0` and `256`;
- exact gas cliff (`PUSHINT n; SETGASLIMIT; QADDRSHIFTMODR`) exact vs minus-one.
-/

private def qaddrshiftmodrId : InstrId := { name := "QADDRSHIFTMODR" }

private def qaddrshiftmodrInstr : Instr :=
  .arithExt (.shrMod false true 3 0 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qaddrshiftmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qaddrshiftmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qaddrshiftmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQaddrshiftmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qaddrshiftmodrInstr stack

private def runQaddrshiftmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 947)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def qaddrshiftmodrSetGasExact : Int :=
  computeExactGasBudget qaddrshiftmodrInstr

private def qaddrshiftmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qaddrshiftmodrInstr

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieShift1Pool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieShift2Pool : Array Int :=
  #[-14, -10, -6, -2, 2, 6, 10, 14]

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

private def classifyQaddrshiftmodr (x w : Int) (shift : Nat) : String :=
  let sum := x + w
  if shift = 0 then
    if intFitsSigned257 sum then
      "shift0"
    else
      "overflow-shift0"
  else
    let p := pow2 shift
    let rem := Int.emod sum p
    if rem = pow2 (shift - 1) then
      "tie"
    else if rem = 0 then
      "exact"
    else if x = maxInt257 || x = minInt257 || w = maxInt257 || w = minInt257 then
      "boundary"
    else
      "inexact"

private def genQaddrshiftmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyQaddrshiftmodr x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-x-boundary-w-boundary-shift"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyQaddrshiftmodr x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-x-signed-w-boundary-shift"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyQaddrshiftmodr x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-x-signed-w-random-shift"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyQaddrshiftmodr x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-x-signed-w"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyQaddrshiftmodr x w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-x-boundary-w"
        #[intV x, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let kind := classifyQaddrshiftmodr x 0 shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/w-zero"
        #[intV x, intV 0, intV (Int.ofNat shift)], r3)
    else if shape = 6 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let kind := classifyQaddrshiftmodr 0 w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/x-zero"
        #[intV 0, intV w, intV (Int.ofNat shift)], r3)
    else if shape = 7 then
      let (sum, r2) := pickFromPool tieShift1Pool rng1
      (mkCase s!"fuzz/shape-{shape}/ok/tie/shift1" #[intV sum, intV 0, intV 1], r2)
    else if shape = 8 then
      let (sum, r2) := pickFromPool tieShift2Pool rng1
      (mkCase s!"fuzz/shape-{shape}/ok/tie/shift2" #[intV sum, intV 0, intV 2], r2)
    else if shape = 9 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let w := if useMax then 1 else -1
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-shift0-funnel" #[intV x, intV w, intV 0], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/shift256-edge" #[intV x, intV w, intV 256], r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-item" #[intV x], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-items" #[intV x, intV w], r3)
    else if shape = 14 then
      let (a, r2) := pickNonInt rng1
      let (b, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-type-two-items" #[a, b], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-pop-first" #[intV x, intV w, yLike], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let (wLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/w-pop-second"
        #[intV x, wLike, intV (Int.ofNat shift)], r4)
    else if shape = 17 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/x-pop-third"
        #[xLike, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 18 then
      let (xLike, r2) := pickNonInt rng1
      let (wLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/type-shift-before-w-when-both-non-int"
        #[xLike, wLike, .null], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative" #[intV x, intV w, intV (-1)], r3)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-over256" #[intV x, intV w, intV 257], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/shift-nan-via-program"
        #[.num x, .num w, .nan], r3)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-w-via-program"
        #[.num x, .nan, .num (Int.ofNat shift)], r3)
    else if shape = 23 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num w, .num (Int.ofNat shift)], r3)
    else if shape = 24 then
      let (shift, r2) := pickShiftMixed rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program"
        #[.nan, .nan, .num (Int.ofNat shift)], r2)
    else if shape = 25 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-x-before-op"
        #[.num xOut, .num w, .num (Int.ofNat shift)], r4)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-w-before-op"
        #[.num x, .num wOut, .num (Int.ofNat shift)], r4)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-w-type-via-program"
        #[intV x, .null] #[.pushInt (.num (-1)), qaddrshiftmodrInstr], r2)
    else if shape = 28 then
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num (-1)), qaddrshiftmodrInstr], rng1)
    else
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-shift-before-op"
        #[.num x, .num w, .num shiftOut], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qaddrshiftmodrId
  unit := #[
    { name := "unit/ok/nearest-rounding-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (5, 2, 1, 4, -1),
            (-10, 3, 1, -3, -1),
            (2, -1, 1, 1, -1),
            (-2, 1, 1, 0, -1),
            (8, -2, 2, 2, -2),
            (-8, 2, 2, -1, -2),
            (7, -8, 2, 0, -1),
            (-7, 8, 2, 0, 1),
            (21, 11, 1, 16, 0),
            (-21, 5, 2, -4, 0),
            (9, -9, 5, 0, 0),
            (5, 3, 0, 8, 0),
            (-5, -3, 0, -8, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"(x={x},w={w},shift={shift})"
            (runQaddrshiftmodrDirect #[intV x, intV w, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/ok/boundary-shift256-and-stack-shape"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 0, 0, maxInt257, 0),
            (minInt257, 0, 0, minInt257, 0),
            (maxInt257, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 0, minInt257 + 1, 0),
            (maxInt257, minInt257, 0, -1, 0),
            (maxInt257, maxInt257, 256, 2, -2),
            (minInt257, minInt257, 256, -2, 0),
            (maxInt257, 0, 256, 1, -1),
            (minInt257, 0, 256, -1, 0),
            (maxInt257 - 1, 0, 256, 1, -2),
            (minInt257 + 1, 0, 256, -1, 1),
            (minInt257, 1, 256, -1, 1)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"boundary/(x={x},w={w},shift={shift})"
            (runQaddrshiftmodrDirect #[intV x, intV w, intV (Int.ofNat shift)])
            #[intV q, intV r]
        expectOkStack "below-null-preserved"
          (runQaddrshiftmodrDirect #[.null, intV 5, intV 2, intV 1])
          #[.null, intV 4, intV (-1)]
        expectOkStack "below-cell-preserved"
          (runQaddrshiftmodrDirect #[.cell Cell.empty, intV (-10), intV 3, intV 1])
          #[.cell Cell.empty, intV (-3), intV (-1)] }
    ,
    { name := "unit/quiet/nan-and-overflow-funnels"
      run := do
        expectOkStack "quiet/overflow-max-plus-one-shift0"
          (runQaddrshiftmodrDirect #[intV maxInt257, intV 1, intV 0]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow-min-minus-one-shift0"
          (runQaddrshiftmodrDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan, intV 0]
        expectOkStack "quiet/nan-x"
          (runQaddrshiftmodrDirect #[.int .nan, intV 5, intV 1]) #[intV 0, .int .nan]
        expectOkStack "quiet/nan-w"
          (runQaddrshiftmodrDirect #[intV 5, .int .nan, intV 1]) #[intV 0, .int .nan]
        expectOkStack "quiet/nan-both"
          (runQaddrshiftmodrDirect #[.int .nan, .int .nan, intV 1]) #[intV 0, .int .nan] }
    ,
    { name := "unit/error-order/underflow-shift-range-and-pop-precedence"
      run := do
        expectErr "underflow/empty" (runQaddrshiftmodrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runQaddrshiftmodrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-items" (runQaddrshiftmodrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "underflow/two-non-int-items" (runQaddrshiftmodrDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/shift-pop-first-null" (runQaddrshiftmodrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/shift-pop-first-cell" (runQaddrshiftmodrDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "range/shift-negative" (runQaddrshiftmodrDirect #[intV 5, intV 6, intV (-1)]) .rangeChk
        expectErr "range/shift-over256" (runQaddrshiftmodrDirect #[intV 5, intV 6, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runQaddrshiftmodrDirect #[intV 5, intV 6, .int .nan]) .rangeChk
        expectErr "error-order/range-before-w-type-neg-shift"
          (runQaddrshiftmodrDirect #[intV 5, .null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-over256-shift"
          (runQaddrshiftmodrDirect #[.null, intV 5, intV 257]) .rangeChk
        expectErr "type/w-pop-second"
          (runQaddrshiftmodrDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/x-pop-third"
          (runQaddrshiftmodrDirect #[.null, intV 5, intV 1]) .typeChk
        expectErr "error-order/type-shift-before-w-when-both-non-int"
          (runQaddrshiftmodrDirect #[intV 5, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/type-w-before-x-when-shift-valid"
          (runQaddrshiftmodrDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-qaddrshiftmodr-sequence"
      run := do
        let program : Array Instr := #[qaddrshiftmodrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qaddrshiftmodr" s0 qaddrshiftmodrInstr 24
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQaddrshiftmodrDispatchFallback #[]) #[intV 947] }
  ]
  oracle := #[
    mkCase "ok/round/tie-pos-shift1" #[intV 5, intV 2, intV 1],
    mkCase "ok/round/tie-neg-shift1" #[intV (-10), intV 3, intV 1],
    mkCase "ok/round/half-pos-shift1" #[intV 2, intV (-1), intV 1],
    mkCase "ok/round/half-neg-shift1" #[intV (-2), intV 1, intV 1],
    mkCase "ok/round/tie-pos-shift2" #[intV 8, intV (-2), intV 2],
    mkCase "ok/round/tie-neg-shift2" #[intV (-8), intV 2, intV 2],
    mkCase "ok/round/non-tie-pos-shift2" #[intV 7, intV 2, intV 2],
    mkCase "ok/round/non-tie-neg-shift2" #[intV (-7), intV (-2), intV 2],
    mkCase "ok/round/non-tie-pos-shift3" #[intV 5, intV 0, intV 3],
    mkCase "ok/round/non-tie-neg-shift3" #[intV (-5), intV 0, intV 3],
    mkCase "ok/exact/sum-divisible-shift1" #[intV 21, intV 11, intV 1],
    mkCase "ok/exact/sum-divisible-shift2-neg" #[intV (-21), intV 5, intV 2],
    mkCase "ok/shift0/zero-sum" #[intV 9, intV (-9), intV 0],
    mkCase "ok/shift0/positive-sum" #[intV 5, intV 3, intV 0],
    mkCase "ok/shift0/negative-sum" #[intV (-5), intV (-3), intV 0],
    mkCase "ok/boundary/max-plus-zero-shift0" #[intV maxInt257, intV 0, intV 0],
    mkCase "ok/boundary/min-plus-zero-shift0" #[intV minInt257, intV 0, intV 0],
    mkCase "ok/boundary/max-plus-min-shift0" #[intV maxInt257, intV minInt257, intV 0],
    mkCase "ok/boundary/max-plus-max-shift256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/boundary/min-plus-min-shift256" #[intV minInt257, intV minInt257, intV 256],
    mkCase "ok/boundary/max-plus-zero-shift256" #[intV maxInt257, intV 0, intV 256],
    mkCase "ok/boundary/min-plus-zero-shift256" #[intV minInt257, intV 0, intV 256],
    mkCase "ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 0, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 0, intV 256],
    mkCase "ok/order/below-null-preserved" #[.null, intV 5, intV 2, intV 1],
    mkCase "ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-10), intV 3, intV 1],
    mkCase "quiet/overflow/max-plus-one-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "quiet/overflow/min-minus-one-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCaseFromIntVals "quiet/nan/x-via-program-shift1" #[.nan, .num 5, .num 1],
    mkCaseFromIntVals "quiet/nan/w-via-program-shift1" #[.num 5, .nan, .num 1],
    mkCaseFromIntVals "quiet/nan/both-via-program-shift1" #[.nan, .nan, .num 1],
    mkCaseFromIntVals "quiet/nan/x-via-program-shift0" #[.nan, .num 5, .num 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-two-items-non-int" #[.null, .cell Cell.empty],
    mkCase "type/shift-pop-first-null" #[intV 1, intV 2, .null],
    mkCase "type/shift-pop-first-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/w-pop-second-null" #[intV 5, .null, intV 1],
    mkCase "type/x-pop-third-null" #[.null, intV 5, intV 1],
    mkCase "error-order/type-shift-before-w-when-both-non-int" #[intV 5, .cell Cell.empty, .null],
    mkCase "error-order/type-w-before-x-when-shift-valid" #[.null, .cell Cell.empty, intV 1],
    mkCase "range/shift-negative" #[intV 5, intV 6, intV (-1)],
    mkCase "range/shift-over256" #[intV 5, intV 6, intV 257],
    mkCaseFromIntVals "range/shift-nan-via-program" #[.num 5, .num 6, .nan],
    mkCase "error-order/range-before-w-type-negative-shift" #[intV 5, .null, intV (-1)],
    mkCase "error-order/range-before-x-type-over256-shift" #[.null, intV 5, intV 257],
    mkCaseFromIntVals "error-order/pushint-range-x-high-before-op"
      #[.num (maxInt257 + 1), .num 5, .num 1],
    mkCaseFromIntVals "error-order/pushint-range-x-low-before-op"
      #[.num (minInt257 - 1), .num 5, .num 1],
    mkCaseFromIntVals "error-order/pushint-range-w-high-before-op"
      #[.num 5, .num (maxInt257 + 1), .num 1],
    mkCaseFromIntVals "error-order/pushint-range-shift-high-before-op"
      #[.num 5, .num 6, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-range-both-before-op"
      #[.num (pow2 257), .num (-(pow2 257)), .num 1],
    mkCase "error-order/range-before-w-type-via-program" #[intV 5, .null]
      #[.pushInt (.num (-1)), qaddrshiftmodrInstr],
    mkCase "error-order/underflow-before-range-via-program" #[]
      #[.pushInt (.num (-1)), qaddrshiftmodrInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 5, intV 2, intV 1]
      #[.pushInt (.num qaddrshiftmodrSetGasExact), .tonEnvOp .setGasLimit, qaddrshiftmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 5, intV 2, intV 1]
      #[.pushInt (.num qaddrshiftmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qaddrshiftmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020841
      count := 700
      gen := genQaddrshiftmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADDRSHIFTMODR
