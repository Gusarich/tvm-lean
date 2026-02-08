import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULADDRSHIFTRMOD

/-
MULADDRSHIFTRMOD branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true true 3 0 false none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type ordering)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, runtime-shift `z=0` floor rewrite)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb6a9a*` decode path for non-quiet runtime-shift MUL+ADD+SHR/MOD family)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode wiring)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`DoubleInt::rshift`, `DoubleInt::mod_pow2`)

Branch counts used for this suite (MULADDRSHIFTRMOD specialization):
- Lean: ~10 branch sites / ~14 terminal outcomes
  (dispatch/fallback; stack-depth precheck; runtime-shift pop type/range gate;
   `w`/`y`/`x` pop type ordering; early non-quiet bad-shift `rangeChk`;
   shift-zero round rewrite; numeric-vs-invalid operand split;
   dual push with overflow-to-`intOv` at quotient push).
- C++: ~9 branch sites / ~12 aligned terminal outcomes
  (`check_underflow(4)`; runtime `pop_long`; non-quiet range gate;
   `w`/`y`/`x` pop order; invalid-input funnel;
   quotient/remainder push with overflow error path).

Key risk areas covered:
- pop/error precedence is runtime shift `z` first, then `w`, then `y`, then `x`;
- in non-quiet mode, invalid runtime shift (`z<0`, `z>256`, or NaN shift) throws `rangeChk`
  before popping `w`/`y`/`x`;
- combined-op rounding sensitivity (`x*y + w`) with nearest ties for `z>0`,
  and `z=0` rewrite to floor mode (`roundMode := -1`);
- `q` then `r` output ordering, including sign/tie behavior;
- boundary behavior at shifts `0` and `256`, including signed-257 endpoints;
- signed-257 overflow funnels to `intOv` (both arithmetic overflow and invalid inputs);
- NaN and out-of-range integer injection is oracle-only via `PUSHINT` prelude;
- exact gas cliff (`PUSHINT n; SETGASLIMIT; MULADDRSHIFTRMOD`) exact vs minus-one.
-/

private def muladdrshiftrmodId : InstrId := { name := "MULADDRSHIFTRMOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def muladdrshiftrmodInstr : Instr :=
  .arithExt (.shrMod true true 3 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muladdrshiftrmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := muladdrshiftrmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[muladdrshiftrmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runMuladdrshiftrmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt muladdrshiftrmodInstr stack

private def runMuladdrshiftrmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9087)) stack

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

private def muladdrshiftrmodSetGasExact : Int :=
  computeExactGasBudget muladdrshiftrmodInstr

private def muladdrshiftrmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muladdrshiftrmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieShift1Pool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieShift2Pool : Array Int :=
  #[-14, -10, -6, -2, 2, 6, 10, 14]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

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

private def classifyMuladdrshiftrmod (x y w : Int) (shift : Nat) : String :=
  let tmp : Int := x * y + w
  let roundMode : Int := if shift = 0 then -1 else 0
  let q := rshiftPow2Round tmp shift roundMode
  let r := modPow2Round tmp shift roundMode
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "overflow"
  else if shift = 0 then
    "shift0"
  else
    let p := pow2 shift
    let rem := Int.emod tmp p
    if rem = pow2 (shift - 1) then
      "tie"
    else if rem = 0 then
      "exact"
    else if x = maxInt257 || x = minInt257 || y = maxInt257 || y = minInt257 || w = maxInt257 || w = minInt257 then
      "boundary"
    else
      "inexact"

private def genMuladdrshiftrmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftBoundary r4
      let kind := classifyMuladdrshiftrmod x y w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-boundary-boundary-boundary-shift"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftBoundary r4
      let kind := classifyMuladdrshiftrmod x y w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-signed-signed-boundary-shift"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftMixed r4
      let kind := classifyMuladdrshiftrmod x y w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-signed-signed"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftMixed r4
      let kind := classifyMuladdrshiftrmod x y w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-boundary-signed"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftMixed r4
      let kind := classifyMuladdrshiftrmod x y w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/signed-signed-boundary"
        #[intV x, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyMuladdrshiftrmod x y 0 shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/w-zero"
        #[intV x, intV y, intV 0, intV (Int.ofNat shift)], r4)
    else if shape = 6 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyMuladdrshiftrmod 0 y w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/x-zero"
        #[intV 0, intV y, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyMuladdrshiftrmod x 0 w shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/y-zero"
        #[intV x, intV 0, intV w, intV (Int.ofNat shift)], r4)
    else if shape = 8 then
      let (tmp, r2) := pickFromPool tieShift1Pool rng1
      (mkCase s!"fuzz/shape-{shape}/ok/tie/shift1"
        #[intV tmp, intV 1, intV 0, intV 1], r2)
    else if shape = 9 then
      let (tmp, r2) := pickFromPool tieShift2Pool rng1
      (mkCase s!"fuzz/shape-{shape}/ok/tie/shift2"
        #[intV tmp, intV 1, intV 0, intV 2], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"fuzz/shape-{shape}/ok/boundary/shift256-edge"
        #[intV x, intV y, intV w, intV 256], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let kind := classifyMuladdrshiftrmod x y w 0
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/shift0-floor-rewrite"
        #[intV x, intV y, intV w, intV 0], r4)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/intov/overflow-shift0-max-times-two"
        #[intV maxInt257, intV 2, intV 0, intV 0], rng1)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/intov/overflow-shift0-min-times-negone"
        #[intV minInt257, intV (-1), intV 0, intV 0], rng1)
    else if shape = 14 then
      (mkCase s!"fuzz/shape-{shape}/intov/overflow-shift1-max-times-max"
        #[intV maxInt257, intV maxInt257, intV 0, intV 1], rng1)
    else if shape = 15 then
      (mkCase s!"fuzz/shape-{shape}/intov/overflow-shift1-min-times-min"
        #[intV minInt257, intV minInt257, intV 0, intV 1], rng1)
    else if shape = 16 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-item" #[intV x], r2)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-items" #[intV x, intV y], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"fuzz/shape-{shape}/underflow/three-items" #[intV x, intV y, intV w], r4)
    else if shape = 20 then
      let (a, r2) := pickNonInt rng1
      let (b, r3) := pickNonInt r2
      let (c, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-type-three-items"
        #[a, b, c], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (zLike, r5) := pickNonInt r4
      (mkCase s!"fuzz/shape-{shape}/type/shift-pop-first"
        #[intV x, intV y, intV w, zLike], r5)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let (wLike, r5) := pickNonInt r4
      (mkCase s!"fuzz/shape-{shape}/type/w-pop-second"
        #[intV x, intV y, wLike, intV (Int.ofNat shift)], r5)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let (yLike, r5) := pickNonInt r4
      (mkCase s!"fuzz/shape-{shape}/type/y-pop-third"
        #[intV x, yLike, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 24 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      let (xLike, r5) := pickNonInt r4
      (mkCase s!"fuzz/shape-{shape}/type/x-pop-fourth"
        #[xLike, intV y, intV w, intV (Int.ofNat shift)], r5)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative"
        #[intV x, intV y, intV w, intV (-1)], r4)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"fuzz/shape-{shape}/range/shift-over256"
        #[intV x, intV y, intV w, intV 257], r4)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-before-w-type"
        #[intV x, intV y, wLike, intV (-1)], r4)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-before-y-type"
        #[intV x, yLike, intV w, intV 257], r4)
    else if shape = 29 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-before-x-type"
        #[xLike, intV y, intV w, intV (-1)], r4)
    else if shape = 30 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range/shift-nan-via-program"
        #[.num x, .num y, .num w, .nan], r4)
    else if shape = 31 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/intov/nan/w-via-program"
        #[.num x, .num y, .nan, .num (Int.ofNat shift)], r4)
    else if shape = 32 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/intov/nan/y-via-program"
        #[.num x, .nan, .num w, .num (Int.ofNat shift)], r4)
    else if shape = 33 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/intov/nan/x-via-program"
        #[.nan, .num y, .num w, .num (Int.ofNat shift)], r4)
    else if shape = 34 then
      let (shift, r2) := pickShiftMixed rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/intov/nan/all-operands-via-program"
        #[.nan, .nan, .nan, .num (Int.ofNat shift)], r2)
    else if shape = 35 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftMixed r4
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-x-before-op"
        #[.num xOut, .num y, .num w, .num (Int.ofNat shift)], r5)
    else if shape = 36 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftMixed r4
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-y-before-op"
        #[.num x, .num yOut, .num w, .num (Int.ofNat shift)], r5)
    else if shape = 37 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wOut, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftMixed r4
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-w-before-op"
        #[.num x, .num y, .num wOut, .num (Int.ofNat shift)], r5)
    else if shape = 38 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shiftOut, r5) := pickInt257OutOfRange r4
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-range-shift-before-op"
        #[.num x, .num y, .num w, .num shiftOut], r5)
    else
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num (-1)), muladdrshiftrmodInstr], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := muladdrshiftrmodId
  unit := #[
    { name := "/unit/ok/nearest-rounding-sign-ties-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 1, 11, 0),
            (7, 3, 0, 1, 11, -1),
            (-7, 3, 0, 1, -10, -1),
            (7, -3, 0, 1, -10, -1),
            (-7, -3, 0, 1, 11, -1),
            (5, 5, 0, 1, 13, -1),
            (-5, 5, 0, 1, -12, -1),
            (5, -5, 0, 1, -12, -1),
            (-5, -5, 0, 1, 13, -1),
            (42, 6, 3, 3, 32, -1),
            (-42, 6, 3, 3, -31, -1),
            (42, -6, 3, 3, -31, -1),
            (-42, -6, 3, 3, 32, -1),
            (5, 3, 2, 0, 17, 0),
            (-5, 3, 2, 0, -13, 0),
            (1, 1, 0, 1, 1, -1),
            (-1, 1, 0, 1, 0, -1),
            (0, 9, 0, 7, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, w, shift, q, r) =>
              expectOkStack s!"/unit/ok/x={x}/y={y}/w={w}/z={shift}"
                (runMuladdrshiftrmodDirect #[intV x, intV y, intV w, intV (Int.ofNat shift)])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-shift256-and-pop-order"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 1, 0, 0, maxInt257, 0),
            (minInt257, 1, 0, 0, minInt257, 0),
            (maxInt257, 1, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 1, 0, minInt257 + 1, 0),
            (maxInt257, 1, 0, 256, 1, -1),
            (minInt257, 1, 0, 256, -1, 0),
            (maxInt257, 1, -1, 256, 1, -2),
            (minInt257, 1, 1, 256, -1, 1),
            (maxInt257, maxInt257, 0, 256, maxInt257 - 1, 1),
            (maxInt257, 0, maxInt257, 256, 1, -1)
          ]
        for c in checks do
          match c with
          | (x, y, w, shift, q, r) =>
              expectOkStack s!"/unit/boundary/x={x}/y={y}/w={w}/z={shift}"
                (runMuladdrshiftrmodDirect #[intV x, intV y, intV w, intV (Int.ofNat shift)])
                #[intV q, intV r]
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMuladdrshiftrmodDirect #[.null, intV 7, intV 3, intV 0, intV 1])
          #[.null, intV 11, intV (-1)]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMuladdrshiftrmodDirect #[.cell Cell.empty, intV (-7), intV 3, intV 0, intV 1])
          #[.cell Cell.empty, intV (-10), intV (-1)] }
    ,
    { name := "/unit/error/underflow-type-range-and-error-order"
      run := do
        expectErr "/unit/error/underflow/empty" (runMuladdrshiftrmodDirect #[]) .stkUnd
        expectErr "/unit/error/underflow/one-item" (runMuladdrshiftrmodDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow/two-items" (runMuladdrshiftrmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow/three-items" (runMuladdrshiftrmodDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-three-items"
          (runMuladdrshiftrmodDirect #[.null, .cell Cell.empty, .null]) .stkUnd
        expectErr "/unit/error/type/shift-pop-first-null"
          (runMuladdrshiftrmodDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/unit/error/type/shift-pop-first-cell"
          (runMuladdrshiftrmodDirect #[intV 1, intV 2, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type/w-pop-second"
          (runMuladdrshiftrmodDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/unit/error/type/y-pop-third"
          (runMuladdrshiftrmodDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "/unit/error/type/x-pop-fourth"
          (runMuladdrshiftrmodDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/unit/error/range/shift-negative"
          (runMuladdrshiftrmodDirect #[intV 7, intV 3, intV 1, intV (-1)]) .rangeChk
        expectErr "/unit/error/range/shift-over256"
          (runMuladdrshiftrmodDirect #[intV 7, intV 3, intV 1, intV 257]) .rangeChk
        expectErr "/unit/error-order/shift-range-before-w-type"
          (runMuladdrshiftrmodDirect #[intV 7, intV 3, .null, intV (-1)]) .rangeChk
        expectErr "/unit/error-order/shift-range-before-y-type"
          (runMuladdrshiftrmodDirect #[intV 7, .null, intV 3, intV 257]) .rangeChk
        expectErr "/unit/error-order/shift-range-before-x-type"
          (runMuladdrshiftrmodDirect #[.null, intV 7, intV 3, intV (-1)]) .rangeChk }
    ,
    { name := "/unit/error/intov-from-overflow"
      run := do
        expectErr "/unit/intov/overflow-shift0-max-times-two"
          (runMuladdrshiftrmodDirect #[intV maxInt257, intV 2, intV 0, intV 0]) .intOv
        expectErr "/unit/intov/overflow-shift0-min-times-negone"
          (runMuladdrshiftrmodDirect #[intV minInt257, intV (-1), intV 0, intV 0]) .intOv
        expectErr "/unit/intov/overflow-shift1-max-times-max"
          (runMuladdrshiftrmodDirect #[intV maxInt257, intV maxInt257, intV 0, intV 1]) .intOv
        expectErr "/unit/intov/overflow-shift1-min-times-min"
          (runMuladdrshiftrmodDirect #[intV minInt257, intV minInt257, intV 0, intV 1]) .intOv }
    ,
    { name := "/unit/opcode/decode-muladdrshiftrmod-sequence"
      run := do
        let program : Array Instr := #[muladdrshiftrmodInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/opcode/assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode-muladdrshiftrmod" s0 muladdrshiftrmodInstr 24
        let s2 ← expectDecodeStep "/unit/opcode/decode-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMuladdrshiftrmodDispatchFallback #[]) #[intV 9087] }
  ]
  oracle := #[
    mkCase "/ok/round/inexact-pos-pos" #[intV 7, intV 3, intV 1, intV 1],
    mkCase "/ok/round/tie-pos-shift1" #[intV 7, intV 3, intV 0, intV 1],
    mkCase "/ok/round/tie-neg-shift1" #[intV (-7), intV 3, intV 0, intV 1],
    mkCase "/ok/round/tie-pos-negmul-shift1" #[intV 7, intV (-3), intV 0, intV 1],
    mkCase "/ok/round/tie-neg-negmul-shift1" #[intV (-7), intV (-3), intV 0, intV 1],
    mkCase "/ok/round/tie-pos-shift2" #[intV 8, intV 1, intV 0, intV 2],
    mkCase "/ok/round/tie-neg-shift2" #[intV (-8), intV 1, intV 0, intV 2],
    mkCase "/ok/round/non-tie-pos-shift2" #[intV 7, intV 1, intV 0, intV 2],
    mkCase "/ok/round/non-tie-neg-shift2" #[intV (-7), intV 1, intV 0, intV 2],
    mkCase "/ok/round/non-tie-pos-shift3" #[intV 5, intV 1, intV 0, intV 3],
    mkCase "/ok/round/non-tie-neg-shift3" #[intV (-5), intV 1, intV 0, intV 3],
    mkCase "/ok/exact/divisible-shift1" #[intV 21, intV 1, intV 11, intV 1],
    mkCase "/ok/exact/divisible-shift2-neg" #[intV (-21), intV 1, intV 5, intV 2],
    mkCase "/ok/shift0/zero-result" #[intV 9, intV 1, intV (-9), intV 0],
    mkCase "/ok/shift0/positive-result" #[intV 5, intV 3, intV 2, intV 0],
    mkCase "/ok/shift0/negative-result" #[intV (-5), intV 3, intV 2, intV 0],
    mkCase "/ok/boundary/max-times-one-shift0" #[intV maxInt257, intV 1, intV 0, intV 0],
    mkCase "/ok/boundary/min-times-one-shift0" #[intV minInt257, intV 1, intV 0, intV 0],
    mkCase "/ok/boundary/max-times-one-minus-one-shift0" #[intV maxInt257, intV 1, intV (-1), intV 0],
    mkCase "/ok/boundary/min-times-one-plus-one-shift0" #[intV minInt257, intV 1, intV 1, intV 0],
    mkCase "/ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 0, intV 256],
    mkCase "/ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 0, intV 256],
    mkCase "/ok/boundary/max-times-one-minus-one-shift256" #[intV maxInt257, intV 1, intV (-1), intV 256],
    mkCase "/ok/boundary/min-times-one-plus-one-shift256" #[intV minInt257, intV 1, intV 1, intV 256],
    mkCase "/ok/boundary/max-times-max-shift256" #[intV maxInt257, intV maxInt257, intV 0, intV 256],
    mkCase "/ok/boundary/w-dominates-shift256" #[intV maxInt257, intV 0, intV maxInt257, intV 256],
    mkCase "/ok/order/below-null-preserved" #[.null, intV 7, intV 3, intV 0, intV 1],
    mkCase "/ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-7), intV 3, intV 0, intV 1],
    mkCase "/intov/overflow/max-times-two-shift0" #[intV maxInt257, intV 2, intV 0, intV 0],
    mkCase "/intov/overflow/min-times-negone-shift0" #[intV minInt257, intV (-1), intV 0, intV 0],
    mkCase "/intov/overflow/max-times-max-shift1" #[intV maxInt257, intV maxInt257, intV 0, intV 1],
    mkCase "/intov/overflow/min-times-min-shift1" #[intV minInt257, intV minInt257, intV 0, intV 1],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-item" #[intV 1],
    mkCase "/underflow/two-items" #[intV 1, intV 2],
    mkCase "/underflow/three-items" #[intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-type-three-items" #[.null, .cell Cell.empty, .null],
    mkCase "/type/shift-pop-first-null" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/shift-pop-first-cell" #[intV 1, intV 2, intV 3, .cell Cell.empty],
    mkCase "/type/w-pop-second-null" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/y-pop-third-null" #[intV 1, .null, intV 2, intV 3],
    mkCase "/type/x-pop-fourth-null" #[.null, intV 1, intV 2, intV 3],
    mkCase "/range/shift-negative" #[intV 5, intV 6, intV 7, intV (-1)],
    mkCase "/range/shift-over256" #[intV 5, intV 6, intV 7, intV 257],
    mkCase "/error-order/shift-range-before-w-type"
      #[intV 5, intV 6, .null, intV (-1)],
    mkCase "/error-order/shift-range-before-y-type"
      #[intV 5, .null, intV 7, intV 257],
    mkCase "/error-order/shift-range-before-x-type"
      #[.null, intV 6, intV 7, intV (-1)],
    mkCaseFromIntVals "/range/shift-nan-via-program"
      #[.num 5, .num 6, .num 7, .nan],
    mkCaseFromIntVals "/intov/nan/w-via-program"
      #[.num 5, .num 6, .nan, .num 1],
    mkCaseFromIntVals "/intov/nan/y-via-program"
      #[.num 5, .nan, .num 7, .num 1],
    mkCaseFromIntVals "/intov/nan/x-via-program"
      #[.nan, .num 6, .num 7, .num 1],
    mkCaseFromIntVals "/intov/nan/all-via-program"
      #[.nan, .nan, .nan, .num 1],
    mkCaseFromIntVals "/error-order/pushint-range-x-high-before-op"
      #[.num (maxInt257 + 1), .num 6, .num 7, .num 1],
    mkCaseFromIntVals "/error-order/pushint-range-x-low-before-op"
      #[.num (minInt257 - 1), .num 6, .num 7, .num 1],
    mkCaseFromIntVals "/error-order/pushint-range-y-high-before-op"
      #[.num 5, .num (maxInt257 + 1), .num 7, .num 1],
    mkCaseFromIntVals "/error-order/pushint-range-y-low-before-op"
      #[.num 5, .num (minInt257 - 1), .num 7, .num 1],
    mkCaseFromIntVals "/error-order/pushint-range-w-high-before-op"
      #[.num 5, .num 6, .num (maxInt257 + 1), .num 1],
    mkCaseFromIntVals "/error-order/pushint-range-w-low-before-op"
      #[.num 5, .num 6, .num (minInt257 - 1), .num 1],
    mkCaseFromIntVals "/error-order/pushint-range-shift-high-before-op"
      #[.num 5, .num 6, .num 7, .num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-range-shift-low-before-op"
      #[.num 5, .num 6, .num 7, .num (minInt257 - 1)],
    mkCaseFromIntVals "/error-order/pushint-range-multiple-before-op"
      #[.num (pow2 257), .num (-(pow2 257)), .num (maxInt257 + 2), .num 1],
    mkCase "/error-order/underflow-before-range-via-program"
      #[]
      #[.pushInt (.num (-1)), muladdrshiftrmodInstr],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1, intV 1]
      #[.pushInt (.num muladdrshiftrmodSetGasExact), .tonEnvOp .setGasLimit, muladdrshiftrmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1, intV 1]
      #[.pushInt (.num muladdrshiftrmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, muladdrshiftrmodInstr]
  ]
  fuzz := #[
    { seed := 2026020861
      count := 700
      gen := genMuladdrshiftrmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFTRMOD
