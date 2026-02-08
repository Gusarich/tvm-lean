import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTADDDIVMODC

/-
LSHIFTADDDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 1 true false none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/range ordering)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, ceil mode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xa9c2` decode branch)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.shlDivMod` add-mode encode path)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, error precedence)

Branch counts used for this suite (LSHIFTADDDIVMODC specialization):
- Lean specialization: 9 branch sites / 15 terminal outcomes
  (dispatch/fallback; arity gate; runtime-shift pop/type; bad-shift range gate;
   `y/w/x` pop ordering; numeric-vs-invalid split; divisor-zero split;
   non-quiet push-int overflow funnels for `d=3`).
- C++ specialization (`exec_shldivmod`, mode=0): 9 branch sites / 14 aligned outcomes
  (version/add-remap guard; invalid-opcode guard; underflow gate;
   runtime shift pop/range gate; `y/w/x` pop_int ordering; divisor-zero split;
   `d=3` two-result push path with overflow traps).

Key risk areas covered:
- ceil quotient/remainder sign behavior for `(x << shift) + w` with mixed signs;
- strict runtime-shift range gate (`rangeChk`) before `y/w/x` pop/type checks;
- explicit pop/error ordering (`shift`, then `y`, then `w`, then `x`);
- non-quiet NaN/divzero/type funnels to exceptions (`rangeChk`, `typeChk`, `intOv`);
- signed 257-bit overflow after large shifts and near-boundary addends;
- deterministic gas cliff via exact and exact-minus-one `SETGASLIMIT`.
-/

private def lshiftadddivmodcId : InstrId := { name := "LSHIFTADDDIVMODC" }

private def lshiftadddivmodcInstr : Instr :=
  .arithExt (.shlDivMod 3 1 true false none)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftadddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftadddivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[lshiftadddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runLshiftadddivmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftadddivmodcInstr stack

private def runLshiftadddivmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9715)) stack

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

private def lshiftadddivmodcSetGasExact : Int :=
  computeExactGasBudget lshiftadddivmodcInstr

private def lshiftadddivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftadddivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 15, 31, 63, 127, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-3, -2, -1, 257, 258, 511]

private def smallXPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def smallWPool : Array Int :=
  #[-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

private def smallNonZeroYPool : Array Int :=
  #[-6, -5, -4, -3, -2, -1, 1, 2, 3, 4, 5, 6]

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode < 3 then
    pickFromNatPool shiftBoundaryPool rng1
  else
    randNat rng1 0 256

private def classifyLshiftadddivmodc (x w y : Int) (shift : Nat) : String :=
  if y = 0 then
    "error/divzero"
  else
    let tmp := x * intPow2 shift + w
    let (q, r) := divModRound tmp y 1
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "error/overflow"
    else if r = 0 then
      "ok/exact"
    else
      "ok/inexact"

private def mkFiniteFuzzCase
    (shape : Nat)
    (x w y : Int)
    (shift : Nat) : OracleCase :=
  let kind := classifyLshiftadddivmodc x w y shift
  mkCase s!"/fuzz/shape-{shape}/{kind}" #[intV x, intV w, intV y, intV (Int.ofNat shift)]

private def genLshiftadddivmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 35
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y0, r4) := pickInt257Boundary r3
      let y := if y0 = 0 then 1 else y0
      let (shift, r5) := pickFromNatPool shiftBoundaryPool r4
      (mkFiniteFuzzCase shape x w y shift, r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickValidShift r4
      (mkFiniteFuzzCase shape x w y shift, r5)
    else if shape = 2 then
      let (x, r2) := pickFromIntPool smallXPool rng1
      let (w, r3) := pickFromIntPool smallWPool r2
      let (y, r4) := pickFromIntPool smallNonZeroYPool r3
      let (shift, r5) := pickFromNatPool shiftBoundaryPool r4
      (mkFiniteFuzzCase shape x w y shift, r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/error/divzero" #[intV x, intV w, intV 0, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      (mkCase s!"/fuzz/shape-{shape}/error/overflow/max-shift1-add2-div1"
        #[intV maxInt257, intV 2, intV 1, intV 1], rng1)
    else if shape = 5 then
      (mkCase s!"/fuzz/shape-{shape}/error/overflow/min-shift1-add0-div1"
        #[intV minInt257, intV 0, intV 1, intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/error/overflow/one-shift256-add1-div1"
        #[intV 1, intV 1, intV 1, intV 256], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/error/overflow/negone-shift256-add-neg1-div-neg1"
        #[intV (-1), intV (-1), intV (-1), intV 256], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/error/range/shift-neg-one" #[intV x, intV w, intV y, intV (-1)], r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/error/range/shift-257" #[intV x, intV w, intV y, intV 257], r4)
    else if shape = 10 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV w], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/underflow/three-args" #[intV x, intV w, intV y], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shiftLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/shift-top-non-int" #[intV x, intV w, intV y, shiftLike], r5)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let (yLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/y-second-non-int"
        #[intV x, intV w, yLike, intV (Int.ofNat shift)], r5)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      let (wLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/w-third-non-int"
        #[intV x, wLike, intV y, intV (Int.ofNat shift)], r5)
    else if shape = 17 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      let (xLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/x-fourth-non-int"
        #[xLike, intV w, intV y, intV (Int.ofNat shift)], r5)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (wLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-shift-before-y-when-both-non-int"
        #[intV x, wLike, .null, .cell Cell.empty], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (wLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-w-after-shift-int"
        #[intV x, wLike, .cell Cell.empty, intV 3], r3)
    else if shape = 20 then
      let (y, r2) := pickNonZeroInt rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-x-after-shift-y-int"
        #[xLike, .cell Cell.empty, intV y, intV 3], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error/range/shift-nan-via-program"
        #[IntVal.num x, IntVal.num w, IntVal.num y, IntVal.nan], r4)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error/intov/nan-y-via-program"
        #[IntVal.num x, IntVal.num w, IntVal.nan, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error/intov/nan-w-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 24 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error/intov/nan-x-via-program"
        #[IntVal.nan, IntVal.num w, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 25 then
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error/range/nan-all-via-program"
        #[IntVal.nan, IntVal.nan, IntVal.nan, IntVal.nan], rng1)
    else if shape = 26 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickValidShift r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xOut, IntVal.num w, IntVal.num y, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickValidShift r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        #[IntVal.num x, IntVal.num wOut, IntVal.num y, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yOut, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickValidShift r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num yOut, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 29 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shiftOut, r5) := pickInt257OutOfRange r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num y, IntVal.num shiftOut], r5)
    else if shape = 30 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (yOut, r4) := pickInt257OutOfRange r3
      let (shiftOut, r5) := pickInt257OutOfRange r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        #[IntVal.num xOut, IntVal.num wOut, IntVal.num yOut, IntVal.num shiftOut], r5)
    else if shape = 31 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (rawShift, r5) := pickFromIntPool shiftInvalidPool r4
      let badShift := if rawShift < 0 then rawShift else 257
      (mkCase s!"/fuzz/shape-{shape}/error/range/invalid-shift-from-pool"
        #[intV x, intV w, intV y, intV badShift], r5)
    else if shape = 32 then
      let (x, r2) := pickSigned257ish rng1
      let (wLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-does-not-mask-y-type"
        #[intV x, wLike, .null, intV 257], r3)
    else if shape = 33 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-does-not-mask-w-type"
        #[intV x, .null, intV y, intV 257], r3)
    else if shape = 34 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-does-not-mask-x-type"
        #[.null, intV w, intV y, intV 257], r3)
    else
      let (x, r2) := pickFromIntPool smallXPool rng1
      let (w, r3) := pickFromIntPool smallWPool r2
      let (y, r4) := pickFromIntPool smallNonZeroYPool r3
      let (shift, r5) := pickFromNatPool shiftBoundaryPool r4
      (mkCase s!"/fuzz/shape-{shape}/ok/below-null-preserved"
        #[.null, intV x, intV w, intV y, intV (Int.ofNat shift)], r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftadddivmodcId
  unit := #[
    { name := "/unit/direct/ceil-sign-shift-and-addend-invariants"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 5, 1, 4, -3),
            (-7, 3, 5, 1, -2, -1),
            (7, -3, 5, 1, 3, -4),
            (-7, -3, 5, 1, -3, -2),
            (7, 3, -5, 1, -3, 2),
            (-7, 3, -5, 1, 3, 4),
            (1, 0, 2, 0, 1, -1),
            (-1, 0, 2, 0, 0, -1),
            (5, -3, 3, 2, 6, -1),
            (-5, 3, 3, 2, -5, -2),
            (5, 3, -3, 2, -7, 2),
            (-5, -3, -3, 2, 8, 1),
            (13, -7, 3, 2, 15, 0),
            (-13, 7, 3, 2, -15, 0),
            (0, 9, 7, 123, 2, -5)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/w={w}/y={y}/shift={shift}"
                (runLshiftadddivmodcDirect #[intV x, intV w, intV y, intV (Int.ofNat shift)])
                #[intV q, intV r] }
    ,
    { name := "/unit/direct/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 0, 1, 0, maxInt257, 0),
            (minInt257, 0, 1, 0, minInt257, 0),
            (minInt257 + 1, 0, -1, 0, maxInt257, 0),
            (maxInt257, -1, 2, 1, maxInt257, -1),
            (minInt257, 1, 2, 1, minInt257 + 1, -1),
            (maxInt257, 0, -2, 1, minInt257 + 1, 0),
            (pow2 255, 0, 2, 1, pow2 255, 0),
            (-(pow2 255), 0, 2, 1, -(pow2 255), 0),
            (maxInt257, -maxInt257, 3, 0, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectOkStack s!"/unit/boundary/x={x}/w={w}/y={y}/shift={shift}"
                (runLshiftadddivmodcDirect #[intV x, intV w, intV y, intV (Int.ofNat shift)])
                #[intV q, intV r] }
    ,
    { name := "/unit/error/divzero-overflow-and-range"
      run := do
        expectErr "/unit/error/divzero/nonzero-over-zero"
          (runLshiftadddivmodcDirect #[intV 7, intV 9, intV 0, intV 1]) .intOv
        expectErr "/unit/error/divzero/zero-over-zero"
          (runLshiftadddivmodcDirect #[intV 0, intV 0, intV 0, intV 3]) .intOv
        expectErr "/unit/error/overflow/max-shift1-add2-div1"
          (runLshiftadddivmodcDirect #[intV maxInt257, intV 2, intV 1, intV 1]) .intOv
        expectErr "/unit/error/overflow/min-shift1-add0-div1"
          (runLshiftadddivmodcDirect #[intV minInt257, intV 0, intV 1, intV 1]) .intOv
        expectErr "/unit/error/overflow/one-shift256-add1-div1"
          (runLshiftadddivmodcDirect #[intV 1, intV 1, intV 1, intV 256]) .intOv
        expectErr "/unit/error/overflow/negone-shift256-add-neg1-div-neg1"
          (runLshiftadddivmodcDirect #[intV (-1), intV (-1), intV (-1), intV 256]) .intOv
        expectErr "/unit/error/range/shift-neg-one"
          (runLshiftadddivmodcDirect #[intV 5, intV 3, intV 7, intV (-1)]) .rangeChk
        expectErr "/unit/error/range/shift-257"
          (runLshiftadddivmodcDirect #[intV 5, intV 3, intV 7, intV 257]) .rangeChk }
    ,
    { name := "/unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "/unit/underflow/empty" (runLshiftadddivmodcDirect #[]) .stkUnd
        expectErr "/unit/underflow/one-arg" (runLshiftadddivmodcDirect #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-args" (runLshiftadddivmodcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/underflow/three-args" (runLshiftadddivmodcDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-with-three-items"
          (runLshiftadddivmodcDirect #[.null, .cell Cell.empty, .null]) .stkUnd
        expectErr "/unit/type/pop-shift-first"
          (runLshiftadddivmodcDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/unit/type/pop-y-second"
          (runLshiftadddivmodcDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/unit/type/pop-w-third"
          (runLshiftadddivmodcDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "/unit/type/pop-x-fourth"
          (runLshiftadddivmodcDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/unit/error-order/pop-shift-before-y-when-both-non-int"
          (runLshiftadddivmodcDirect #[intV 1, .cell Cell.empty, .null, .null]) .typeChk
        expectErr "/unit/error-order/pop-y-before-w-after-shift-int"
          (runLshiftadddivmodcDirect #[intV 1, .null, .cell Cell.empty, intV 3]) .typeChk
        expectErr "/unit/error-order/pop-w-before-x-after-shift-y-int"
          (runLshiftadddivmodcDirect #[.null, .cell Cell.empty, intV 2, intV 3]) .typeChk
        expectErr "/unit/error-order/bad-shift-does-not-mask-y-type"
          (runLshiftadddivmodcDirect #[intV 1, intV 2, .null, intV 257]) .rangeChk
        expectErr "/unit/error-order/bad-shift-does-not-mask-w-type"
          (runLshiftadddivmodcDirect #[intV 1, .null, intV 2, intV 257]) .rangeChk
        expectErr "/unit/error-order/bad-shift-does-not-mask-x-type"
          (runLshiftadddivmodcDirect #[.null, intV 1, intV 2, intV 257]) .rangeChk }
    ,
    { name := "/unit/direct/pop-order-top-four-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-null"
          (runLshiftadddivmodcDirect #[.null, intV 7, intV 3, intV 5, intV 1]) #[.null, intV 4, intV (-3)]
        expectOkStack "/unit/pop-order/below-cell"
          (runLshiftadddivmodcDirect #[.cell Cell.empty, intV (-7), intV 3, intV 5, intV 1])
          #[.cell Cell.empty, intV (-2), intV (-1)] }
    ,
    { name := "/unit/opcode/decode-lshiftadddivmodc-sequence"
      run := do
        let program : Array Instr := #[lshiftadddivmodcInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshiftadddivmodc" s0 lshiftadddivmodcInstr 16
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end-expected-exhausted-got-{s2.bitsRemaining}") }
    ,
    { name := "/unit/dispatch/non-lshiftadddivmodc-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftadddivmodcDispatchFallback #[]) #[intV 9715] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign/pos-pos-pos-shift1" #[intV 7, intV 3, intV 5, intV 1],
    mkCase "/ok/ceil/sign/neg-pos-pos-shift1" #[intV (-7), intV 3, intV 5, intV 1],
    mkCase "/ok/ceil/sign/pos-neg-pos-shift1" #[intV 7, intV (-3), intV 5, intV 1],
    mkCase "/ok/ceil/sign/neg-neg-pos-shift1" #[intV (-7), intV (-3), intV 5, intV 1],
    mkCase "/ok/ceil/sign/pos-pos-negdiv-shift1" #[intV 7, intV 3, intV (-5), intV 1],
    mkCase "/ok/ceil/sign/neg-pos-negdiv-shift1" #[intV (-7), intV 3, intV (-5), intV 1],
    mkCase "/ok/ceil/sign/near-zero-pos-divisor" #[intV 1, intV 0, intV 2, intV 0],
    mkCase "/ok/ceil/sign/near-zero-neg-x-pos-divisor" #[intV (-1), intV 0, intV 2, intV 0],
    mkCase "/ok/ceil/addend/cancel-positive" #[intV 13, intV (-7), intV 3, intV 2],
    mkCase "/ok/ceil/addend/cancel-negative" #[intV (-13), intV 7, intV 3, intV 2],
    mkCase "/ok/ceil/addend/positive-w-only" #[intV 0, intV 9, intV 7, intV 123],
    mkCase "/ok/ceil/addend/negative-w-only" #[intV 0, intV (-9), intV 7, intV 123],
    mkCase "/ok/boundary/max-shift0-div1" #[intV maxInt257, intV 0, intV 1, intV 0],
    mkCase "/ok/boundary/min-shift0-div1" #[intV minInt257, intV 0, intV 1, intV 0],
    mkCase "/ok/boundary/min-plus-one-shift0-div-neg1" #[intV (minInt257 + 1), intV 0, intV (-1), intV 0],
    mkCase "/ok/boundary/max-shift1-add-neg1-div2" #[intV maxInt257, intV (-1), intV 2, intV 1],
    mkCase "/ok/boundary/min-shift1-add-one-div2" #[intV minInt257, intV 1, intV 2, intV 1],
    mkCase "/ok/boundary/max-shift1-div-neg2" #[intV maxInt257, intV 0, intV (-2), intV 1],
    mkCase "/ok/boundary/pow255-shift1-div2" #[intV (pow2 255), intV 0, intV 2, intV 1],
    mkCase "/ok/boundary/neg-pow255-shift1-div2" #[intV (-(pow2 255)), intV 0, intV 2, intV 1],
    mkCase "/ok/order/below-null-preserved" #[.null, intV 7, intV 3, intV 5, intV 1],
    mkCase "/ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-7), intV 3, intV 5, intV 1],
    mkCase "/error/divzero/nonzero-over-zero" #[intV 7, intV 9, intV 0, intV 1],
    mkCase "/error/divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 3],
    mkCase "/error/overflow/max-shift1-add2-div1" #[intV maxInt257, intV 2, intV 1, intV 1],
    mkCase "/error/overflow/min-shift1-add0-div1" #[intV minInt257, intV 0, intV 1, intV 1],
    mkCase "/error/overflow/one-shift256-add1-div1" #[intV 1, intV 1, intV 1, intV 256],
    mkCase "/error/overflow/negone-shift256-add-neg1-div-neg1" #[intV (-1), intV (-1), intV (-1), intV 256],
    mkCase "/error/range/shift-neg-one" #[intV 7, intV 3, intV 5, intV (-1)],
    mkCase "/error/range/shift-over-256" #[intV 7, intV 3, intV 5, intV 257],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-type-with-three-items"
      #[.null, .cell Cell.empty, .null],
    mkCase "/type/pop-shift-first-null" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 1, intV 2, intV 3, .cell Cell.empty],
    mkCase "/type/pop-y-second-null" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/pop-w-third-null" #[intV 1, .null, intV 2, intV 3],
    mkCase "/type/pop-x-fourth-null" #[.null, intV 1, intV 2, intV 3],
    mkCase "/error-order/pop-shift-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null, .null],
    mkCase "/error-order/pop-y-before-w-after-shift-int"
      #[intV 1, .null, .cell Cell.empty, intV 3],
    mkCase "/error-order/pop-w-before-x-after-shift-y-int"
      #[.null, .cell Cell.empty, intV 2, intV 3],
    mkCase "/error-order/bad-shift-does-not-mask-y-type"
      #[intV 1, intV 2, .null, intV 257],
    mkCase "/error-order/bad-shift-does-not-mask-w-type"
      #[intV 1, .null, intV 2, intV 257],
    mkCase "/error-order/bad-shift-does-not-mask-x-type"
      #[.null, intV 1, intV 2, intV 257],
    mkCaseFromIntVals "/error/range/shift-nan-via-program"
      #[IntVal.num 7, IntVal.num 3, IntVal.num 5, IntVal.nan],
    mkCase "/error-order/shift-nan-via-program-before-y-type"
      #[intV 1, intV 2, .null] #[.pushInt .nan, lshiftadddivmodcInstr],
    mkCase "/error-order/shift-nan-via-program-before-w-type"
      #[intV 1, .null, intV 2] #[.pushInt .nan, lshiftadddivmodcInstr],
    mkCase "/error-order/shift-nan-via-program-before-x-type"
      #[.null, intV 1, intV 2] #[.pushInt .nan, lshiftadddivmodcInstr],
    mkCaseFromIntVals "/error/intov/nan-y-via-program"
      #[IntVal.num 7, IntVal.num 3, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "/error/intov/nan-w-via-program"
      #[IntVal.num 7, IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "/error/intov/nan-x-via-program"
      #[IntVal.nan, IntVal.num 3, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "/error/range/nan-all-via-program"
      #[IntVal.nan, IntVal.nan, IntVal.nan, IntVal.nan],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 2, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 2, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-w-high-before-op"
      #[IntVal.num 2, IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-w-low-before-op"
      #[IntVal.num 2, IntVal.num (minInt257 - 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 2, IntVal.num 3, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-low-before-op"
      #[IntVal.num 2, IntVal.num 3, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-high-before-op"
      #[IntVal.num 2, IntVal.num 3, IntVal.num 4, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-low-before-op"
      #[IntVal.num 2, IntVal.num 3, IntVal.num 4, IntVal.num (minInt257 - 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 5, intV 1]
      #[.pushInt (.num lshiftadddivmodcSetGasExact), .tonEnvOp .setGasLimit, lshiftadddivmodcInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 5, intV 1]
      #[.pushInt (.num lshiftadddivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftadddivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020890
      count := 700
      gen := genLshiftadddivmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTADDDIVMODC
