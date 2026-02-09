import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTDIV

/-
LSHIFTDIV branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shlDivMod 1 (-1) false false none)` path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xa9c4..0xa9c6` decode to `.arithExt (.shlDivMod 1 ... false false none)`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, opcode registration in `register_div_ops`)

Branch counts used for this suite:
- Lean (LSHIFTDIV specialization): 8 branch sites / 11 terminal outcomes
  (dispatch/fallback; runtime-shift source; explicit underflow gate; shift range check;
   operand-shape numeric-vs-NaN split; divisor-zero split; round-mode validity split;
   non-quiet `pushIntQuiet` success-vs-`intOv`).
- C++ (`exec_shldivmod`, mode=0): 7 branch sites / 10 aligned outcomes
  (mode/immediate-shift gate; versioned add-remap/invalid-op guard; underflow guard;
   runtime shift range gate; v13 invalid-input/shift funnel; `d` switch;
   `push_int_quiet` overflow/NaN throw in non-quiet mode).

Key risk areas covered:
- floor quotient semantics for mixed signs and `shift ∈ [0, 256]`;
- strict pop/error order: underflow guard before shift type checks, then `shift`, `y`, `x`;
- runtime shift range errors (`-1`, `257`, `NaN` shift via program only);
- divisor-zero and NaN operand funnels to non-quiet `intOv`;
- signed-257 overflow on quotient push for large `x << shift`;
- exact gas boundary for `PUSHINT n; SETGASLIMIT; LSHIFTDIV`.
-/

private def lshiftdivId : InstrId := { name := "LSHIFTDIV" }

private def lshiftdivInstr : Instr :=
  .arithExt (.shlDivMod 1 (-1) false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftdivInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftdivId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push lshiftdivInstr) gasLimits fuel

private def runLshiftdivDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftdivInstr stack

private def runLshiftdivDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4444)) stack

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

private def lshiftdivSetGasExact : Int :=
  computeExactGasBudget lshiftdivInstr

private def lshiftdivSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftdivInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def outOfRangeInputPool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def classifyLshiftdiv (x y : Int) (shift : Nat) : String :=
  if y = 0 then
    "divzero"
  else
    let t : Int := x * pow2 shift
    let (q, r) := divModRound t y (-1)
    if !intFitsSigned257 q then
      "overflow"
    else if t = 0 then
      "zero"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genLshiftdivFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyLshiftdiv x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-x"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyLshiftdiv x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-shift"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyLshiftdiv x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-random"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyLshiftdiv x 0 shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/divisor-zero"
        #[intV x, intV 0, intV (Int.ofNat shift)], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/overflow/max-shift1-div1"
        #[intV maxInt257, intV 1, intV 1], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/overflow/min-shift0-div-neg1"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow/one-non-int" #[.null], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/two-items-top-non-int" #[intV x, .null], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (useCell, r4) := randBool r3
      let shiftLike : Value := if useCell then .cell Cell.empty else .null
      (mkCase s!"fuzz/shape-{shape}/type/shift-pop-first"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (useCell, r4) := randBool r3
      let yLike : Value := if useCell then .cell Cell.empty else .null
      (mkCase s!"fuzz/shape-{shape}/type/y-pop-second"
        #[intV x, yLike, intV (Int.ofNat shift)], r4)
    else if shape = 12 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      let (useCell, r4) := randBool r3
      let xLike : Value := if useCell then .cell Cell.empty else .null
      (mkCase s!"fuzz/shape-{shape}/type/x-pop-third"
        #[xLike, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative-via-program"
        #[intV x, intV y] #[.pushInt (.num (-1)), lshiftdivInstr], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-overmax-via-program"
        #[intV x, intV y] #[.pushInt (.num 257), lshiftdivInstr], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-nan-via-program"
        #[intV x, intV y] #[.pushInt .nan, lshiftdivInstr], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-y-type"
        #[intV x, .null] #[.pushInt (.num 257), lshiftdivInstr], r2)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 18 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan/x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 19 then
      let (oor, r2) := pickFromPool outOfRangeInputPool rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-int/x-via-program"
        #[IntVal.num oor, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (oor, r3) := pickFromPool outOfRangeInputPool r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-int/y-via-program"
        #[IntVal.num x, IntVal.num oor, IntVal.num (Int.ofNat shift)], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-before-op"
        #[intV x, intV y] #[.pushInt (.num (pow2 257)), lshiftdivInstr], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftdivId
  unit := #[
    { name := "unit/direct/floor-sign-zero-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, 4),
            (-7, 3, 1, -5),
            (7, -3, 1, -5),
            (-7, -3, 1, 4),
            (1, 2, 0, 0),
            (-1, 2, 0, -1),
            (5, 1, 0, 5),
            (5, -1, 0, -5),
            (0, 5, 200, 0),
            (13, 3, 2, 17),
            (-13, 3, 2, -18)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}"
            (runLshiftdivDirect #[intV x, intV y, intV (Int.ofNat shift)]) #[intV expected] }
    ,
    { name := "unit/direct/boundary-successes-and-overflow-divzero-intov"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257),
            (minInt257, 1, 0, minInt257),
            (maxInt257, 2, 1, maxInt257),
            (minInt257, 2, 1, minInt257),
            (maxInt257 - 1, 2, 1, maxInt257 - 1),
            (minInt257 + 1, 2, 1, minInt257 + 1),
            (pow2 255, 2, 1, pow2 255),
            (-(pow2 255), 2, 1, -(pow2 255))
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"boundary/({x}<<{shift})/{y}"
            (runLshiftdivDirect #[intV x, intV y, intV (Int.ofNat shift)]) #[intV expected]
        expectErr "divzero/nonzero-over-zero"
          (runLshiftdivDirect #[intV 7, intV 0, intV 1]) .intOv
        expectErr "overflow/min-shift0-div-neg1"
          (runLshiftdivDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "overflow/max-shift1-div1"
          (runLshiftdivDirect #[intV maxInt257, intV 1, intV 1]) .intOv }
    ,
    { name := "unit/error/underflow-type-ordering-and-precheck"
      run := do
        expectErr "underflow/empty" (runLshiftdivDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runLshiftdivDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runLshiftdivDirect #[.null]) .stkUnd
        expectErr "underflow/two-items-top-non-int" (runLshiftdivDirect #[intV 1, .null]) .stkUnd
        expectErr "type/pop-shift-first" (runLshiftdivDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runLshiftdivDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runLshiftdivDirect #[.null, intV 1, intV 2]) .typeChk }
    ,
    { name := "unit/opcode/decode-lshiftdiv-sequence"
      run := do
        let program : Array Instr := #[lshiftdivInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/lshiftdiv" s0 lshiftdivInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-shldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runLshiftdivDispatchFallback #[]) #[intV 4444] }
  ]
  oracle := #[
    mkCase "ok/floor/sign/pos-pos-inexact" #[intV 7, intV 3, intV 1],
    mkCase "ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 1],
    mkCase "ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 1],
    mkCase "ok/floor/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/floor/shift-zero-pos" #[intV 5, intV 2, intV 0],
    mkCase "ok/floor/shift-zero-neg" #[intV (-5), intV 2, intV 0],
    mkCase "ok/floor/zero-numerator" #[intV 0, intV 5, intV 200],
    mkCase "ok/exact/divisible" #[intV 9, intV 3, intV 2],
    mkCase "ok/exact/divisible-negative" #[intV (-9), intV 3, intV 2],
    mkCase "ok/boundary/max-shift0-div1" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-shift0-div1" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/max-shift1-div2" #[intV maxInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-shift1-div2" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/boundary/max-minus-one-shift1-div2" #[intV (maxInt257 - 1), intV 2, intV 1],
    mkCase "ok/boundary/min-plus-one-shift1-div2" #[intV (minInt257 + 1), intV 2, intV 1],
    mkCase "divzero/nonzero-over-zero" #[intV 7, intV 0, intV 1],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 200],
    mkCase "overflow/min-shift0-div-neg1" #[intV minInt257, intV (-1), intV 0],
    mkCase "overflow/max-shift1-div1" #[intV maxInt257, intV 1, intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "underflow/one-non-int" #[.null],
    mkCase "underflow/two-items-top-non-int" #[intV 1, .null],
    mkCase "type/pop-shift-first-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "type/error-order/shift-before-y-before-x" #[.cell Cell.empty, .null, intV 2],
    mkCase "range/shift-negative-via-program" #[intV 7, intV 3]
      #[.pushInt (.num (-1)), lshiftdivInstr],
    mkCase "range/shift-overmax-via-program" #[intV 7, intV 3]
      #[.pushInt (.num 257), lshiftdivInstr],
    mkCase "range/shift-nan-via-program" #[intV 7, intV 3]
      #[.pushInt .nan, lshiftdivInstr],
    mkCase "error-order/range-before-y-type-via-program" #[intV 7, .null]
      #[.pushInt (.num 257), lshiftdivInstr],
    mkCaseFromIntVals "nan/y-via-program" #[IntVal.num 7, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "nan/x-via-program" #[IntVal.nan, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "range-int/x-via-program"
      #[IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "range-int/y-via-program"
      #[IntVal.num 7, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCase "error-order/pushint-overflow-before-op" #[intV 7, intV 3]
      #[.pushInt (.num (pow2 257)), lshiftdivInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftdivSetGasExact), .tonEnvOp .setGasLimit, lshiftdivInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftdivSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftdivInstr]
  ]
  fuzz := #[
    { seed := 2026020814
      count := 700
      gen := genLshiftdivFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTDIV
