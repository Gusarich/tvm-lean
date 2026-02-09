import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTMODR

/-
LSHIFTMODR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod` path)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, nearest mode/ties-to-+∞)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (specialization
`.arithExt (.shlDivMod 2 0 false false none)`):
- Lean: ~8 branch sites / ~11 terminal outcomes
  (dispatch arm; pre-underflow ordering; shift pop/type/range funnel;
   divisor pop/type split; x pop/type split; `y=0` NaN funnel;
   fixed-`d=2` remainder push success vs `intOv`).
- C++: ~7 branch sites / ~11 aligned terminal outcomes
  (`check_underflow(3)`; runtime shift `pop_long` + range gate;
   divisor/x `pop_int` checks; div-by-zero NaN path; `d`-switch for MOD;
   non-quiet `push_int_quiet` overflow behavior).

Key risk areas covered:
- pop/error order: underflow must dominate malformed shift when stack depth < 3;
- shift runtime bounds are strict `[0, 256]` (`rangeChk`) and must be injected via program;
- nearest rounding (R-mode) tie behavior, including negative divisors;
- `y = 0` and NaN operands must surface as non-quiet `intOv`;
- signed-257 boundary behavior near `minInt257`/`maxInt257`;
- exact gas threshold determinism (`PUSHINT n; SETGASLIMIT; LSHIFTMODR`).
-/

private def lshiftModrId : InstrId := { name := "LSHIFTMODR" }

private def lshiftModrInstr : Instr :=
  .arithExt (.shlDivMod 2 0 false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftModrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[lshiftModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runLshiftModrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftModrInstr stack

private def runLshiftModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 606)) stack

private def expectLshiftModr
    (label : String)
    (x : Int)
    (y : Int)
    (shift : Nat)
    (r : Int) : IO Unit :=
  expectOkStack label
    (runLshiftModrDirect #[intV x, intV y, intV (Int.ofNat shift)])
    #[intV r]

private def lshiftModrSetGasExact : Int :=
  computeExactGasBudget lshiftModrInstr

private def lshiftModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftModrInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieXPool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieYPool : Array Int :=
  #[-2, 2]

private def outOfRangeProgramPool : Array Int :=
  #[pow2 257, -(pow2 257)]

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then pickShiftBoundary rng1 else pickShiftUniform rng1

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (outOfRangeProgramPool.size - 1)
  (outOfRangeProgramPool[idx]!, rng')

private def classifyLshiftModr (x y : Int) (shift : Nat) : String :=
  let tmp : Int := x * pow2 shift
  if y = 0 then
    "divzero"
  else
    let (_, r) := divModRound tmp y 0
    if !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genLshiftModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (baseCase, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let y0 := if y = 0 then 1 else y
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyLshiftModr x y0 shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-boundary"
        #[intV x, intV y0, intV (Int.ofNat shift)], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftMixed r3
      let kind := classifyLshiftModr x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-signed"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyLshiftModr x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-x"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 3 then
      let (x, r2) := pickFromPool tieXPool rng1
      let (y, r3) := pickFromPool tieYPool r2
      (mkCase s!"fuzz/shape-{shape}/tie/shift0-pool"
        #[intV x, intV y, intV 0], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/divzero/runtime"
        #[intV x, intV 0, intV (Int.ofNat shift)], r3)
    else if shape = 5 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/zero-x"
        #[intV 0, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyLshiftModr x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/extreme-x"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/type/shift-pop-first"
        #[intV x, intV y, .null], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/type/divisor-pop-second"
        #[intV x, .cell Cell.empty, intV (Int.ofNat shift)], r3)
    else if shape = 9 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/type/x-pop-third"
        #[.null, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/single-item"
        #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative-program"
        #[intV x, intV y] #[.pushInt (.num (-1)), lshiftModrInstr], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-257-program"
        #[intV x, intV y] #[.pushInt (.num 257), lshiftModrInstr], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/range/shift-nan-program"
        #[intV x, intV y] #[.pushInt .nan, lshiftModrInstr], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-y"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 16 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-x"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/range/program-shift-out-of-range-int"
        #[IntVal.num x, IntVal.num y, IntVal.num huge], r4)
    else if shape = 18 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftMixed r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/range/program-x-out-of-range-int"
        #[IntVal.num huge, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let (huge, r4) := pickOutOfRangeProgramInt r3
      (mkInputCase s!"fuzz/shape-{shape}/range/program-y-out-of-range-int"
        #[IntVal.num x, IntVal.num huge, IntVal.num (Int.ofNat shift)], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftModrId
  unit := #[
    { name := "unit/nearest/tie-sign-and-basic-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (0, 5, 0, 0),
            (7, 3, 1, -1),
            (-7, 3, 1, 1),
            (7, -3, 1, -1),
            (-7, -3, 1, 1),
            (3, 2, 0, -1),
            (-3, 2, 0, -1),
            (3, -2, 0, 1),
            (-3, -2, 0, 1),
            (17, 5, 2, -2),
            (-17, 5, 2, 2)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let r := c.2.2.2
          expectLshiftModr s!"{x}<<{shift} modr {y}" x y shift r }
    ,
    { name := "unit/boundary/extremes-shift-edges-and-stack-shape"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 2, 0, -1),
            (minInt257, 2, 0, 0),
            (maxInt257, maxInt257, 1, 0),
            (minInt257, maxInt257, 1, -2),
            (minInt257, minInt257, 0, 0),
            (maxInt257, minInt257, 0, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let r := c.2.2.2
          expectLshiftModr s!"boundary/{x}<<{shift} modr {y}" x y shift r
        expectOkStack "stack/preserve-lower"
          (runLshiftModrDirect #[.null, intV 7, intV 3, intV 1])
          #[.null, intV (-1)] }
    ,
    { name := "unit/error/pop-order-range-and-failure-codes"
      run := do
        expectErr "underflow/empty" (runLshiftModrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runLshiftModrDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int-underflow-before-type" (runLshiftModrDirect #[.null]) .stkUnd
        expectErr "type/shift-pop-first-null" (runLshiftModrDirect #[intV 5, intV 3, .null]) .typeChk
        expectErr "type/divisor-pop-second-null" (runLshiftModrDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/x-pop-third-null" (runLshiftModrDirect #[.null, intV 3, intV 1]) .typeChk
        expectErr "range/shift-negative" (runLshiftModrDirect #[intV 5, intV 3, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runLshiftModrDirect #[intV 5, intV 3, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runLshiftModrDirect #[intV 5, intV 3, .int .nan]) .rangeChk
        expectErr "intov/divisor-zero" (runLshiftModrDirect #[intV 5, intV 0, intV 1]) .intOv }
    ,
    { name := "unit/opcode/encode-decode-roundtrip"
      run := do
        let code ←
          match assembleCp0 [lshiftModrInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        match decodeCp0WithBits (Slice.ofCell code) with
        | .error e =>
            throw (IO.userError s!"decode failed: {e}")
        | .ok (instr, bits, _) =>
            if instr != lshiftModrInstr then
              throw (IO.userError s!"expected {reprStr lshiftModrInstr}, got {reprStr instr}")
            else if bits != 16 then
              throw (IO.userError s!"expected 16-bit decode, got {bits}")
            else
              pure () }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runLshiftModrDispatchFallback #[]) #[intV 606] }
  ]
  oracle := #[
    mkCase "ok/basic/shift0-zero" #[intV 0, intV 5, intV 0],
    mkCase "ok/basic/shift1-pos-pos" #[intV 7, intV 3, intV 1],
    mkCase "ok/basic/shift1-neg-pos" #[intV (-7), intV 3, intV 1],
    mkCase "ok/basic/shift1-pos-neg" #[intV 7, intV (-3), intV 1],
    mkCase "ok/basic/shift1-neg-neg" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/tie/shift0-pos-over-pos2" #[intV 3, intV 2, intV 0],
    mkCase "ok/tie/shift0-neg-over-pos2" #[intV (-3), intV 2, intV 0],
    mkCase "ok/tie/shift0-pos-over-neg2" #[intV 3, intV (-2), intV 0],
    mkCase "ok/tie/shift0-neg-over-neg2" #[intV (-3), intV (-2), intV 0],
    mkCase "ok/exact/shift1-max-over-max" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "ok/exact/shift0-min-over-min" #[intV minInt257, intV minInt257, intV 0],
    mkCase "ok/boundary/max-shift0-over-2" #[intV maxInt257, intV 2, intV 0],
    mkCase "ok/boundary/min-shift0-over-2" #[intV minInt257, intV 2, intV 0],
    mkCase "ok/boundary/min-shift1-over-max" #[intV minInt257, intV maxInt257, intV 1],
    mkCase "ok/boundary/max-shift256-over-max" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256-over-max" #[intV minInt257, intV maxInt257, intV 256],
    mkCase "error/divzero/nonzero-over-zero" #[intV 5, intV 0, intV 1],
    mkCase "error/divzero/zero-over-zero" #[intV 0, intV 0, intV 0],
    mkCase "error/underflow/empty-stack" #[],
    mkCase "error/underflow/one-item" #[intV 1],
    mkCase "error/underflow/two-items" #[intV 1, intV 2],
    mkCase "error/order/single-non-int-underflow-before-type" #[.null],
    mkCase "error/type/shift-pop-first-null" #[intV 5, intV 3, .null],
    mkCase "error/type/divisor-pop-second-null" #[intV 5, .null, intV 1],
    mkCase "error/type/x-pop-third-null" #[.null, intV 3, intV 1],
    mkCase "error/type/order-both-non-int-shift-first" #[.cell Cell.empty, .null, intV 1],
    mkCase "error/range/shift-negative-via-program" #[intV 5, intV 3]
      #[.pushInt (.num (-1)), lshiftModrInstr],
    mkCase "error/range/shift-257-via-program" #[intV 5, intV 3]
      #[.pushInt (.num 257), lshiftModrInstr],
    mkCase "error/range/shift-nan-via-program" #[intV 5, intV 3]
      #[.pushInt .nan, lshiftModrInstr],
    mkCase "error/order/range-before-x-type-via-program" #[.null, intV 3]
      #[.pushInt (.num 257), lshiftModrInstr],
    mkInputCase "error/nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkInputCase "error/nan/x-via-program" #[IntVal.nan, IntVal.num 3, IntVal.num 1],
    mkInputCase "error/range/program-shift-out-of-range-int" #[IntVal.num 5, IntVal.num 3, IntVal.num (pow2 257)],
    mkInputCase "error/range/program-x-out-of-range-int" #[IntVal.num (pow2 257), IntVal.num 3, IntVal.num 1],
    mkInputCase "error/range/program-y-out-of-range-int" #[IntVal.num 5, IntVal.num (-(pow2 257)), IntVal.num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftModrSetGasExact), .tonEnvOp .setGasLimit, lshiftModrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftModrInstr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 700
      gen := genLshiftModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTMODR
