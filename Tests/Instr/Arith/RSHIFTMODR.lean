import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTMODR

/-
RSHIFTMODR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod` path)
  - `TvmLean/Model/Basics/Bytes.lean` (`rshiftPow2Round`, `modPow2Round`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`, `AnyIntView::mod_pow2_any`)

Branch/terminal counts used for this suite (RSHIFTMODR specialization):
- Lean specialization (`.arithExt (.shrMod false false 3 0 false none)`):
  ~8 effective branch sites / ~15 terminal outcomes
  (dispatch arm; stack pre-underflow guard; shift pop/type/range funnel;
   `x` pop/type split; numeric-vs-NaN operand split; round-mode validation;
   `d` switch with `d=3`; first/second `pushIntQuiet` overflow exits).
- C++ specialization (`exec_shrmod`, runtime-shift mode, `d=3`, non-quiet):
  ~7 effective branch sites / ~13 aligned terminal outcomes
  (runtime-vs-const shift mode; global-version add-remap gate; invalid-opcode guard;
   underflow guard; shift range/type funnel via `pop_smallint_range(256)`;
   `y==0` round override; `d`-selected double push with first-push fail path).

Key risk areas covered:
- nearest rounding ties must go toward +∞ for `R` mode;
- shift `0` must force floor mode (`round_mode := -1`) before computation;
- pop/error order (`shift` is popped/range-checked before `x`);
- non-quiet NaN propagation throws `intOv` on first push (`q`) for `d=3`;
- shift range (`0..256`) errors must be `rangeChk`, injected via program;
- 257-bit boundary behavior on `q`/`r` around `±2^256`;
- exact gas threshold (`SETGASLIMIT` exact vs exact-minus-one) remains deterministic.
-/

private def rshiftModrId : InstrId := { name := "RSHIFTMODR" }

private def rshiftModrInstr : Instr := .arithExt (.shrMod false false 3 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rshiftModrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRshiftModrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt rshiftModrInstr stack

private def runRshiftModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 505)) stack

private def expectRshiftModr
    (label : String)
    (x : Int)
    (shift : Nat)
    (q : Int)
    (r : Int) : IO Unit :=
  expectOkStack label (runRshiftModrDirect #[intV x, intV (Int.ofNat shift)]) #[intV q, intV r]

private def rshiftModrSetGasExact : Int :=
  computeExactGasBudget rshiftModrInstr

private def rshiftModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftModrInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieShift1Pool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieShift2Pool : Array Int :=
  #[-14, -10, -6, -2, 2, 6, 10, 14]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genRshiftModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let ((x, shift), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (s0, r3) := pickShiftBoundary r2
      ((x0, s0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (s0, r3) := pickShiftBoundary r2
      ((x0, s0), r3)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (s0, r3) := pickShiftUniform r2
      ((x0, s0), r3)
    else if shape = 3 then
      let (x0, r2) := pickInt257Boundary rng1
      let (s0, r3) := pickShiftUniform r2
      ((x0, s0), r3)
    else if shape = 4 then
      let (x0, r2) := pickIntPool tieShift1Pool rng1
      ((x0, 1), r2)
    else if shape = 5 then
      let (x0, r2) := pickIntPool tieShift2Pool rng1
      ((x0, 2), r2)
    else if shape = 6 then
      let (s0, r2) := pickShiftUniform rng1
      ((0, s0), r2)
    else if shape = 7 then
      let (useMax, r2) := randBool rng1
      let x0 := if useMax then maxInt257 else minInt257
      let (s0, r3) := pickShiftBoundary r2
      ((x0, s0), r3)
    else if shape = 8 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 256), r2)
  let tie :=
    if shift = 0 then
      false
    else
      let p := pow2 shift
      Int.emod x p = pow2 (shift - 1)
  let kind :=
    if shift = 0 then
      "shift0"
    else if tie then
      "tie"
    else if x = maxInt257 || x = minInt257 then
      "boundary"
    else if Int.emod x (pow2 shift) = 0 then
      "exact"
    else
      "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV (Int.ofNat shift)], rng3)

def suite : InstrSuite where
  id := rshiftModrId
  unit := #[
    { name := "unit/nearest/tie-and-sign-invariants"
      run := do
        let checks : Array (Int × Nat × (Int × Int)) :=
          #[
            (7, 1, (4, -1)),
            (-7, 1, (-3, -1)),
            (9, 2, (2, 1)),
            (-9, 2, (-2, -1)),
            (7, 2, (2, -1)),
            (-7, 2, (-2, 1)),
            (1, 1, (1, -1)),
            (-1, 1, (0, -1)),
            (5, 3, (1, -3)),
            (-5, 3, (-1, 3))
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectRshiftModr s!"{x}>>#{shift}" x shift q r }
    ,
    { name := "unit/boundary/shift-zero-shift256-and-extremes"
      run := do
        let checks : Array (Int × Nat × (Int × Int)) :=
          #[
            (maxInt257, 0, (maxInt257, 0)),
            (minInt257, 0, (minInt257, 0)),
            (maxInt257, 1, (pow2 255, -1)),
            (minInt257, 1, (-(pow2 255), 0)),
            (maxInt257, 256, (1, -1)),
            (maxInt257 - 1, 256, (1, -2)),
            (minInt257, 256, (-1, 0)),
            (minInt257 + 1, 256, (-1, 1))
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectRshiftModr s!"boundary/{x}>>#{shift}" x shift q r }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runRshiftModrDirect #[]) .stkUnd
        expectErr "underflow/one-arg-int" (runRshiftModrDirect #[intV 1]) .stkUnd
        expectErr "error-order/one-arg-non-int-underflow-first" (runRshiftModrDirect #[.null]) .stkUnd
        expectErr "type/shift-top-first" (runRshiftModrDirect #[intV 1, .null]) .typeChk
        expectErr "type/x-second" (runRshiftModrDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-shift-first" (runRshiftModrDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runRshiftModrDispatchFallback #[]) #[intV 505] }
  ]
  oracle := #[
    mkCase "ok/shift0/zero-numerator" #[intV 0, intV 0],
    mkCase "ok/shift0/positive-numerator" #[intV 17, intV 0],
    mkCase "ok/shift0/negative-numerator" #[intV (-17), intV 0],
    mkCase "ok/tie/pos-half" #[intV 1, intV 1],
    mkCase "ok/tie/neg-half" #[intV (-1), intV 1],
    mkCase "ok/tie/pos-three-halves" #[intV 3, intV 1],
    mkCase "ok/tie/neg-three-halves" #[intV (-3), intV 1],
    mkCase "ok/general/pos-shift2" #[intV 9, intV 2],
    mkCase "ok/general/neg-shift2" #[intV (-9), intV 2],
    mkCase "ok/general/pos-shift8" #[intV 12345, intV 8],
    mkCase "ok/general/neg-shift8" #[intV (-12345), intV 8],
    mkCase "ok/exact/divisible-by-pow2-pos" #[intV 1024, intV 5],
    mkCase "ok/exact/divisible-by-pow2-neg" #[intV (-1024), intV 5],
    mkCase "boundary/max-shift0" #[intV maxInt257, intV 0],
    mkCase "boundary/min-shift0" #[intV minInt257, intV 0],
    mkCase "boundary/max-shift1" #[intV maxInt257, intV 1],
    mkCase "boundary/min-shift1" #[intV minInt257, intV 1],
    mkCase "boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "type/shift-top-non-int" #[intV 1, .null],
    mkCase "type/x-second-non-int" #[.null, intV 1],
    mkCase "type/error-order-both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative-via-program" #[intV 5] #[.pushInt (.num (-1)), rshiftModrInstr],
    mkCase "range/shift-257-via-program" #[intV 5] #[.pushInt (.num 257), rshiftModrInstr],
    mkCase "error-order/range-before-x-type-via-program" #[.null] #[.pushInt (.num 257), rshiftModrInstr],
    mkCase "nan/shift-via-program" #[intV 5] #[.pushInt .nan, rshiftModrInstr],
    mkCase "nan/x-via-program" #[intV 1] #[.pushInt .nan, .xchg0 1, rshiftModrInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num rshiftModrSetGasExact), .tonEnvOp .setGasLimit, rshiftModrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num rshiftModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftModrInstr]
  ]
  fuzz := #[
    { seed := 2026020808
      count := 700
      gen := genRshiftModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTMODR
