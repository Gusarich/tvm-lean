import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODPOW2C

/-
MODPOW2C branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false false 2 1 false none)` path)
  - `TvmLean/Model/Basics/Bytes.lean` (`modPow2Round`, `rshiftPow2Round`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (MODPOW2C specialization): 7 branch points / 10 terminal outcomes
  (dispatch/fallback; underflow gate; shift pop type/range/success; x pop type/success;
   finite-vs-NaN split; `shift = 0` floor override; non-quiet push success/error).
- C++ (MODPOW2C in `exec_shrmod`): 7 branch points / 10 aligned outcomes
  (invalid-op guard; underflow check; `pop_smallint_range` type/range/success;
   `y = 0` round override; `pop_int` type/success; `mod_pow2` finite-vs-NaN;
   non-quiet `push_int_quiet` success/error).

Key risk areas covered:
- ceil-mod sign/tie behavior (`r = x - ceil(x / 2^y) * 2^y`);
- runtime `shift = 0` override to floor mode (must return remainder `0`);
- strict shift bounds `[0, 256]` with range/type ordering before `x` pop;
- pop-order/error-order (`y` popped before `x`);
- non-quiet NaN funnel (`intOv`) injected via program;
- exact gas threshold via `PUSHINT n; SETGASLIMIT; MODPOW2C`.
-/

private def modpow2cId : InstrId := { name := "MODPOW2C" }

private def modpow2cInstr : Instr :=
  .arithExt (.shrMod false false 2 1 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modpow2cInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := modpow2cId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runModpow2cDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt modpow2cInstr stack

private def runModpow2cDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9202)) stack

private def modpow2cSetGasExact : Int :=
  computeExactGasBudget modpow2cInstr

private def modpow2cSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modpow2cInstr

private def mkShiftInjectedCase (name : String) (x : Value) (shift : IntVal) : OracleCase :=
  mkCase name #[x] #[.pushInt shift, modpow2cInstr]

private def mkXNanInjectedCase (name : String) (shift : Int) : OracleCase :=
  mkCase name #[intV shift] #[.pushInt .nan, .xchg0 1, modpow2cInstr]

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftNegativePool : Array Int :=
  #[-3, -2, -1]

private def shiftOverMaxPool : Array Int :=
  #[257, 258, 300, 511]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromIntPool validShiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickNegativeShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftNegativePool rng

private def pickOverMaxShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftOverMaxPool rng

private def genModpow2cFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-shift" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-inrange-shift" #[intV x, intV shift], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/ok-shift-zero-floor-override" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/ok-shift-256-boundary" #[intV x, intV 256], r2)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickNegativeShift r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-negative-via-program" (intV x) (.num shift), r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickOverMaxShift r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-overmax-via-program" (intV x) (.num shift), r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" (intV x) .nan, r2)
    else if shape = 7 then
      let (shift, r2) := pickShiftInRange rng1
      (mkXNanInjectedCase s!"fuzz/shape-{shape}/nan-x-via-program" shift, r2)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-int" #[intV x], r2)
    else if shape = 10 then
      let (pickNull, r2) := randBool rng1
      let v : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int" #[v], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (pickNull, r3) := randBool r2
      let yLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-shift-non-int" #[intV x, yLike], r3)
    else if shape = 12 then
      let (shift, r2) := pickShiftInRange rng1
      let (pickNull, r3) := randBool r2
      let xLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, intV shift], r3)
    else
      let (pickNull, r2) := randBool rng1
      let xLike : Value := if pickNull then .null else .cell Cell.empty
      let (pickNeg, r3) := randBool r2
      let (shift, r4) :=
        if pickNeg then pickNegativeShift r3 else pickOverMaxShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order-range-before-x-type-via-program" xLike (.num shift), r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := modpow2cId
  unit := #[
    { name := "unit/direct/ceil-mod-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 1, -1),
            (7, 2, -1),
            (9, 2, -3),
            (-7, 1, -1),
            (-7, 2, -3),
            (-9, 2, -1),
            (1, 1, -1),
            (-1, 1, -1),
            (42, 1, 0),
            (-42, 1, 0),
            (5, 3, -3),
            (-5, 3, -5)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%2^{shift}" (runModpow2cDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/shift-zero-and-256-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 0, 0),
            (minInt257, 0, 0),
            (maxInt257, 256, -1),
            (maxInt257 - 1, 256, -2),
            (minInt257, 256, 0),
            (minInt257 + 1, 256, minInt257 + 1),
            (0, 256, 0),
            (1, 256, minInt257 + 1),
            (-1, 256, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"boundary/{x}%2^{shift}" (runModpow2cDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/error/underflow-pop-order-and-range-type-ordering"
      run := do
        expectErr "underflow/empty" (runModpow2cDirect #[]) .stkUnd
        expectErr "underflow/single-int" (runModpow2cDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runModpow2cDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runModpow2cDirect #[intV 7, .null]) .typeChk
        expectErr "type/pop-x-second" (runModpow2cDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/pop-y-before-x-when-both-non-int"
          (runModpow2cDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "error-order/shift-range-before-x-type-negative"
          (runModpow2cDirect #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/shift-range-before-x-type-overmax"
          (runModpow2cDirect #[.cell Cell.empty, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runModpow2cDispatchFallback #[]) #[intV 9202] }
  ]
  oracle := #[
    mkCase "ok/ceil/pos-shift1" #[intV 7, intV 1],
    mkCase "ok/ceil/pos-shift2" #[intV 7, intV 2],
    mkCase "ok/ceil/neg-shift1" #[intV (-7), intV 1],
    mkCase "ok/ceil/neg-shift2" #[intV (-7), intV 2],
    mkCase "ok/ceil/tie-pos-half" #[intV 1, intV 1],
    mkCase "ok/ceil/tie-neg-half" #[intV (-1), intV 1],
    mkCase "ok/ceil/exact-pos" #[intV 42, intV 1],
    mkCase "ok/ceil/exact-neg" #[intV (-42), intV 1],
    mkCase "ok/shift-zero/max" #[intV maxInt257, intV 0],
    mkCase "ok/shift-zero/min" #[intV minInt257, intV 0],
    mkCase "ok/shift-zero/arbitrary" #[intV 12345, intV 0],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/one-shift256" #[intV 1, intV 256],
    mkCase "ok/boundary/minus-one-shift256" #[intV (-1), intV 256],
    mkShiftInjectedCase "range/shift-negative-via-program" (intV 7) (.num (-1)),
    mkShiftInjectedCase "range/shift-overmax-via-program" (intV 7) (.num 257),
    mkCase "range/shift-nan-via-program" #[intV 7] #[.pushInt .nan, modpow2cInstr],
    mkXNanInjectedCase "nan/x-via-program-intov" 3,
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/single-int" #[intV 1],
    mkCase "underflow/single-non-int" #[.null],
    mkCase "type/shift-top-null" #[intV 5, .null],
    mkCase "type/x-second-null" #[.null, intV 1],
    mkCase "type/shift-top-cell" #[intV 5, .cell Cell.empty],
    mkCase "type/x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/pop-y-before-x-when-both-non-int" #[.cell Cell.empty, .null],
    mkShiftInjectedCase "error-order/shift-range-before-x-type-negative-via-program" .null (.num (-1)),
    mkShiftInjectedCase "error-order/shift-range-before-x-type-overmax-via-program" (.cell Cell.empty) (.num 257),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num modpow2cSetGasExact), .tonEnvOp .setGasLimit, modpow2cInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num modpow2cSetGasExactMinusOne), .tonEnvOp .setGasLimit, modpow2cInstr]
  ]
  fuzz := #[
    { seed := 2026020814
      count := 700
      gen := genModpow2cFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2C
