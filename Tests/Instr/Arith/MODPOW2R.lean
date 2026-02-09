import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODPOW2R

/-
MODPOW2R branch-mapping notes (Lean + C++ reference):
- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod` with
     `mulMode=false`, `addMode=false`, `d=2`, `roundMode=0`, `quiet=false`, `zOpt=none`).
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range`, `pop_int`, `push_int_quiet`).

Branch counts used for this suite:
- Lean specialization: 6 branch sites / 7 terminal outcomes
  (dispatch arm; stack underflow precheck; shift-pop `typeChk`/`rangeChk`/ok;
   x-pop `typeChk`; finite-vs-NaN x split; non-quiet push split).
- C++ specialization: 5 branch sites / 7 aligned terminal outcomes
  (opcode guard; underflow check; `pop_smallint_range` type/range split;
   second-pop type split; `push_int_quiet` non-quiet `int_ov` split).

Key risk areas covered:
- shift pop-order (`shift` before `x`) and error precedence;
- strict runtime shift bounds (`0..256`) and `-1`/`257` rejection;
- `shift=0` remap to floor mode (not nearest);
- NaN routing differences: NaN shift => `rangeChk`, NaN x => `intOv`;
- nearest-round modulo tie behavior for negative numerators;
- exact gas boundary determinism (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def modPow2RId : InstrId := { name := "MODPOW2R" }

private def modPow2RInstr : Instr :=
  .arithExt (.shrMod false false 2 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modPow2RInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := modPow2RId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runModPow2RDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt modPow2RInstr stack

private def runModPow2RDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 909)) stack

private def modPow2RSetGasExact : Int :=
  computeExactGasBudget modPow2RInstr

private def modPow2RSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modPow2RInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftUniform rng1

private def genModPow2RFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let ((kind, stack, program), rng2) :
      (String × Array Value × Array Instr) × StdGen :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (shift0, r3) := pickShiftBoundary r2
      (("ok-boundary", #[intV x0, intV (Int.ofNat shift0)], #[modPow2RInstr]), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (shift0, r3) := pickShiftBoundary r2
      (("ok-random-x-boundary-shift", #[intV x0, intV (Int.ofNat shift0)], #[modPow2RInstr]), r3)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (shift0, r3) := pickShiftUniform r2
      (("ok-boundary-x-random-shift", #[intV x0, intV (Int.ofNat shift0)], #[modPow2RInstr]), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (shift0, r3) := pickShiftMixed r2
      (("ok-random", #[intV x0, intV (Int.ofNat shift0)], #[modPow2RInstr]), r3)
    else if shape = 4 then
      let (shift0, r2) := pickShiftMixed rng1
      (("ok-zero-x", #[intV 0, intV (Int.ofNat shift0)], #[modPow2RInstr]), r2)
    else if shape = 5 then
      let (useMax, r2) := randBool rng1
      let x0 := if useMax then maxInt257 else minInt257
      let (shift0, r3) := pickShiftBoundary r2
      (("ok-extreme-x", #[intV x0, intV (Int.ofNat shift0)], #[modPow2RInstr]), r3)
    else if shape = 6 then
      let (x0, r2) := pickSigned257ish rng1
      (("range-shift-over256-via-program", #[intV x0], #[.pushInt (.num 257), modPow2RInstr]), r2)
    else if shape = 7 then
      let (x0, r2) := pickSigned257ish rng1
      (("range-shift-negative-via-program", #[intV x0], #[.pushInt (.num (-1)), modPow2RInstr]), r2)
    else if shape = 8 then
      let (x0, r2) := pickSigned257ish rng1
      (("range-shift-nan-via-program", #[intV x0], #[.pushInt .nan, modPow2RInstr]), r2)
    else if shape = 9 then
      let (shift0, r2) := pickShiftMixed rng1
      (("intov-x-nan-via-program", #[intV (Int.ofNat shift0)], #[.pushInt .nan, .xchg0 1, modPow2RInstr]), r2)
    else if shape = 10 then
      let (x0, r2) := pickSigned257ish rng1
      (("type-shift-pop-first", #[intV x0, .null], #[modPow2RInstr]), r2)
    else
      let (shift0, r2) := pickShiftMixed rng1
      (("type-x-pop-second", #[.null, intV (Int.ofNat shift0)], #[modPow2RInstr]), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" stack program, rng3)

def suite : InstrSuite where
  id := modPow2RId
  unit := #[
    { name := "unit/nearest-mod-sign-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (1, 1, -1),
            (-1, 1, -1),
            (3, 2, -1),
            (-3, 2, 1),
            (5, 2, 1),
            (-5, 2, -1),
            (6, 2, -2),
            (-6, 2, -2),
            (7, 3, -1),
            (-7, 3, 1),
            (17, 4, 1),
            (-17, 4, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} modPow2R {shift}" (runModPow2RDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/boundary-257-and-shift-edges"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 256, -1),
            (maxInt257, 255, -1),
            (maxInt257 - 1, 256, -2),
            (maxInt257, 0, 0),
            (minInt257, 256, 0),
            (minInt257, 255, 0),
            (minInt257 + 1, 256, 1),
            (minInt257, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} modPow2R {shift}" (runModPow2RDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/error-order-pop-order-and-failure-codes"
      run := do
        expectErr "underflow/empty" (runModPow2RDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runModPow2RDirect #[intV 7]) .stkUnd
        expectErr "error-order/single-item-underflow-before-type" (runModPow2RDirect #[.null]) .stkUnd
        expectErr "type/shift-pop-first-null" (runModPow2RDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-pop-second-null" (runModPow2RDirect #[.null, intV 7]) .typeChk
        expectErr "error-order/shift-range-before-x-type" (runModPow2RDirect #[.null, intV (-1)]) .rangeChk
        expectErr "range/shift-negative" (runModPow2RDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runModPow2RDirect #[intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runModPow2RDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "intov/x-nan-after-valid-shift" (runModPow2RDirect #[.int .nan, intV 5]) .intOv }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runModPow2RDispatchFallback #[]) #[intV 909] }
  ]
  oracle := #[
    mkCase "ok/shift0/zero" #[intV 0, intV 0],
    mkCase "ok/shift0/positive" #[intV 123, intV 0],
    mkCase "ok/shift0/negative" #[intV (-123), intV 0],
    mkCase "ok/sign/pos-shift1" #[intV 7, intV 1],
    mkCase "ok/sign/neg-shift1" #[intV (-7), intV 1],
    mkCase "ok/sign/pos-shift2" #[intV 7, intV 2],
    mkCase "ok/sign/neg-shift2" #[intV (-7), intV 2],
    mkCase "ok/sign/pos-shift4" #[intV 17, intV 4],
    mkCase "ok/sign/neg-shift4" #[intV (-17), intV 4],
    mkCase "ok/tie/pos-half-shift2" #[intV 6, intV 2],
    mkCase "ok/tie/neg-half-shift2" #[intV (-6), intV 2],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/max-minus-one-shift256" #[intV (maxInt257 - 1), intV 256],
    mkCase "ok/boundary/max-shift255" #[intV maxInt257, intV 255],
    mkCase "ok/boundary/max-shift0" #[intV maxInt257, intV 0],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/min-shift255" #[intV minInt257, intV 255],
    mkCase "ok/boundary/min-shift0" #[intV minInt257, intV 0],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 1],
    mkCase "error-order/single-item-underflow-before-type" #[.null],
    mkCase "type/shift-pop-first-null" #[intV 7, .null],
    mkCase "type/x-pop-second-null" #[.null, intV 7],
    mkCase "type/error-order-both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative-via-program" #[intV 7] #[.pushInt (.num (-1)), modPow2RInstr],
    mkCase "range/shift-over-256-via-program" #[intV 7] #[.pushInt (.num 257), modPow2RInstr],
    mkCase "range/shift-nan-via-program" #[intV 7] #[.pushInt .nan, modPow2RInstr],
    mkCase "error-order/shift-range-before-x-type-via-program" #[.null]
      #[.pushInt (.num (-1)), modPow2RInstr],
    mkCase "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, modPow2RInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num modPow2RSetGasExact), .tonEnvOp .setGasLimit, modPow2RInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num modPow2RSetGasExactMinusOne), .tonEnvOp .setGasLimit, modPow2RInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 500
      gen := genModPow2RFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2R
