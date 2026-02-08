import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTC

/-
RSHIFTC branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Ext.lean`
  (the `.arithExt (.shrMod false false 1 1 false none)` path).
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_shrmod`, opcode registration in `register_div_ops`).

Branch counts used for this suite:
- Lean (RSHIFTC path): 7 branch points / 10 terminal outcomes
  (opcode dispatch, underflow gate, shift pop/range/type, x pop/type,
   numeric-vs-NaN split, `shift==0` round override, push-int result/error).
- C++ (RSHIFTC path): 7 branch points / 10 aligned outcomes
  (invalid-op gate, explicit underflow check, `pop_smallint_range` checks,
   `y==0` round override, `pop_int` type check, `rshift` finite-vs-NaN,
   non-quiet `push_int_quiet` throw path).

Key risk areas covered:
- ceil-vs-floor behavior for mixed signs and odd/even divisors;
- dynamic shift boundary (`0`, `1`, `255`, `256`) behavior;
- strict error ordering (`stkUnd` before shift type/range with insufficient depth);
- non-int shift/x type-check ordering;
- C++ invalid-int compat (`x=NaN` with positive shift yields `0`, while shift `0` still throws `intOv`);
- exact gas boundary via `PUSHINT n; SETGASLIMIT; RSHIFTC`.
-/

private def rshiftcId : InstrId := { name := "RSHIFTC" }

private def rshiftcInstr : Instr :=
  .arithExt (.shrMod false false 1 1 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rshiftcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRshiftcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt rshiftcInstr stack

private def rshiftcSetGasExact : Int :=
  computeExactGasBudget rshiftcInstr

private def rshiftcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftcInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftUpTo256 (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def genRshiftcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
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
      let (x0, r2) := pickInt257Boundary rng1
      let (s0, r3) := pickShiftUpTo256 r2
      ((x0, s0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (s0, r3) := pickShiftUpTo256 r2
      ((x0, s0), r3)
    else if shape = 4 then
      let (useMin, r2) := randBool rng1
      let x0 := if useMin then minInt257 else maxInt257
      let (s0, r3) := pickShiftBoundary r2
      ((x0, s0), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV shift], rng3)

def suite : InstrSuite where
  id := rshiftcId
  unit := #[
    { name := "unit/direct/ceil-rounding-sign-cases"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 1, 4),
            (7, 2, 2),
            (15, 3, 2),
            (-7, 1, -3),
            (-7, 2, -1),
            (-15, 3, -1),
            (-1, 1, 0),
            (1, 1, 1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>{shift}" (runRshiftcDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/zero-and-boundary-shifts"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 0, maxInt257),
            (minInt257, 0, minInt257),
            (maxInt257, 256, 1),
            (minInt257, 256, -1),
            (-1, 256, 0),
            (1, 256, 1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"boundary/{x}>>{shift}" (runRshiftcDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/error-ordering-and-types"
      run := do
        expectErr "underflow/empty" (runRshiftcDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runRshiftcDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-arg-non-int" (runRshiftcDirect #[.null]) .stkUnd
        expectErr "type/shift-top" (runRshiftcDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second" (runRshiftcDirect #[.null, intV 1]) .typeChk }
  ]
  oracle := #[
    mkCase "ok/ceil/pos-odd-shift1" #[intV 7, intV 1],
    mkCase "ok/ceil/pos-odd-shift2" #[intV 7, intV 2],
    mkCase "ok/ceil/neg-odd-shift1" #[intV (-7), intV 1],
    mkCase "ok/ceil/neg-odd-shift2" #[intV (-7), intV 2],
    mkCase "ok/ceil/neg-half-to-zero" #[intV (-1), intV 1],
    mkCase "ok/ceil/zero-shift-identity" #[intV 123, intV 0],
    mkCase "ok/ceil/zero-input" #[intV 0, intV 200],
    mkCase "ok/boundary/max-shift1" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/min-shift1" #[intV minInt257, intV 1],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-valid-shift" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "error-order/one-arg-push257-underflow-first" #[]
      #[.pushInt (.num 257), rshiftcInstr],
    mkCase "error-order/one-arg-pushnan-underflow-first" #[]
      #[.pushInt .nan, rshiftcInstr],
    mkCase "type/shift-top-null" #[intV 5, .null],
    mkCase "type/x-second-null" #[.null, intV 1],
    mkCase "error-order/shift-range-before-x-type" #[.null]
      #[.pushInt (.num 257), rshiftcInstr],
    mkCase "range/shift-negative-via-program" #[intV 5]
      #[.pushInt (.num (-1)), rshiftcInstr],
    mkCase "range/shift-257-via-program" #[intV 5]
      #[.pushInt (.num 257), rshiftcInstr],
    mkCase "range/shift-nan-via-program" #[intV 5]
      #[.pushInt .nan, rshiftcInstr],
    mkCase "nan/x-via-program-shift1-yields-zero" #[]
      #[.pushInt .nan, .pushInt (.num 1), rshiftcInstr],
    mkCase "nan/x-via-program-shift0-intov" #[]
      #[.pushInt .nan, .pushInt (.num 0), rshiftcInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 1]
      #[.pushInt (.num rshiftcSetGasExact), .tonEnvOp .setGasLimit, rshiftcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 1]
      #[.pushInt (.num rshiftcSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftcInstr]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 500
      gen := genRshiftcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTC
