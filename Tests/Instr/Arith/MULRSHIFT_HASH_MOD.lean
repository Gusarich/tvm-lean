import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFT_HASH_MOD

/-
MULRSHIFT#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 3 (-1) false (some z)` specialization)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type behavior, non-quiet `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, floor quotient/remainder behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, non-quiet `push_int_quiet`)

Branch/terminal counts used for this suite (`mul=true`, `add=false`, `d=3`,
`roundMode=-1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: ~7 branch sites / ~8 terminal outcomes
  (dispatch/fallback; pre-pop underflow gate; immediate-shift range gate;
   `y` pop type split; `x` pop type split; numeric-vs-invalid operand split;
   dual-result non-quiet push overflow funnel).
- C++ specialization: ~7 branch sites / ~8 aligned terminal outcomes
  (`check_underflow(2)` in immediate mode; immediate range gate;
   `pop_int` for `y` then `x`; finite-vs-invalid operand split;
   floor q/r computation; non-quiet push overflow/NaN funnel).

Key risk areas covered:
- hash-immediate pop discipline (`z` encoded, never popped from stack);
- mixed-sign floor quotient/remainder semantics and output order (`q` then `r`);
- boundary shifts (`1`, `255`, `256`) on signed-257 extremes;
- strict error order: underflow before type, and invalid immediate range before `y/x` pops;
- pop order (`y` first, then `x`) and lower-stack preservation;
- NaN/out-of-range operand injection via program prelude only;
- exact gas cliff (`SETGASLIMIT`: exact succeeds, exact-minus-one fails).
-/

private def mulrshiftHashModId : InstrId := { name := "MULRSHIFT#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulrshiftHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod true false 3 (-1) false (some shift))

private def mulrshiftHashModInstrDefault : Instr :=
  mkMulrshiftHashModInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftHashModInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulrshiftHashModId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftStackCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkMulrshiftHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x y : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkMulrshiftHashModInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runMulrshiftHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkMulrshiftHashModInstr shift) stack

private def runMulrshiftHashModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 7341)) stack

private def mulrshiftHashModGasProbeInstr : Instr :=
  mkMulrshiftHashModInstr 7

private def mulrshiftHashModSetGasExact : Int :=
  computeExactGasBudget mulrshiftHashModGasProbeInstr

private def mulrshiftHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallOperandPool : Array Int :=
  #[-17, -13, -9, -7, -5, -3, -2, -1, 0, 1, 2, 3, 5, 7, 9, 13, 17]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftInRange rng1

private def pickSmallOperand (rng : StdGen) : Int × StdGen :=
  pickFromPool smallOperandPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def classifyMulrshiftHashMod (x y : Int) (shift : Nat) : String :=
  let tmp : Int := x * y
  let q := rshiftPow2Round tmp shift (-1)
  let r := modPow2Round tmp shift (-1)
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "intov"
  else if tmp = 0 then
    "ok-zero"
  else if r = 0 then
    "ok-exact"
  else if decide (x < 0) != decide (y < 0) then
    "ok-inexact-mixed-sign"
  else
    "ok-inexact-same-sign"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyMulrshiftHashMod x y shift
  mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}" shift (.num x) (.num y)

private def genMulrshiftHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 4 then
      let (x, r2) := pickSmallOperand rng1
      let (y, r3) := pickSmallOperand r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 5 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape 0 y shift, r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape x 0 shift, r3)
    else if shape = 7 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkFiniteFuzzCase shape x y 256, r3)
    else if shape = 8 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-max-max-shift1"
        1 (.num maxInt257) (.num maxInt257), rng1)
    else if shape = 9 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-min-min-shift1"
        1 (.num minInt257) (.num minInt257), rng1)
    else if shape = 10 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-min-min-shift256"
        256 (.num minInt257) (.num minInt257), rng1)
    else if shape = 11 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/one-int" shift #[intV x], r3)
    else if shape = 13 then
      let (bad, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-single-non-int"
        shift #[bad], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (badY, r3) := pickNonInt r2
      let (shift, r4) := pickShiftMixed r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-y-first"
        shift #[intV x, badY], r4)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (badX, r3) := pickNonInt r2
      let (shift, r4) := pickShiftMixed r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-x-second"
        shift #[badX, intV y], r4)
    else if shape = 16 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 17 then
      let (x, r2) := pickSmallOperand rng1
      let (y, r3) := pickSmallOperand r2
      let (shift, r4) := pickShiftBoundary r3
      let (below, r5) := pickNonInt r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/pop-order/lower-preserved"
        shift #[below, intV x, intV y], r5)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/ok-or-intov/immediate-max"
        256 #[intV x, intV y], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/y-non-int-at-immediate-max"
        256 #[intV x, .null], r2)
    else if shape = 20 then
      let (y, r2) := pickSigned257ish rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/x-non-int-at-immediate-max"
        256 #[.null, intV y], r2)
    else if shape = 21 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift .nan (.num y), r3)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        shift (.num x) .nan, r3)
    else if shape = 23 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift (.num xo) (.num y), r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift (.num x) (.num yo), r4)
    else if shape = 25 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        shift (.num xo) (.num yo), r4)
    else if shape = 26 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-type-check"
        #[.null] #[.pushInt (.num (pow2 257)), mkMulrshiftHashModInstr shift], r2)
    else
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-underflow"
        #[] #[.pushInt (.num (-(pow2 257))), mkMulrshiftHashModInstr shift], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftHashModId
  unit := #[
    { name := "/unit/direct/floor-quot-rem-mixed-sign-and-boundary-shifts"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 10, 1),
            (-7, 3, 1, -11, 1),
            (7, -3, 1, -11, 1),
            (-7, -3, 1, 10, 1),
            (5, 5, 2, 6, 1),
            (-5, 5, 2, -7, 3),
            (5, -5, 2, -7, 3),
            (-5, -5, 2, 6, 1),
            (0, 9, 256, 0, 0),
            (maxInt257, 2, 1, maxInt257, 0),
            (minInt257, 2, 1, minInt257, 0),
            (maxInt257, 1, 256, 0, maxInt257),
            (minInt257, 1, 256, -1, 0),
            (minInt257, -1, 256, 1, 0),
            (maxInt257, -1, 256, -1, 1),
            (maxInt257, maxInt257, 256, maxInt257 - 1, 1),
            (minInt257 + 1, minInt257 + 1, 256, maxInt257 - 1, 1),
            (1, 1, 256, 0, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"/unit/direct/x={x}/y={y}/shift={shift}"
            (runMulrshiftHashModDirect shift #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "/unit/pop-order/hash-immediate-does-not-pop-third-item"
      run := do
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMulrshiftHashModDirect 1 #[.null, intV 7, intV 3]) #[.null, intV 10, intV 1]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMulrshiftHashModDirect 2 #[.cell Cell.empty, intV (-7), intV 3])
          #[.cell Cell.empty, intV (-6), intV 3] }
    ,
    { name := "/unit/error/intov-underflow-type-and-pop-order"
      run := do
        expectErr "/unit/intov/overflow-max-max-shift1"
          (runMulrshiftHashModDirect 1 #[intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/intov/overflow-min-min-shift1"
          (runMulrshiftHashModDirect 1 #[intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/intov/overflow-min-min-shift256"
          (runMulrshiftHashModDirect 256 #[intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/underflow/empty"
          (runMulrshiftHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int"
          (runMulrshiftHashModDirect 1 #[intV 7]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runMulrshiftHashModDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runMulrshiftHashModDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/type/pop-y-first-cell"
          (runMulrshiftHashModDirect 1 #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runMulrshiftHashModDirect 1 #[.null, intV 7]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runMulrshiftHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-precedence"
      run := do
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate-empty"
          (runMulrshiftHashModDirect 257 #[]) .stkUnd
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate-one-item"
          (runMulrshiftHashModDirect 257 #[intV 7]) .stkUnd
        expectErr "/unit/range/immediate-overmax"
          (runMulrshiftHashModDirect 257 #[intV 7, intV 3]) .rangeChk
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate"
          (runMulrshiftHashModDirect 257 #[intV 7, .null]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate"
          (runMulrshiftHashModDirect 257 #[.null, intV 7]) .rangeChk }
    ,
    { name := "/unit/dispatch/non-mulrshift-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulrshiftHashModDispatchFallback #[]) #[intV 7341] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/sign/pos-pos-shift1" 1 (.num 7) (.num 3),
    mkShiftInputCase "/ok/floor/sign/neg-pos-shift1" 1 (.num (-7)) (.num 3),
    mkShiftInputCase "/ok/floor/sign/pos-neg-shift1" 1 (.num 7) (.num (-3)),
    mkShiftInputCase "/ok/floor/sign/neg-neg-shift1" 1 (.num (-7)) (.num (-3)),
    mkShiftInputCase "/ok/floor/inexact/pos-pos-shift2" 2 (.num 5) (.num 5),
    mkShiftInputCase "/ok/floor/inexact/mixed-sign-shift2" 2 (.num 5) (.num (-5)),
    mkShiftInputCase "/ok/floor/exact/divisible-pos-shift3" 3 (.num 8) (.num 4),
    mkShiftInputCase "/ok/floor/exact/divisible-neg-shift3" 3 (.num (-8)) (.num 4),
    mkShiftInputCase "/ok/floor/zero-left-factor" 17 (.num 0) (.num 9),
    mkShiftInputCase "/ok/floor/zero-right-factor" 17 (.num 9) (.num 0),
    mkShiftInputCase "/ok/boundary/max-times-one-shift1" 1 (.num maxInt257) (.num 1),
    mkShiftInputCase "/ok/boundary/min-times-one-shift1" 1 (.num minInt257) (.num 1),
    mkShiftInputCase "/ok/boundary/max-times-one-shift255" 255 (.num maxInt257) (.num 1),
    mkShiftInputCase "/ok/boundary/min-times-one-shift255" 255 (.num minInt257) (.num 1),
    mkShiftInputCase "/ok/boundary/max-times-one-shift256" 256 (.num maxInt257) (.num 1),
    mkShiftInputCase "/ok/boundary/min-times-one-shift256" 256 (.num minInt257) (.num 1),
    mkShiftInputCase "/ok/boundary/min-times-neg-one-shift256" 256 (.num minInt257) (.num (-1)),
    mkShiftInputCase "/ok/boundary/max-times-neg-one-shift256" 256 (.num maxInt257) (.num (-1)),
    mkShiftInputCase "/ok/boundary/max-times-max-shift256" 256 (.num maxInt257) (.num maxInt257),
    mkShiftInputCase "/ok/boundary/min-plus-one-times-min-plus-one-shift256"
      256 (.num (minInt257 + 1)) (.num (minInt257 + 1)),
    mkShiftStackCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 7, intV 3],
    mkShiftStackCase "/ok/pop-order/lower-cell-preserved" 2 #[.cell Cell.empty, intV (-7), intV 3],
    mkShiftInputCase "/intov/overflow-max-max-shift1" 1 (.num maxInt257) (.num maxInt257),
    mkShiftInputCase "/intov/overflow-min-min-shift1" 1 (.num minInt257) (.num minInt257),
    mkShiftInputCase "/intov/overflow-min-min-shift256" 256 (.num minInt257) (.num minInt257),
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/underflow/one-int" 1 #[intV 7],
    mkShiftStackCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftStackCase "/type/pop-y-first-null" 1 #[intV 7, .null],
    mkShiftStackCase "/type/pop-y-first-cell" 1 #[intV 7, .cell Cell.empty],
    mkShiftStackCase "/type/pop-x-second-null" 1 #[.null, intV 7],
    mkShiftStackCase "/error-order/pop-y-before-x-when-both-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program" 1 .nan (.num 3),
    mkShiftInputCase "/intov/nan-y-via-program" 1 (.num 7) .nan,
    mkShiftInputCase "/intov/nan-both-via-program" 1 .nan .nan,
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      1 (.num (maxInt257 + 1)) (.num 3),
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op"
      1 (.num 7) (.num (minInt257 - 1)),
    mkShiftInputCase "/error-order/pushint-overflow-both-before-op"
      1 (.num (maxInt257 + 1)) (.num (minInt257 - 1)),
    mkCase "/error-order/pushint-overflow-before-op-type-check" #[.null]
      #[.pushInt (.num (pow2 257)), mkMulrshiftHashModInstr 1],
    mkCase "/error-order/pushint-overflow-before-op-underflow" #[]
      #[.pushInt (.num (-(pow2 257))), mkMulrshiftHashModInstr 1],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num mulrshiftHashModSetGasExact), .tonEnvOp .setGasLimit, mulrshiftHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num mulrshiftHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020892
      count := 700
      gen := genMulrshiftHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFT_HASH_MOD
