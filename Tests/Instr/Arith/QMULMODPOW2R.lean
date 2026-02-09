import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULMODPOW2R

/-
QMULMODPOW2R branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 2 0 true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, quiet `pushIntQuiet` NaN funnel)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, registration in `register_div_ops`, quiet opcode `0xb7a9a9`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (specialized path `mul=true`, `add=false`, `d=2`, `round=0`, `quiet=true`):
- Lean: 9 branch sites / 11 terminal outcomes
  (dispatch/fallback; explicit arity gate; shift pop type path; bad-shift gate;
   `y` pop type path; `x` pop type path; shift-zero round remap;
   numeric-vs-NaN operand split; quiet result push fit-vs-NaN funnel).
- C++: 8 aligned branch sites / 11 terminal outcomes
  (underflow gate; runtime shift pop/range handling; `y`/`x` pop order;
   quiet bad-shift NaN path; nearest-round remainder path; quiet push funnel).

Key risk areas covered:
- nearest-round modulo sign/tie behavior after multiply;
- `shift=0` remap to floor-mode remainder (`0`) in runtime-shift form;
- quiet bad-shift behavior (`<0`, `>256`, `NaN`) should push NaN, not throw;
- pop/error ordering (`shift` first, then `y`, then `x`), including bad-shift + type precedence;
- NaN/out-of-range integer oracle/fuzz inputs are injected via `PUSHINT` prelude only;
- exact gas cliff with `PUSHINT n; SETGASLIMIT; QMULMODPOW2R`.
-/

private def qmulmodpow2rId : InstrId := { name := "QMULMODPOW2R" }

private def qmulmodpow2rInstr : Instr :=
  .arithExt (.shrMod true false 2 0 true none)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulmodpow2rInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulmodpow2rId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def shiftFitsQmulmodpow2rRange (v : IntVal) : Bool :=
  match v with
  | .nan => false
  | .num n => decide (0 ≤ n ∧ n ≤ 256)

private def mkInputCase
    (name : String)
    (x y shift : IntVal)
    (below : Array Value := #[])
    (programSuffix : Array Instr := #[qmulmodpow2rInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let forceProgramInject : Bool :=
    !(intValOracleSerializable x) || !(intValOracleSerializable y) || !(shiftFitsQmulmodpow2rRange shift)
  let (stack, progPrefix) :=
    if forceProgramInject then
      (#[], #[.pushInt x, .pushInt y, .pushInt shift])
    else
      oracleIntInputsToStackOrProgram #[x, y, shift]
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def runQmulmodpow2rDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulmodpow2rInstr stack

private def runQmulmodpow2rDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4791)) stack

private def qmulmodpow2rSetGasExact : Int :=
  computeExactGasBudget qmulmodpow2rInstr

private def qmulmodpow2rSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulmodpow2rInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOverflowPool : Array Int :=
  #[257, 258, 300, 1024]

private def tieFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 256
  (Int.ofNat n, rng')

private def pickShiftMixed (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftInRange rng1

private def pickShiftNegative (rng : StdGen) : Int × StdGen :=
  let (mag, rng') := randNat rng 1 8
  (-Int.ofNat mag, rng')

private def pickShiftOverMax (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftOverflowPool rng

private def pickShiftInvalid (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 1
  if mode = 0 then
    pickShiftNegative rng1
  else
    pickShiftOverMax rng1

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQmulmodpow2rFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkInputCase s!"/fuzz/shape-{shape}/ok/boundary-triplet"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkInputCase s!"/fuzz/shape-{shape}/ok/signed-triplet"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkInputCase s!"/fuzz/shape-{shape}/ok/x-boundary"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftMixed r3
      (mkInputCase s!"/fuzz/shape-{shape}/ok/y-boundary"
        (.num x) (.num y) (.num shift), r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok/x-zero"
        (.num 0) (.num y) (.num shift), r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok/y-zero"
        (.num x) (.num 0) (.num shift), r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok/shift-zero-floor-remap"
        (.num x) (.num y) (.num 0), r3)
    else if shape = 7 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok/nearest-half-ties-shift1"
        (.num x) (.num y) (.num 1), r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftBad, r4) := pickShiftNegative r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/bad-shift-negative-via-program"
        (.num x) (.num y) (.num shiftBad), r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftBad, r4) := pickShiftOverMax r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/bad-shift-overmax-via-program"
        (.num x) (.num y) (.num shiftBad), r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/bad-shift-nan-via-program"
        (.num x) (.num y) .nan, r3)
    else if shape = 11 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        .nan (.num y) (.num shift), r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        (.num x) .nan (.num shift), r3)
    else if shape = 13 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-item" #[intV x], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-items" #[intV x, intV y], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/y-second-non-int"
        #[intV x, yLike, intV shift], r4)
    else if shape = 18 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/x-third-non-int"
        #[xLike, intV y, intV shift], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftBad, r3) := pickShiftInvalid r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/type-y-before-bad-shift-via-program"
        #[intV x, .null] #[.pushInt (.num shiftBad), qmulmodpow2rInstr], r3)
    else if shape = 20 then
      let (y, r2) := pickSigned257ish rng1
      let (shiftBad, r3) := pickShiftInvalid r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/type-x-before-bad-shift-via-program"
        #[.null, intV y] #[.pushInt (.num shiftBad), qmulmodpow2rInstr], r3)
    else if shape = 21 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num y) (.num shift), r4)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftMixed r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        (.num x) (.num yOut) (.num shift), r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        (.num x) (.num y) (.num shiftOut), r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulmodpow2rId
  unit := #[
    { name := "/unit/direct/nearest-mod-product-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 5, 1, -1),
            (-7, 5, 1, -1),
            (7, -5, 1, -1),
            (-7, -5, 1, -1),
            (3, 2, 2, -2),
            (-3, 2, 2, -2),
            (3, -2, 2, -2),
            (5, 1, 3, -3),
            (-5, 1, 3, 3),
            (9, 1, 2, 1),
            (-9, 1, 2, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"/unit/direct/x={x}/y={y}/shift={shift}"
            (runQmulmodpow2rDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "/unit/direct/shift-zero-and-boundary-edges"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 256, -1),
            (maxInt257 - 1, 1, 256, -2),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, 1, 256, 1),
            (maxInt257, -1, 256, 1),
            (minInt257, -1, 256, 0),
            (maxInt257, 2, 0, 0),
            (minInt257, -1, 0, 0),
            (maxInt257, 0, 255, 0),
            (minInt257, 0, 255, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"/unit/boundary/x={x}/y={y}/shift={shift}"
            (runQmulmodpow2rDirect #[intV x, intV y, intV shift]) #[intV expected] }
    ,
    { name := "/unit/quiet/nan-and-bad-shift-funnels"
      run := do
        expectOkStack "/unit/quiet/shift-negative"
          (runQmulmodpow2rDirect #[intV 7, intV 5, intV (-1)]) #[.int .nan]
        expectOkStack "/unit/quiet/shift-overmax"
          (runQmulmodpow2rDirect #[intV 7, intV 5, intV 257]) #[.int .nan]
        expectOkStack "/unit/quiet/shift-nan"
          (runQmulmodpow2rDirect #[intV 7, intV 5, .int .nan]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQmulmodpow2rDirect #[intV 7, .int .nan, intV 4]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQmulmodpow2rDirect #[.int .nan, intV 7, intV 4]) #[.int .nan] }
    ,
    { name := "/unit/error-order/pop-order-and-precedence"
      run := do
        expectErr "/unit/error/underflow-empty" (runQmulmodpow2rDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-one-item" (runQmulmodpow2rDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-items" (runQmulmodpow2rDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow-before-shift-type-with-two-items"
          (runQmulmodpow2rDirect #[intV 1, .null]) .stkUnd
        expectErr "/unit/error/type-shift-pop-first"
          (runQmulmodpow2rDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type-y-pop-second"
          (runQmulmodpow2rDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type-x-pop-third"
          (runQmulmodpow2rDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error/pop-shift-before-y-when-both-non-int"
          (runQmulmodpow2rDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error/pop-y-before-x-when-shift-valid"
          (runQmulmodpow2rDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "/unit/error/order-bad-shift-does-not-mask-y-type"
          (runQmulmodpow2rDirect #[intV 1, .null, intV 300]) .typeChk
        expectErr "/unit/error/order-bad-shift-does-not-mask-x-type"
          (runQmulmodpow2rDirect #[.null, intV 1, intV 300]) .typeChk }
    ,
    { name := "/unit/direct/pop-order-top-three-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-null"
          (runQmulmodpow2rDirect #[.null, intV 9, intV 1, intV 2]) #[.null, intV 1]
        expectOkStack "/unit/pop-order/below-cell-quiet-bad-shift"
          (runQmulmodpow2rDirect #[.cell Cell.empty, intV 7, intV 5, intV 300])
          #[.cell Cell.empty, .int .nan] }
    ,
    { name := "/unit/dispatch/non-qmulmodpow2r-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmulmodpow2rDispatchFallback #[]) #[intV 4791] }
  ]
  oracle := #[
    mkInputCase "/ok/round/sign/pos-pos-shift1" (.num 7) (.num 5) (.num 1),
    mkInputCase "/ok/round/sign/neg-pos-shift1" (.num (-7)) (.num 5) (.num 1),
    mkInputCase "/ok/round/sign/pos-neg-shift1" (.num 7) (.num (-5)) (.num 1),
    mkInputCase "/ok/round/sign/neg-neg-shift1" (.num (-7)) (.num (-5)) (.num 1),
    mkInputCase "/ok/round/tie/plus-half-shift2" (.num 3) (.num 2) (.num 2),
    mkInputCase "/ok/round/tie/minus-half-shift2" (.num (-3)) (.num 2) (.num 2),
    mkInputCase "/ok/round/general/pos-shift3" (.num 5) (.num 1) (.num 3),
    mkInputCase "/ok/round/general/neg-shift3" (.num (-5)) (.num 1) (.num 3),
    mkInputCase "/ok/round/general/pos-neg-shift3" (.num 5) (.num (-1)) (.num 3),
    mkInputCase "/ok/shift-zero/zero-product" (.num 0) (.num 17) (.num 0),
    mkInputCase "/ok/shift-zero/nonzero-product" (.num 9) (.num (-11)) (.num 0),
    mkInputCase "/ok/boundary/max-times-one-shift256" (.num maxInt257) (.num 1) (.num 256),
    mkInputCase "/ok/boundary/max-minus-one-times-one-shift256"
      (.num (maxInt257 - 1)) (.num 1) (.num 256),
    mkInputCase "/ok/boundary/min-times-one-shift256" (.num minInt257) (.num 1) (.num 256),
    mkInputCase "/ok/boundary/min-plus-one-times-one-shift256"
      (.num (minInt257 + 1)) (.num 1) (.num 256),
    mkInputCase "/ok/boundary/max-times-neg1-shift256" (.num maxInt257) (.num (-1)) (.num 256),
    mkInputCase "/ok/boundary/min-times-neg1-shift256" (.num minInt257) (.num (-1)) (.num 256),
    mkInputCase "/ok/boundary/max-times-one-shift255" (.num maxInt257) (.num 1) (.num 255),
    mkInputCase "/ok/boundary/max-times-two-shift0" (.num maxInt257) (.num 2) (.num 0),
    mkInputCase "/ok/boundary/min-times-neg1-shift0" (.num minInt257) (.num (-1)) (.num 0),
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-item" #[intV 1],
    mkCase "/underflow/two-items" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-shift-type-with-two-items" #[intV 1, .null],
    mkCase "/type/pop-shift-first-null" #[intV 1, intV 2, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "/type/pop-y-second-null" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third-null" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-shift-before-y-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-when-shift-valid" #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/bad-shift-does-not-mask-y-type-via-program" #[intV 1, .null]
      #[.pushInt (.num 300), qmulmodpow2rInstr],
    mkCase "/error-order/bad-shift-does-not-mask-x-type-via-program" #[.null, intV 1]
      #[.pushInt (.num 300), qmulmodpow2rInstr],
    mkInputCase "/quiet/shift-negative-via-program" (.num 7) (.num 5) (.num (-1)),
    mkInputCase "/quiet/shift-overmax-via-program" (.num 7) (.num 5) (.num 257),
    mkInputCase "/quiet/shift-nan-via-program" (.num 7) (.num 5) .nan,
    mkInputCase "/quiet/nan/x-via-program" .nan (.num 5) (.num 3),
    mkInputCase "/quiet/nan/y-via-program" (.num 7) .nan (.num 3),
    mkInputCase "/error-order/pushint-overflow-x-high-before-op"
      (.num (maxInt257 + 1)) (.num 7) (.num 3),
    mkInputCase "/error-order/pushint-overflow-x-low-before-op"
      (.num (minInt257 - 1)) (.num 7) (.num 3),
    mkInputCase "/error-order/pushint-overflow-y-high-before-op"
      (.num 7) (.num (maxInt257 + 1)) (.num 3),
    mkInputCase "/error-order/pushint-overflow-y-low-before-op"
      (.num 7) (.num (minInt257 - 1)) (.num 3),
    mkInputCase "/error-order/pushint-overflow-shift-high-before-op"
      (.num 7) (.num 5) (.num (maxInt257 + 1)),
    mkInputCase "/error-order/pushint-overflow-shift-low-before-op"
      (.num 7) (.num 5) (.num (minInt257 - 1)),
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodpow2rSetGasExact), .tonEnvOp .setGasLimit, qmulmodpow2rInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodpow2rSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulmodpow2rInstr]
  ]
  fuzz := #[
    { seed := 2026020853
      count := 700
      gen := genQmulmodpow2rFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULMODPOW2R
