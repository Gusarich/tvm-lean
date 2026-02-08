import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTDIVMODC

/-
QLSHIFTDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 1 false true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, quiet `pushIntQuiet`, underflow/type ordering)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, ceil mode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (QLSHIFTDIVMODC specialization):
- Lean specialization: 8 branch sites / 14 terminal outcomes
  (dispatch/fallback; depth gate; runtime-shift pop/type; non-quiet range gate
   bypassed for Q; divisor/x pop type gates; bad-shift quiet NaN funnel;
   numeric-vs-NaN operand split; divisor-zero split; `d=3` two-result quiet pushes).
- C++ specialization (`exec_shldivmod`, mode=1): 8 branch sites / 13 aligned outcomes
  (global-version add-remap/invalid-op guard; underflow gate;
   runtime shift pop + relaxed range behavior; divisor/x `pop_int` gates;
   v13 invalid-input quiet funnel; `d` switch with `DIVMOD` double-push).

Key risk areas covered:
- ceil quotient/remainder sign behavior for mixed-sign operands after left shift;
- quiet behavior for div-by-zero, bad shifts, NaN operands, and quotient overflow;
- pop/error ordering (`shift` first, then divisor, then x) including bad-shift + type precedence;
- underflow precedence on short stacks before all type/range checks;
- oracle serialization hygiene (`NaN` / out-of-range only via program `PUSHINT`);
- deterministic gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qlshiftdivmodcId : InstrId := { name := "QLSHIFTDIVMODC" }

private def qlshiftdivmodcInstr : Instr :=
  .arithExt (.shlDivMod 3 1 false true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftdivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftdivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qlshiftdivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQlshiftdivmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftdivmodcInstr stack

private def runQlshiftdivmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5152)) stack

private def qlshiftdivmodcSetGasExact : Int :=
  computeExactGasBudget qlshiftdivmodcInstr

private def qlshiftdivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftdivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 15, 31, 63, 127, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-3, -1, 257, 258, 511]

private def smallSignedPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def smallNonZeroPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftValid (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode < 3 then
    pickFromNatPool shiftBoundaryPool rng1
  else
    randNat rng1 0 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQlshiftdivmodc (x y : Int) (shift : Nat) : String :=
  if y = 0 then
    "quiet-divzero"
  else
    let tmp := x * intPow2 shift
    let (q, r) := divModRound tmp y 1
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def mkFiniteFuzzCase
    (shape : Nat)
    (kind : String)
    (x y : Int)
    (shift : Nat) : OracleCase :=
  mkCase s!"fuzz/shape-{shape}/{kind}" #[intV x, intV y, intV (Int.ofNat shift)]

private def genQlshiftdivmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (case0, rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickNonZeroInt r2
      let (z0, r4) := pickFromNatPool shiftBoundaryPool r3
      let kind := classifyQlshiftdivmodc x0 y0 z0
      (mkFiniteFuzzCase shape kind x0 y0 z0, r4)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0b, r3) := pickInt257Boundary r2
      let y0 := if y0b = 0 then 1 else y0b
      let (z0, r4) := pickShiftValid r3
      let kind := classifyQlshiftdivmodc x0 y0 z0
      (mkFiniteFuzzCase shape kind x0 y0 z0, r4)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      let (z0, r4) := pickShiftValid r3
      let kind := classifyQlshiftdivmodc x0 y0 z0
      (mkFiniteFuzzCase shape kind x0 y0 z0, r4)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickShiftValid r2
      (mkFiniteFuzzCase shape "quiet-divzero" x0 0 z0, r3)
    else if shape = 4 then
      (mkFiniteFuzzCase shape "quiet-overflow-max-shift1-div1" maxInt257 1 1, rng1)
    else if shape = 5 then
      (mkFiniteFuzzCase shape "quiet-overflow-min-shift1-div-neg1" minInt257 (-1) 1, rng1)
    else if shape = 6 then
      (mkFiniteFuzzCase shape "quiet-overflow-one-shift256-div1" 1 1 256, rng1)
    else if shape = 7 then
      (mkFiniteFuzzCase shape "quiet-overflow-negone-shift256-div-neg1" (-1) (-1) 256, rng1)
    else if shape = 8 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/quiet/range-shift-negative" #[intV x0, intV y0, intV (-1)], r3)
    else if shape = 9 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/quiet/range-shift-over-256" #[intV x0, intV y0, intV 257], r3)
    else if shape = 10 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/range-shift-nan-via-program"
        #[.num x0, .num y0, .nan], r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 12 then
      let (x0, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-item-int" #[intV x0], r2)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow/two-items-non-int" #[.null, .cell Cell.empty], rng1)
    else if shape = 14 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-top-non-int" #[intV x0, intV y0, shiftLike], r4)
    else if shape = 15 then
      let (x0, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (z0, r4) := pickShiftValid r3
      (mkCase s!"fuzz/shape-{shape}/type/divisor-second-non-int"
        #[intV x0, yLike, intV (Int.ofNat z0)], r4)
    else if shape = 16 then
      let (xLike, r2) := pickNonInt rng1
      let (y0, r3) := pickNonZeroInt r2
      let (z0, r4) := pickShiftValid r3
      (mkCase s!"fuzz/shape-{shape}/type/x-third-non-int"
        #[xLike, intV y0, intV (Int.ofNat z0)], r4)
    else if shape = 17 then
      let (x0, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/bad-shift-before-divisor-type"
        #[intV x0, yLike, intV 257], r3)
    else if shape = 18 then
      let (xLike, r2) := pickNonInt rng1
      let (y0, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/bad-shift-before-x-type"
        #[xLike, intV y0, intV 257], r3)
    else if shape = 19 then
      let (y0, r2) := pickNonZeroInt rng1
      let (z0, r3) := pickShiftValid r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num y0, .num (Int.ofNat z0)], r3)
    else if shape = 20 then
      let (x0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickShiftValid r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-divisor-via-program"
        #[.num x0, .nan, .num (Int.ofNat z0)], r3)
    else if shape = 21 then
      let (z0, r2) := pickShiftValid rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program"
        #[.nan, .nan, .num (Int.ofNat z0)], r2)
    else if shape = 22 then
      let (y0, r2) := pickNonZeroInt rng1
      let (z0, r3) := pickShiftValid r2
      let (hugeX, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[.num hugeX, .num y0, .num (Int.ofNat z0)], r4)
    else if shape = 23 then
      let (x0, r2) := pickSigned257ish rng1
      let (z0, r3) := pickShiftValid r2
      let (hugeY, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-divisor-before-op"
        #[.num x0, .num hugeY, .num (Int.ofNat z0)], r4)
    else if shape = 24 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      let (hugeShift, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[.num x0, .num y0, .num hugeShift], r4)
    else if shape = 25 then
      let (hugeX, r2) := pickInt257OutOfRange rng1
      let (hugeY, r3) := pickInt257OutOfRange r2
      let (hugeShift, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        #[.num hugeX, .num hugeY, .num hugeShift], r4)
    else if shape = 26 then
      let (x0, r2) := pickFromIntPool smallSignedPool rng1
      let (y0, r3) := pickFromIntPool smallNonZeroPool r2
      let (z0, r4) := pickFromNatPool shiftBoundaryPool r3
      let kind := classifyQlshiftdivmodc x0 y0 z0
      (mkFiniteFuzzCase shape kind x0 y0 z0, r4)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      let (rawShift, r4) := pickFromIntPool shiftInvalidPool r3
      let badShift := if rawShift < 0 then rawShift else 257
      (mkCase s!"fuzz/shape-{shape}/quiet/range-invalid-shift-from-pool"
        #[intV x0, intV y0, intV badShift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftdivmodcId
  unit := #[
    { name := "unit/ok/ceil-sign-shift-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 5, -1),
            (-7, 3, 1, -4, -2),
            (7, -3, 1, -4, 2),
            (-7, -3, 1, 5, 1),
            (1, 2, 0, 1, -1),
            (-1, 2, 0, 0, -1),
            (5, 3, 2, 7, -1),
            (-5, 3, 2, -6, -2),
            (5, -3, 2, -6, 2),
            (-5, -3, 2, 7, 1),
            (0, 5, 42, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}"
            (runQlshiftdivmodcDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/ok/pop-order-and-below-preservation"
      run := do
        expectOkStack "below-null"
          (runQlshiftdivmodcDirect #[.null, intV 7, intV 3, intV 1])
          #[.null, intV 5, intV (-1)]
        expectOkStack "below-cell-quiet-bad-shift"
          (runQlshiftdivmodcDirect #[.cell Cell.empty, intV 7, intV 3, intV (-1)])
          #[.cell Cell.empty, .int .nan, .int .nan] }
    ,
    { name := "unit/quiet/nan-funnels-divzero-overflow-and-range"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQlshiftdivmodcDirect #[intV 5, intV 0, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQlshiftdivmodcDirect #[intV 0, intV 0, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "quiet/overflow/max-shift1-div1"
          (runQlshiftdivmodcDirect #[intV maxInt257, intV 1, intV 1]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/min-shift1-div-neg1"
          (runQlshiftdivmodcDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/one-shift256-div1"
          (runQlshiftdivmodcDirect #[intV 1, intV 1, intV 256]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/negone-shift256-div-neg1"
          (runQlshiftdivmodcDirect #[intV (-1), intV (-1), intV 256]) #[.int .nan, intV 0]
        expectOkStack "quiet/range/shift-neg-one"
          (runQlshiftdivmodcDirect #[intV 5, intV 3, intV (-1)]) #[.int .nan, .int .nan]
        expectOkStack "quiet/range/shift-257"
          (runQlshiftdivmodcDirect #[intV 5, intV 3, intV 257]) #[.int .nan, .int .nan]
        expectOkStack "quiet/range/shift-nan"
          (runQlshiftdivmodcDirect #[intV 5, intV 3, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/divisor"
          (runQlshiftdivmodcDirect #[intV 5, .int .nan, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/x"
          (runQlshiftdivmodcDirect #[.int .nan, intV 3, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/both"
          (runQlshiftdivmodcDirect #[.int .nan, .int .nan, intV 1]) #[.int .nan, .int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-bad-shift-precedence"
      run := do
        expectErr "underflow/empty" (runQlshiftdivmodcDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runQlshiftdivmodcDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runQlshiftdivmodcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type-with-two-items"
          (runQlshiftdivmodcDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-shift-first"
          (runQlshiftdivmodcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-divisor-second"
          (runQlshiftdivmodcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third"
          (runQlshiftdivmodcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-shift-before-divisor-when-both-non-int"
          (runQlshiftdivmodcDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/pop-divisor-before-x-after-bad-shift"
          (runQlshiftdivmodcDirect #[.null, .cell Cell.empty, intV 257]) .typeChk
        expectErr "error-order/pop-x-after-divisor-when-bad-shift"
          (runQlshiftdivmodcDirect #[.null, intV 3, intV 257]) .typeChk
        expectErr "error-order/pop-divisor-after-shift-nan"
          (runQlshiftdivmodcDirect #[intV 5, .null, .int .nan]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQlshiftdivmodcDispatchFallback #[]) #[intV 5152] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 1],
    mkCase "ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 1],
    mkCase "ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 1],
    mkCase "ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/ceil/sign/near-zero-pos-div" #[intV 1, intV 2, intV 0],
    mkCase "ok/ceil/sign/neg-near-zero-pos-div" #[intV (-1), intV 2, intV 0],
    mkCase "ok/ceil/exact/zero-left" #[intV 0, intV 5, intV 42],
    mkCase "ok/ceil/exact/max-shift255-div-two" #[intV 1, intV 2, intV 255],
    mkCase "ok/ceil/exact/neg-one-shift256-div-neg-two" #[intV (-1), intV (-2), intV 256],
    mkCase "ok/ceil/boundary/max-shift0-div-one" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/ceil/boundary/min-shift0-div-one" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/ceil/boundary/min-plus-one-shift0-div-neg-one" #[intV (minInt257 + 1), intV (-1), intV 0],
    mkCase "ok/ceil/boundary/max-shift1-div-neg-two" #[intV maxInt257, intV (-2), intV 1],
    mkCase "ok/ceil/boundary/min-shift1-div-two" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/ceil/boundary/min-plus-one-shift1-div-two" #[intV (minInt257 + 1), intV 2, intV 1],
    mkCase "ok/ceil/boundary/max-shift0-div-three" #[intV maxInt257, intV 3, intV 0],
    mkCase "ok/ceil/boundary/min-shift0-div-three" #[intV minInt257, intV 3, intV 0],
    mkCase "ok/order/below-null-preserved" #[.null, intV 7, intV 3, intV 1],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0, intV 1],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 3],
    mkCase "quiet/overflow/max-shift1-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "quiet/overflow/min-shift1-div-neg-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "quiet/overflow/one-shift256-div-one" #[intV 1, intV 1, intV 256],
    mkCase "quiet/overflow/neg-one-shift256-div-neg-one" #[intV (-1), intV (-1), intV 256],
    mkCase "quiet/range/shift-neg-one" #[intV 5, intV 3, intV (-1)],
    mkCase "quiet/range/shift-257" #[intV 5, intV 3, intV 257],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "type/pop-shift-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-divisor-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-shift-before-divisor-when-both-non-int"
      #[intV 1, .null, .cell Cell.empty],
    mkCase "error-order/pop-divisor-before-x-after-bad-shift"
      #[.null, .cell Cell.empty, intV 257],
    mkCase "error-order/pop-x-after-divisor-with-bad-shift"
      #[.null, intV 3, intV 257],
    mkCase "error-order/pop-divisor-after-shift-nan-via-program" #[intV 5, .null]
      #[.pushInt .nan, qlshiftdivmodcInstr],
    mkCaseFromIntVals "quiet/nan/shift-via-program"
      #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "quiet/nan/divisor-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "quiet/nan/x-via-program"
      #[IntVal.nan, IntVal.num 7, IntVal.num 1],
    mkCaseFromIntVals "quiet/nan/all-via-program"
      #[IntVal.nan, IntVal.nan, IntVal.nan],
    mkCaseFromIntVals "error-order/pushint-out-of-range-high-x-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-out-of-range-low-divisor-before-op"
      #[IntVal.num 1, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "error-order/pushint-out-of-range-high-shift-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-out-of-range-low-shift-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qlshiftdivmodcSetGasExact), .tonEnvOp .setGasLimit, qlshiftdivmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qlshiftdivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftdivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020837
      count := 700
      gen := genQlshiftdivmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTDIVMODC
