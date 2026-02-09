import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTMODR

/-
QLSHIFTMODR branch-mapping notes (Lean + C++ analyzed sources):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 2 0 false true none`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet `.shlDivMod` encoding via `0xb7 ++ 0xa9c8..0xa9ca`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-shldivmod decode for `0xb7a9c8..0xb7a9ca`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (`execInstrArithExt` `.shlDivMod` generic helper): 8 branch sites / 16 terminal outcomes.
- Lean (QLSHIFTMODR specialization): 7 branch sites / 7 reachable terminal outcomes
  (finite `ok`; tie `ok`; quiet-NaN `ok`; `stkUnd`; shift `typeChk`; y `typeChk`; x `typeChk`).
- C++ (`exec_shldivmod`, quiet runtime-shift): 8 branch sites / 14 aligned terminal outcomes.

Key risk areas covered:
- nearest remainder semantics (R-mode ties go toward `+∞`) across sign mixes and shifts `0..256`;
- strict pop/error order (`shift`, then `y`, then `x`) even when shift is quiet-invalid;
- quiet NaN funnels for divisor-zero, NaN operands, and invalid runtime shift;
- oracle serialization constraints (NaN/out-of-range injected via `PUSHINT` prelude only);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QLSHIFTMODR`.
-/

private def qlshiftmodrId : InstrId := { name := "QLSHIFTMODR" }

private def qlshiftmodrInstr : Instr :=
  .arithExt (.shlDivMod 2 0 false true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qlshiftmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def mkShiftInjectedCase
    (name : String)
    (x : Int)
    (y : Int)
    (shift : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x, intV y] #[.pushInt shift, qlshiftmodrInstr] gasLimits fuel

private def runQlshiftmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftmodrInstr stack

private def runQlshiftmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 7309)) stack

private def qlshiftmodrSetGasExact : Int :=
  computeExactGasBudget qlshiftmodrInstr

private def qlshiftmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftmodrInstr

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOutOfRangePool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def tieNumeratorPool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieDivisorPool : Array Int :=
  #[-2, 2]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromPool validShiftBoundaryPool rng1
  else
    let (n, rng2) := randNat rng1 0 256
    (Int.ofNat n, rng2)

private def pickOutOfRangeShift (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftOutOfRangePool rng

private def pickNonZeroSigned257ish (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQlshiftmodr (x y shift : Int) : String :=
  if shift < 0 || shift > 256 then
    "quiet-range-shift"
  else if y = 0 then
    "quiet-divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat
    let (_, r) := divModRound tmp y 0
    if !intFitsSigned257 r then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genQlshiftmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let y := if y0 = 0 then 1 else y0
      let (shift, r4) := pickFromPool validShiftBoundaryPool r3
      let kind := classifyQlshiftmodr x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-boundary-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickFromPool validShiftBoundaryPool r3
      let kind := classifyQlshiftmodr x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/random-boundary-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let kind := classifyQlshiftmodr x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/random-random-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      (mkCase s!"fuzz/shape-{shape}/ok/tie/shift0-pool" #[intV x, intV y, intV 0], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero-random" #[intV x, intV 0, intV shift], r3)
    else if shape = 5 then
      let (x, r2) := pickInt257Boundary rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero-boundary-shift0" #[intV x, intV 0, intV 0], r2)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (badShift, r4) := pickOutOfRangeShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/quiet/shift-range-via-program" x y (.num badShift), r4)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/quiet/shift-nan-via-program" x y .nan, r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-top-non-int" #[intV x, intV y, shiftLike], r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/y-second-non-int" #[intV x, yLike, intV shift], r4)
    else if shape = 10 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/x-third-non-int" #[xLike, intV y, intV shift], r4)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 12 then
      let (shift, r2) := pickValidShift rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-arg" #[intV shift], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-args" #[intV x, intV shift], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 15 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 16 then
      let (shift, r2) := pickValidShift rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program"
        #[IntVal.nan, IntVal.nan, IntVal.num shift], r2)
    else if shape = 17 then
      let (shift, r2) := pickValidShift rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/both-non-int-y-before-x"
        #[.cell Cell.empty, .null, intV shift], r2)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-type-before-y-type"
        #[intV x, .null, .cell Cell.empty], r2)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-does-not-mask-y-type"
        #[intV x, .null] #[.pushInt (.num 257), qlshiftmodrInstr], r2)
    else if shape = 20 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-does-not-mask-x-type"
        #[.null, intV y] #[.pushInt (.num 257), qlshiftmodrInstr], r2)
    else if shape = 21 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xo, IntVal.num y, IntVal.num shift], r4)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num yo, IntVal.num shift], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shiftOut], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftmodrId
  unit := #[
    { name := "unit/round/nearest-remainder-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, -1),
            (-7, 3, 1, 1),
            (7, -3, 1, -1),
            (-7, -3, 1, 1),
            (3, 2, 0, -1),
            (-3, 2, 0, -1),
            (3, -2, 0, 1),
            (-3, -2, 0, 1),
            (1, 2, 0, -1),
            (-1, 2, 0, -1),
            (1, -2, 0, 1),
            (-1, -2, 0, 1),
            (17, 5, 2, -2),
            (-17, 5, 2, 2)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"x={x}/y={y}/shift={shift}"
            (runQlshiftmodrDirect #[intV x, intV y, intV shift]) #[intV r] }
    ,
    { name := "unit/round/boundary-shift-edges-and-extremes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 2, 0, -1),
            (minInt257, 2, 0, 0),
            (maxInt257, maxInt257, 1, 0),
            (minInt257, maxInt257, 1, -2),
            (maxInt257, maxInt257, 256, 0),
            (minInt257, 1, 256, 0),
            (1, 2, 256, 0),
            (-1, 2, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"boundary/x={x}/y={y}/shift={shift}"
            (runQlshiftmodrDirect #[intV x, intV y, intV shift]) #[intV r]
        expectOkStack "pop-order/below-null-preserved"
          (runQlshiftmodrDirect #[.null, intV 7, intV 3, intV 1]) #[.null, intV (-1)]
        expectOkStack "pop-order/below-cell-preserved-on-quiet-shift-range"
          (runQlshiftmodrDirect #[.cell Cell.empty, intV 7, intV 3, intV 257]) #[.cell Cell.empty, .int .nan] }
    ,
    { name := "unit/quiet/nan-funnels-for-divzero-shift-and-operands"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQlshiftmodrDirect #[intV 5, intV 0, intV 3]) #[.int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQlshiftmodrDirect #[intV 0, intV 0, intV 3]) #[.int .nan]
        expectOkStack "quiet/shift-negative"
          (runQlshiftmodrDirect #[intV 5, intV 7, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/shift-overmax"
          (runQlshiftmodrDirect #[intV 5, intV 7, intV 257]) #[.int .nan]
        expectOkStack "quiet/shift-nan"
          (runQlshiftmodrDirect #[intV 5, intV 7, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan-y"
          (runQlshiftmodrDirect #[intV 5, .int .nan, intV 3]) #[.int .nan]
        expectOkStack "quiet/nan-x"
          (runQlshiftmodrDirect #[.int .nan, intV 5, intV 3]) #[.int .nan]
        expectOkStack "quiet/nan-both"
          (runQlshiftmodrDirect #[.int .nan, .int .nan, intV 3]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-quiet-range-precedence"
      run := do
        expectErr "underflow/empty" (runQlshiftmodrDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runQlshiftmodrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runQlshiftmodrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "type/shift-top-null" (runQlshiftmodrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/shift-top-cell" (runQlshiftmodrDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "type/y-second-null" (runQlshiftmodrDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/x-third-null" (runQlshiftmodrDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/both-non-int-y-before-x"
          (runQlshiftmodrDirect #[.cell Cell.empty, .null, intV 2]) .typeChk
        expectErr "error-order/shift-type-before-y-type"
          (runQlshiftmodrDirect #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "error-order/shift-range-does-not-mask-y-type"
          (runQlshiftmodrDirect #[intV 1, .null, intV 257]) .typeChk
        expectErr "error-order/shift-range-does-not-mask-x-type"
          (runQlshiftmodrDirect #[.null, intV 1, intV 257]) .typeChk
        expectErr "error-order/shift-nan-does-not-mask-y-type"
          (runQlshiftmodrDirect #[intV 1, .null, .int .nan]) .typeChk }
    ,
    { name := "unit/dispatch/non-qlshiftmodr-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQlshiftmodrDispatchFallback #[]) #[intV 7309] }
  ]
  oracle := #[
    mkCase "ok/round/sign/pos-pos-shift1-inexact" #[intV 7, intV 3, intV 1],
    mkCase "ok/round/sign/neg-pos-shift1-inexact" #[intV (-7), intV 3, intV 1],
    mkCase "ok/round/sign/pos-neg-shift1-inexact" #[intV 7, intV (-3), intV 1],
    mkCase "ok/round/sign/neg-neg-shift1-inexact" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/round/tie/pos-over-pos-two-shift0" #[intV 3, intV 2, intV 0],
    mkCase "ok/round/tie/neg-over-pos-two-shift0" #[intV (-3), intV 2, intV 0],
    mkCase "ok/round/tie/pos-over-neg-two-shift0" #[intV 3, intV (-2), intV 0],
    mkCase "ok/round/tie/neg-over-neg-two-shift0" #[intV (-3), intV (-2), intV 0],
    mkCase "ok/round/tie/one-over-pos-two-shift0" #[intV 1, intV 2, intV 0],
    mkCase "ok/round/tie/neg-one-over-pos-two-shift0" #[intV (-1), intV 2, intV 0],
    mkCase "ok/round/tie/one-over-neg-two-shift0" #[intV 1, intV (-2), intV 0],
    mkCase "ok/round/tie/neg-one-over-neg-two-shift0" #[intV (-1), intV (-2), intV 0],
    mkCase "ok/round/exact/zero-numerator" #[intV 0, intV 5, intV 7],
    mkCase "ok/round/exact/shift-zero-noop" #[intV 37, intV 5, intV 0],
    mkCase "ok/round/large-shift-pos" #[intV 1, intV 2, intV 8],
    mkCase "ok/round/large-shift-neg" #[intV (-1), intV 2, intV 8],
    mkCase "ok/boundary/max-shift0-div2" #[intV maxInt257, intV 2, intV 0],
    mkCase "ok/boundary/min-shift0-div2" #[intV minInt257, intV 2, intV 0],
    mkCase "ok/boundary/max-shift1-divmax" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "ok/boundary/min-shift1-divmax" #[intV minInt257, intV maxInt257, intV 1],
    mkCase "ok/boundary/max-shift256-divmax" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256-div1" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/pop-order/below-null-preserved" #[.null, intV 7, intV 3, intV 1],
    mkCase "ok/pop-order/below-cell-preserved" #[.cell Cell.empty, intV (-7), intV 3, intV 1],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0, intV 3],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 3],
    mkShiftInjectedCase "quiet/shift-negative-via-program" 5 7 (.num (-1)),
    mkShiftInjectedCase "quiet/shift-overmax-via-program" 5 7 (.num 257),
    mkShiftInjectedCase "quiet/shift-nan-via-program" 5 7 .nan,
    mkCaseFromIntVals "quiet/nan-y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 3],
    mkCaseFromIntVals "quiet/nan-x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "quiet/nan-both-via-program" #[IntVal.nan, IntVal.nan, IntVal.num 3],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "type/shift-top-null" #[intV 1, intV 2, .null],
    mkCase "type/y-second-null" #[intV 1, .null, intV 2],
    mkCase "type/x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/both-non-int-y-first" #[.cell Cell.empty, .null, intV 2],
    mkCase "error-order/shift-range-does-not-mask-y-type-via-program"
      #[intV 5, .null] #[.pushInt (.num 257), qlshiftmodrInstr],
    mkCase "error-order/shift-range-does-not-mask-x-type-via-program"
      #[.null, intV 5] #[.pushInt (.num 257), qlshiftmodrInstr],
    mkCase "error-order/shift-nan-does-not-mask-y-type-via-program"
      #[intV 5, .null] #[.pushInt .nan, qlshiftmodrInstr],
    mkCaseFromIntVals "error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 5, IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-y-low-before-op"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-high-before-op"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-low-before-op"
      #[IntVal.num 5, IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-both-before-op"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (maxInt257 + 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftmodrSetGasExact), .tonEnvOp .setGasLimit, qlshiftmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num qlshiftmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020853
      count := 700
      gen := genQlshiftmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTMODR
