import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QRSHIFTMOD

/-
QRSHIFTMOD branch-mapping notes (Lean + C++ analyzed sources):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 3 (-1) true none`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet `.shrMod` encoding via `0xb7 ++ 0xa92c..0xa92e`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-shrmod decode for `0xb7a92c..0xb7a92e`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (`execInstrArithExt` `.shrMod` generic helper): 9 branch sites / 20 terminal outcomes.
- Lean (QRSHIFTMOD specialization): 6 branch sites / 6 reachable terminal outcomes
  (`ok` numeric pair, `ok` quiet-NaN pair, `stkUnd`, shift `typeChk`,
   shift `rangeChk`, x `typeChk`).
- C++ (`exec_shrmod` runtime-shift + Q registration): 7 branch sites / 14 terminal outcomes.

Key risk areas covered:
- floor quotient/remainder behavior across sign combinations and shift boundaries;
- strict runtime shift validation (`0..256`) even for quiet opcodes;
- pop/error ordering (`stkUnd` before type checks, shift failures before x pop);
- quiet NaN behavior (`x = NaN` yields pushed NaN pair, no throw);
- oracle serialization constraints (NaN/out-of-range only via program prelude);
- exact gas boundary for `PUSHINT n; SETGASLIMIT; QRSHIFTMOD`.
-/

private def qrshiftmodId : InstrId := { name := "QRSHIFTMOD" }

private def qrshiftmodInstr : Instr :=
  .arithExt (.shrMod false false 3 (-1) true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qrshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qrshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x shift : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, shift]
  mkCase name (below ++ stack) (progPrefix.push qrshiftmodInstr) gasLimits fuel

private def runQrshiftmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qrshiftmodInstr stack

private def runQrshiftmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 2026)) stack

private def qrshiftmodSetGasExact : Int :=
  computeExactGasBudget qrshiftmodInstr

private def qrshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qrshiftmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-2, -1, 257, 258, 400]

private def smallSignPool : Array Int :=
  #[-33, -13, -9, -7, -5, -1, 0, 1, 5, 7, 9, 13, 33]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def genQrshiftmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-x-boundary-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-x-random-shift"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool smallSignPool rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/small-sign-mix"
        #[intV x, intV (Int.ofNat shift)], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (badShift, r3) := pickFromPool shiftInvalidPool r2
      let badShift := if badShift < 0 then badShift else 257
      (mkCase s!"fuzz/shape-{shape}/range/shift-negative-or-over"
        #[intV x, intV badShift], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (badShift, r3) := pickFromPool shiftInvalidPool r2
      let badShift := if badShift > 256 then badShift else 258
      (mkCase s!"fuzz/shape-{shape}/range/shift-over-256"
        #[intV x, intV badShift], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type/shift-top-non-int" #[intV x, shiftLike], r3)
    else if shape = 8 then
      let (xLike, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftMixed r2
      (mkCase s!"fuzz/shape-{shape}/type/x-second-non-int"
        #[xLike, intV (Int.ofNat shift)], r3)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 10 then
      let (shift, r2) := pickShiftMixed rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/missing-x-after-shift-pop"
        #[intV (Int.ofNat shift)], r2)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow/one-non-int" #[.null], rng1)
    else if shape = 12 then
      let (shift, r2) := pickShiftMixed rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        .nan (.num (Int.ofNat shift)), r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/range/shift-nan-via-program"
        (.num x) .nan, r2)
    else if shape = 14 then
      let (badShift, r2) := pickFromPool shiftInvalidPool rng1
      let badShift := if badShift < 0 then badShift else 257
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-range-before-x-type"
        #[xLike, intV badShift], r3)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/shift-type-before-x-type"
        #[xLike, shiftLike], r3)
    else if shape = 16 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftMixed r2
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num (Int.ofNat shift)), r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftOut, r3) := pickInt257OutOfRange r2
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        (.num x) (.num shiftOut), r3)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shiftOut, r3) := pickInt257OutOfRange r2
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        (.num xOut) (.num shiftOut), r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qrshiftmodId
  unit := #[
    { name := "unit/direct/floor-quot-rem-sign-and-boundaries"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (13, 2, 3, 1),
            (-13, 2, -4, 3),
            (7, 3, 0, 7),
            (-7, 3, -1, 1),
            (1, 1, 0, 1),
            (-1, 1, -1, 1),
            (0, 200, 0, 0),
            (9, 0, 9, 0),
            (-9, 0, -9, 0),
            (maxInt257, 1, (pow2 255) - 1, 1),
            (minInt257, 1, -(pow2 255), 0),
            (maxInt257, 256, 0, maxInt257),
            (minInt257, 256, -1, 0),
            (minInt257 + 1, 256, -1, 1),
            (-1, 256, -1, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"x={x}/shift={shift}"
            (runQrshiftmodDirect #[intV x, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/direct/pop-order-top-consumed-below-preserved"
      run := do
        expectOkStack "below-null"
          (runQrshiftmodDirect #[.null, intV 13, intV 2])
          #[.null, intV 3, intV 1]
        expectOkStack "below-cell"
          (runQrshiftmodDirect #[.cell Cell.empty, intV (-13), intV 2])
          #[.cell Cell.empty, intV (-4), intV 3] }
    ,
    { name := "unit/error-order/underflow-type-range-and-precedence"
      run := do
        expectErr "underflow/empty" (runQrshiftmodDirect #[]) .stkUnd
        expectErr "underflow/missing-x-after-shift-pop" (runQrshiftmodDirect #[intV 3]) .stkUnd
        expectErr "underflow/one-non-int" (runQrshiftmodDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runQrshiftmodDirect #[intV 9, .null]) .typeChk
        expectErr "type/shift-top-cell" (runQrshiftmodDirect #[intV 9, .cell Cell.empty]) .typeChk
        expectErr "type/x-second-null" (runQrshiftmodDirect #[.null, intV 3]) .typeChk
        expectErr "range/shift-negative" (runQrshiftmodDirect #[intV 9, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runQrshiftmodDirect #[intV 9, intV 257]) .rangeChk
        expectErr "error-order/range-before-x-type-neg"
          (runQrshiftmodDirect #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-over"
          (runQrshiftmodDirect #[.cell Cell.empty, intV 257]) .rangeChk
        expectErr "error-order/type-on-shift-before-x"
          (runQrshiftmodDirect #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/quiet/nan-x-pair-and-shift-range-strictness"
      run := do
        expectOkStack "quiet/nan-x-shift5"
          (runQrshiftmodDirect #[.int .nan, intV 5]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan-x-shift0"
          (runQrshiftmodDirect #[.int .nan, intV 0]) #[.int .nan, .int .nan]
        expectErr "range/shift-nan" (runQrshiftmodDirect #[intV 5, .int .nan]) .rangeChk
        expectErr "error-order/shift-nan-before-x-type"
          (runQrshiftmodDirect #[.null, .int .nan]) .rangeChk }
    ,
    { name := "unit/dispatch/non-qrshiftmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQrshiftmodDispatchFallback #[]) #[intV 2026] }
  ]
  oracle := #[
    mkCase "ok/floor/sign/pos-shift2" #[intV 13, intV 2],
    mkCase "ok/floor/sign/neg-shift2" #[intV (-13), intV 2],
    mkCase "ok/floor/sign/pos-shift3" #[intV 7, intV 3],
    mkCase "ok/floor/sign/neg-shift3" #[intV (-7), intV 3],
    mkCase "ok/floor/sign/neg-near-zero" #[intV (-1), intV 1],
    mkCase "ok/floor/exact/zero-large-shift" #[intV 0, intV 200],
    mkCase "ok/floor/shift-zero-pos" #[intV 9, intV 0],
    mkCase "ok/floor/shift-zero-neg" #[intV (-9), intV 0],
    mkCase "ok/boundary/max-shift1" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/min-shift1" #[intV minInt257, intV 1],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/neg-one-shift256" #[intV (-1), intV 256],
    mkCase "ok/order/below-null-preserved" #[.null, intV 13, intV 2],
    mkCase "ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-13), intV 2],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 3],
    mkCase "underflow/one-non-int" #[.null],
    mkCase "type/shift-top-null" #[intV 9, .null],
    mkCase "type/shift-top-cell" #[intV 9, .cell Cell.empty],
    mkCase "type/x-second-null" #[.null, intV 3],
    mkCase "error-order/both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative" #[intV 9, intV (-1)],
    mkCase "range/shift-over-256" #[intV 9, intV 257],
    mkCase "error-order/range-before-x-type-neg" #[.null, intV (-1)],
    mkCase "error-order/range-before-x-type-over" #[.cell Cell.empty, intV 257],
    mkInputCase "quiet/nan-x-via-program" .nan (.num 5),
    mkInputCase "quiet/nan-x-via-program-shift0" .nan (.num 0),
    mkInputCase "range/shift-nan-via-program" (.num 5) .nan,
    mkInputCase "error-order/shift-nan-before-x-nan-via-program" .nan .nan,
    mkInputCase "error-order/pushint-overflow-x-high-before-op" (.num (maxInt257 + 1)) (.num 5),
    mkInputCase "error-order/pushint-overflow-x-low-before-op" (.num (minInt257 - 1)) (.num 5),
    mkInputCase "error-order/pushint-overflow-shift-high-before-op" (.num 5) (.num (maxInt257 + 1)),
    mkInputCase "error-order/pushint-overflow-shift-low-before-op" (.num 5) (.num (minInt257 - 1)),
    mkInputCase "error-order/pushint-overflow-both-before-op" (.num (pow2 257)) (.num (-(pow2 257))),
    mkCase "gas/exact-cost-succeeds" #[intV 13, intV 2]
      #[.pushInt (.num qrshiftmodSetGasExact), .tonEnvOp .setGasLimit, qrshiftmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 13, intV 2]
      #[.pushInt (.num qrshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qrshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020836
      count := 700
      gen := genQrshiftmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFTMOD
