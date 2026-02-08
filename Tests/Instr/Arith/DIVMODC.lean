import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.DIVMODC

/-
DIVMODC branch map (Lean + C++ analyzed sources):

- Lean: `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  with rounding math from `TvmLean/Model/Basics/Bytes.lean` (`divModRound`).
  - 2 dispatch outcomes (`.divMod` / fallthrough).
  - Inside `.divMod`: 6 branch sites, 14 terminal outcomes total:
    - `addMode` pop path (2), operand-shape split (2), divisor-zero split (2),
      round-mode validity split (2), `d` switch (4), non-num `d==3` split (2).
  - DIVMODC specialization fixes `d=3`, `roundMode=1`, `addMode=false`, `quiet=false`.

- C++ reference: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  - `exec_divmod`: 4 branch sites, 10 terminal outcomes:
    - add-mode remap gate (2), invalid-opcode guard (2),
      underflow guard (2), add/non-add split with `d` switch (4).
  - Opcode mapping in `register_div_ops`: DIVMODC is args4=`0xe` under `0xa90`,
    quiet variant under `0xb7a90`.

Key risk areas covered:
- ceil quotient/remainder semantics for all sign combinations and near-zero fractions;
- division-by-zero and NaN funnels in non-quiet mode (`intOv`);
- pop order / error order (`y` is popped before `x`, underflow before type on short stack);
- signed 257-bit overflow edge (`minInt257 / -1`);
- deterministic gas boundary (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def divmodcId : InstrId := { name := "DIVMODC" }

private def divmodcInstr : Instr := .divMod 3 1 false false

private def mkDivmodcOracle
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[divmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := divmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDivmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod divmodcInstr stack

private def runDivmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 1707)) stack

private def divmodcSetGasExact : Int :=
  computeExactGasBudget divmodcInstr

private def divmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne divmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def ceilNumeratorPool : Array Int :=
  #[-7, -5, -1, 0, 1, 5, 7]

private def ceilDenominatorPool : Array Int :=
  #[-3, -2, -1, 1, 2, 3]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genDivmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let ((x, y), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
    else if shape = 3 then
      let (x0, r2) := pickFromPool ceilNumeratorPool rng1
      let (y0, r3) := pickFromPool ceilDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 4 then
      ((minInt257, -1), rng1)
    else if shape = 5 then
      ((maxInt257, -1), rng1)
    else if shape = 6 then
      ((minInt257 + 1, -1), rng1)
    else if shape = 7 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool ceilDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 8 then
      let (x0, r2) := pickFromPool ceilNumeratorPool rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, y0), r3)
    else if shape = 9 then
      let (y0, r2) := pickNonZeroInt rng1
      ((0, y0), r2)
    else if shape = 10 then
      ((maxInt257, 1), rng1)
    else
      ((minInt257, 1), rng1)
  let kind :=
    if y = 0 then
      "divzero"
    else if x = minInt257 && y = -1 then
      "overflow"
    else
      "ok"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkDivmodcOracle s!"fuzz/{kind}/shape-{shape}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := divmodcId
  unit := #[
    { name := "unit/ceil/sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 3, -2),
            (-7, 3, -2, -1),
            (7, -3, -2, 1),
            (-7, -3, 3, 2),
            (-1, 2, 0, -1),
            (1, -2, 0, 1),
            (-5, 2, -2, -1),
            (5, -2, -2, 1),
            (42, 7, 6, 0),
            (-42, 7, -6, 0),
            (42, -7, -6, 0),
            (-42, -7, 6, 0),
            (0, 5, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"{x}/{y}" (runDivmodcDirect #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/ceil/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257, 0),
            (maxInt257, -1, -maxInt257, 0),
            (minInt257, 1, minInt257, 0),
            (minInt257 + 1, -1, maxInt257, 0),
            (maxInt257, 2, pow2 255, -1),
            (minInt257, 2, -(pow2 255), 0),
            (minInt257, -2, pow2 255, 0),
            (maxInt257, -2, 1 - (pow2 255), 1),
            (0, -1, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"{x}/{y}" (runDivmodcDirect #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "div-by-zero" (runDivmodcDirect #[intV 5, intV 0]) .intOv
        expectErr "overflow/min-div-neg1" (runDivmodcDirect #[intV minInt257, intV (-1)]) .intOv }
    ,
    { name := "unit/error/pop-order-and-type-ordering"
      run := do
        expectErr "empty" (runDivmodcDirect #[]) .stkUnd
        expectErr "missing-x-after-y-pop" (runDivmodcDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow-first" (runDivmodcDirect #[.null]) .stkUnd
        expectErr "type-y-first" (runDivmodcDirect #[intV 1, .null]) .typeChk
        expectErr "type-x-second" (runDivmodcDirect #[.null, intV 1]) .typeChk
        expectErr "type-both-non-int-y-first" (runDivmodcDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runDivmodcDispatchFallback #[]) #[intV 1707] }
  ]
  oracle := #[
    mkDivmodcOracle "ok/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkDivmodcOracle "ok/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkDivmodcOracle "ok/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkDivmodcOracle "ok/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkDivmodcOracle "ok/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkDivmodcOracle "ok/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkDivmodcOracle "ok/sign/neg-pos-half" #[intV (-5), intV 2],
    mkDivmodcOracle "ok/sign/pos-neg-half" #[intV 5, intV (-2)],
    mkDivmodcOracle "ok/exact/pos-pos" #[intV 42, intV 7],
    mkDivmodcOracle "ok/exact/neg-pos" #[intV (-42), intV 7],
    mkDivmodcOracle "ok/exact/pos-neg" #[intV 42, intV (-7)],
    mkDivmodcOracle "ok/exact/neg-neg" #[intV (-42), intV (-7)],
    mkDivmodcOracle "ok/exact/zero-numerator" #[intV 0, intV 5],
    mkDivmodcOracle "divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkDivmodcOracle "nan/y-via-program" #[intV 5] #[.pushInt .nan, divmodcInstr],
    mkDivmodcOracle "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, divmodcInstr],
    mkDivmodcOracle "underflow/empty-stack" #[],
    mkDivmodcOracle "underflow/missing-x-after-y-pop" #[intV 1],
    mkDivmodcOracle "type/pop-y-first-null" #[intV 1, .null],
    mkDivmodcOracle "type/pop-x-second-null" #[.null, intV 1],
    mkDivmodcOracle "error-order/single-non-int-underflow-before-type" #[.null],
    mkDivmodcOracle "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkDivmodcOracle "ok/boundary/max-div-one" #[intV maxInt257, intV 1],
    mkDivmodcOracle "ok/boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkDivmodcOracle "ok/boundary/min-div-one" #[intV minInt257, intV 1],
    mkDivmodcOracle "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkDivmodcOracle "ok/boundary/max-div-two" #[intV maxInt257, intV 2],
    mkDivmodcOracle "ok/boundary/min-div-two" #[intV minInt257, intV 2],
    mkDivmodcOracle "ok/boundary/min-div-neg-two" #[intV minInt257, intV (-2)],
    mkDivmodcOracle "overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkDivmodcOracle "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num divmodcSetGasExact), .tonEnvOp .setGasLimit, divmodcInstr],
    mkDivmodcOracle "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num divmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, divmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 700
      gen := genDivmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.DIVMODC
