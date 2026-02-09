import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.DIVMOD

/-
DIVMOD branch map (Lean + C++ analyzed sources):

- Lean: `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - 2 outer dispatch outcomes (`.divMod` / fallthrough).
  - Inside `.divMod`: 6 branch sites, 14 terminal outcomes total:
    - `addMode` pop path (2), operand-shape split (2), divisor-zero split (2),
      round-mode validity split (2), `d` switch (4), non-num `d==3` split (2).
  - DIVMOD specialization fixes `d=3`, `roundMode=-1`, `addMode=false`, `quiet=false`.

- C++ reference: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  - `exec_divmod`: 4 branch sites, 10 terminal outcomes:
    - add-mode remap gate (2), invalid-opcode guard (2),
      underflow guard (2), add/non-add split with `d` switch (4).
  - Opcode mapping in `register_div_ops`: DIVMOD is args4=`0xc` under `0xa90`,
    quiet variant under `0xb7a90`.

Key risk areas covered:
- quotient/remainder sign semantics for floor mode across sign combinations;
- exact vs inexact division behavior;
- division-by-zero and NaN funnels in non-quiet mode (`intOv`);
- pop/type error ordering (`y` pops before `x`);
- 257-bit overflow edge (`minInt257 / -1`);
- deterministic gas boundary (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def divmodId : InstrId := { name := "DIVMOD" }

private def divmodInstr : Instr := .divMod 3 (-1) false false

private def mkDivmodOracle
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[divmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := divmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod divmodInstr stack

private def runDivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 707)) stack

private def divmodSetGasExact : Int :=
  computeExactGasBudget divmodInstr

private def divmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne divmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def floorNumeratorPool : Array Int :=
  #[-7, -5, -1, 0, 1, 5, 7]

private def floorDenominatorPool : Array Int :=
  #[-3, -2, -1, 1, 2, 3]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genDivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
      let (x0, r2) := pickFromPool floorNumeratorPool rng1
      let (y0, r3) := pickFromPool floorDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 4 then
      ((minInt257, -1), rng1)
    else if shape = 5 then
      ((maxInt257, -1), rng1)
    else if shape = 6 then
      ((minInt257 + 1, -1), rng1)
    else if shape = 7 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickFromPool floorDenominatorPool r2
      ((x0, y0), r3)
    else if shape = 8 then
      let (x0, r2) := pickFromPool floorNumeratorPool rng1
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
    else if x % y = 0 then
      "exact"
    else
      "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkDivmodOracle s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := divmodId
  unit := #[
    { name := "unit/floor/sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 1),
            (-7, 3, -3, 2),
            (7, -3, -3, -2),
            (-7, -3, 2, -1),
            (-1, 2, -1, 1),
            (1, -2, -1, -1),
            (-5, 2, -3, 1),
            (5, -2, -3, -1),
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
          expectOkStack s!"{x}/{y}" (runDivmodDirect #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/floor/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257, 0),
            (maxInt257, -1, -maxInt257, 0),
            (minInt257, 1, minInt257, 0),
            (minInt257 + 1, -1, maxInt257, 0),
            (maxInt257, 2, (pow2 255) - 1, 1),
            (minInt257, 2, -(pow2 255), 0),
            (minInt257, -2, pow2 255, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"{x}/{y}" (runDivmodDirect #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-nan-overflow-intov"
      run := do
        expectErr "div-by-zero" (runDivmodDirect #[intV 5, intV 0]) .intOv
        expectErr "overflow/min-div-neg1" (runDivmodDirect #[intV minInt257, intV (-1)]) .intOv
        expectErr "nan-as-y" (runDivmodDirect #[intV 5, .int .nan]) .intOv
        expectErr "nan-as-x" (runDivmodDirect #[.int .nan, intV 5]) .intOv }
    ,
    { name := "unit/error/pop-order-and-type-ordering"
      run := do
        expectErr "empty" (runDivmodDirect #[]) .stkUnd
        expectErr "missing-x-after-y-pop" (runDivmodDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow-first" (runDivmodDirect #[.null]) .stkUnd
        expectErr "y-non-int-top" (runDivmodDirect #[intV 1, .null]) .typeChk
        expectErr "x-non-int-second" (runDivmodDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-pop-first" (runDivmodDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runDivmodDispatchFallback #[]) #[intV 707] }
  ]
  oracle := #[
    mkDivmodOracle "floor/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkDivmodOracle "floor/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkDivmodOracle "floor/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkDivmodOracle "floor/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkDivmodOracle "floor/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkDivmodOracle "floor/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkDivmodOracle "floor/sign/neg-pos-half" #[intV (-5), intV 2],
    mkDivmodOracle "floor/sign/pos-neg-half" #[intV 5, intV (-2)],
    mkDivmodOracle "floor/exact/pos-pos" #[intV 42, intV 7],
    mkDivmodOracle "floor/exact/neg-pos" #[intV (-42), intV 7],
    mkDivmodOracle "floor/exact/pos-neg" #[intV 42, intV (-7)],
    mkDivmodOracle "floor/exact/neg-neg" #[intV (-42), intV (-7)],
    mkDivmodOracle "floor/exact/zero-numerator" #[intV 0, intV 5],
    mkDivmodOracle "divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkDivmodOracle "nan/y-via-program" #[intV 5] #[.pushInt .nan, divmodInstr],
    mkDivmodOracle "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, divmodInstr],
    mkDivmodOracle "underflow/empty-stack" #[],
    mkDivmodOracle "underflow/missing-x-after-y-pop" #[intV 1],
    mkDivmodOracle "type/y-non-int-top" #[intV 1, .null],
    mkDivmodOracle "type/x-non-int-second" #[.null, intV 1],
    mkDivmodOracle "error-order/single-non-int-underflow-first" #[.null],
    mkDivmodOracle "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkDivmodOracle "boundary/max-div-one" #[intV maxInt257, intV 1],
    mkDivmodOracle "boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkDivmodOracle "boundary/min-div-one" #[intV minInt257, intV 1],
    mkDivmodOracle "boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkDivmodOracle "boundary/max-div-two" #[intV maxInt257, intV 2],
    mkDivmodOracle "boundary/min-div-two" #[intV minInt257, intV 2],
    mkDivmodOracle "boundary/min-div-neg-two" #[intV minInt257, intV (-2)],
    mkDivmodOracle "overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkDivmodOracle "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num divmodSetGasExact), .tonEnvOp .setGasLimit, divmodInstr],
    mkDivmodOracle "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num divmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, divmodInstr]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 700
      gen := genDivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.DIVMOD
