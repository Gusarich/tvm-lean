import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDDIVMOD

/-
ADDDIVMOD branch map (Lean + C++ analyzed sources):

- Lean execution path: `TvmLean/Semantics/Exec/Arith/DivMod.lean`
  (`execInstrArithDivMod`), plus CP0 decode wiring in
  `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa90` + args4 decode to
  `.divMod d roundMode addMode quiet` with `dEnc=0 => d=3, addMode=true`).

- C++ reference path: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_divmod`, `dump_divmod`, and `register_div_ops`).
  ADDDIVMOD is routed through `0xa90` with args4=`0x0`
  (floor round, add-mode remap, `d=3`).

Branch counts used for this suite:
- Lean (generic `.divMod` handler): 6 branch sites / 14 terminal outcomes
  (add-mode pop path, operand-shape split, divisor-zero split,
   round-mode validity split, `d` switch, non-num `d==3` split).
- C++ (`exec_divmod`): 4 branch sites / 10 terminal outcomes
  (add-mode remap gate, invalid-opcode guard, underflow guard,
   add/non-add execution split with `d` handling).

Key ADDDIVMOD risk areas covered:
- add-mode pop order (`y`, then `w`, then `x`) and corresponding type/error ordering;
- divisor-zero and NaN funneling to non-quiet `intOv` via `push_int_quiet`;
- quotient overflow from large `(x + w)` intermediates, even when both inputs fit 257-bit;
- signed floor quotient/remainder invariants across sign combinations;
- exact gas boundary behavior under `PUSHINT n; SETGASLIMIT; ADDDIVMOD`.
-/

private def addDivmodId : InstrId := { name := "ADDDIVMOD" }

private def addDivmodInstr : Instr := .divMod 3 (-1) true false

private def mkAddDivmodOracle
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[addDivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := addDivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAddDivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod addDivmodInstr stack

private def runAddDivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 909)) stack

private def addDivmodSetGasExact : Int :=
  computeExactGasBudget addDivmodInstr

private def addDivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne addDivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def floorNumeratorPool : Array Int :=
  #[-9, -7, -5, -1, 0, 1, 5, 7, 9]

private def floorDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def addendPool : Array Int :=
  #[-3, -2, -1, 0, 1, 2, 3]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genAddDivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let ((x, w, y), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickSigned257ish r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickInt257Boundary r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickInt257Boundary r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (y0, r4) := pickNonZeroInt r3
      ((x0, w0, y0), r4)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      ((x0, w0, 0), r3)
    else if shape = 5 then
      let (x0, r2) := pickFromPool floorNumeratorPool rng1
      let (w0, r3) := pickFromPool addendPool r2
      let (y0, r4) := pickFromPool floorDenominatorPool r3
      ((x0, w0, y0), r4)
    else if shape = 6 then
      ((minInt257, 0, -1), rng1)
    else if shape = 7 then
      ((minInt257 + 1, 0, -1), rng1)
    else if shape = 8 then
      ((maxInt257, 0, 1), rng1)
    else if shape = 9 then
      ((maxInt257, -1, 1), rng1)
    else if shape = 10 then
      ((maxInt257, maxInt257, 1), rng1)
    else if shape = 11 then
      ((minInt257, minInt257, 1), rng1)
    else if shape = 12 then
      let (w0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      ((0, w0, y0), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickNonZeroInt r2
      ((x0, 0, y0), r3)
  let total := x + w
  let kind :=
    if y = 0 then
      "divzero"
    else
      let (q, r) := divModRound total y (-1)
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else
        "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkAddDivmodOracle s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV w, intV y], rng3)

def suite : InstrSuite where
  id := addDivmodId
  unit := #[
    { name := "unit/floor/sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 1, 3, 2, 2),
            (-7, -1, 3, -3, 1),
            (7, 1, -3, -3, -1),
            (-7, -1, -3, 2, -2),
            (-1, 0, 2, -1, 1),
            (1, 0, -2, -1, -1),
            (5, -7, 3, -1, 1),
            (-5, 7, -3, -1, -1),
            (40, 2, 7, 6, 0),
            (-40, -2, 7, -6, 0),
            (0, 0, 5, 0, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let y := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}+{w})/{y}" (runAddDivmodDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 1, maxInt257, 0),
            (minInt257, 0, 1, minInt257, 0),
            (minInt257 + 1, 0, -1, maxInt257, 0),
            (maxInt257, -1, 1, maxInt257 - 1, 0),
            (minInt257, 1, 2, -(pow2 255), 1),
            (maxInt257, -1, 2, (pow2 255) - 1, 0)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let y := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}+{w})/{y}" (runAddDivmodDirect #[intV x, intV w, intV y]) #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "div-by-zero" (runAddDivmodDirect #[intV 5, intV 1, intV 0]) .intOv
        expectErr "overflow/min-plus-zero-div-neg-one"
          (runAddDivmodDirect #[intV minInt257, intV 0, intV (-1)]) .intOv
        expectErr "overflow/max-plus-max-div-one"
          (runAddDivmodDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-plus-min-div-one"
          (runAddDivmodDirect #[intV minInt257, intV minInt257, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-type-ordering"
      run := do
        expectErr "underflow/empty" (runAddDivmodDirect #[]) .stkUnd
        expectErr "underflow/two-items" (runAddDivmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "type/pop-y-first" (runAddDivmodDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-w-second" (runAddDivmodDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runAddDivmodDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/y-before-w-when-both-non-int"
          (runAddDivmodDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/w-before-x-when-y-int"
          (runAddDivmodDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runAddDivmodDispatchFallback #[]) #[intV 909] }
  ]
  oracle := #[
    mkAddDivmodOracle "ok/floor/sign/pos-pos-inexact" #[intV 7, intV 1, intV 3],
    mkAddDivmodOracle "ok/floor/sign/neg-pos-inexact" #[intV (-7), intV (-1), intV 3],
    mkAddDivmodOracle "ok/floor/sign/pos-neg-inexact" #[intV 7, intV 1, intV (-3)],
    mkAddDivmodOracle "ok/floor/sign/neg-neg-inexact" #[intV (-7), intV (-1), intV (-3)],
    mkAddDivmodOracle "ok/floor/sign/neg-near-zero" #[intV (-1), intV 0, intV 2],
    mkAddDivmodOracle "ok/floor/sign/pos-neg-near-zero" #[intV 1, intV 0, intV (-2)],
    mkAddDivmodOracle "ok/floor/addend/negative" #[intV 5, intV (-7), intV 3],
    mkAddDivmodOracle "ok/floor/addend/positive" #[intV (-5), intV 7, intV (-3)],
    mkAddDivmodOracle "ok/exact/pos" #[intV 40, intV 2, intV 7],
    mkAddDivmodOracle "ok/exact/neg" #[intV (-40), intV (-2), intV 7],
    mkAddDivmodOracle "ok/exact/zero-total" #[intV 5, intV (-5), intV 3],
    mkAddDivmodOracle "ok/boundary/max-plus-zero-div-one" #[intV maxInt257, intV 0, intV 1],
    mkAddDivmodOracle "ok/boundary/min-plus-zero-div-one" #[intV minInt257, intV 0, intV 1],
    mkAddDivmodOracle "ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV 0, intV (-1)],
    mkAddDivmodOracle "ok/boundary/max-minus-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkAddDivmodOracle "ok/boundary/min-plus-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkAddDivmodOracle "ok/boundary/max-minus-one-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkAddDivmodOracle "overflow/min-plus-zero-div-neg-one" #[intV minInt257, intV 0, intV (-1)],
    mkAddDivmodOracle "overflow/max-plus-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkAddDivmodOracle "overflow/min-plus-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkAddDivmodOracle "divzero/nonzero-total-over-zero" #[intV 5, intV 1, intV 0],
    mkAddDivmodOracle "divzero/zero-total-over-zero" #[intV 0, intV 0, intV 0],
    mkAddDivmodOracle "nan/y-via-program" #[intV 7, intV 1] #[.pushInt .nan, addDivmodInstr],
    mkAddDivmodOracle "nan/w-via-program" #[intV 7, intV 3]
      #[.pushInt .nan, .xchg0 1, addDivmodInstr],
    mkAddDivmodOracle "nan/x-via-program" #[intV 3]
      #[.pushInt .nan, .xchg0 1, .pushInt (.num 2), .xchg0 1, addDivmodInstr],
    mkAddDivmodOracle "underflow/empty-stack" #[],
    mkAddDivmodOracle "underflow/two-items" #[intV 1, intV 2],
    mkAddDivmodOracle "type/pop-y-first-top-non-int" #[intV 1, intV 2, .null],
    mkAddDivmodOracle "type/pop-w-second-non-int" #[intV 1, .null, intV 2],
    mkAddDivmodOracle "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkAddDivmodOracle "error-order/underflow-before-type-with-two-items" #[.null, intV 1],
    mkAddDivmodOracle "error-order/pop-y-before-w-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkAddDivmodOracle "error-order/pop-w-before-x-when-y-int"
      #[.null, .cell Cell.empty, intV 1],
    mkAddDivmodOracle "gas/exact-cost-succeeds" #[intV 7, intV 1, intV 3]
      #[.pushInt (.num addDivmodSetGasExact), .tonEnvOp .setGasLimit, addDivmodInstr],
    mkAddDivmodOracle "gas/exact-minus-one-out-of-gas" #[intV 7, intV 1, intV 3]
      #[.pushInt (.num addDivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, addDivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 700
      gen := genAddDivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDDIVMOD
