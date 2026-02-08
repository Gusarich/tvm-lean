import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MOD

/-
MOD branch map (Lean + C++ analyzed sources):

- Lean: `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - General helper: 6 branch sites / 14 terminal outcomes.
  - MOD specialization (`.divMod 2 (-1) false false`): 5 reachable terminal outcomes
    (`ok`, `stkUnd`, `typeChk`, `intOv` via divisor zero, `intOv` via NaN funnel).

- C++: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_divmod`, `register_div_ops`) plus
  `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
  (`Stack::pop_int`, `Stack::push_int_quiet`).
  - MOD opcode wiring uses args4=`0x8` (`0xa908`), quiet variant `0xb7a908`.
  - MOD runtime path has 4 main branch sites / 6 reachable terminal outcomes
    (underflow; `y` type check; `x` type check; `td::mod` finite-vs-NaN through
     `push_int_quiet` in non-quiet mode).

Key risk areas covered:
- floor remainder sign semantics across mixed signs;
- divisor-zero and NaN operands flowing to non-quiet `intOv`;
- pop order and error ordering (`stkUnd` before type checks, `y` before `x`);
- signed-257 boundary behavior near `minInt257`/`maxInt257` with `±1`, `±2`;
- exact gas boundary for `PUSHINT n; SETGASLIMIT; MOD`.
-/

private def modId : InstrId := { name := "MOD" }

private def modInstr : Instr := .divMod 2 (-1) false false

private def mkModOracle
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := modId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod modInstr stack

private def runModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 909)) stack

private def modSetGasExact : Int :=
  computeExactGasBudget modInstr

private def modSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modInstr

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

private def genModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
      ((maxInt257, 1), rng1)
    else if shape = 5 then
      ((maxInt257, -1), rng1)
    else if shape = 6 then
      ((maxInt257, 2), rng1)
    else if shape = 7 then
      ((minInt257, 1), rng1)
    else if shape = 8 then
      ((minInt257, -1), rng1)
    else if shape = 9 then
      ((minInt257, 2), rng1)
    else if shape = 10 then
      ((minInt257, -2), rng1)
    else
      let (y0, r2) := pickNonZeroInt rng1
      ((0, y0), r2)
  let kind :=
    if y = 0 then
      "divzero"
    else if x = 0 then
      "zero"
    else if x % y = 0 then
      "exact"
    else
      "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkModOracle s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y], rng3)

def suite : InstrSuite where
  id := modId
  unit := #[
    { name := "unit/floor/sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 1),
            (-7, 3, 2),
            (7, -3, -2),
            (-7, -3, -1),
            (-1, 2, 1),
            (1, -2, -1),
            (-5, 2, 1),
            (5, -2, -1),
            (42, 7, 0),
            (-42, 7, 0),
            (42, -7, 0),
            (-42, -7, 0),
            (0, 5, 0),
            (0, -5, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let r := c.2.2
          expectOkStack s!"{x}%{y}" (runModDirect #[intV x, intV y]) #[intV r] }
    ,
    { name := "unit/floor/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, 0),
            (maxInt257, -1, 0),
            (maxInt257, 2, 1),
            (minInt257, 1, 0),
            (minInt257, -1, 0),
            (minInt257, 2, 0),
            (minInt257, -2, 0),
            (minInt257 + 1, -1, 0),
            (minInt257 + 1, 2, 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let r := c.2.2
          expectOkStack s!"{x}%{y}" (runModDirect #[intV x, intV y]) #[intV r] }
    ,
    { name := "unit/error/intov-and-pop-ordering"
      run := do
        expectErr "div-by-zero" (runModDirect #[intV 5, intV 0]) .intOv
        expectErr "empty" (runModDirect #[]) .stkUnd
        expectErr "missing-x-after-y-pop" (runModDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow-first" (runModDirect #[.null]) .stkUnd
        expectErr "y-non-int-top" (runModDirect #[intV 1, .null]) .typeChk
        expectErr "x-non-int-second" (runModDirect #[.null, intV 1]) .typeChk
        expectErr "both-non-int-y-pop-first" (runModDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "fallback" (runModDispatchFallback #[]) #[intV 909] }
  ]
  oracle := #[
    mkModOracle "ok/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkModOracle "ok/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkModOracle "ok/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkModOracle "ok/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkModOracle "ok/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkModOracle "ok/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkModOracle "ok/sign/neg-pos-half" #[intV (-5), intV 2],
    mkModOracle "ok/sign/pos-neg-half" #[intV 5, intV (-2)],
    mkModOracle "ok/exact/pos-pos" #[intV 42, intV 7],
    mkModOracle "ok/exact/neg-pos" #[intV (-42), intV 7],
    mkModOracle "ok/exact/pos-neg" #[intV 42, intV (-7)],
    mkModOracle "ok/exact/neg-neg" #[intV (-42), intV (-7)],
    mkModOracle "ok/exact/zero-numerator-pos-divisor" #[intV 0, intV 5],
    mkModOracle "ok/exact/zero-numerator-neg-divisor" #[intV 0, intV (-5)],
    mkModOracle "boundary/max-mod-one" #[intV maxInt257, intV 1],
    mkModOracle "boundary/max-mod-neg-one" #[intV maxInt257, intV (-1)],
    mkModOracle "boundary/max-mod-two" #[intV maxInt257, intV 2],
    mkModOracle "boundary/min-mod-one" #[intV minInt257, intV 1],
    mkModOracle "boundary/min-mod-neg-one" #[intV minInt257, intV (-1)],
    mkModOracle "boundary/min-mod-two" #[intV minInt257, intV 2],
    mkModOracle "boundary/min-mod-neg-two" #[intV minInt257, intV (-2)],
    mkModOracle "boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 2],
    mkModOracle "intov/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkModOracle "nan/y-via-program" #[intV 5] #[.pushInt .nan, modInstr],
    mkModOracle "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, modInstr],
    mkModOracle "underflow/empty-stack" #[],
    mkModOracle "underflow/missing-x-after-y-pop" #[intV 1],
    mkModOracle "type/y-non-int-top" #[intV 1, .null],
    mkModOracle "type/x-non-int-second" #[.null, intV 1],
    mkModOracle "error-order/single-non-int-underflow-first" #[.null],
    mkModOracle "error-order/both-non-int-y-pop-first" #[.cell Cell.empty, .null],
    mkModOracle "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num modSetGasExact), .tonEnvOp .setGasLimit, modInstr],
    mkModOracle "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num modSetGasExactMinusOne), .tonEnvOp .setGasLimit, modInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 700
      gen := genModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MOD
