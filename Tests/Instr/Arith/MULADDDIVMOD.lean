import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULADDDIVMOD

/-
MULADDDIVMOD branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
  (handler `execInstrArithMulDivMod` for `.mulDivMod d roundMode addMode quiet`).
- Lean decode wiring: `TvmLean/Model/Instr/Codepage/Cp0.lean`
  (`0xa98` + args4, where `dEnc=0` maps to `d=3, addMode=true`).
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_muldivmod`, `dump_muldivmod`, and opcode registration in `register_div_ops`).

Branch counts used for this suite:
- Lean (generic `.mulDivMod` handler): 7 branch sites / 16 terminal outcomes
  (stack-underflow guard; add-mode pop path; operand-shape match;
   divisor-zero split; round-mode validity split; `d` switch;
   non-numeric fallback `d==3` split).
- C++ (`exec_muldivmod`): 5 branch sites / 11 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add operand pop path; `d` result-shape switch).

Key risk areas covered:
- underflow-vs-type error ordering (`check_underflow(4)` must win);
- operand pop order in add-mode (`z`, then `w`, then `y`, then `x`);
- NaN funneling in non-quiet mode (`intOv`) with NaN injected via program only;
- quotient/remainder 257-bit boundary overflow for large `x*y + w`;
- signed floor quotient/remainder invariants for mixed signs;
- exact gas boundaries under `PUSHINT n; SETGASLIMIT; MULADDDIVMOD`.
-/

private def mulAddDivmodId : InstrId := { name := "MULADDDIVMOD" }

private def mulAddDivmodInstr : Instr := .mulDivMod 3 (-1) true false

private def mkMulAddDivmodOracle
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulAddDivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulAddDivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulAddDivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod mulAddDivmodInstr stack

private def runMulAddDivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 913)) stack

private def mulAddDivmodSetGasExact : Int :=
  computeExactGasBudget mulAddDivmodInstr

private def mulAddDivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulAddDivmodInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def floorFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def floorDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def floorAddendPool : Array Int :=
  #[-6, -3, -1, 0, 1, 3, 6]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genMulAddDivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let ((x, y, w, z), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 1 then
      let (x0, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickInt257Boundary r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 2 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickInt257Boundary r2
      let (w0, r4) := pickInt257Boundary r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
    else if shape = 4 then
      let (y0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((0, y0, w0, z0), r4)
    else if shape = 5 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, 0, w0, z0), r4)
    else if shape = 6 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (z0, r4) := pickNonZeroInt r3
      ((x0, y0, 0, z0), r4)
    else if shape = 7 then
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      ((x0, y0, w0, 0), r4)
    else if shape = 8 then
      ((minInt257, 1, 0, -1), rng1)
    else if shape = 9 then
      ((maxInt257, maxInt257, 0, 1), rng1)
    else if shape = 10 then
      ((minInt257, minInt257, 0, 1), rng1)
    else if shape = 11 then
      ((maxInt257, 1, -1, 2), rng1)
    else if shape = 12 then
      ((minInt257, 1, 1, 2), rng1)
    else if shape = 13 then
      ((minInt257 + 1, -1, 0, 1), rng1)
    else if shape = 14 then
      let (x0, r2) := pickFromPool floorFactorPool rng1
      let (y0, r3) := pickFromPool floorFactorPool r2
      let (w0, r4) := pickFromPool floorAddendPool r3
      let (z0, r5) := pickFromPool floorDivisorPool r4
      ((x0, y0, w0, z0), r5)
    else
      let (x0, r2) := pickSigned257ish rng1
      let (y0, r3) := pickSigned257ish r2
      let (w0, r4) := pickSigned257ish r3
      let (z0, r5) := pickNonZeroInt r4
      ((x0, y0, w0, z0), r5)
  let tmp := x * y + w
  let kind :=
    if z = 0 then
      "divzero"
    else
      let (q, r) := divModRound tmp z (-1)
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else
        "inexact"
  let (tag, rng3) := randNat rng2 0 999_999
  (mkMulAddDivmodOracle s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV w, intV z], rng3)

def suite : InstrSuite where
  id := mulAddDivmodId
  unit := #[
    { name := "unit/floor/sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 5, 4, 2),
            (-7, 3, -1, 5, -5, 3),
            (7, -3, 1, 5, -4, 0),
            (7, 3, 1, -5, -5, -3),
            (-7, -3, -1, -5, -4, 0),
            (-1, 2, 0, 3, -1, 1),
            (1, -2, 0, 3, -1, 1),
            (-1, 2, 0, -3, 0, -2),
            (1, -2, 0, -3, 0, -2),
            (40, 2, 2, 7, 11, 5),
            (-40, 2, -2, 7, -12, 2)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let w := c.2.2.1
          let z := c.2.2.2.1
          let q := c.2.2.2.2.1
          let r := c.2.2.2.2.2
          expectOkStack s!"({x}*{y}+{w})/{z}"
            (runMulAddDivmodDirect #[intV x, intV y, intV w, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 1, maxInt257, 0),
            (minInt257, 1, 0, 1, minInt257, 0),
            (minInt257 + 1, -1, 0, 1, maxInt257, 0),
            (maxInt257, 1, -1, 2, (pow2 255) - 1, 0),
            (minInt257, 1, 1, 2, -(pow2 255), 1),
            (maxInt257, 0, -1, 1, -1, 0),
            (minInt257, 0, 1, 1, 1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let w := c.2.2.1
          let z := c.2.2.2.1
          let q := c.2.2.2.2.1
          let r := c.2.2.2.2.2
          expectOkStack s!"({x}*{y}+{w})/{z}"
            (runMulAddDivmodDirect #[intV x, intV y, intV w, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "div-by-zero" (runMulAddDivmodDirect #[intV 5, intV 7, intV 1, intV 0]) .intOv
        expectErr "overflow/min-times-one-div-neg-one"
          (runMulAddDivmodDirect #[intV minInt257, intV 1, intV 0, intV (-1)]) .intOv
        expectErr "overflow/max-times-max-div-one"
          (runMulAddDivmodDirect #[intV maxInt257, intV maxInt257, intV 0, intV 1]) .intOv
        expectErr "overflow/min-times-min-div-one"
          (runMulAddDivmodDirect #[intV minInt257, intV minInt257, intV 0, intV 1]) .intOv
        expectErr "overflow/max-times-two-plus-one-div-one"
          (runMulAddDivmodDirect #[intV maxInt257, intV 2, intV 1, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runMulAddDivmodDirect #[]) .stkUnd
        expectErr "underflow/one-non-int" (runMulAddDivmodDirect #[.null]) .stkUnd
        expectErr "underflow/three-with-top-non-int"
          (runMulAddDivmodDirect #[intV 1, intV 2, .null]) .stkUnd
        expectErr "type/pop-z-first"
          (runMulAddDivmodDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "type/pop-w-second"
          (runMulAddDivmodDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "type/pop-y-third"
          (runMulAddDivmodDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "type/pop-x-fourth"
          (runMulAddDivmodDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "error-order/pop-z-before-w-when-both-non-int"
          (runMulAddDivmodDirect #[intV 1, intV 2, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-w-before-y-when-z-int"
          (runMulAddDivmodDirect #[intV 1, .null, .cell Cell.empty, intV 2]) .typeChk
        expectErr "error-order/pop-y-before-x-when-z-w-int"
          (runMulAddDivmodDirect #[.null, .cell Cell.empty, intV 1, intV 2]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulAddDivmodDispatchFallback #[]) #[intV 913] }
  ]
  oracle := #[
    mkMulAddDivmodOracle "ok/floor/sign/pos-pos-inexact" #[intV 7, intV 3, intV 1, intV 5],
    mkMulAddDivmodOracle "ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 3, intV (-1), intV 5],
    mkMulAddDivmodOracle "ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 1, intV 5],
    mkMulAddDivmodOracle "ok/floor/sign/pos-neg-divisor-inexact" #[intV 7, intV 3, intV 1, intV (-5)],
    mkMulAddDivmodOracle "ok/floor/sign/neg-neg-divisor-exact" #[intV (-7), intV (-3), intV (-1), intV (-5)],
    mkMulAddDivmodOracle "ok/floor/near-zero-pos-divisor" #[intV (-1), intV 2, intV 0, intV 3],
    mkMulAddDivmodOracle "ok/floor/near-zero-neg-divisor" #[intV (-1), intV 2, intV 0, intV (-3)],
    mkMulAddDivmodOracle "ok/floor/addend-negative" #[intV 5, intV 4, intV (-7), intV 3],
    mkMulAddDivmodOracle "ok/floor/addend-positive" #[intV (-5), intV 4, intV 7, intV (-3)],
    mkMulAddDivmodOracle "ok/exact/positive-total" #[intV 42, intV 2, intV 0, intV 7],
    mkMulAddDivmodOracle "ok/exact/negative-total" #[intV (-42), intV 2, intV 0, intV 7],
    mkMulAddDivmodOracle "ok/exact/zero-total" #[intV 5, intV 7, intV (-35), intV 3],
    mkMulAddDivmodOracle "ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 0, intV 1],
    mkMulAddDivmodOracle "ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 0, intV 1],
    mkMulAddDivmodOracle "ok/boundary/min-plus-one-negated-div-one"
      #[intV (minInt257 + 1), intV (-1), intV 0, intV 1],
    mkMulAddDivmodOracle "ok/boundary/max-minus-one-div-two"
      #[intV maxInt257, intV 1, intV (-1), intV 2],
    mkMulAddDivmodOracle "ok/boundary/min-plus-one-div-two"
      #[intV minInt257, intV 1, intV 1, intV 2],
    mkMulAddDivmodOracle "overflow/min-times-one-div-neg-one"
      #[intV minInt257, intV 1, intV 0, intV (-1)],
    mkMulAddDivmodOracle "overflow/max-times-max-div-one"
      #[intV maxInt257, intV maxInt257, intV 0, intV 1],
    mkMulAddDivmodOracle "overflow/min-times-min-div-one"
      #[intV minInt257, intV minInt257, intV 0, intV 1],
    mkMulAddDivmodOracle "overflow/max-times-two-plus-one-div-one"
      #[intV maxInt257, intV 2, intV 1, intV 1],
    mkMulAddDivmodOracle "divzero/nonzero-total-over-zero"
      #[intV 5, intV 7, intV 1, intV 0],
    mkMulAddDivmodOracle "divzero/zero-total-over-zero"
      #[intV 0, intV 123, intV 0, intV 0],
    mkMulAddDivmodOracle "underflow/empty-stack" #[],
    mkMulAddDivmodOracle "underflow/one-item" #[intV 1],
    mkMulAddDivmodOracle "underflow/three-items-top-non-int" #[intV 1, intV 2, .null],
    mkMulAddDivmodOracle "type/pop-z-first-top-non-int"
      #[intV 1, intV 2, intV 3, .null],
    mkMulAddDivmodOracle "type/pop-w-second-non-int"
      #[intV 1, intV 2, .null, intV 3],
    mkMulAddDivmodOracle "type/pop-y-third-non-int"
      #[intV 1, .null, intV 2, intV 3],
    mkMulAddDivmodOracle "type/pop-x-fourth-non-int"
      #[.null, intV 1, intV 2, intV 3],
    mkMulAddDivmodOracle "error-order/pop-z-before-w-when-both-non-int"
      #[intV 1, intV 2, .cell Cell.empty, .null],
    mkMulAddDivmodOracle "error-order/pop-w-before-y-when-z-int"
      #[intV 1, .null, .cell Cell.empty, intV 2],
    mkMulAddDivmodOracle "error-order/pop-y-before-x-when-z-w-int"
      #[.null, .cell Cell.empty, intV 1, intV 2],
    mkMulAddDivmodOracle "nan/z-via-program" #[intV 7, intV 3, intV 1]
      #[.pushInt .nan, mulAddDivmodInstr],
    mkMulAddDivmodOracle "nan/w-via-program" #[intV 7, intV 3, intV 5]
      #[.pushInt .nan, .xchg0 1, mulAddDivmodInstr],
    mkMulAddDivmodOracle "nan/y-via-program" #[intV 7, intV 5, intV 3]
      #[.pushInt .nan, .xchg0 2, .xchg0 1, mulAddDivmodInstr],
    mkMulAddDivmodOracle "nan/x-via-program" #[intV 5, intV 3, intV 2]
      #[.pushInt .nan, .xchg0 3, .xchg0 2, .xchg0 1, mulAddDivmodInstr],
    mkMulAddDivmodOracle "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1, intV 5]
      #[.pushInt (.num mulAddDivmodSetGasExact), .tonEnvOp .setGasLimit, mulAddDivmodInstr],
    mkMulAddDivmodOracle "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1, intV 5]
      #[.pushInt (.num mulAddDivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulAddDivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020809
      count := 700
      gen := genMulAddDivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDDIVMOD
