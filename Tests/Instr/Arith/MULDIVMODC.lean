import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULDIVMODC

/-
MULDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `1` / ceil)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa98` + args4 decode to `.mulDivMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (generic `.mulDivMod`): 6 branch sites / 14 terminal outcomes
  (dispatch arm; add-mode pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch with non-num `d=3` split).
- C++ (`exec_muldivmod`): 5 branch sites / 10 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add tmp-init split; `d` result-shape switch).

MULDIVMODC specialization:
- opcode args4=`0xe` under `0xa98`;
- fixed params: `d=3`, `roundMode=1` (ceil), `addMode=false`, `quiet=false`.

Key risk areas covered:
- ceil quotient/remainder sign behavior on mixed-sign products;
- pop order and error ordering (`z`, then `y`, then `x`);
- non-quiet NaN/divzero funnels to `intOv` (NaN injected via program only);
- out-of-range literal injection via program (`PUSHINT`) ordering vs opcode execution;
- signed 257-bit overflow on quotient push near `minInt257`/`maxInt257`;
- deterministic gas boundary via exact / exact-minus-one `SETGASLIMIT`.
-/

private def muldivmodcId : InstrId := { name := "MULDIVMODC" }

private def muldivmodcInstr : Instr := .mulDivMod 3 1 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muldivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muldivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInjectedCase
    (name : String)
    (vals : Array IntVal)
    (suffix : Array Instr := #[muldivmodcInstr]) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ suffix)

private def runMulDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod muldivmodcInstr stack

private def runMulDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 4040)) stack

private def muldivmodcSetGasExact : Int :=
  computeExactGasBudget muldivmodcInstr

private def muldivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muldivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def ceilFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def ceilDivisorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def mkFiniteFuzzCase (shape : Nat) (tag : Nat) (x y z : Int) : OracleCase :=
  let tmp := x * y
  let kind :=
    if z = 0 then
      "divzero"
    else
      let (q, r) := divModRound tmp z 1
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else
        "inexact"
  mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV z]

private def genMulDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x0, r3) := pickInt257Boundary rng2
    let (y0, r4) := pickInt257Boundary r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 1 then
    let (x0, r3) := pickInt257Boundary rng2
    let (y0, r4) := pickSigned257ish r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 2 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickInt257Boundary r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 3 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    let (z0, r5) := pickNonZeroInt r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 4 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkFiniteFuzzCase shape tag x0 y0 0, r4)
  else if shape = 5 then
    let (x0, r3) := pickFromPool ceilFactorPool rng2
    let (y0, r4) := pickFromPool ceilFactorPool r3
    let (z0, r5) := pickFromPool ceilDivisorPool r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 6 then
    (mkFiniteFuzzCase shape tag minInt257 (-1) 1, rng2)
  else if shape = 7 then
    (mkFiniteFuzzCase shape tag maxInt257 maxInt257 1, rng2)
  else if shape = 8 then
    (mkFiniteFuzzCase shape tag minInt257 minInt257 1, rng2)
  else if shape = 9 then
    let (y0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkFiniteFuzzCase shape tag 0 y0 z0, r4)
  else if shape = 10 then
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkFiniteFuzzCase shape tag x0 0 z0, r4)
  else if shape = 11 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkFiniteFuzzCase shape tag x0 y0 1, r4)
  else if shape = 12 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkFiniteFuzzCase shape tag x0 y0 (-1), r4)
  else if shape = 13 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickSigned257ish r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-z-{tag}"
      #[IntVal.num x0, IntVal.num y0, IntVal.nan], r4)
  else if shape = 14 then
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-y-{tag}"
      #[IntVal.num x0, IntVal.nan, IntVal.num z0], r4)
  else if shape = 15 then
    let (y0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickNonZeroInt r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-x-{tag}"
      #[IntVal.nan, IntVal.num y0, IntVal.num z0], r4)
  else if shape = 16 then
    let (slot, r3) := randNat rng2 0 2
    let (delta, r4) := randNat r3 1 4096
    let hi := maxInt257 + Int.ofNat delta
    let vals :=
      if slot = 0 then
        #[IntVal.num hi, IntVal.num 1, IntVal.num 1]
      else if slot = 1 then
        #[IntVal.num 1, IntVal.num hi, IntVal.num 1]
      else
        #[IntVal.num 1, IntVal.num 1, IntVal.num hi]
    (mkInjectedCase s!"fuzz/shape-{shape}/out-of-range-high-slot-{slot}-{tag}" vals, r4)
  else
    let (slot, r3) := randNat rng2 0 2
    let (delta, r4) := randNat r3 1 4096
    let lo := minInt257 - Int.ofNat delta
    let vals :=
      if slot = 0 then
        #[IntVal.num lo, IntVal.num 1, IntVal.num 1]
      else if slot = 1 then
        #[IntVal.num 1, IntVal.num lo, IntVal.num 1]
      else
        #[IntVal.num 1, IntVal.num 1, IntVal.num lo]
    (mkInjectedCase s!"fuzz/shape-{shape}/out-of-range-low-slot-{slot}-{tag}" vals, r4)

def suite : InstrSuite where
  id := muldivmodcId
  unit := #[
    { name := "unit/ok/ceil-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 11, -1),
            (-7, 3, 2, -10, -1),
            (7, -3, 2, -10, -1),
            (-7, -3, 2, 11, -1),
            (5, 5, 2, 13, -1),
            (-5, 5, 2, -12, -1),
            (5, -5, 2, -12, -1),
            (-5, -5, 2, 13, -1),
            (-1, 1, 2, 0, -1),
            (1, -1, 2, 0, -1),
            (-1, -1, 2, 1, -1),
            (0, 9, 5, 0, 0),
            (9, 0, 5, 0, 0),
            (42, 6, 7, 36, 0),
            (-42, 6, 7, -36, 0),
            (42, -6, 7, -36, 0),
            (-42, -6, 7, 36, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})/{z}"
            (runMulDivModCDirect #[intV x, intV y, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/ok/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, maxInt257, 0),
            (maxInt257, -1, 1, -maxInt257, 0),
            (minInt257, 1, 1, minInt257, 0),
            (minInt257, -1, -1, minInt257, 0),
            (minInt257 + 1, -1, -1, -maxInt257, 0),
            (maxInt257, 1, 2, pow2 255, -1),
            (maxInt257, -1, 2, 1 - (pow2 255), -1),
            (minInt257, 1, 2, -(pow2 255), 0),
            (minInt257, 1, -2, pow2 255, 0),
            (minInt257 + 1, -1, 2, pow2 255, -1),
            (maxInt257, 1, -2, 1 - (pow2 255), 1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})/{z}"
            (runMulDivModCDirect #[intV x, intV y, intV z])
            #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-and-overflow-intov"
      run := do
        expectErr "divzero/nonzero-product-over-zero"
          (runMulDivModCDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "divzero/zero-product-over-zero"
          (runMulDivModCDirect #[intV 0, intV 7, intV 0]) .intOv
        expectErr "overflow/min-times-neg-one-div-one"
          (runMulDivModCDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/min-times-one-div-neg-one"
          (runMulDivModCDirect #[intV minInt257, intV 1, intV (-1)]) .intOv
        expectErr "overflow/max-times-max-div-one"
          (runMulDivModCDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-times-min-div-one"
          (runMulDivModCDirect #[intV minInt257, intV minInt257, intV 1]) .intOv }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runMulDivModCDirect #[]) .stkUnd
        expectErr "underflow/one-int-before-missing-y" (runMulDivModCDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-ints-before-missing-x" (runMulDivModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type-with-two-items"
          (runMulDivModCDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-z-first"
          (runMulDivModCDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second"
          (runMulDivModCDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third"
          (runMulDivModCDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-z-before-y-when-both-non-int"
          (runMulDivModCDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-z-int"
          (runMulDivModCDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runMulDivModCDispatchFallback #[]) #[intV 4040] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "ok/ceil/sign/neg-pos-near-zero" #[intV (-1), intV 1, intV 2],
    mkCase "ok/ceil/sign/pos-neg-near-zero" #[intV 1, intV (-1), intV 2],
    mkCase "ok/ceil/sign/neg-neg-near-zero" #[intV (-1), intV (-1), intV 2],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 6, intV 7],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 6, intV 7],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-6), intV 7],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-6), intV 7],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "ok/boundary/max-times-neg-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 1],
    mkCase "ok/boundary/min-times-neg-one-div-neg-one" #[intV minInt257, intV (-1), intV (-1)],
    mkCase "ok/boundary/min-plus-one-times-neg-one-div-neg-one"
      #[intV (minInt257 + 1), intV (-1), intV (-1)],
    mkCase "ok/boundary/max-times-one-div-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "ok/boundary/max-times-neg-one-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "ok/boundary/min-times-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "ok/boundary/min-times-one-div-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "ok/boundary/min-plus-one-times-neg-one-div-two"
      #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "ok/boundary/max-times-one-div-neg-two" #[intV maxInt257, intV 1, intV (-2)],
    mkCase "divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "overflow/min-times-neg-one-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "overflow/min-times-one-div-neg-one" #[intV minInt257, intV 1, intV (-1)],
    mkCase "overflow/max-times-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "overflow/min-times-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-int-before-missing-y" #[intV 1],
    mkCase "underflow/two-ints-before-missing-x" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkInjectedCase "nan/z-via-program" #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInjectedCase "nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkInjectedCase "nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkInjectedCase "nan/all-via-program" #[IntVal.nan, IntVal.nan, IntVal.nan],
    mkInjectedCase "error-order/pushint-out-of-range-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 1, IntVal.num 1],
    mkInjectedCase "error-order/pushint-out-of-range-low-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivmodcSetGasExact), .tonEnvOp .setGasLimit, muldivmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num muldivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, muldivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genMulDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULDIVMODC
