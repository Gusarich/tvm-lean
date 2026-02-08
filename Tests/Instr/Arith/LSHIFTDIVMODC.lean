import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTDIVMODC

/-
LSHIFTDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shlDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, mode `1` / ceil)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa9ce` decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (`.arithExt (.shlDivMod ...)` runtime-shift specialization):
  8 branch sites / 14 terminal outcomes
  (dispatch; stack-depth gate; runtime-shift source; shift-range gate;
   operand-shape split; divisor-zero split; round-mode validity; `d` switch).
- C++ (`exec_shldivmod`, mode=0):
  7 branch sites / 13 aligned terminal outcomes
  (add-mode remap gate; invalid-opcode gate; underflow gate; shift-range gate;
   post-pop validity gate; `d` switch; non-quiet push-int overflow paths).

LSHIFTDIVMODC specialization:
- opcode `0xa9ce`;
- fixed params: `d=3`, `roundMode=1` (ceil), `addMode=false`, `quiet=false`;
- runtime shift is popped first from stack (`x z shift`, top=`shift`).

Key risk areas covered:
- ceil quotient/remainder sign behavior on mixed-sign inputs;
- runtime shift range boundary and ordering (`rangeChk` before divisor/type checks);
- stack underflow/type-check ordering (`check_underflow(3)` semantics);
- division-by-zero and NaN propagation in non-quiet mode (`intOv`);
- signed 257-bit overflow on quotient push after large shifts;
- deterministic gas boundary via exact / exact-minus-one `SETGASLIMIT`.
-/

private def lshiftdivmodcId : InstrId := { name := "LSHIFTDIVMODC" }

private def lshiftdivmodcInstr : Instr :=
  .arithExt (.shlDivMod 3 1 false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftdivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftdivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInjectedCase
    (name : String)
    (vals : Array IntVal)
    (suffix : Array Instr := #[lshiftdivmodcInstr]) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ suffix)

private def runLShiftDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftdivmodcInstr stack

private def runLShiftDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5151)) stack

private def lshiftdivmodcSetGasExact : Int :=
  computeExactGasBudget lshiftdivmodcInstr

private def lshiftdivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftdivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 31, 63, 127, 255, 256]

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

private def mkFiniteFuzzCase (shape : Nat) (tag : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let tmp := x * intPow2 shift
  let kind :=
    if y = 0 then
      "divzero"
    else
      let (q, r) := divModRound tmp y 1
      if !intFitsSigned257 q || !intFitsSigned257 r then
        "overflow"
      else if r = 0 then
        "exact"
      else
        "inexact"
  mkCase s!"fuzz/shape-{shape}/{kind}-{tag}" #[intV x, intV y, intV (Int.ofNat shift)]

private def genLShiftDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x0, r3) := pickInt257Boundary rng2
    let (y0, r4) := pickNonZeroInt r3
    let (z0, r5) := pickFromNatPool shiftBoundaryPool r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 1 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickInt257Boundary r3
    let y1 := if y0 = 0 then 1 else y0
    let (z0, r5) := pickShiftValid r4
    (mkFiniteFuzzCase shape tag x0 y1 z0, r5)
  else if shape = 2 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    let (z0, r5) := pickShiftValid r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 3 then
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickShiftValid r3
    (mkFiniteFuzzCase shape tag x0 0 z0, r4)
  else if shape = 4 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    (mkCase s!"fuzz/shape-{shape}/range-neg-{tag}" #[intV x0, intV y0, intV (-1)], r4)
  else if shape = 5 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    (mkCase s!"fuzz/shape-{shape}/range-hi-{tag}" #[intV x0, intV y0, intV 257], r4)
  else if shape = 6 then
    (mkFiniteFuzzCase shape tag maxInt257 1 1, rng2)
  else if shape = 7 then
    (mkFiniteFuzzCase shape tag minInt257 (-1) 1, rng2)
  else if shape = 8 then
    (mkFiniteFuzzCase shape tag minInt257 1 0, rng2)
  else if shape = 9 then
    let (x0, r3) := pickFromIntPool smallSignedPool rng2
    let (y0, r4) := pickFromIntPool smallNonZeroPool r3
    let (z0, r5) := pickFromNatPool shiftBoundaryPool r4
    (mkFiniteFuzzCase shape tag x0 y0 z0, r5)
  else if shape = 10 then
    let (y0, r3) := pickNonZeroInt rng2
    let (z0, r4) := pickShiftValid r3
    (mkFiniteFuzzCase shape tag 0 y0 z0, r4)
  else if shape = 11 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-shift-{tag}"
      #[IntVal.num x0, IntVal.num y0, IntVal.nan], r4)
  else if shape = 12 then
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickShiftValid r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-divisor-{tag}"
      #[IntVal.num x0, IntVal.nan, IntVal.num (Int.ofNat z0)], r4)
  else if shape = 13 then
    let (y0, r3) := pickNonZeroInt rng2
    let (z0, r4) := pickShiftValid r3
    (mkInjectedCase s!"fuzz/shape-{shape}/nan-x-{tag}"
      #[IntVal.nan, IntVal.num y0, IntVal.num (Int.ofNat z0)], r4)
  else if shape = 14 then
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
  else if shape = 15 then
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
  else if shape = 16 then
    let (x0, r3) := pickSigned257ish rng2
    let (y0, r4) := pickNonZeroInt r3
    let (z0, r5) := pickShiftValid r4
    let caseName := s!"fuzz/shape-{shape}/underflow-empty-{tag}"
    let _ := (x0, y0, z0)
    (mkCase caseName #[], r5)
  else if shape = 17 then
    let (asType, r3) := randBool rng2
    if asType then
      (mkCase s!"fuzz/shape-{shape}/underflow-two-items-{tag}" #[.null, .cell Cell.empty], r3)
    else
      (mkCase s!"fuzz/shape-{shape}/underflow-one-item-{tag}" #[intV 1], r3)
  else
    let (x0, r3) := pickSigned257ish rng2
    let (z0, r4) := pickShiftValid r3
    (mkCase s!"fuzz/shape-{shape}/type-divisor-{tag}" #[intV x0, .null, intV (Int.ofNat z0)], r4)

def suite : InstrSuite where
  id := lshiftdivmodcId
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
            (runLShiftDivModCDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/ok/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257, 0),
            (minInt257, 1, 0, minInt257, 0),
            (minInt257 + 1, -1, 0, maxInt257, 0),
            (maxInt257, -2, 1, -maxInt257, 0),
            (minInt257, 2, 1, minInt257, 0),
            (minInt257 + 1, 2, 1, minInt257 + 1, 0),
            (maxInt257, 3, 0, (pow2 256 - 1) / 3, 0),
            (minInt257, 3, 0, -((pow2 256 - 1) / 3), -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}<<{shift})/{y}"
            (runLShiftDivModCDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/error/divzero-overflow-range"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runLShiftDivModCDirect #[intV 5, intV 0, intV 1]) .intOv
        expectErr "divzero/zero-over-zero"
          (runLShiftDivModCDirect #[intV 0, intV 0, intV 3]) .intOv
        expectErr "overflow/max-shift1-div-one"
          (runLShiftDivModCDirect #[intV maxInt257, intV 1, intV 1]) .intOv
        expectErr "overflow/min-shift1-div-neg-one"
          (runLShiftDivModCDirect #[intV minInt257, intV (-1), intV 1]) .intOv
        expectErr "overflow/one-shift256-div-one"
          (runLShiftDivModCDirect #[intV 1, intV 1, intV 256]) .intOv
        expectErr "range/shift-neg-one"
          (runLShiftDivModCDirect #[intV 5, intV 3, intV (-1)]) .rangeChk
        expectErr "range/shift-257"
          (runLShiftDivModCDirect #[intV 5, intV 3, intV 257]) .rangeChk }
    ,
    { name := "unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "underflow/empty" (runLShiftDivModCDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runLShiftDivModCDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runLShiftDivModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type-with-two-items"
          (runLShiftDivModCDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "type/pop-shift-first"
          (runLShiftDivModCDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-divisor-second"
          (runLShiftDivModCDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third"
          (runLShiftDivModCDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-shift-before-divisor-when-both-non-int"
          (runLShiftDivModCDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-divisor-before-x-after-shift-int"
          (runLShiftDivModCDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "error-order/range-before-divisor-type"
          (runLShiftDivModCDirect #[.null, .cell Cell.empty, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runLShiftDivModCDispatchFallback #[]) #[intV 5151] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 1],
    mkCase "ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 1],
    mkCase "ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 1],
    mkCase "ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/ceil/sign/near-zero-pos-div" #[intV 1, intV 2, intV 0],
    mkCase "ok/ceil/sign/near-zero-neg-div" #[intV 1, intV (-2), intV 0],
    mkCase "ok/ceil/sign/neg-near-zero-pos-div" #[intV (-1), intV 2, intV 0],
    mkCase "ok/exact/zero-left" #[intV 0, intV 5, intV 42],
    mkCase "ok/exact/max-shift255-div-two" #[intV 1, intV 2, intV 255],
    mkCase "ok/exact/max-shift256-div-neg-one" #[intV (-1), intV (-1), intV 256],
    mkCase "ok/boundary/max-shift0-div-one" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-shift0-div-one" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-plus-one-shift0-div-neg-one" #[intV (minInt257 + 1), intV (-1), intV 0],
    mkCase "ok/boundary/max-shift1-div-neg-two" #[intV maxInt257, intV (-2), intV 1],
    mkCase "ok/boundary/min-shift1-div-two" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-plus-one-shift1-div-two" #[intV (minInt257 + 1), intV 2, intV 1],
    mkCase "ok/boundary/max-shift0-div-three" #[intV maxInt257, intV 3, intV 0],
    mkCase "ok/boundary/min-shift0-div-three" #[intV minInt257, intV 3, intV 0],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0, intV 1],
    mkCase "divzero/zero-over-zero" #[intV 0, intV 0, intV 3],
    mkCase "overflow/max-shift1-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "overflow/min-shift1-div-neg-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "overflow/one-shift256-div-one" #[intV 1, intV 1, intV 256],
    mkCase "overflow/neg-one-shift256-div-neg-one" #[intV (-1), intV (-1), intV 256],
    mkCase "range/shift-neg-one" #[intV 5, intV 3, intV (-1)],
    mkCase "range/shift-257" #[intV 5, intV 3, intV 257],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "type/pop-shift-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "type/pop-divisor-second-non-int" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-shift-before-divisor-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-divisor-before-x-after-shift-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "error-order/range-before-divisor-type"
      #[.null, .cell Cell.empty, intV 257],
    mkInjectedCase "nan/shift-via-program"
      #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkInjectedCase "nan/divisor-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkInjectedCase "nan/x-via-program"
      #[IntVal.nan, IntVal.num 7, IntVal.num 1],
    mkInjectedCase "nan/all-via-program"
      #[IntVal.nan, IntVal.nan, IntVal.nan],
    mkInjectedCase "error-order/pushint-out-of-range-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 1, IntVal.num 1],
    mkInjectedCase "error-order/pushint-out-of-range-low-before-op"
      #[IntVal.num 1, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkInjectedCase "error-order/pushint-out-of-range-high-shift-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (maxInt257 + 1)],
    mkInjectedCase "error-order/pushint-out-of-range-low-shift-before-op"
      #[IntVal.num 1, IntVal.num 1, IntVal.num (minInt257 - 1)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num lshiftdivmodcSetGasExact), .tonEnvOp .setGasLimit, lshiftdivmodcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num lshiftdivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftdivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 700
      gen := genLShiftDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTDIVMODC
