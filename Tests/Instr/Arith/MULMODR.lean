import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODR

/-
MULMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`divModRound`, nearest mode `roundMode=0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xa98` + args4 decode to `.mulDivMod d roundMode addMode quiet`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, opcode wiring in `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean generic `.mulDivMod`: 7 branch sites / 16 terminal outcomes
  (dispatch arm; add-mode pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch; non-num `d==3` split).
- C++ `exec_muldivmod`: 5 branch sites / 11 terminal outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard;
   add/non-add pop path; `d` result-shape switch).

MULMODR specialization:
- opcode args4=`0x9` under `0xa98` family;
- fixed params: `d=2`, `roundMode=0` (nearest with tie-to-+∞),
  `addMode=false`, `quiet=false`.

Key risk areas covered:
- nearest-rounding remainder behavior for mixed signs and half ties;
- pop/type error ordering (`z`, then `y`, then `x`) with underflow precedence;
- non-quiet NaN funnel to `intOv` (NaN injected via program only);
- out-of-range numeric operand injection via program only, including
  large-input remainder overflow and large-input exact-success cases;
- deterministic gas boundary around `PUSHINT n; SETGASLIMIT; MULMODR`.
-/

private def mulmodrId : InstrId := { name := "MULMODR" }

private def mulmodrInstr : Instr := .mulDivMod 2 0 false false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulmodrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[mulmodrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runMulmodrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod mulmodrInstr stack

private def runMulmodrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 909)) stack

private def mulmodrSetGasExact : Int :=
  computeExactGasBudget mulmodrInstr

private def mulmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulmodrInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (value, rng1) := pickSigned257ish rng0
  (if value = 0 then 1 else value, rng1)

private def nearestFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def nearestDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def tieFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def tieDivisorPool : Array Int :=
  #[-2, 2]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def largeInputPos : Int := maxInt257 + 1

private def largeInputNeg : Int := minInt257 - 1

private def largeDivisorOutOfRange : Int := (pow2 257) + 1

private def classifyMulmodrCase (x y z : Int) : String :=
  if z = 0 then
    "divzero"
  else
    let (_, r) := divModRound (x * y) z 0
    if !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if Int.natAbs r * 2 = Int.natAbs z then
      "tie"
    else
      "inexact"

private def genMulmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyMulmodrCase x y z
      (mkCase s!"fuzz/shape-{shape}/{kind}" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyMulmodrCase x y z
      (mkCase s!"fuzz/shape-{shape}/{kind}" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/divzero" #[intV x, intV y, intV 0], r3)
    else if shape = 3 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      let (z, r4) := pickFromPool tieDivisorPool r3
      let kind := classifyMulmodrCase x y z
      (mkCase s!"fuzz/shape-{shape}/{kind}" #[intV x, intV y, intV z], r4)
    else if shape = 4 then
      let (x, r2) := pickFromPool nearestFactorPool rng1
      let (y, r3) := pickFromPool nearestFactorPool r2
      let (z, r4) := pickFromPool nearestDivisorPool r3
      let kind := classifyMulmodrCase x y z
      (mkCase s!"fuzz/shape-{shape}/{kind}" #[intV x, intV y, intV z], r4)
    else if shape = 5 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyMulmodrCase 0 y z
      (mkCase s!"fuzz/shape-{shape}/{kind}" #[intV 0, intV y, intV z], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyMulmodrCase x 0 z
      (mkCase s!"fuzz/shape-{shape}/{kind}" #[intV x, intV 0, intV z], r3)
    else if shape = 7 then
      let (zNeg, r2) := randBool rng1
      let z := if zNeg then (-2 : Int) else (2 : Int)
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/program-injected-large-input-exact"
          #[IntVal.num largeInputPos, IntVal.num 1, IntVal.num z], r2)
    else if shape = 8 then
      let (useNeg, r2) := randBool rng1
      let x := if useNeg then largeInputNeg else largeInputPos
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/program-injected-large-rem-overflow"
          #[IntVal.num x, IntVal.num 1, IntVal.num largeDivisorOutOfRange], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-z-via-program"
          #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-y-via-program"
          #[IntVal.num x, IntVal.nan, IntVal.num z], r3)
    else if shape = 11 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program"
          #[IntVal.nan, IntVal.num y, IntVal.num z], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-z-first" #[intV x, intV y, .null], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-y-second" #[intV x, .null, intV z], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/type-pop-x-third" #[.null, intV x, intV y], r3)
    else
      let (arity, r2) := randNat rng1 0 2
      if arity = 0 then
        (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], r2)
      else if arity = 1 then
        let (x, r3) := pickSigned257ish r2
        (mkCase s!"fuzz/shape-{shape}/underflow-one-arg" #[intV x], r3)
      else
        let (x, r3) := pickSigned257ish r2
        let (y, r4) := pickSigned257ish r3
        (mkCase s!"fuzz/shape-{shape}/underflow-two-args" #[intV x, intV y], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulmodrId
  unit := #[
    { name := "unit/ok/nearest-sign-tie-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, -1),
            (-7, 3, 2, -1),
            (7, -3, 2, -1),
            (-7, -3, 2, -1),
            (7, 3, -2, 1),
            (-7, 3, -2, 1),
            (1, 1, 2, -1),
            (-1, 1, 2, -1),
            (1, 1, -2, 1),
            (-1, 1, -2, 1),
            (42, 6, 7, 0),
            (0, 9, 5, 0),
            (9, 0, 5, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})%{z}" (runMulmodrDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, 0),
            (maxInt257, -1, 1, 0),
            (minInt257, 1, 1, 0),
            (minInt257, -1, -1, 0),
            (maxInt257, 1, 2, -1),
            (minInt257, 1, 2, 0),
            (minInt257, 1, -2, 0),
            (minInt257 + 1, -1, 2, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let z := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"({x}*{y})%{z}" (runMulmodrDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "unit/error/divzero-and-pop-ordering"
      run := do
        expectErr "divzero/nonzero-product-over-zero"
          (runMulmodrDirect #[intV 5, intV 7, intV 0]) .intOv
        expectErr "divzero/zero-product-over-zero"
          (runMulmodrDirect #[intV 0, intV 7, intV 0]) .intOv
        expectErr "underflow/empty" (runMulmodrDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runMulmodrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runMulmodrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/underflow-before-type-with-two-items"
          (runMulmodrDirect #[intV 1, .null]) .stkUnd
        expectErr "type/pop-z-first" (runMulmodrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-y-second" (runMulmodrDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-x-third" (runMulmodrDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "error-order/pop-z-before-y-when-both-non-int"
          (runMulmodrDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "error-order/pop-y-before-x-after-z-int"
          (runMulmodrDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulmodrDispatchFallback #[]) #[intV 909] }
  ]
  oracle := #[
    mkCaseFromIntVals "ok/round/pos-pos-inexact" #[IntVal.num 7, IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "ok/round/neg-pos-inexact" #[IntVal.num (-7), IntVal.num 3, IntVal.num 2],
    mkCaseFromIntVals "ok/round/pos-neg-inexact" #[IntVal.num 7, IntVal.num (-3), IntVal.num 2],
    mkCaseFromIntVals "ok/round/neg-neg-inexact" #[IntVal.num (-7), IntVal.num (-3), IntVal.num 2],
    mkCaseFromIntVals "ok/round/pos-pos-negdivisor" #[IntVal.num 7, IntVal.num 3, IntVal.num (-2)],
    mkCaseFromIntVals "ok/round/neg-pos-negdivisor" #[IntVal.num (-7), IntVal.num 3, IntVal.num (-2)],
    mkCaseFromIntVals "ok/tie/one-over-two" #[IntVal.num 1, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/tie/neg-one-over-two" #[IntVal.num (-1), IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/tie/one-over-neg-two" #[IntVal.num 1, IntVal.num 1, IntVal.num (-2)],
    mkCaseFromIntVals "ok/tie/neg-one-over-neg-two" #[IntVal.num (-1), IntVal.num 1, IntVal.num (-2)],
    mkCaseFromIntVals "ok/exact/pos-pos" #[IntVal.num 42, IntVal.num 6, IntVal.num 7],
    mkCaseFromIntVals "ok/exact/neg-pos" #[IntVal.num (-42), IntVal.num 6, IntVal.num 7],
    mkCaseFromIntVals "ok/exact/pos-neg" #[IntVal.num 42, IntVal.num (-6), IntVal.num 7],
    mkCaseFromIntVals "ok/exact/zero-left-factor" #[IntVal.num 0, IntVal.num 17, IntVal.num 5],
    mkCaseFromIntVals "ok/exact/zero-right-factor" #[IntVal.num 17, IntVal.num 0, IntVal.num 5],
    mkCaseFromIntVals "ok/boundary/max-times-one-mod-one" #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/boundary/max-times-neg-one-mod-one" #[IntVal.num maxInt257, IntVal.num (-1), IntVal.num 1],
    mkCaseFromIntVals "ok/boundary/min-times-one-mod-one" #[IntVal.num minInt257, IntVal.num 1, IntVal.num 1],
    mkCaseFromIntVals "ok/boundary/min-times-neg-one-mod-neg-one"
      #[IntVal.num minInt257, IntVal.num (-1), IntVal.num (-1)],
    mkCaseFromIntVals "ok/boundary/max-times-one-mod-two"
      #[IntVal.num maxInt257, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/boundary/min-times-one-mod-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/boundary/min-times-one-mod-neg-two"
      #[IntVal.num minInt257, IntVal.num 1, IntVal.num (-2)],
    mkCaseFromIntVals "ok/boundary/min-plus-one-negated-mod-two"
      #[IntVal.num (minInt257 + 1), IntVal.num (-1), IntVal.num 2],
    mkCaseFromIntVals "ok/program-injected/large-inputs-exact-zero-rem"
      #[IntVal.num largeInputPos, IntVal.num 1, IntVal.num 2],
    mkCaseFromIntVals "ok/program-injected/large-inputs-exact-zero-rem-negdivisor"
      #[IntVal.num largeInputPos, IntVal.num 1, IntVal.num (-2)],
    mkCaseFromIntVals "divzero/nonzero-product-over-zero"
      #[IntVal.num 5, IntVal.num 7, IntVal.num 0],
    mkCaseFromIntVals "divzero/zero-product-over-zero"
      #[IntVal.num 0, IntVal.num 7, IntVal.num 0],
    mkCaseFromIntVals "overflow/program-injected/large-rem-overflow-pos-input"
      #[IntVal.num largeInputPos, IntVal.num 1, IntVal.num largeDivisorOutOfRange],
    mkCaseFromIntVals "overflow/program-injected/large-rem-overflow-neg-input"
      #[IntVal.num largeInputNeg, IntVal.num 1, IntVal.num largeDivisorOutOfRange],
    mkCaseFromIntVals "nan/z-via-program"
      #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "nan/y-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkCaseFromIntVals "nan/x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-items" #[intV 1, .null],
    mkCase "type/pop-z-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-z-before-y-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-y-before-x-after-z-int" #[.null, .cell Cell.empty, intV 1],
    mkCase "gas/exact-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodrSetGasExact), .tonEnvOp .setGasLimit, mulmodrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulmodrInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genMulmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODR
