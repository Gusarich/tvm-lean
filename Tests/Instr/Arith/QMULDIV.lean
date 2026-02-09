import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULDIV

/-
QMULDIV branch-map notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean` (`execInstrArithMulDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb7a98` + args4 decode to `.mulDivMod d roundMode addMode true`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean generic `.mulDivMod`: 7 branch sites / 16 terminal outcomes
  (dispatch arm; add-mode pop path; operand-shape split; divisor-zero split;
   round-mode validity split; `d` switch; non-num `d=3` split).
- C++ `exec_muldivmod`: 5 branch sites / 11 terminal outcomes
  (global-version add-remap gate; invalid-opcode guard; underflow guard;
   add/non-add path; `d` switch push shape).

QMULDIV specialization:
- opcode family `0xb7a98`, args4=`0x4`;
- fixed params: `d=1`, `roundMode=-1` (floor), `addMode=false`, `quiet=true`.

Key risk areas covered:
- floor quotient semantics for mixed signs and near-zero products;
- quiet funnels: division by zero, NaN operands, and quotient overflow -> NaN;
- pop/error ordering (`z`, then `y`, then `x`) and underflow-before-type behavior;
- NaN/out-of-range operand injection via prelude (`PUSHINT`) rather than `initStack`;
- exact gas cliff under `PUSHINT n; SETGASLIMIT; QMULDIV` (exact vs exact-minus-one).
-/

private def qmuldivId : InstrId := { name := "QMULDIV" }

private def qmuldivInstr : Instr := .mulDivMod 1 (-1) false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuldivInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmuldivId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qmuldivInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programTail) gasLimits fuel

private def runQmuldivDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuldivInstr stack

private def runQmuldivDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 8224)) stack

private def qmuldivSetGasExact : Int :=
  computeExactGasBudget qmuldivInstr

private def qmuldivSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuldivInstr

private def floorFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def floorDivisorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def classifyQmuldiv (x y z : Int) : String :=
  if z = 0 then
    "quiet-divzero"
  else
    let tmp : Int := x * y
    let (q, _) := divModRound tmp z (-1)
    if !intFitsSigned257 q then
      "quiet-overflow"
    else if tmp = 0 then
      "zero"
    else if tmp % z = 0 then
      "exact"
    else
      "inexact"

private def genQmuldivFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmuldiv x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmuldiv x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-signed" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmuldiv x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-boundary" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmuldiv x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-signed" #[intV x, intV y, intV z], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/quiet-divzero/random" #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool floorFactorPool rng1
      let (y, r3) := pickFromPool floorFactorPool r2
      let (z, r4) := pickFromPool floorDivisorPool r3
      let kind := classifyQmuldiv x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/small-sign-pool" #[intV x, intV y, intV z], r4)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow/min-times-neg-one-div-one"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow/max-times-max-div-one"
        #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/quiet-overflow/min-times-min-div-one"
        #[intV minInt257, intV minInt257, intV 1], rng1)
    else if shape = 9 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQmuldiv 0 y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQmuldiv x 0 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQmuldiv x y 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/div-by-one" #[intV x, intV y, intV 1], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyQmuldiv x y (-1)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/div-by-neg-one" #[intV x, intV y, intV (-1)], r3)
    else if shape = 13 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-ints" #[intV x, intV y], r3)
    else if shape = 16 then
      let (zLike, r2) := pickNonInt rng1
      (mkCase s!"/fuzz/shape-{shape}/type/pop-z-first" #[intV 1, intV 2, zLike], r2)
    else if shape = 17 then
      let (yLike, r2) := pickNonInt rng1
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second" #[intV 1, yLike, intV 2], r2)
    else if shape = 18 then
      let (xLike, r2) := pickNonInt rng1
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xLike, intV 1, intV 2], r2)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-z-via-program" #[.num x, .num y, .nan], r3)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program" #[.num x, .nan, .num z], r3)
    else if shape = 21 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program" #[.nan, .num y, .num z], r3)
    else
      let (variant, r2) := randNat rng1 0 3
      if variant = 0 then
        let (x, r3) := pickSigned257ish r2
        let (y, r4) := pickSigned257ish r3
        let (zHuge, r5) := pickInt257OutOfRange r4
        (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/range-z-via-program"
          #[.num x, .num y, .num zHuge], r5)
      else if variant = 1 then
        let (x, r3) := pickSigned257ish r2
        let (yHuge, r4) := pickInt257OutOfRange r3
        let (z, r5) := pickNonZeroInt r4
        (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/range-y-via-program"
          #[.num x, .num yHuge, .num z], r5)
      else if variant = 2 then
        let (xHuge, r3) := pickInt257OutOfRange r2
        let (y, r4) := pickSigned257ish r3
        let (z, r5) := pickNonZeroInt r4
        (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/range-x-via-program"
          #[.num xHuge, .num y, .num z], r5)
      else
        let (xHuge, r3) := pickInt257OutOfRange r2
        let (yHuge, r4) := pickInt257OutOfRange r3
        let (zHuge, r5) := pickInt257OutOfRange r4
        (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/range-all-via-program"
          #[.num xHuge, .num yHuge, .num zHuge], r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuldivId
  unit := #[
    { name := "/unit/ok/floor-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 2, 10),
            (-7, 3, 2, -11),
            (7, -3, 2, -11),
            (-7, -3, 2, 10),
            (5, 5, 2, 12),
            (-5, 5, 2, -13),
            (5, -5, 2, -13),
            (-5, -5, 2, 12),
            (-1, 1, 2, -1),
            (1, -1, 2, -1),
            (-1, -1, 2, 0),
            (0, 9, 5, 0),
            (9, 0, 5, 0),
            (42, 6, 7, 36),
            (-42, 6, 7, -36),
            (42, -6, 7, -36),
            (-42, -6, 7, 36)
          ]
        for c in checks do
          match c with
          | (x, y, z, q) =>
              expectOkStack s!"/unit/checks/{x}*{y}/{z}" (runQmuldivDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "/unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, maxInt257),
            (maxInt257, -1, 1, -maxInt257),
            (minInt257, 1, 1, minInt257),
            (minInt257, -1, -1, minInt257),
            (minInt257 + 1, -1, -1, -maxInt257),
            (maxInt257, 1, 2, (pow2 255) - 1),
            (maxInt257, -1, 2, -(pow2 255)),
            (minInt257, 1, 2, -(pow2 255)),
            (minInt257, 1, -2, pow2 255),
            (minInt257 + 1, -1, 2, (pow2 255) - 1)
          ]
        for c in checks do
          match c with
          | (x, y, z, q) =>
              expectOkStack s!"/unit/boundary/{x}*{y}/{z}" (runQmuldivDirect #[intV x, intV y, intV z]) #[intV q] }
    ,
    { name := "/unit/quiet/divzero-and-overflow-produce-nan"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-product-over-zero"
          (runQmuldivDirect #[intV 5, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/quiet/divzero/zero-product-over-zero"
          (runQmuldivDirect #[intV 0, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/quiet/overflow/min-times-neg-one-div-one"
          (runQmuldivDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan]
        expectOkStack "/unit/quiet/overflow/max-times-max-div-one"
          (runQmuldivDirect #[intV maxInt257, intV maxInt257, intV 1]) #[.int .nan]
        expectOkStack "/unit/quiet/overflow/min-times-min-div-one"
          (runQmuldivDirect #[intV minInt257, intV minInt257, intV 1]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/underflow/empty" (runQmuldivDirect #[]) .stkUnd
        expectErr "/unit/underflow/one-int-before-missing-y" (runQmuldivDirect #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-ints-before-missing-x" (runQmuldivDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/type/pop-z-first" (runQmuldivDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/type/pop-y-second" (runQmuldivDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/type/pop-x-third" (runQmuldivDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error-order/pop-z-before-y-when-both-non-int"
          (runQmuldivDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-after-z-int"
          (runQmuldivDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/dispatch/non-muldiv-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback" (runQmuldivDispatchFallback #[]) #[intV 8224] }
  ]
  oracle := #[
    mkCase "/ok/floor/sign/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "/ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "/ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "/ok/floor/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "/ok/floor/sign/neg-pos-near-zero" #[intV (-1), intV 1, intV 2],
    mkCase "/ok/floor/sign/pos-neg-near-zero" #[intV 1, intV (-1), intV 2],
    mkCase "/ok/floor/sign/neg-neg-near-zero" #[intV (-1), intV (-1), intV 2],
    mkCase "/ok/exact/pos-pos" #[intV 42, intV 6, intV 7],
    mkCase "/ok/exact/neg-pos" #[intV (-42), intV 6, intV 7],
    mkCase "/ok/exact/pos-neg" #[intV 42, intV (-6), intV 7],
    mkCase "/ok/exact/neg-neg" #[intV (-42), intV (-6), intV 7],
    mkCase "/ok/exact/zero-left-factor" #[intV 0, intV 17, intV 5],
    mkCase "/ok/exact/zero-right-factor" #[intV 17, intV 0, intV 5],
    mkCase "/ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-neg-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "/ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-times-neg-one-div-neg-one" #[intV minInt257, intV (-1), intV (-1)],
    mkCase "/ok/boundary/min-plus-one-times-neg-one-div-neg-one"
      #[intV (minInt257 + 1), intV (-1), intV (-1)],
    mkCase "/ok/boundary/max-times-one-div-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "/ok/boundary/max-times-neg-one-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "/ok/boundary/min-times-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "/ok/boundary/min-times-one-div-neg-two" #[intV minInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/min-plus-one-times-neg-one-div-two"
      #[intV (minInt257 + 1), intV (-1), intV 2],
    mkCase "/quiet/divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "/quiet/overflow/min-times-neg-one-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "/quiet/overflow/max-times-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "/quiet/overflow/max-times-max-div-neg-one" #[intV maxInt257, intV maxInt257, intV (-1)],
    mkCase "/quiet/overflow/min-times-min-div-one" #[intV minInt257, intV minInt257, intV 1],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-int-before-missing-y" #[intV 1],
    mkCase "/underflow/two-ints-before-missing-x" #[intV 1, intV 2],
    mkCase "/type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "/quiet/nan/z-via-program" #[.num 5, .num 7, .nan],
    mkCaseFromIntVals "/quiet/nan/y-via-program" #[.num 5, .nan, .num 7],
    mkCaseFromIntVals "/quiet/nan/x-via-program" #[.nan, .num 5, .num 7],
    mkCaseFromIntVals "/quiet/nan/all-via-program" #[.nan, .nan, .nan],
    mkCaseFromIntVals "/quiet/range/z-out-of-range-via-program"
      #[.num 5, .num 7, .num (maxInt257 + 1)],
    mkCaseFromIntVals "/quiet/range/y-out-of-range-via-program"
      #[.num 5, .num (minInt257 - 1), .num 7],
    mkCaseFromIntVals "/quiet/range/x-out-of-range-via-program"
      #[.num (pow2 257), .num 5, .num 7],
    mkCaseFromIntVals "/quiet/range/all-out-of-range-via-program"
      #[.num (maxInt257 + 1), .num (minInt257 - 1), .num (-(pow2 257))],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivSetGasExact), .tonEnvOp .setGasLimit, qmuldivInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmuldivSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuldivInstr]
  ]
  fuzz := #[
    { seed := 2026020826
      count := 750
      gen := genQmuldivFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULDIV
