import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QDIVC

/-
QDIVC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type/quiet-NaN paths)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `dump_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean: 6 branch sites / 14 terminal outcomes in `execInstrArithDivMod`
  (dispatch arm; arity split; operand-shape split; divisor-zero split;
   round-mode validation split; `d` switch with `d=3` non-num split).
- C++: 4 branch sites / 10 aligned outcomes in `exec_divmod`
  (opcode remap/guard; stack-underflow guard; add-vs-non-add path; `d` switch).

QDIVC specialization:
- opcode `args4 = 0x6` in the `0xb7a90` quiet DIV/MOD family;
- fixed parameters are `d=1`, `roundMode=1` (ceil), `addMode=false`, `quiet=true`.

Key risk areas covered:
- ceil rounding across sign combinations and near-zero fractions;
- zero-divisor/NaN/overflow funnels in quiet mode (must push NaN, not throw);
- pop-order and error-ordering (`y` before `x`, underflow before type on short stacks);
- deterministic gas edge via `PUSHINT n; SETGASLIMIT; QDIVC`;
- NaN and out-of-range inputs injected via program (serialization-safe oracle cases).
-/

private def qdivcId : InstrId := { name := "QDIVC" }

private def qdivcInstr : Instr := .divMod 1 1 false true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qdivcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qdivcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qdivcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programTail) gasLimits fuel

private def runQdivcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qdivcInstr stack

private def runQdivcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 2904)) stack

private def qdivcSetGasExact : Int :=
  computeExactGasBudget qdivcInstr

private def qdivcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qdivcInstr

private def ceilNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def ceilDenominatorPool : Array Int :=
  #[-4, -3, -2, -1, 1, 2, 3, 4]

private def qdivcOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickQdivcOutOfRange (rng : StdGen) : Int × StdGen :=
  pickFromPool qdivcOutOfRangePool rng

private def genQdivcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-nonzero" #[intV x, intV y], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-nonzero" #[intV x, intV y], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/quiet/divzero" #[intV x, intV 0], r2)
    else if shape = 3 then
      let (x, r2) := pickFromPool ceilNumeratorPool rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      (mkCase s!"fuzz/shape-{shape}/ok/ceil-pools" #[intV x, intV y], r3)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-min-div-neg-one"
        #[intV minInt257, intV (-1)], rng1)
    else if shape = 5 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-div-pools" #[intV x, intV y], r3)
    else if shape = 6 then
      let (x, r2) := pickFromPool ceilNumeratorPool rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/ok/ceil-numerators" #[intV x, intV y], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickFromPool ceilDenominatorPool r2
      (mkCase s!"fuzz/shape-{shape}/ok/signed-vs-pool-divisor" #[intV x, intV y], r3)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/ok/zero-over-neg-one" #[intV 0, intV (-1)], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/ok/max-div-one" #[intV maxInt257, intV 1], rng1)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-first" #[intV x, .null], r2)
    else if shape = 13 then
      let (y, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-second" #[.null, intV y], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[.num x, .nan], r2)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num y], r2)
    else if shape = 16 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program"
        #[.nan, .nan], rng1)
    else if shape = 17 then
      let (x, r2) := pickQdivcOutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/range-x-before-op"
        #[.num x, .num y], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickQdivcOutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/range-y-before-op"
        #[.num x, .num y], r3)
    else
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/overflow-pushint-high-x-via-program"
        #[.num (maxInt257 + 1), .num 1], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qdivcId
  unit := #[
    { name := "unit/ceil/sign-combos-and-near-zero-fractions"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 3, 3),
            (-7, 3, -2),
            (7, -3, -2),
            (-7, -3, 3),
            (-1, 2, 0),
            (1, -2, 0),
            (5, 2, 3),
            (-5, 2, -2),
            (5, -2, -2),
            (-5, -2, 3),
            (42, 7, 6),
            (-42, 7, -6),
            (42, -7, -6),
            (-42, -7, 6)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"ok/{x}/{y}" (runQdivcDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/ceil/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257),
            (maxInt257, -1, -maxInt257),
            (minInt257, 1, minInt257),
            (minInt257 + 1, -1, maxInt257),
            (maxInt257, 2, pow2 255),
            (minInt257, 2, -(pow2 255)),
            (minInt257, -2, pow2 255),
            (0, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"ok/{x}/{y}" (runQdivcDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/quiet/divzero-nan-and-overflow-push-nan"
      run := do
        expectOkStack "quiet/div-by-zero" (runQdivcDirect #[intV 5, intV 0]) #[.int .nan]
        expectOkStack "quiet/min-div-neg-one" (runQdivcDirect #[intV minInt257, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/nan-as-y" (runQdivcDirect #[intV 5, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan-as-x" (runQdivcDirect #[.int .nan, intV 5]) #[.int .nan]
        expectOkStack "quiet/out-of-range-x" (runQdivcDirect #[intV (maxInt257 + 1), intV 1]) #[.int .nan] }
    ,
    { name := "unit/error-order/pop-order-and-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runQdivcDirect #[]) .stkUnd
        expectErr "underflow/missing-x-after-y-pop" (runQdivcDirect #[intV 1]) .stkUnd
        expectErr "error-order/single-non-int-underflow-first" (runQdivcDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQdivcDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQdivcDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-pop-y-first" (runQdivcDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQdivcDispatchFallback #[]) #[intV 2904] }
  ]
  oracle := #[
    mkCase "ceil/sign/pos-pos-inexact" #[intV 7, intV 3],
    mkCase "ceil/sign/neg-pos-inexact" #[intV (-7), intV 3],
    mkCase "ceil/sign/pos-neg-inexact" #[intV 7, intV (-3)],
    mkCase "ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3)],
    mkCase "ceil/sign/neg-pos-near-zero" #[intV (-1), intV 2],
    mkCase "ceil/sign/pos-neg-near-zero" #[intV 1, intV (-2)],
    mkCase "ceil/sign/pos-pos-half" #[intV 5, intV 2],
    mkCase "ceil/sign/neg-neg-half" #[intV (-5), intV (-2)],
    mkCase "ceil/exact/pos-pos" #[intV 42, intV 7],
    mkCase "ceil/exact/neg-pos" #[intV (-42), intV 7],
    mkCase "ceil/exact/pos-neg" #[intV 42, intV (-7)],
    mkCase "ceil/exact/neg-neg" #[intV (-42), intV (-7)],
    mkCase "ceil/exact/zero-numerator" #[intV 0, intV (-5)],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0],
    mkCase "quiet/overflow/min-div-neg-one" #[intV minInt257, intV (-1)],
    mkCase "boundary/max-div-one" #[intV maxInt257, intV 1],
    mkCase "boundary/max-div-neg-one" #[intV maxInt257, intV (-1)],
    mkCase "boundary/min-div-one" #[intV minInt257, intV 1],
    mkCase "boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV (-1)],
    mkCase "boundary/max-div-two" #[intV maxInt257, intV 2],
    mkCase "boundary/min-div-two" #[intV minInt257, intV 2],
    mkCaseFromIntVals "quiet/overflow/x-from-pushint-high-via-program"
      #[.num (maxInt257 + 1), .num 1],
    mkCaseFromIntVals "quiet/nan/y-via-program" #[.num 5, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program" #[.nan, .num 5],
    mkCaseFromIntVals "quiet/nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-out-of-range-high-before-op"
      #[.num (maxInt257 + 1), .num 7],
    mkCaseFromIntVals "error-order/pushint-out-of-range-low-before-op"
      #[.num 7, .num (minInt257 - 1)],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/error-order-both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num qdivcSetGasExact), .tonEnvOp .setGasLimit, qdivcInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num qdivcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qdivcInstr]
  ]
  fuzz := #[
    { seed := 2026020831
      count := 700
      gen := genQdivcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QDIVC
