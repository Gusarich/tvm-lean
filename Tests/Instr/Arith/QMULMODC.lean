import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULMODC

/-
QMULMODC branch-mapping notes (Lean + C++ reviewed sources):

- Lean reviewed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
    (`execInstrArithMulDivMod`, specialization `.mulDivMod 2 1 false true`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode family `0xb7a98 + args4`, with QMULMODC at args4=`0xA`)
- C++ reviewed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean generic `.mulDivMod`: 7 branch sites / 16 terminal outcomes.
- C++ `exec_muldivmod`: 5 branch sites / 11 terminal outcomes.
- QMULMODC reachable subset: 7 branch sites / 8 reachable outcomes
  (`ok`, `stkUnd`, `typeChk` at pop-`z`/`y`/`x`, quiet-NaN from divzero,
   quiet-NaN from non-num input, quiet-NaN from remainder push range failure).

Key risk areas covered:
- ceil-remainder sign semantics for mixed-sign products and negative divisors;
- quiet NaN funnels for divzero, NaN operands, and out-of-range remainder pushes;
- strict pop and error ordering (`z` then `y` then `x`, underflow before type when <3);
- oracle serialization hygiene (NaN/out-of-range inputs injected via prelude only);
- deterministic gas cliff via exact / exact-minus-one
  `PUSHINT n; SETGASLIMIT; QMULMODC`.
-/

private def qmulmodcId : InstrId := { name := "QMULMODC" }

private def qmulmodcInstr : Instr := .mulDivMod 2 1 false true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programTail : Array Instr := #[qmulmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programTail) gasLimits fuel

private def runQmulmodcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmulmodcInstr stack

private def runQmulmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 4210)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def qmulmodcSetGasExact : Int :=
  computeExactGasBudget qmulmodcInstr

private def qmulmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def ceilFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def ceilDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def classifyQmulmodc (x y z : Int) : String :=
  if z = 0 then
    "quiet/divzero"
  else
    let (_, r) := divModRound (x * y) z 1
    if !intFitsSigned257 r then
      "quiet/overflow"
    else if r = 0 then
      "ok/exact"
    else
      "ok/inexact"

private def genQmulmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 25
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmulmodc x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-x" #[intV x, intV y, intV z], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmulmodc x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-y" #[intV x, intV y, intV z], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let kind := classifyQmulmodc x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/random" #[intV x, intV y, intV z], r4)
    else if shape = 3 then
      let (x, r2) := pickFromPool ceilFactorPool rng1
      let (y, r3) := pickFromPool ceilFactorPool r2
      let (z, r4) := pickFromPool ceilDivisorPool r3
      let kind := classifyQmulmodc x y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/small-sign-pool" #[intV x, intV y, intV z], r4)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero/boundary" #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero/random" #[intV x, intV y, intV 0], r3)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/ok/exact/huge-quotient-max-max" #[intV maxInt257, intV maxInt257, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/ok/exact/huge-quotient-min-neg-one" #[intV minInt257, intV 1, intV (-1)], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/ok/exact/huge-quotient-min-plus-one" #[intV (minInt257 + 1), intV (-1), intV 1], rng1)
    else if shape = 9 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQmulmodc 0 y z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-left-factor" #[intV 0, intV y, intV z], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      let kind := classifyQmulmodc x 0 z
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-right-factor" #[intV x, intV 0, intV z], r3)
    else if shape = 11 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zLike, r4) := pickNonIntLike r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-z-first" #[intV x, intV y, zLike], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second" #[intV x, yLike, intV z], r4)
    else if shape = 16 then
      let (xLike, r2) := pickNonIntLike rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xLike, intV y, intV z], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      let (zLike, r4) := pickNonIntLike r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-z-before-y-when-both-non-int"
        #[intV x, yLike, zLike], r4)
    else if shape = 18 then
      let (xLike, r2) := pickNonIntLike rng1
      let (yLike, r3) := pickNonIntLike r2
      let (z, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-after-z-int"
        #[xLike, yLike, intV z], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonIntLike r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/type-before-divzero-funnel"
        #[intV x, yLike, intV 0], r3)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[.num x, .num y, .nan], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[.num x, .nan, .num z], r3)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      let (z, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[.nan, .num y, .num z], r3)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (zOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-range-z-before-op"
        #[.num x, .num y, .num zOut], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-range-y-before-op"
        #[.num x, .num yOut, .num z], r4)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-range-x-before-op"
        #[.num xOut, .num y, .num z], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulmodcId
  unit := #[
    { name := "/unit/direct/ceil-mod-sign-and-exactness"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 5, -4),
            (-7, 3, 5, -1),
            (7, -3, 5, -1),
            (-7, -3, 5, -4),
            (-1, 1, 2, -1),
            (1, -1, 2, -1),
            (-1, -1, -2, 1),
            (1, 1, -2, 1),
            (6, 7, 3, 0),
            (5, -7, 3, -2),
            (-5, 7, -3, 1),
            (0, 9, 5, 0),
            (9, 0, -5, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"/unit/direct/ceil/{x}/{y}/{z}"
                (runQmulmodcDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-and-huge-quotient-remainder"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 1, 0),
            (maxInt257, 1, -1, 0),
            (minInt257, 1, 1, 0),
            (minInt257, 1, -1, 0),
            (maxInt257, 1, 2, -1),
            (maxInt257, 1, -2, 1),
            (minInt257 + 1, 1, 2, -1),
            (minInt257 + 1, 1, -2, 1),
            (maxInt257, maxInt257, 1, 0),
            (minInt257, minInt257, 1, 0),
            (0, maxInt257, -1, 0)
          ]
        for c in checks do
          match c with
          | (x, y, z, expected) =>
              expectOkStack s!"/unit/direct/boundary/{x}/{y}/{z}"
                (runQmulmodcDirect #[intV x, intV y, intV z]) #[intV expected] }
    ,
    { name := "/unit/direct/quiet-funnels-divzero-nan-and-range-overflow"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQmulmodcDirect #[intV 5, intV 7, intV 0]) #[.int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQmulmodcDirect #[intV 0, intV 0, intV 0]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-z"
          (runQmulmodcDirect #[intV 5, intV 7, .int .nan]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQmulmodcDirect #[intV 5, .int .nan, intV 3]) #[.int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQmulmodcDirect #[.int .nan, intV 5, intV 3]) #[.int .nan]
        expectOkStack "/unit/quiet/range-overflow-remainder-from-large-divisor"
          (runQmulmodcDirect #[intV 5, intV 7, intV (pow2 257)]) #[.int .nan]
        expectOkStack "/unit/quiet/range-overflow-remainder-from-large-x"
          (runQmulmodcDirect #[intV (maxInt257 + 1), intV 1, intV (-(pow2 257))]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-type-and-pop-sequencing"
      run := do
        expectErr "/unit/underflow/empty"
          (runQmulmodcDirect #[]) .stkUnd
        expectErr "/unit/underflow/one-arg"
          (runQmulmodcDirect #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-args"
          (runQmulmodcDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-with-two-non-int"
          (runQmulmodcDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/type/pop-z-first"
          (runQmulmodcDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/type/pop-y-second"
          (runQmulmodcDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/type/pop-x-third"
          (runQmulmodcDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error-order/pop-z-before-y-when-both-non-int"
          (runQmulmodcDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-after-z-int"
          (runQmulmodcDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "/unit/error-order/type-before-divzero-funnel"
          (runQmulmodcDirect #[intV 5, .null, intV 0]) .typeChk }
    ,
    { name := "/unit/direct/pop-order-top-three-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-null"
          (runQmulmodcDirect #[.null, intV 3, intV 4, intV 5]) #[.null, intV (-3)]
        expectOkStack "/unit/pop-order/below-cell-quiet-overflow"
          (runQmulmodcDirect #[.cell Cell.empty, intV (maxInt257 + 1), intV 1, intV (-(pow2 257))])
          #[.cell Cell.empty, .int .nan] }
    ,
    { name := "/unit/opcode/decode-qmulmodc-sequence"
      run := do
        let program : Array Instr := #[qmulmodcInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/qmulmodc" s0 qmulmodcInstr 24
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end-expected-exhausted-got-{s2.bitsRemaining}") }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmulmodcDispatchFallback #[]) #[intV 4210] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 3, intV 5],
    mkCase "/ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV 3, intV 5],
    mkCase "/ok/ceil/sign/pos-neg-inexact" #[intV 7, intV (-3), intV 5],
    mkCase "/ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-3), intV 5],
    mkCase "/ok/ceil/sign/neg-pos-near-zero" #[intV (-1), intV 1, intV 2],
    mkCase "/ok/ceil/sign/pos-neg-near-zero" #[intV 1, intV (-1), intV 2],
    mkCase "/ok/ceil/sign/neg-neg-divisor-near-zero" #[intV (-1), intV (-1), intV (-2)],
    mkCase "/ok/ceil/sign/pos-pos-neg-divisor-near-zero" #[intV 1, intV 1, intV (-2)],
    mkCase "/ok/exact/positive-product" #[intV 6, intV 7, intV 3],
    mkCase "/ok/exact/negative-product" #[intV (-6), intV 7, intV 3],
    mkCase "/ok/exact/zero-left-factor" #[intV 0, intV 33, intV 7],
    mkCase "/ok/exact/zero-right-factor" #[intV 33, intV 0, intV (-7)],
    mkCase "/ok/boundary/max-times-one-mod-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-one-mod-neg-one" #[intV maxInt257, intV 1, intV (-1)],
    mkCase "/ok/boundary/min-times-one-mod-one" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-times-one-mod-neg-one" #[intV minInt257, intV 1, intV (-1)],
    mkCase "/ok/boundary/max-times-one-mod-two" #[intV maxInt257, intV 1, intV 2],
    mkCase "/ok/boundary/max-times-one-mod-neg-two" #[intV maxInt257, intV 1, intV (-2)],
    mkCase "/ok/boundary/min-plus-one-mod-two" #[intV (minInt257 + 1), intV 1, intV 2],
    mkCase "/ok/boundary/min-plus-one-mod-neg-two" #[intV (minInt257 + 1), intV 1, intV (-2)],
    mkCase "/ok/boundary/huge-quotient-max-max-remains-zero" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "/ok/boundary/huge-quotient-min-min-remains-zero" #[intV minInt257, intV minInt257, intV 1],
    mkCase "/ok/boundary/huge-quotient-min-neg-one-remains-zero" #[intV minInt257, intV 1, intV (-1)],
    mkCase "/quiet/divzero/nonzero-product-over-zero" #[intV 5, intV 7, intV 0],
    mkCase "/quiet/divzero/zero-product-over-zero" #[intV 0, intV 7, intV 0],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-type-with-two-non-int" #[.null, .cell Cell.empty],
    mkCase "/type/pop-z-first-top-non-int" #[intV 1, intV 2, .null],
    mkCase "/type/pop-y-second-non-int" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third-non-int" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-z-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-z-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/type-before-divzero-funnel" #[intV 5, .null, intV 0],
    mkCaseFromIntVals "/quiet/nan/z-via-program" #[.num 5, .num 7, .nan],
    mkCaseFromIntVals "/quiet/nan/y-via-program" #[.num 5, .nan, .num 7],
    mkCaseFromIntVals "/quiet/nan/x-via-program" #[.nan, .num 5, .num 7],
    mkCaseFromIntVals "/quiet/range/z-out-of-range-via-program" #[.num 5, .num 7, .num (pow2 257)],
    mkCaseFromIntVals "/quiet/range/y-out-of-range-via-program" #[.num 5, .num (minInt257 - 1), .num 7],
    mkCaseFromIntVals "/quiet/range/x-out-of-range-via-program" #[.num (-(pow2 257)), .num 5, .num 7],
    mkCaseFromIntVals "/error-order/pushint-range-all-before-op"
      #[.num (maxInt257 + 1), .num (minInt257 - 1), .num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodcSetGasExact), .tonEnvOp .setGasLimit, qmulmodcInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020864
      count := 700
      gen := genQmulmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULMODC
