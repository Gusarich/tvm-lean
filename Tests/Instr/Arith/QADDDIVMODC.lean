import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADDDIVMODC

/-
QADDDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/DivMod.lean`
    (`execInstrArithDivMod`, specialization `.divMod 3 1 true true`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, mode `1` / ceil)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet 24-bit decode `0xb7a90 + args4`, `args4=0x2` for `QADDDIVMODC`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet encode path for `.divMod ... quiet=true`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_divmod`, `dump_divmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (generic `.divMod`): 6 branch sites / 14 terminal outcomes.
- Lean (QADDDIVMODC specialization): 7 branch sites / 8 reachable terminal outcomes
  (dispatch fallthrough, `stkUnd`, `typeChk` at `y/w/x`, quiet `(nan,nan)`,
   quiet `(nan,r)`, finite `(q,r)`).
- C++ (`exec_divmod` quiet add-mode path): 5 branch sites / 9 terminal outcomes.

Key risk areas covered:
- ceil quotient/remainder sign behavior for additive numerator `(x + w)` and mixed signs;
- strict pop/error ordering in add mode (`y`, then `w`, then `x`);
- quiet funnels for divisor-zero and non-numeric operands to `(nan, nan)`;
- quiet overflow shape where quotient becomes `nan` and remainder is preserved;
- oracle serialization hygiene (NaN / out-of-range operands injected via `PUSHINT`);
- deterministic gas cliff via exact / exact-minus-one `SETGASLIMIT`.
-/

private def qadddivmodcId : InstrId := { name := "QADDDIVMODC" }

private def qadddivmodcInstr : Instr := .divMod 3 1 true true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qadddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qadddivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qadddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQAddDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithDivMod qadddivmodcInstr stack

private def runQAddDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithDivMod .add (VM.push (intV 4242)) stack

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

private def qadddivmodcSetGasExact : Int :=
  computeExactGasBudget qadddivmodcInstr

private def qadddivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qadddivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def ceilNumeratorPool : Array Int :=
  #[-11, -9, -7, -5, -1, 0, 1, 5, 7, 9, 11]

private def ceilAddendPool : Array Int :=
  #[-4, -3, -2, -1, 0, 1, 2, 3, 4]

private def ceilDenominatorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def classifyQAddDivModC (x w y : Int) : String :=
  if y = 0 then
    "quiet/divzero"
  else
    let numer : Int := x + w
    let (q, r) := divModRound numer y 1
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet/overflow"
    else if r = 0 then
      "ok/exact"
    else
      "ok/inexact"

private def mkFiniteFuzzCase (shape : Nat) (x w y : Int) : OracleCase :=
  let kind := classifyQAddDivModC x w y
  mkCase s!"/fuzz/shape-{shape}/{kind}" #[intV x, intV w, intV y]

private def genQAddDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      (mkFiniteFuzzCase shape x w y, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkFiniteFuzzCase shape x w y, r4)
    else if shape = 2 then
      let (x, r2) := pickFromPool ceilNumeratorPool rng1
      let (w, r3) := pickFromPool ceilAddendPool r2
      let (y, r4) := pickFromPool ceilDenominatorPool r3
      (mkFiniteFuzzCase shape x w y, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkFiniteFuzzCase shape x w 0, r3)
    else if shape = 4 then
      (mkFiniteFuzzCase shape minInt257 0 (-1), rng1)
    else if shape = 5 then
      (mkFiniteFuzzCase shape maxInt257 1 1, rng1)
    else if shape = 6 then
      (mkFiniteFuzzCase shape minInt257 (-1) 1, rng1)
    else if shape = 7 then
      (mkFiniteFuzzCase shape maxInt257 maxInt257 1, rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV w], r3)
    else if shape = 11 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-with-two-items"
        #[.null, .cell Cell.empty], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-first" #[intV x, intV w, yLike], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-w-second" #[intV x, wLike, intV y], r4)
    else if shape = 14 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third" #[xLike, intV w, intV y], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (wLike, r3) := pickNonInt r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-w-when-both-non-int"
        #[intV x, wLike, yLike], r4)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      let (wLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-x-when-y-int"
        #[xLike, wLike, intV y], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.num w, IntVal.nan], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-w-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num y], r3)
    else if shape = 19 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num w, IntVal.num y], r3)
    else if shape = 20 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xOut, IntVal.num w, IntVal.num y], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        #[IntVal.num x, IntVal.num wOut, IntVal.num y], r4)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num yOut], r4)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (yOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        #[IntVal.num xOut, IntVal.num wOut, IntVal.num yOut], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qadddivmodcId
  unit := #[
    { name := "/unit/direct/ceil-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 1, 3, 3, -1),
            (-7, -1, 3, -2, -2),
            (7, 1, -3, -2, 2),
            (-7, -1, -3, 3, 1),
            (-1, 0, 2, 0, -1),
            (1, 0, -2, 0, 1),
            (5, -7, 3, 0, -2),
            (-5, 7, -3, 0, 2),
            (40, 2, 7, 6, 0),
            (-40, -2, 7, -6, 0),
            (4, 1, 2, 3, -1),
            (0, 0, 5, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, w, y, q, r) =>
              expectOkStack s!"/unit/direct/ceil/x={x}/w={w}/y={y}"
                (runQAddDivModCDirect #[intV x, intV w, intV y])
                #[intV q, intV r] }
    ,
    { name := "/unit/direct/boundary-successes-and-quiet-overflow-shapes"
      run := do
        let checks : Array (Int × Int × Int × Value × Value) :=
          #[
            (maxInt257, 0, 1, intV maxInt257, intV 0),
            (minInt257, 0, 1, intV minInt257, intV 0),
            (minInt257 + 1, 0, -1, intV maxInt257, intV 0),
            (maxInt257, -1, 1, intV (maxInt257 - 1), intV 0),
            (minInt257, 1, 2, intV (1 - (pow2 255)), intV (-1)),
            (maxInt257, -1, 2, intV ((pow2 255) - 1), intV 0),
            (minInt257, 0, -1, .int .nan, intV 0),
            (maxInt257, 1, 1, .int .nan, intV 0),
            (maxInt257, maxInt257, 1, .int .nan, intV 0)
          ]
        for c in checks do
          match c with
          | (x, w, y, q, r) =>
              expectOkStack s!"/unit/direct/boundary/x={x}/w={w}/y={y}"
                (runQAddDivModCDirect #[intV x, intV w, intV y])
                #[q, r] }
    ,
    { name := "/unit/quiet/funnels-divzero-and-nan-to-nan-pairs"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQAddDivModCDirect #[intV 5, intV 1, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQAddDivModCDirect #[intV 0, intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQAddDivModCDirect #[intV 5, intV 1, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-w"
          (runQAddDivModCDirect #[intV 5, .int .nan, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQAddDivModCDirect #[.int .nan, intV 1, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/below-stack-preserved"
          (runQAddDivModCDirect #[.null, intV 7, intV 1, intV 3]) #[.null, intV 3, intV (-1)] }
    ,
    { name := "/unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "/unit/underflow/empty" (runQAddDivModCDirect #[]) .stkUnd
        expectErr "/unit/underflow/one-arg" (runQAddDivModCDirect #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-args" (runQAddDivModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-with-two-items"
          (runQAddDivModCDirect #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/type/pop-y-first"
          (runQAddDivModCDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/type/pop-w-second"
          (runQAddDivModCDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/type/pop-x-third"
          (runQAddDivModCDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error-order/pop-y-before-w-when-both-non-int"
          (runQAddDivModCDirect #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-w-before-x-when-y-int"
          (runQAddDivModCDirect #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/direct/pop-order-top-three-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-cell-finite"
          (runQAddDivModCDirect #[.cell Cell.empty, intV 5, intV (-7), intV 3])
          #[.cell Cell.empty, intV 0, intV (-2)]
        expectOkStack "/unit/pop-order/below-null-overflow-q-nan-r-preserved"
          (runQAddDivModCDirect #[.null, intV maxInt257, intV 1, intV 1])
          #[.null, .int .nan, intV 0] }
    ,
    { name := "/unit/opcode/decode-qadddivmodc-sequence"
      run := do
        let program : Array Instr := #[qadddivmodcInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/qadddivmodc" s0 qadddivmodcInstr 24
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end-expected-exhausted-got-{s2.bitsRemaining}") }
    ,
    { name := "/unit/dispatch/non-divmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQAddDivModCDispatchFallback #[]) #[intV 4242] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign/pos-pos-inexact" #[intV 7, intV 1, intV 3],
    mkCase "/ok/ceil/sign/neg-pos-inexact" #[intV (-7), intV (-1), intV 3],
    mkCase "/ok/ceil/sign/pos-neg-inexact" #[intV 7, intV 1, intV (-3)],
    mkCase "/ok/ceil/sign/neg-neg-inexact" #[intV (-7), intV (-1), intV (-3)],
    mkCase "/ok/ceil/near-zero/neg-pos" #[intV (-1), intV 0, intV 2],
    mkCase "/ok/ceil/near-zero/pos-neg" #[intV 1, intV 0, intV (-2)],
    mkCase "/ok/ceil/addend/negative-total" #[intV 5, intV (-7), intV 3],
    mkCase "/ok/ceil/addend/positive-total-neg-divisor" #[intV (-5), intV 7, intV (-3)],
    mkCase "/ok/exact/positive" #[intV 40, intV 2, intV 7],
    mkCase "/ok/exact/negative" #[intV (-40), intV (-2), intV 7],
    mkCase "/ok/exact/zero-total" #[intV 5, intV (-5), intV 3],
    mkCase "/ok/boundary/max-plus-zero-div-one" #[intV maxInt257, intV 0, intV 1],
    mkCase "/ok/boundary/min-plus-zero-div-one" #[intV minInt257, intV 0, intV 1],
    mkCase "/ok/boundary/min-plus-one-div-neg-one" #[intV (minInt257 + 1), intV 0, intV (-1)],
    mkCase "/ok/boundary/max-minus-one-div-one" #[intV maxInt257, intV (-1), intV 1],
    mkCase "/ok/boundary/min-plus-one-div-two" #[intV minInt257, intV 1, intV 2],
    mkCase "/ok/boundary/max-minus-one-div-two" #[intV maxInt257, intV (-1), intV 2],
    mkCase "/ok/boundary/max-div-neg-two" #[intV maxInt257, intV 0, intV (-2)],
    mkCase "/ok/boundary/min-div-neg-two" #[intV minInt257, intV 0, intV (-2)],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 5, intV 1, intV 0],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0],
    mkCase "/quiet/overflow/min-plus-zero-div-neg-one" #[intV minInt257, intV 0, intV (-1)],
    mkCase "/quiet/overflow/max-plus-one-div-one" #[intV maxInt257, intV 1, intV 1],
    mkCase "/quiet/overflow/min-minus-one-div-one" #[intV minInt257, intV (-1), intV 1],
    mkCase "/quiet/overflow/max-plus-max-div-one" #[intV maxInt257, intV maxInt257, intV 1],
    mkCaseFromIntVals "/quiet/nan-y-via-program"
      #[IntVal.num 5, IntVal.num 7, IntVal.nan],
    mkCaseFromIntVals "/quiet/nan-w-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 7],
    mkCaseFromIntVals "/quiet/nan-x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 7],
    mkCaseFromIntVals "/quiet/nan-all-via-program"
      #[IntVal.nan, IntVal.nan, IntVal.nan],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-type-with-two-items" #[.null, .cell Cell.empty],
    mkCase "/type/pop-y-first" #[intV 1, intV 2, .null],
    mkCase "/type/pop-w-second" #[intV 1, .null, intV 2],
    mkCase "/type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "/error-order/pop-y-before-w-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-w-before-x-when-y-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 2, IntVal.num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 2, IntVal.num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-w-high-before-op"
      #[IntVal.num 2, IntVal.num (maxInt257 + 1), IntVal.num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 2, IntVal.num 3, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-all-before-op"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (maxInt257 + 2)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qadddivmodcSetGasExact), .tonEnvOp .setGasLimit, qadddivmodcInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qadddivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qadddivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020891
      count := 700
      gen := genQAddDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADDDIVMODC
