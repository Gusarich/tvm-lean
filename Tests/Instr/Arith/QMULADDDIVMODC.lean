import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULADDDIVMODC

/-
QMULADDDIVMODC branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulDivMod.lean`
    (`execInstrArithMulDivMod`, `.mulDivMod 3 1 true true`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, mode `1` / ceil)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode path `0xb7a982` → `.mulDivMod 3 1 true true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet encode path for `.mulDivMod ... quiet=true`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_muldivmod`, `dump_muldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (generic `.mulDivMod`): 6 branch sites / 14 terminal outcomes.
- Lean (QMULADDDIVMODC specialization): 7 branch sites / 8 reachable terminal outcomes
  (dispatch fallthrough, `stkUnd`, `typeChk` at `z/w/y/x`, quiet `(nan,nan)`,
   quiet `(nan,r)`, finite `(q,r)`).
- C++ (`exec_muldivmod` quiet add-mode path): 6 branch sites / 11 terminal outcomes.

Key risk areas covered:
- ceil quotient/remainder sign behavior with additive numerator `(x*y)+w` and mixed signs;
- strict pop/error ordering in add mode (`z`, then `w`, then `y`, then `x`);
- quiet funnels for divisor-zero, NaN operands, and quotient overflow (`q=NaN`, `r` preserved);
- oracle serialization safety (NaN / out-of-range integers injected only via program prelude);
- deterministic gas cliff via exact / exact-minus-one `PUSHINT n; SETGASLIMIT`.
-/

private def qmuladddivmodcId : InstrId := { name := "QMULADDDIVMODC" }

private def qmuladddivmodcInstr : Instr := .mulDivMod 3 1 true true

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuladddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmuladddivmodcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmuladddivmodcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQMulAddDivModCDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulDivMod qmuladddivmodcInstr stack

private def runQMulAddDivModCDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulDivMod .add (VM.push (intV 8531)) stack

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

private def qmuladddivmodcSetGasExact : Int :=
  computeExactGasBudget qmuladddivmodcInstr

private def qmuladddivmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuladddivmodcInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def ceilMulPool : Array Int :=
  #[-9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9]

private def ceilAddendPool : Array Int :=
  #[-4, -3, -2, -1, 0, 1, 2, 3, 4]

private def ceilDivisorPool : Array Int :=
  #[-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def classifyQMulAddDivModC (x y w z : Int) : String :=
  if z = 0 then
    "quiet/divzero"
  else
    let numer : Int := x * y + w
    let (q, r) := divModRound numer z 1
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet/overflow"
    else if r = 0 then
      "ok/exact"
    else
      "ok/inexact"

private def mkFiniteFuzzCase (shape : Nat) (x y w z : Int) : OracleCase :=
  let kind := classifyQMulAddDivModC x y w z
  mkCase s!"/fuzz/shape-{shape}/{kind}" #[intV x, intV y, intV w, intV z]

private def genQMulAddDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickInt257Boundary r3
      let (z0, r5) := pickInt257Boundary r4
      let z := if z0 = 0 then 1 else z0
      (mkFiniteFuzzCase shape x y w z, r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      (mkFiniteFuzzCase shape x y w z, r5)
    else if shape = 2 then
      let (x, r2) := pickFromPool ceilMulPool rng1
      let (y, r3) := pickFromPool ceilMulPool r2
      let (w, r4) := pickFromPool ceilAddendPool r3
      let (z, r5) := pickFromPool ceilDivisorPool r4
      (mkFiniteFuzzCase shape x y w z, r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkFiniteFuzzCase shape x y w 0, r4)
    else if shape = 4 then
      (mkFiniteFuzzCase shape maxInt257 2 1 2, rng1)
    else if shape = 5 then
      (mkFiniteFuzzCase shape minInt257 2 0 1, rng1)
    else if shape = 6 then
      (mkFiniteFuzzCase shape minInt257 (-1) 0 1, rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg" #[intV x], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args" #[intV x, intV y], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCase s!"/fuzz/shape-{shape}/underflow/three-args" #[intV x, intV y, intV w], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (zLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/z-top-non-int" #[intV x, intV y, intV w, zLike], r5)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let (wLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/w-second-non-int" #[intV x, intV y, wLike, intV z], r5)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let (yLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/y-third-non-int" #[intV x, yLike, intV w, intV z], r5)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      let (xLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/x-fourth-non-int" #[xLike, intV y, intV w, intV z], r5)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-z-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.num w, IntVal.nan], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-w-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan, IntVal.num z], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num w, IntVal.num z], r4)
    else if shape = 18 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (z, r4) := pickNonZeroInt r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num w, IntVal.num z], r4)
    else if shape = 19 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num w, IntVal.num z], r5)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (z, r5) := pickNonZeroInt r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num w, IntVal.num z], r5)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wOut, r4) := pickInt257OutOfRange r3
      let (z, r5) := pickNonZeroInt r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num wOut, IntVal.num z], r5)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (zOut, r5) := pickInt257OutOfRange r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-z-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num w, IntVal.num zOut], r5)
    else if shape = 23 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (wo, r4) := pickInt257OutOfRange r3
      let (zo, r5) := pickInt257OutOfRange r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        #[IntVal.num xo, IntVal.num yo, IntVal.num wo, IntVal.num zo], r5)
    else
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (negDiv, r5) := randBool r4
      let z := if negDiv then (-1) else 1
      (mkFiniteFuzzCase shape x y w z, r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuladddivmodcId
  unit := #[
    { name := "/unit/direct/ceil-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (3, 4, 5, 2, 9, -1),
            (3, -4, 5, 2, -3, -1),
            (-3, 4, 5, 2, -3, -1),
            (-3, -4, 5, 2, 9, -1),
            (7, 1, 0, 3, 3, -2),
            (7, 1, 0, -3, -2, 1),
            (-7, -1, 0, 3, 3, -2),
            (-7, -1, 0, -3, -2, 1),
            (5, -7, 0, 3, -11, -2),
            (-5, 7, 0, -3, 12, 1),
            (0, 100, 5, 7, 1, -2),
            (8, 9, -72, 5, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, w, z, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/w={w}/z={z}"
                (runQMulAddDivModCDirect #[intV x, intV y, intV w, intV z]) #[intV q, intV r] }
    ,
    { name := "/unit/direct/ceil-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 1, maxInt257, 0),
            (minInt257, 1, 0, 1, minInt257, 0),
            (maxInt257, -1, 0, -1, maxInt257, 0),
            (minInt257 + 1, -1, 0, 1, maxInt257, 0),
            (maxInt257, 1, -1, 2, (pow2 255) - 1, 0),
            (minInt257, 1, 1, 2, 1 - (pow2 255), -1),
            (maxInt257, 0, -1, -2, 1, 1),
            (minInt257, 0, 1, -2, 0, 1)
          ]
        for c in checks do
          match c with
          | (x, y, w, z, q, r) =>
              expectOkStack s!"/unit/direct/boundary/x={x}/y={y}/w={w}/z={z}"
                (runQMulAddDivModCDirect #[intV x, intV y, intV w, intV z]) #[intV q, intV r] }
    ,
    { name := "/unit/direct/quiet-funnels-divzero-nan-and-overflow"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQMulAddDivModCDirect #[intV 7, intV 9, intV 2, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQMulAddDivModCDirect #[intV 0, intV 0, intV 0, intV 0]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-z"
          (runQMulAddDivModCDirect #[intV 7, intV 9, intV 2, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-w"
          (runQMulAddDivModCDirect #[intV 7, intV 9, .int .nan, intV 2]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQMulAddDivModCDirect #[intV 7, .int .nan, intV 2, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQMulAddDivModCDirect #[.int .nan, intV 9, intV 2, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow-max-times-two"
          (runQMulAddDivModCDirect #[intV maxInt257, intV 2, intV 0, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow-min-times-two"
          (runQMulAddDivModCDirect #[intV minInt257, intV 2, intV 0, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow-max-times-two-plus-one-over-two"
          (runQMulAddDivModCDirect #[intV maxInt257, intV 2, intV 1, intV 2]) #[.int .nan, intV (-1)] }
    ,
    { name := "/unit/error-order/underflow-and-type-precedence"
      run := do
        expectErr "/unit/underflow/empty" (runQMulAddDivModCDirect #[]) .stkUnd
        expectErr "/unit/underflow/one-arg" (runQMulAddDivModCDirect #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-args" (runQMulAddDivModCDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/underflow/three-args" (runQMulAddDivModCDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-with-three-items"
          (runQMulAddDivModCDirect #[.null, .cell Cell.empty, .null]) .stkUnd
        expectErr "/unit/type/pop-z-first"
          (runQMulAddDivModCDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/unit/type/pop-w-second"
          (runQMulAddDivModCDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/unit/type/pop-y-third"
          (runQMulAddDivModCDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "/unit/type/pop-x-fourth"
          (runQMulAddDivModCDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/unit/error-order/pop-z-before-w-when-both-non-int"
          (runQMulAddDivModCDirect #[intV 1, intV 2, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-w-before-y-when-z-int"
          (runQMulAddDivModCDirect #[intV 1, .null, .cell Cell.empty, intV 3]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-zw-int"
          (runQMulAddDivModCDirect #[.null, .cell Cell.empty, intV 2, intV 3]) .typeChk }
    ,
    { name := "/unit/direct/pop-order-top-four-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-null"
          (runQMulAddDivModCDirect #[.null, intV 3, intV 4, intV 5, intV 2]) #[.null, intV 9, intV (-1)]
        expectOkStack "/unit/pop-order/below-cell-overflow-q-nan-r-preserved"
          (runQMulAddDivModCDirect #[.cell Cell.empty, intV maxInt257, intV 2, intV 1, intV 2])
          #[.cell Cell.empty, .int .nan, intV (-1)] }
    ,
    { name := "/unit/opcode/decode-qmuladddivmodc-sequence"
      run := do
        let program : Array Instr := #[qmuladddivmodcInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/qmuladddivmodc" s0 qmuladddivmodcInstr 24
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end-expected-exhausted-got-{s2.bitsRemaining}") }
    ,
    { name := "/unit/dispatch/non-muldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQMulAddDivModCDispatchFallback #[]) #[intV 8531] }
  ]
  oracle := #[
    mkCase "/ok/ceil/sign/pos-pos-pos-div-pos" #[intV 3, intV 4, intV 5, intV 2],
    mkCase "/ok/ceil/sign/pos-neg-pos-div-pos" #[intV 3, intV (-4), intV 5, intV 2],
    mkCase "/ok/ceil/sign/neg-pos-pos-div-pos" #[intV (-3), intV 4, intV 5, intV 2],
    mkCase "/ok/ceil/sign/neg-neg-pos-div-pos" #[intV (-3), intV (-4), intV 5, intV 2],
    mkCase "/ok/ceil/sign/pos-pos-div-neg" #[intV 7, intV 1, intV 0, intV (-3)],
    mkCase "/ok/ceil/sign/neg-neg-div-neg" #[intV (-7), intV (-1), intV 0, intV (-3)],
    mkCase "/ok/ceil/addend/negative-total" #[intV 5, intV (-7), intV 0, intV 3],
    mkCase "/ok/ceil/addend/negative-total-neg-divisor" #[intV (-5), intV 7, intV 0, intV (-3)],
    mkCase "/ok/exact/positive" #[intV 8, intV 9, intV (-72), intV 5],
    mkCase "/ok/exact/negative" #[intV (-8), intV 9, intV 72, intV 5],
    mkCase "/ok/exact/zero-numerator" #[intV 0, intV 100, intV 0, intV 7],
    mkCase "/ok/boundary/max-times-one-div-one" #[intV maxInt257, intV 1, intV 0, intV 1],
    mkCase "/ok/boundary/min-times-one-div-one" #[intV minInt257, intV 1, intV 0, intV 1],
    mkCase "/ok/boundary/max-times-neg-one-div-neg-one" #[intV maxInt257, intV (-1), intV 0, intV (-1)],
    mkCase "/ok/boundary/min-plus-one-times-neg-one-div-one" #[intV (minInt257 + 1), intV (-1), intV 0, intV 1],
    mkCase "/ok/boundary/max-minus-one-over-two" #[intV maxInt257, intV 1, intV (-1), intV 2],
    mkCase "/ok/boundary/min-plus-one-over-two" #[intV minInt257, intV 1, intV 1, intV 2],
    mkCase "/ok/boundary/w-only-div-neg-two" #[intV maxInt257, intV 0, intV (-1), intV (-2)],
    mkCase "/ok/boundary/w-only-min-div-neg-two" #[intV minInt257, intV 0, intV 1, intV (-2)],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 7, intV 9, intV 2, intV 0],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 0],
    mkCase "/quiet/overflow/max-times-two" #[intV maxInt257, intV 2, intV 0, intV 1],
    mkCase "/quiet/overflow/min-times-two" #[intV minInt257, intV 2, intV 0, intV 1],
    mkCase "/quiet/overflow/min-times-neg-one" #[intV minInt257, intV (-1), intV 0, intV 1],
    mkCase "/quiet/overflow/max-times-two-plus-one-over-two" #[intV maxInt257, intV 2, intV 1, intV 2],
    mkCaseFromIntVals "/quiet/nan-z-via-program"
      #[IntVal.num 11, IntVal.num 13, IntVal.num 17, IntVal.nan],
    mkCaseFromIntVals "/quiet/nan-w-via-program"
      #[IntVal.num 11, IntVal.num 13, IntVal.nan, IntVal.num 17],
    mkCaseFromIntVals "/quiet/nan-y-via-program"
      #[IntVal.num 11, IntVal.nan, IntVal.num 13, IntVal.num 17],
    mkCaseFromIntVals "/quiet/nan-x-via-program"
      #[IntVal.nan, IntVal.num 11, IntVal.num 13, IntVal.num 17],
    mkCaseFromIntVals "/quiet/nan-all-via-program"
      #[IntVal.nan, IntVal.nan, IntVal.nan, IntVal.nan],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-type-with-three-items" #[.null, .cell Cell.empty, .null],
    mkCase "/type/pop-z-first" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/pop-w-second" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/pop-y-third" #[intV 1, .null, intV 2, intV 3],
    mkCase "/type/pop-x-fourth" #[.null, intV 1, intV 2, intV 3],
    mkCase "/error-order/pop-z-before-w-when-both-non-int"
      #[intV 1, intV 2, .cell Cell.empty, .null],
    mkCase "/error-order/pop-w-before-y-when-z-int"
      #[intV 1, .null, .cell Cell.empty, intV 3],
    mkCase "/error-order/pop-y-before-x-when-zw-int"
      #[.null, .cell Cell.empty, intV 2, intV 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 2, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 2, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 2, IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-w-high-before-op"
      #[IntVal.num 2, IntVal.num 3, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-z-high-before-op"
      #[IntVal.num 2, IntVal.num 3, IntVal.num 4, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-all-before-op"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (maxInt257 + 2), IntVal.num (minInt257 - 2)],
    mkCase "/gas/exact-cost-succeeds" #[intV 3, intV 4, intV 5, intV 2]
      #[.pushInt (.num qmuladddivmodcSetGasExact), .tonEnvOp .setGasLimit, qmuladddivmodcInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 3, intV 4, intV 5, intV 2]
      #[.pushInt (.num qmuladddivmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuladddivmodcInstr]
  ]
  fuzz := #[
    { seed := 2026020882
      count := 700
      gen := genQMulAddDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULADDDIVMODC
