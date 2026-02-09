import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTADDDIVMOD

/-
QLSHIFTADDDIVMOD branch-mapping notes (Lean + C++ analyzed sources):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 (-1) true true none`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet `.shlDivMod` encoding via `0xb7 ++ 0xa9c0..0xa9c2`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-shldivmod decode for `0xb7a9c0..0xb7a9c2`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, quiet `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (`execInstrArithExt` `.shlDivMod` generic helper): 9 branch sites / 18 terminal outcomes.
- Lean (QLSHIFTADDDIVMOD specialization): 8 branch sites / 10 reachable terminal outcomes
  (finite `(q,r)`, quiet `(nan,nan)`, quiet `(nan,r)`, `stkUnd`,
   shift `typeChk`, y `typeChk`, w `typeChk`, x `typeChk`).
- C++ (`exec_shldivmod` add+quiet runtime-shift specialization): 8 branch sites / 16 terminal outcomes.

Key risk areas covered:
- floor quotient/remainder semantics and output order (`q` then `r`) with additive pre-dividend;
- strict pop/error order (`shift`, then `y`, then `w`, then `x`), including bad-shift precedence;
- quiet NaN funnels for bad shift, divisor-zero, NaN operands, and quotient overflow;
- oracle serialization safety (NaN / signed-257 out-of-range only via `PUSHINT` prelude);
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QLSHIFTADDDIVMOD`.
-/

private def qlshiftadddivmodId : InstrId := { name := "QLSHIFTADDDIVMOD" }

private def qlshiftadddivmodInstr : Instr :=
  .arithExt (.shlDivMod 3 (-1) true true none)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftadddivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qlshiftadddivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qlshiftadddivmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def mkShiftInjectedCase
    (name : String)
    (x : Int)
    (w : Int)
    (y : Int)
    (shift : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x, intV w, intV y] #[.pushInt shift, qlshiftadddivmodInstr] gasLimits fuel

private def runQlshiftadddivmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftadddivmodInstr stack

private def runQlshiftadddivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9679)) stack

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

private def qlshiftadddivmodSetGasExact : Int :=
  computeExactGasBudget qlshiftadddivmodInstr

private def qlshiftadddivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftadddivmodInstr

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOutOfRangePool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromPool validShiftBoundaryPool rng1
  else
    let (n, rng2) := randNat rng1 0 256
    (Int.ofNat n, rng2)

private def pickOutOfRangeShift (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftOutOfRangePool rng

private def pickNonZeroSigned257ish (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQlshiftadddivmod (x w y shift : Int) : String :=
  if shift < 0 || shift > 256 then
    "quiet-range-shift"
  else if y = 0 then
    "quiet-divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat + w
    let (q, r) := divModRound tmp y (-1)
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "quiet-overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def genQlshiftadddivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y0, r4) := pickInt257Boundary r3
      let y := if y0 = 0 then 1 else y0
      let (shift, r5) := pickFromPool validShiftBoundaryPool r4
      let kind := classifyQlshiftadddivmod x w y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-boundary-shift"
        #[intV x, intV w, intV y, intV shift], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroSigned257ish r3
      let (shift, r5) := pickFromPool validShiftBoundaryPool r4
      let kind := classifyQlshiftadddivmod x w y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/random-boundary-shift"
        #[intV x, intV w, intV y, intV shift], r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroSigned257ish r3
      let (shift, r5) := pickValidShift r4
      let kind := classifyQlshiftadddivmod x w y shift
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/random-random-shift"
        #[intV x, intV w, intV y, intV shift], r5)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y0, r4) := pickInt257Boundary r3
      let y := if y0 = 0 then 1 else y0
      let kind := classifyQlshiftadddivmod x w y 256
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-shift-256"
        #[intV x, intV w, intV y, intV 256], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero-random"
        #[intV x, intV w, intV 0, intV shift], r4)
    else if shape = 5 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      (mkCase s!"/fuzz/shape-{shape}/quiet/divzero-boundary-shift0"
        #[intV x, intV w, intV 0, intV 0], r3)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-shift1-div1"
        #[intV maxInt257, intV 0, intV 1, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-shift1-div1"
        #[intV minInt257, intV 0, intV 1, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-div-neg1"
        #[intV minInt257, intV 0, intV (-1), intV 0], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroSigned257ish r3
      let (shiftLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV w, intV y, shiftLike], r5)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let (yLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/y-second-non-int"
        #[intV x, intV w, yLike, intV shift], r5)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let (wLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/w-third-non-int"
        #[intV x, wLike, intV y, intV shift], r5)
    else if shape = 12 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let (xLike, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/x-fourth-non-int"
        #[xLike, intV w, intV y, intV shift], r5)
    else if shape = 13 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (shift, r2) := pickValidShift rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg"
        #[intV shift], r2)
    else if shape = 15 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args"
        #[intV y, intV shift], r3)
    else if shape = 16 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/underflow/three-args"
        #[intV w, intV y, intV shift], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroSigned257ish r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/nan-shift-via-program"
        x w y .nan, r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        #[IntVal.num x, IntVal.num w, IntVal.nan, IntVal.num shift], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-w-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num y, IntVal.num shift], r4)
    else if shape = 20 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        #[IntVal.nan, IntVal.num w, IntVal.num y, IntVal.num shift], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroSigned257ish r3
      let (badShift, r5) := pickOutOfRangeShift r4
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/shift-range-via-program"
        x w y (.num badShift), r5)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/shift-range-does-not-mask-y-type"
        #[intV x, intV w, .null] #[.pushInt (.num 257), qlshiftadddivmodInstr], r3)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/shift-range-does-not-mask-w-type"
        #[intV x, .null, intV y] #[.pushInt (.num 257), qlshiftadddivmodInstr], r3)
    else if shape = 24 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/shift-nan-does-not-mask-x-type"
        #[.null, intV w, intV y] #[.pushInt .nan, qlshiftadddivmodInstr], r3)
    else if shape = 25 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroSigned257ish r3
      let (shift, r5) := pickValidShift r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xo, IntVal.num w, IntVal.num y, IntVal.num shift], r5)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (wo, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroSigned257ish r3
      let (shift, r5) := pickValidShift r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        #[IntVal.num x, IntVal.num wo, IntVal.num y, IntVal.num shift], r5)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yo, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickValidShift r4
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num yo, IntVal.num shift], r5)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroSigned257ish r3
      let (pickNeg, r5) := randBool r4
      let shiftOut : Int := if pickNeg then -1 else 257
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num y, IntVal.num shiftOut], r5)
    else
      let xo : Int := maxInt257 + 1
      let wo : Int := minInt257 - 1
      let yo : Int := maxInt257 + 1
      let so : Int := 257
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        #[IntVal.num xo, IntVal.num wo, IntVal.num yo, IntVal.num so], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftadddivmodId
  unit := #[
    { name := "/unit/direct/floor-sign-addend-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 1, 5, 1, 3, 0),
            (-7, 1, 5, 1, -3, 2),
            (7, -1, -5, 1, -3, -2),
            (-7, -1, -5, 1, 3, 0),
            (1, 2, 8, 8, 32, 2),
            (-1, 2, 8, 8, -32, 2),
            (13, 3, 7, 2, 7, 6),
            (-13, 3, 7, 1, -4, 5),
            (13, 3, -7, 2, -8, -1),
            (0, 5, 3, 256, 1, 2),
            (maxInt257, 0, 2, 1, maxInt257, 0),
            (minInt257, 0, 2, 1, minInt257, 0),
            (minInt257 + 1, 0, 2, 1, minInt257 + 1, 0)
          ]
        for c in checks do
          let (x, w, y, shift, q, r) := c
          expectOkStack s!"/unit/direct/x={x}/w={w}/y={y}/shift={shift}"
            (runQlshiftadddivmodDirect #[intV x, intV w, intV y, intV shift])
            #[intV q, intV r] }
    ,
    { name := "/unit/direct/quiet-nan-funnels-divzero-range-and-overflow"
      run := do
        expectOkStack "/unit/quiet/divzero/nonzero-over-zero"
          (runQlshiftadddivmodDirect #[intV 7, intV 1, intV 0, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/divzero/zero-over-zero"
          (runQlshiftadddivmodDirect #[intV 0, intV 0, intV 0, intV 200]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/shift-negative"
          (runQlshiftadddivmodDirect #[intV 7, intV 1, intV 3, intV (-1)]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/shift-overmax"
          (runQlshiftadddivmodDirect #[intV 7, intV 1, intV 3, intV 257]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/shift-nan"
          (runQlshiftadddivmodDirect #[intV 7, intV 1, intV 3, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQlshiftadddivmodDirect #[intV 7, intV 1, .int .nan, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-w"
          (runQlshiftadddivmodDirect #[intV 7, .int .nan, intV 3, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQlshiftadddivmodDirect #[.int .nan, intV 1, intV 3, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow/max-shift1-div1"
          (runQlshiftadddivmodDirect #[intV maxInt257, intV 0, intV 1, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-shift1-div1"
          (runQlshiftadddivmodDirect #[intV minInt257, intV 0, intV 1, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/min-div-neg1-shift0"
          (runQlshiftadddivmodDirect #[intV minInt257, intV 0, intV (-1), intV 0]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow/max-plus-max-div1"
          (runQlshiftadddivmodDirect #[intV maxInt257, intV maxInt257, intV 1, intV 0]) #[.int .nan, intV 0] }
    ,
    { name := "/unit/error-order/underflow-type-and-quiet-range-precedence"
      run := do
        expectErr "/unit/underflow/empty" (runQlshiftadddivmodDirect #[]) .stkUnd
        expectErr "/unit/underflow/one-arg" (runQlshiftadddivmodDirect #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-args" (runQlshiftadddivmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/underflow/three-args" (runQlshiftadddivmodDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/unit/type/shift-top-null"
          (runQlshiftadddivmodDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/unit/type/shift-top-cell"
          (runQlshiftadddivmodDirect #[intV 1, intV 2, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/y-second-null"
          (runQlshiftadddivmodDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/unit/type/w-third-null"
          (runQlshiftadddivmodDirect #[intV 1, .null, intV 3, intV 1]) .typeChk
        expectErr "/unit/type/x-fourth-null"
          (runQlshiftadddivmodDirect #[.null, intV 2, intV 3, intV 1]) .typeChk
        expectErr "/unit/error-order/y-before-w-when-both-non-int"
          (runQlshiftadddivmodDirect #[intV 1, .cell Cell.empty, .null, intV 1]) .typeChk
        expectErr "/unit/error-order/w-before-x-when-y-int"
          (runQlshiftadddivmodDirect #[.null, .cell Cell.empty, intV 3, intV 1]) .typeChk
        expectErr "/unit/error-order/shift-range-does-not-mask-y-type"
          (runQlshiftadddivmodDirect #[intV 1, intV 2, .null, intV 257]) .typeChk
        expectErr "/unit/error-order/shift-range-does-not-mask-w-type"
          (runQlshiftadddivmodDirect #[intV 1, .null, intV 3, intV 257]) .typeChk
        expectErr "/unit/error-order/shift-nan-does-not-mask-x-type"
          (runQlshiftadddivmodDirect #[.null, intV 2, intV 3, .int .nan]) .typeChk }
    ,
    { name := "/unit/direct/pop-order-top-four-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-null"
          (runQlshiftadddivmodDirect #[.null, intV 7, intV 1, intV 5, intV 1])
          #[.null, intV 3, intV 0]
        expectOkStack "/unit/pop-order/below-cell-quiet-shift-range"
          (runQlshiftadddivmodDirect #[.cell Cell.empty, intV 7, intV 1, intV 5, intV 257])
          #[.cell Cell.empty, .int .nan, .int .nan] }
    ,
    { name := "/unit/opcode/decode-qlshiftadddivmod-sequence"
      run := do
        let program : Array Instr := #[qlshiftadddivmodInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/qlshiftadddivmod" s0 qlshiftadddivmodInstr 24
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end-expected-exhausted-got-{s2.bitsRemaining}") }
    ,
    { name := "/unit/dispatch/non-qlshiftadddivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQlshiftadddivmodDispatchFallback #[]) #[intV 9679] }
  ]
  oracle := #[
    mkCase "/ok/floor/sign/pos-pos-inexact" #[intV 7, intV 1, intV 5, intV 1],
    mkCase "/ok/floor/sign/neg-pos-inexact" #[intV (-7), intV 1, intV 5, intV 1],
    mkCase "/ok/floor/sign/pos-neg-inexact" #[intV 7, intV (-1), intV (-5), intV 1],
    mkCase "/ok/floor/sign/neg-neg-exact" #[intV (-7), intV (-1), intV (-5), intV 1],
    mkCase "/ok/floor/near-zero-pos-divisor" #[intV (-1), intV 0, intV 3, intV 0],
    mkCase "/ok/floor/near-zero-neg-divisor" #[intV 1, intV 0, intV (-3), intV 0],
    mkCase "/ok/floor/shift-zero-addend-neg" #[intV 5, intV (-7), intV 3, intV 0],
    mkCase "/ok/floor/shift-zero-addend-pos" #[intV (-5), intV 7, intV (-3), intV 0],
    mkCase "/ok/floor/inexact/pos-pos-shift2" #[intV 13, intV 3, intV 7, intV 2],
    mkCase "/ok/floor/inexact/neg-pos-shift1" #[intV (-13), intV 3, intV 7, intV 1],
    mkCase "/ok/floor/inexact/pos-neg-shift2" #[intV 13, intV 3, intV (-7), intV 2],
    mkCase "/ok/floor/exact/zero-x-large-shift" #[intV 0, intV 5, intV 3, intV 256],
    mkCase "/ok/boundary/max-shift0-div1" #[intV maxInt257, intV 0, intV 1, intV 0],
    mkCase "/ok/boundary/min-shift0-div1" #[intV minInt257, intV 0, intV 1, intV 0],
    mkCase "/ok/boundary/max-shift1-div2" #[intV maxInt257, intV 0, intV 2, intV 1],
    mkCase "/ok/boundary/min-shift1-div2" #[intV minInt257, intV 0, intV 2, intV 1],
    mkCase "/ok/boundary/min-plus-one-shift1-div2" #[intV (minInt257 + 1), intV 0, intV 2, intV 1],
    mkCase "/ok/boundary/pow255-shift1-div2" #[intV (pow2 255), intV 0, intV 2, intV 1],
    mkCase "/ok/boundary/neg-pow255-shift1-div2" #[intV (-(pow2 255)), intV 0, intV 2, intV 1],
    mkCase "/ok/boundary/one-over-max-shift256" #[intV 1, intV 0, intV maxInt257, intV 256],
    mkCase "/ok/boundary/negone-over-max-shift256" #[intV (-1), intV 0, intV maxInt257, intV 256],
    mkCase "/ok/boundary/one-over-min-shift256" #[intV 1, intV 0, intV minInt257, intV 256],
    mkCase "/ok/boundary/negone-over-min-shift256" #[intV (-1), intV 0, intV minInt257, intV 256],
    mkCase "/ok/pop-order/below-null-preserved" #[.null, intV 7, intV 1, intV 5, intV 1],
    mkCase "/ok/pop-order/below-cell-preserved" #[.cell Cell.empty, intV (-7), intV 1, intV 5, intV 1],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 7, intV 1, intV 0, intV 1],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 200],
    mkShiftInjectedCase "/quiet/shift-negative-via-program" 7 1 3 (.num (-1)),
    mkShiftInjectedCase "/quiet/shift-overmax-via-program" 7 1 3 (.num 257),
    mkShiftInjectedCase "/quiet/shift-way-overmax-via-program" 7 1 3 (.num 300),
    mkShiftInjectedCase "/quiet/shift-nan-via-program" 7 1 3 .nan,
    mkCaseFromIntVals "/quiet/nan-y-via-program" #[IntVal.num 7, IntVal.num 1, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "/quiet/nan-w-via-program" #[IntVal.num 7, IntVal.nan, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/quiet/nan-x-via-program" #[IntVal.nan, IntVal.num 1, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/quiet/nan-all-via-program" #[IntVal.nan, IntVal.nan, IntVal.nan, IntVal.num 1],
    mkCase "/quiet/overflow/max-shift1-div1" #[intV maxInt257, intV 0, intV 1, intV 1],
    mkCase "/quiet/overflow/min-shift1-div1" #[intV minInt257, intV 0, intV 1, intV 1],
    mkCase "/quiet/overflow/min-div-neg1-shift0" #[intV minInt257, intV 0, intV (-1), intV 0],
    mkCase "/quiet/overflow/max-plus-max-div1" #[intV maxInt257, intV maxInt257, intV 1, intV 0],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/type/shift-top-null" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/shift-top-cell" #[intV 1, intV 2, intV 3, .cell Cell.empty],
    mkCase "/type/y-second-null" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/w-third-null" #[intV 1, .null, intV 3, intV 1],
    mkCase "/type/x-fourth-null" #[.null, intV 2, intV 3, intV 1],
    mkCase "/error-order/y-before-w-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null, intV 1],
    mkCase "/error-order/w-before-x-when-y-int"
      #[.null, .cell Cell.empty, intV 3, intV 1],
    mkCase "/error-order/shift-range-does-not-mask-y-type-via-program"
      #[intV 7, intV 1, .null] #[.pushInt (.num 257), qlshiftadddivmodInstr],
    mkCase "/error-order/shift-range-does-not-mask-w-type-via-program"
      #[intV 7, .null, intV 3] #[.pushInt (.num 257), qlshiftadddivmodInstr],
    mkCase "/error-order/shift-nan-does-not-mask-x-type-via-program"
      #[.null, intV 1, intV 3] #[.pushInt .nan, qlshiftadddivmodInstr],
    mkCase "/error-order/underflow-before-range-via-program"
      #[] #[.pushInt (.num (-1)), qlshiftadddivmodInstr],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 1, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 1, IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-w-high-before-op"
      #[IntVal.num 7, IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-w-low-before-op"
      #[IntVal.num 7, IntVal.num (minInt257 - 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 7, IntVal.num 1, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-low-before-op"
      #[IntVal.num 7, IntVal.num 1, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-high-before-op"
      #[IntVal.num 7, IntVal.num 1, IntVal.num 3, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-low-before-op"
      #[IntVal.num 7, IntVal.num 1, IntVal.num 3, IntVal.num (minInt257 - 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 1, intV 3, intV 1]
      #[.pushInt (.num qlshiftadddivmodSetGasExact), .tonEnvOp .setGasLimit, qlshiftadddivmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 1, intV 3, intV 1]
      #[.pushInt (.num qlshiftadddivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftadddivmodInstr]
  ]
  fuzz := #[
    { seed := 2026020867
      count := 700
      gen := genQlshiftadddivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTADDDIVMOD
