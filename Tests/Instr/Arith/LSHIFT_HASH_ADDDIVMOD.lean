import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_ADDDIVMOD

/-
LSHIFT#ADDDIVMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 (-1) true false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate `0xa9d0..0xa9d2` with `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0xa9d0..0xa9d2` decode to `.shlDivMod 3 ... (some z)`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`d=3`, `roundMode=-1`, `add=true`, `quiet=false`, `zOpt=some z` specialization):
- Lean specialization: 8 branch sites / 11 terminal outcomes
  (dispatch/fallback; arity precheck; immediate-shift range gate; pop/type order
   for `y`, then `w`, then `x`; numeric-vs-invalid split; divisor-zero split;
   non-quiet `pushIntQuiet` overflow funnel).
- C++ specialization: 7 branch sites / 11 aligned terminal outcomes
  (underflow guard; immediate-shift validity; ordered pops; numeric-vs-invalid path;
   divisor-zero split; floor divmod path; non-quiet push funnel).

Key risk areas covered:
- floor quotient/remainder semantics for `(x << z) + w` across sign combinations;
- hash-immediate behavior: `z` is fixed by opcode and must not be popped from stack;
- explicit pop/error ordering (`y`, then `w`, then `x`) plus below-stack preservation;
- non-quiet funnels (`intOv`) for divisor-zero and arithmetic overflow;
- NaN / out-of-range integer injection via program prelude only (`PUSHINT`);
- exact gas boundary via `computeExactGasBudget*` and `SETGASLIMIT`.
-/

private def lshiftHashAdddivmodId : InstrId := { name := "LSHIFT#ADDDIVMOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkLshiftHashAdddivmodInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 3 (-1) true false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftHashAdddivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkLshiftHashAdddivmodInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkLshiftHashAdddivmodInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runLshiftHashAdddivmodDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashAdddivmodInstr shift) stack

private def runLshiftHashAdddivmodDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5631)) stack

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

private def lshiftHashAdddivmodGasProbeInstr : Instr :=
  mkLshiftHashAdddivmodInstr 7

private def lshiftHashAdddivmodSetGasExact : Int :=
  computeExactGasBudget lshiftHashAdddivmodGasProbeInstr

private def lshiftHashAdddivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashAdddivmodGasProbeInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def floorNumeratorPool : Array Int :=
  #[-11, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 11]

private def floorAddendPool : Array Int :=
  #[-5, -3, -1, 0, 1, 3, 5]

private def floorDivisorPool : Array Int :=
  #[-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def classifyLshiftHashAdddivmod (x w y : Int) (shift : Nat) : String :=
  if y = 0 then
    "intov-divzero"
  else
    let tmp : Int := x * intPow2 shift + w
    let (q, r) := divModRound tmp y (-1)
    if !(intFitsSigned257 q && intFitsSigned257 r) then
      "intov-overflow"
    else if r = 0 then
      "ok-exact"
    else
      "ok-inexact"

private def genLshiftHashAdddivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      let kind := classifyLshiftHashAdddivmod x w y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-stack"
        shift #[intV x, intV w, intV y], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftInRange r4
      let kind := classifyLshiftHashAdddivmod x w y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/random-stack"
        shift #[intV x, intV w, intV y], r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-divzero"
        shift #[intV x, intV w, intV 0], r4)
    else if shape = 3 then
      let (x, r2) := pickIntFromPool floorNumeratorPool rng1
      let (w, r3) := pickIntFromPool floorAddendPool r2
      let (y, r4) := pickIntFromPool floorDivisorPool r3
      let (shift, r5) := pickShiftBoundary r4
      let kind := classifyLshiftHashAdddivmod x w y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/small-floor"
        shift #[intV x, intV w, intV y], r5)
    else if shape = 4 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-overflow/max-shift1-div1"
        1 #[.num maxInt257, .num 0, .num 1], rng1)
    else if shape = 5 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-overflow/min-shift1-div1"
        1 #[.num minInt257, .num 0, .num 1], rng1)
    else if shape = 6 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-overflow/min-div-neg1-shift1"
        1 #[.num minInt257, .num 0, .num (-1)], rng1)
    else if shape = 7 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-overflow/max-plus-max"
        1 #[.num maxInt257, .num maxInt257, .num 1], rng1)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty"
        shift #[], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item"
        shift #[intV x], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/two-items"
        shift #[intV x, intV w], r4)
    else if shape = 11 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-single-non-int"
        shift #[.null], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      let (yLike, r5) := pickNonInt r4
      (mkShiftCase s!"/fuzz/shape-{shape}/type/y-top-non-int"
        shift #[intV x, intV w, yLike], r5)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let (wLike, r5) := pickNonInt r4
      (mkShiftCase s!"/fuzz/shape-{shape}/type/w-second-non-int"
        shift #[intV x, wLike, intV y], r5)
    else if shape = 14 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let (xLike, r5) := pickNonInt r4
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-third-non-int"
        shift #[xLike, intV w, intV y], r5)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/y-before-w-when-both-non-int"
        shift #[intV x, .cell Cell.empty, .null], r3)
    else if shape = 16 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/w-before-x-when-y-int"
        shift #[.null, .cell Cell.empty, intV 1], r2)
    else if shape = 17 then
      let (x, r2) := pickIntFromPool floorNumeratorPool rng1
      let (shift, r3) := randNat r2 1 4
      let (pickNull, r4) := randBool r3
      let below : Value := if pickNull then .null else .cell Cell.empty
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift #[below, intV x, intV 1, intV 5], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        shift #[.num x, .num w, .nan], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-w-via-program"
        shift #[.num x, .nan, .num y], r4)
    else if shape = 20 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift #[.nan, .num w, .num y], r4)
    else if shape = 21 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xo, .num w, .num y], r5)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (wo, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        shift #[.num x, .num wo, .num y], r5)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yo, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift #[.num x, .num w, .num yo], r5)
    else if shape = 24 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/boundary/shift256"
        256 #[.num 1, .num 0, .num 2], rng1)
    else if shape = 25 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/inexact/shift1-neg-divisor"
        1 #[.num 7, .num 1, .num (-5)], rng1)
    else if shape = 26 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/divzero-shift256"
        256 #[.num 5, .num 1, .num 0], rng1)
    else
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/exact/div-by-one"
        1 #[.num x, .num 0, .num 1], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashAdddivmodId
  unit := #[
    { name := "/unit/direct/floor-sign-addend-shift-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
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
            (5, -7, 3, 1, 1, 0),
            (maxInt257, 0, 2, 1, maxInt257, 0),
            (minInt257, 0, 2, 1, minInt257, 0),
            (minInt257 + 1, 0, 2, 1, minInt257 + 1, 0)
          ]
        for c in checks do
          let (x, w, y, shift, q, r) := c
          expectOkStack s!"/unit/direct/x={x}/w={w}/y={y}/z={shift}"
            (runLshiftHashAdddivmodDirect shift #[intV x, intV w, intV y])
            #[intV q, intV r] }
    ,
    { name := "/unit/direct/boundary-success-and-pop-order"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 0, 2, 1, maxInt257, 0),
            (minInt257, 0, 2, 1, minInt257, 0),
            (minInt257 + 1, 0, 2, 1, minInt257 + 1, 0),
            (minInt257, 1, 2, 1, minInt257, 1),
            (maxInt257, -1, 2, 1, maxInt257 - 1, 1),
            (1, 0, 2, 256, pow2 255, 0),
            (-1, 0, 2, 256, -(pow2 255), 0)
          ]
        for c in checks do
          let (x, w, y, shift, q, r) := c
          expectOkStack s!"/unit/boundary/x={x}/w={w}/y={y}/z={shift}"
            (runLshiftHashAdddivmodDirect shift #[intV x, intV w, intV y])
            #[intV q, intV r]
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runLshiftHashAdddivmodDirect 1 #[.null, intV 7, intV 1, intV 5])
          #[.null, intV 3, intV 0]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runLshiftHashAdddivmodDirect 2 #[.cell Cell.empty, intV (-13), intV 3, intV 7])
          #[.cell Cell.empty, intV (-7), intV 0] }
    ,
    { name := "/unit/error/intov-funnels-divzero-and-overflow"
      run := do
        expectErr "/unit/intov/divzero/nonzero-over-zero"
          (runLshiftHashAdddivmodDirect 1 #[intV 7, intV 1, intV 0]) .intOv
        expectErr "/unit/intov/divzero/zero-over-zero"
          (runLshiftHashAdddivmodDirect 256 #[intV 0, intV 0, intV 0]) .intOv
        expectErr "/unit/intov/overflow/max-shift1-div1"
          (runLshiftHashAdddivmodDirect 1 #[intV maxInt257, intV 0, intV 1]) .intOv
        expectErr "/unit/intov/overflow/min-shift1-div1"
          (runLshiftHashAdddivmodDirect 1 #[intV minInt257, intV 0, intV 1]) .intOv
        expectErr "/unit/intov/overflow/min-div-neg1-shift1"
          (runLshiftHashAdddivmodDirect 1 #[intV minInt257, intV 0, intV (-1)]) .intOv
        expectErr "/unit/intov/overflow/max-plus-max-div1"
          (runLshiftHashAdddivmodDirect 1 #[intV maxInt257, intV maxInt257, intV 1]) .intOv }
    ,
    { name := "/unit/error/underflow-type-pop-order-and-error-order"
      run := do
        expectErr "/unit/underflow/empty"
          (runLshiftHashAdddivmodDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-item"
          (runLshiftHashAdddivmodDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-items"
          (runLshiftHashAdddivmodDirect 1 #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runLshiftHashAdddivmodDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/y-top-non-int"
          (runLshiftHashAdddivmodDirect 1 #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/type/w-second-non-int"
          (runLshiftHashAdddivmodDirect 1 #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/type/x-third-non-int"
          (runLshiftHashAdddivmodDirect 1 #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error-order/pop-y-before-w-when-both-non-int"
          (runLshiftHashAdddivmodDirect 1 #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-w-before-x-when-y-int"
          (runLshiftHashAdddivmodDirect 1 #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-before-pop"
      run := do
        expectErr "/unit/range/shift0-before-y-pop"
          (runLshiftHashAdddivmodDirect 0 #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "/unit/range/shift257-before-pop"
          (runLshiftHashAdddivmodDirect 257 #[.null, .cell Cell.empty, intV 1]) .rangeChk
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runLshiftHashAdddivmodDirect 0 #[]) .stkUnd }
    ,
    { name := "/unit/opcode/decode-hash-sequence"
      run := do
        let instr1 := mkLshiftHashAdddivmodInstr 1
        let instr256 := mkLshiftHashAdddivmodInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/lshift-hash-adddivmod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "decode/lshift-hash-adddivmod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-adddivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashAdddivmodDispatchFallback #[]) #[intV 5631] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/sign/pos-pos-exact" 1 #[.num 7, .num 1, .num 5],
    mkShiftInputCase "/ok/floor/sign/neg-pos-inexact" 1 #[.num (-7), .num 1, .num 5],
    mkShiftInputCase "/ok/floor/sign/pos-neg-inexact" 1 #[.num 7, .num (-1), .num (-5)],
    mkShiftInputCase "/ok/floor/sign/neg-neg-exact" 1 #[.num (-7), .num (-1), .num (-5)],
    mkShiftInputCase "/ok/floor/shift1-addend-neg" 1 #[.num 5, .num (-7), .num 3],
    mkShiftInputCase "/ok/floor/shift1-addend-pos-negdiv" 1 #[.num (-5), .num 7, .num (-3)],
    mkShiftInputCase "/ok/floor/inexact/shift2-pos" 2 #[.num 13, .num 3, .num 7],
    mkShiftInputCase "/ok/floor/inexact/shift1-neg" 1 #[.num (-13), .num 3, .num 7],
    mkShiftInputCase "/ok/floor/inexact/shift2-negdiv" 2 #[.num 13, .num 3, .num (-7)],
    mkShiftInputCase "/ok/floor/exact/zero-x-shift256" 256 #[.num 0, .num 5, .num 3],
    mkShiftInputCase "/ok/boundary/max-shift1-div2" 1 #[.num maxInt257, .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/min-shift1-div2" 1 #[.num minInt257, .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift1-div2"
      1 #[.num (minInt257 + 1), .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/min-plus-one-addend-shift1-div2"
      1 #[.num minInt257, .num 1, .num 2],
    mkShiftInputCase "/ok/boundary/max-minus-one-addend-shift1-div2"
      1 #[.num maxInt257, .num (-1), .num 2],
    mkShiftInputCase "/ok/boundary/one-shift256-div2" 256 #[.num 1, .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/negone-shift256-div2" 256 #[.num (-1), .num 0, .num 2],
    mkShiftCase "/ok/pop-order/below-null-preserved" 1 #[.null, intV 7, intV 1, intV 5],
    mkShiftCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-13), intV 3, intV 7],
    mkShiftInputCase "/intov/divzero/nonzero-over-zero" 1 #[.num 7, .num 1, .num 0],
    mkShiftInputCase "/intov/divzero/zero-over-zero-shift256" 256 #[.num 0, .num 0, .num 0],
    mkShiftInputCase "/intov/overflow/max-shift1-div1" 1 #[.num maxInt257, .num 0, .num 1],
    mkShiftInputCase "/intov/overflow/min-shift1-div1" 1 #[.num minInt257, .num 0, .num 1],
    mkShiftInputCase "/intov/overflow/min-div-neg1-shift1" 1 #[.num minInt257, .num 0, .num (-1)],
    mkShiftInputCase "/intov/overflow/max-plus-max-div1" 1 #[.num maxInt257, .num maxInt257, .num 1],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/underflow/two-items" 1 #[intV 1, intV 2],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/type/y-top-non-int" 1 #[intV 1, intV 2, .null],
    mkShiftCase "/type/w-second-non-int" 1 #[intV 1, .null, intV 2],
    mkShiftCase "/type/x-third-non-int" 1 #[.null, intV 1, intV 2],
    mkShiftCase "/error-order/pop-y-before-w-when-both-non-int" 1 #[intV 1, .cell Cell.empty, .null],
    mkShiftCase "/error-order/pop-w-before-x-when-y-int" 1 #[.null, .cell Cell.empty, intV 1],
    mkShiftInputCase "/intov/nan-y-via-program" 1 #[.num 7, .num 1, .nan],
    mkShiftInputCase "/intov/nan-w-via-program" 1 #[.num 7, .nan, .num 5],
    mkShiftInputCase "/intov/nan-x-via-program" 1 #[.nan, .num 1, .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      1 #[.num (maxInt257 + 1), .num 1, .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-w-before-op"
      1 #[.num 7, .num (maxInt257 + 1), .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op"
      1 #[.num 7, .num 1, .num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-all-before-op"
      1 #[.num (pow2 257), .num (-(pow2 257)), .num (maxInt257 + 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 1, intV 5]
      #[.pushInt (.num lshiftHashAdddivmodSetGasExact), .tonEnvOp .setGasLimit, lshiftHashAdddivmodGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 1, intV 5]
      #[.pushInt (.num lshiftHashAdddivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashAdddivmodGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020881
      count := 700
      gen := genLshiftHashAdddivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_ADDDIVMOD
