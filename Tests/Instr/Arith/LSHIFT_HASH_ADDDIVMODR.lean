import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_ADDDIVMODR

/-
LSHIFT#ADDDIVMODR branch-map notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 0 true false (some z)` specialization)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/overflow behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, nearest rounding ties toward `+∞`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (hash-immediate decode family `0xa9d0..0xa9d2`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, add-mode handling, non-quiet funnel)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`mod_div` nearest rounding and quotient/remainder production)

Branch/terminal counts used for this suite (`d=3`, `roundMode=0`, `add=true`,
`quiet=false`, `zOpt=some`):
- Lean specialization: 9 branch sites / 13 terminal outcomes
  (dispatch/fallback; underflow gate; immediate-range gate; pop order `y→w→x`;
   numeric-vs-invalid split; divisor-zero split; dual-push path `q,r` with
   non-quiet overflow behavior).
- C++ specialization: 8 branch sites / 12 aligned outcomes
  (underflow gate; immediate-shift gate; operand pop/type order; divisor-zero
   and non-finite funnel; quotient/remainder push behavior).

Key risk areas covered:
- nearest rounding ties toward `+∞` for `((x << z) + w) / y`;
- hash-immediate behavior (`z` is encoded, never popped);
- strict pop/error ordering (`y`, then `w`, then `x`) and below-stack preservation;
- range-gate precedence for malformed immediates (`z = 0`, `z = 257`);
- non-quiet `intOv` funnels (div-zero, NaN via prelude, pushint-range via prelude, quotient overflow);
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def lshiftHashAddDivModrId : InstrId := { name := "LSHIFT#ADDDIVMODR" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkLshiftHashAddDivModrInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 3 0 true false (some shift))

private def lshiftHashAddDivModrInstrDefault : Instr :=
  mkLshiftHashAddDivModrInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftHashAddDivModrInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftHashAddDivModrId
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
  mkCase name stack #[mkLshiftHashAddDivModrInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkLshiftHashAddDivModrInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runLshiftHashAddDivModrDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashAddDivModrInstr shift) stack

private def runLshiftHashAddDivModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6785)) stack

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

private def lshiftHashAddDivModrGasProbeInstr : Instr :=
  mkLshiftHashAddDivModrInstr 7

private def lshiftHashAddDivModrSetGasExact : Int :=
  computeExactGasBudget lshiftHashAddDivModrGasProbeInstr

private def lshiftHashAddDivModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashAddDivModrGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieNumeratorPool : Array Int :=
  #[-11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def smallDenominatorPool : Array Int :=
  #[-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def classifyLshiftHashAddDivModr (x w y : Int) (shift : Nat) : String :=
  if y = 0 then
    "intov-divzero"
  else
    let tmp : Int := x * intPow2 shift + w
    let (q, r) := divModRound tmp y 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "intov-overflow"
    else if r = 0 then
      "ok-exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "ok-tie"
    else
      "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (x w y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashAddDivModr x w y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x, intV w, intV y]

private def genLshiftHashAddDivModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkFiniteFuzzCase shape x w y shift, r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftInRange r4
      (mkFiniteFuzzCase shape x w y shift, r5)
    else if shape = 2 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDenominatorPool r2
      (mkFiniteFuzzCase shape t 0 y 1, r3)
    else if shape = 3 then
      let (t, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDenominatorPool r2
      (mkFiniteFuzzCase shape (t - 1) 1 y 1, r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool #[-1, 0, 1] rng1
      let (w, r3) := pickFromPool #[-1, 0, 1] r2
      let (y, r4) := pickFromPool smallDenominatorPool r3
      (mkFiniteFuzzCase shape x w y 256, r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-divzero" shift #[intV x, intV w, intV 0], r4)
    else if shape = 6 then
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-overflow-max-shift1-div1"
        1 #[intV maxInt257, intV 0, intV 1], rng1)
    else if shape = 7 then
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-overflow-min-shift1-div1"
        1 #[intV minInt257, intV 0, intV 1], rng1)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow-empty" shift #[], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow-one-item" shift #[intV x], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow-two-items" shift #[intV x, intV w], r4)
    else if shape = 11 then
      let (v, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order-underflow-before-type-single-non-int"
        shift #[v], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (yBad, r5) := pickNonInt r4
      (mkShiftCase s!"/fuzz/shape-{shape}/type-pop-y-first" shift #[intV x, intV w, yBad], r5)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      let (wBad, r5) := pickNonInt r4
      (mkShiftCase s!"/fuzz/shape-{shape}/type-pop-w-second" shift #[intV x, wBad, intV y], r5)
    else if shape = 14 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      let (xBad, r5) := pickNonInt r4
      (mkShiftCase s!"/fuzz/shape-{shape}/type-pop-x-third" shift #[xBad, intV w, intV y], r5)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order-pop-y-before-w-when-both-non-int"
        shift #[intV x, .null, .cell Cell.empty], r3)
    else if shape = 16 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order-pop-w-before-x-when-y-int"
        shift #[.null, .cell Cell.empty, intV y], r3)
    else if shape = 17 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order-underflow-before-type-two-non-int"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      let (belowCell, r6) := randBool r5
      let below : Value := if belowCell then .cell Cell.empty else .null
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order-lower-preserved"
        shift #[below, intV x, intV w, intV y], r6)
    else if shape = 19 then
      let (x, r2) := pickFromPool #[-1, 0, 1] rng1
      let (w, r3) := pickFromPool #[-1, 0, 1] r2
      let (y, r4) := pickFromPool smallDenominatorPool r3
      (mkFiniteFuzzCase shape x w y 256, r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-y-via-program"
        shift #[.num x, .num w, .nan], r4)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-w-via-program"
        shift #[.num x, .nan, .num y], r4)
    else if shape = 22 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-x-via-program"
        shift #[.nan, .num w, .num y], r4)
    else if shape = 23 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-all-via-program"
        shift #[.nan, .nan, .nan], r2)
    else if shape = 24 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-x-before-op"
        shift #[.num xo, .num w, .num y], r5)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (wo, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-w-before-op"
        shift #[.num x, .num wo, .num y], r5)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yo, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-y-before-op"
        shift #[.num x, .num w, .num yo], r5)
    else
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkFiniteFuzzCase shape x w 1 1, r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashAddDivModrId
  unit := #[
    { name := "/unit/ok/nearest-rounding-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 5, 1, 3, 2),
            (-7, 3, 5, 1, -2, -1),
            (7, -3, 5, 1, 2, 1),
            (-7, -3, 5, 1, -3, -2),
            (5, 0, 4, 1, 3, -2),
            (-5, 0, 4, 1, -2, -2),
            (5, 0, -4, 1, -2, 2),
            (-5, 0, -4, 1, 3, 2),
            (1, 0, 4, 1, 1, -2),
            (-1, 0, 4, 1, 0, -2),
            (1, 0, -4, 1, 0, 2),
            (-1, 0, -4, 1, 1, 2),
            (7, 5, 2, 2, 17, -1),
            (-7, 5, 2, 2, -11, -1),
            (7, -5, 2, 2, 12, -1),
            (-7, -5, 2, 2, -16, -1),
            (42, 0, 7, 3, 48, 0),
            (0, 9, 5, 8, 2, -1),
            (0, -9, 5, 8, -2, 1),
            (3, 1, 5, 1, 1, 2)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectOkStack s!"/unit/ok/({x}<<{shift})+{w}/{y}"
                (runLshiftHashAddDivModrDirect shift #[intV x, intV w, intV y])
                #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-success-and-pop-order"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 0, 4, 1, pow2 255, -2),
            (maxInt257, (-2), 4, 1, (pow2 255) - 1, 0),
            (minInt257, 0, 4, 1, -(pow2 255), 0),
            (minInt257, 2, 4, 1, -(pow2 255) + 1, -2),
            (minInt257 + 1, 0, -4, 1, pow2 255, 2),
            (1, 0, maxInt257, 256, 1, 1),
            (-1, 0, maxInt257, 256, -1, -1),
            (1, 0, minInt257, 256, -1, 0),
            (-1, 0, minInt257, 256, 1, 0),
            (0, 5, 3, 1, 2, -1)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectOkStack s!"/unit/boundary/({x}<<{shift})+{w}/{y}"
                (runLshiftHashAddDivModrDirect shift #[intV x, intV w, intV y])
                #[intV q, intV r]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runLshiftHashAddDivModrDirect 1 #[.cell Cell.empty, intV 7, intV 3, intV 5])
          #[.cell Cell.empty, intV 3, intV 2]
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runLshiftHashAddDivModrDirect 1 #[.null, intV 7, intV (-3), intV 5])
          #[.null, intV 2, intV 1] }
    ,
    { name := "/unit/error/intov-divzero-and-overflow-funnels"
      run := do
        expectErr "/unit/intov/divzero/nonzero-over-zero"
          (runLshiftHashAddDivModrDirect 1 #[intV 7, intV 3, intV 0]) .intOv
        expectErr "/unit/intov/divzero/zero-over-zero"
          (runLshiftHashAddDivModrDirect 256 #[intV 0, intV 0, intV 0]) .intOv
        expectErr "/unit/intov/overflow/max-shift1-div1"
          (runLshiftHashAddDivModrDirect 1 #[intV maxInt257, intV 0, intV 1]) .intOv
        expectErr "/unit/intov/overflow/min-shift1-div1"
          (runLshiftHashAddDivModrDirect 1 #[intV minInt257, intV 0, intV 1]) .intOv
        expectErr "/unit/intov/overflow/max-plus-one-shift1-div2"
          (runLshiftHashAddDivModrDirect 1 #[intV maxInt257, intV 1, intV 2]) .intOv
        expectErr "/unit/intov/overflow/min-minus-one-shift1-div2"
          (runLshiftHashAddDivModrDirect 1 #[intV minInt257, intV (-2), intV 2]) .intOv }
    ,
    { name := "/unit/error/pop-order-and-error-ordering"
      run := do
        expectErr "/unit/underflow/empty" (runLshiftHashAddDivModrDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-item" (runLshiftHashAddDivModrDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/underflow/two-items" (runLshiftHashAddDivModrDirect 1 #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runLshiftHashAddDivModrDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runLshiftHashAddDivModrDirect 1 #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/type/pop-w-second-null"
          (runLshiftHashAddDivModrDirect 1 #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/type/pop-x-third-null"
          (runLshiftHashAddDivModrDirect 1 #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error-order/pop-y-before-w-when-both-non-int"
          (runLshiftHashAddDivModrDirect 1 #[intV 1, .null, .cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/pop-w-before-x-when-y-int"
          (runLshiftHashAddDivModrDirect 1 #[.null, .cell Cell.empty, intV 2]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-precedence"
      run := do
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runLshiftHashAddDivModrDirect 0 #[]) .stkUnd
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate-low"
          (runLshiftHashAddDivModrDirect 0 #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error-order/range-before-w-type-invalid-immediate-high"
          (runLshiftHashAddDivModrDirect 257 #[intV 1, .null, intV 2]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate-high"
          (runLshiftHashAddDivModrDirect 257 #[.null, intV 1, intV 2]) .rangeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkLshiftHashAddDivModrInstr 1
        let instr256 := mkLshiftHashAddDivModrInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-adddivmodr-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/lshift-hash-adddivmodr-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-adddivmodr-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashAddDivModrDispatchFallback #[]) #[intV 6785] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/round/inexact-pos-pos-shift1" 1 #[.num 7, .num 3, .num 5],
    mkShiftInputCase "/ok/round/inexact-neg-pos-shift1" 1 #[.num (-7), .num 3, .num 5],
    mkShiftInputCase "/ok/round/inexact-pos-neg-shift1" 1 #[.num 7, .num (-3), .num 5],
    mkShiftInputCase "/ok/round/inexact-neg-neg-shift1" 1 #[.num (-7), .num (-3), .num 5],
    mkShiftInputCase "/ok/tie/pos-over-pos-four-shift1" 1 #[.num 5, .num 0, .num 4],
    mkShiftInputCase "/ok/tie/neg-over-pos-four-shift1" 1 #[.num (-5), .num 0, .num 4],
    mkShiftInputCase "/ok/tie/pos-over-neg-four-shift1" 1 #[.num 5, .num 0, .num (-4)],
    mkShiftInputCase "/ok/tie/neg-over-neg-four-shift1" 1 #[.num (-5), .num 0, .num (-4)],
    mkShiftInputCase "/ok/tie/near-zero-neg-over-pos-four-shift1" 1 #[.num (-1), .num 0, .num 4],
    mkShiftInputCase "/ok/tie/near-zero-pos-over-neg-four-shift1" 1 #[.num 1, .num 0, .num (-4)],
    mkShiftInputCase "/ok/tie/near-zero-neg-over-neg-four-shift1" 1 #[.num (-1), .num 0, .num (-4)],
    mkShiftInputCase "/ok/exact/shift3-divisible" 3 #[.num 42, .num 0, .num 7],
    mkShiftInputCase "/ok/exact/addend-only-positive" 8 #[.num 0, .num 9, .num 5],
    mkShiftInputCase "/ok/exact/addend-only-negative" 8 #[.num 0, .num (-9), .num 5],
    mkShiftInputCase "/ok/exact/addend-cancels-shifted" 1 #[.num 3, .num (-6), .num 5],
    mkShiftInputCase "/ok/boundary/max-shift1-div4" 1 #[.num maxInt257, .num 0, .num 4],
    mkShiftInputCase "/ok/boundary/max-plus-neg2-shift1-div4" 1 #[.num maxInt257, .num (-2), .num 4],
    mkShiftInputCase "/ok/boundary/min-shift1-div4" 1 #[.num minInt257, .num 0, .num 4],
    mkShiftInputCase "/ok/boundary/min-plus-two-shift1-div4" 1 #[.num minInt257, .num 2, .num 4],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift1-div-neg4" 1 #[.num (minInt257 + 1), .num 0, .num (-4)],
    mkShiftInputCase "/ok/boundary/one-shift256-div-max" 256 #[.num 1, .num 0, .num maxInt257],
    mkShiftInputCase "/ok/boundary/neg-one-shift256-div-max" 256 #[.num (-1), .num 0, .num maxInt257],
    mkShiftInputCase "/ok/boundary/one-shift256-div-min" 256 #[.num 1, .num 0, .num minInt257],
    mkShiftInputCase "/ok/boundary/neg-one-shift256-div-min" 256 #[.num (-1), .num 0, .num minInt257],
    mkShiftCase "/ok/pop-order/lower-preserved-cell" 1 #[.cell Cell.empty, intV 7, intV 3, intV 5],
    mkShiftCase "/ok/pop-order/lower-preserved-null" 1 #[.null, intV 7, intV (-3), intV 5],
    mkShiftInputCase "/intov/divzero/nonzero-over-zero" 1 #[.num 7, .num 3, .num 0],
    mkShiftInputCase "/intov/divzero/zero-over-zero" 256 #[.num 0, .num 0, .num 0],
    mkShiftInputCase "/intov/overflow/max-shift1-div1" 1 #[.num maxInt257, .num 0, .num 1],
    mkShiftInputCase "/intov/overflow/min-shift1-div1" 1 #[.num minInt257, .num 0, .num 1],
    mkShiftInputCase "/intov/overflow/max-plus-one-shift1-div2" 1 #[.num maxInt257, .num 1, .num 2],
    mkShiftInputCase "/intov/overflow/min-minus-one-shift1-div2" 1 #[.num minInt257, .num (-2), .num 2],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/underflow/two-items" 1 #[intV 1, intV 2],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/error-order/underflow-before-type-two-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftCase "/type/pop-y-first" 1 #[intV 1, intV 2, .null],
    mkShiftCase "/type/pop-w-second" 1 #[intV 1, .null, intV 2],
    mkShiftCase "/type/pop-x-third" 1 #[.null, intV 1, intV 2],
    mkShiftCase "/error-order/pop-y-before-w-when-both-non-int" 1 #[intV 1, .null, .cell Cell.empty],
    mkShiftCase "/error-order/pop-w-before-x-when-y-int" 1 #[.null, .cell Cell.empty, intV 2],
    mkShiftInputCase "/intov/nan/program-y" 1 #[.num 7, .num 3, .nan],
    mkShiftInputCase "/intov/nan/program-w" 1 #[.num 7, .nan, .num 5],
    mkShiftInputCase "/intov/nan/program-x" 1 #[.nan, .num 3, .num 5],
    mkShiftInputCase "/intov/nan/program-all" 1 #[.nan, .nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op" 1 #[.num (maxInt257 + 1), .num 3, .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-w-before-op" 1 #[.num 7, .num (minInt257 - 1), .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op" 1 #[.num 7, .num 3, .num (pow2 257)],
    mkShiftInputCase "/error-order/pushint-overflow-all-before-op" 1
      #[.num (pow2 257), .num (-(pow2 257)), .num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 5]
      #[.pushInt (.num lshiftHashAddDivModrSetGasExact), .tonEnvOp .setGasLimit, lshiftHashAddDivModrGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 5]
      #[.pushInt (.num lshiftHashAddDivModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashAddDivModrGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020861
      count := 700
      gen := genLshiftHashAddDivModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_ADDDIVMODR
