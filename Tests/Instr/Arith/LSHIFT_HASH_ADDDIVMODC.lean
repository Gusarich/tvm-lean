import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_ADDDIVMODC

/-
LSHIFT#ADDDIVMODC branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 1 true false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, `0xa9d0..0xa9d2` with immediate `z` in `[1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash decode family `0xa9d0..0xa9d2`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type behavior, non-quiet `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, ceil rounding)

Branch/terminal counts used for this suite (`d=3`, `roundMode=1`, `add=true`,
`quiet=false`, `zOpt=some`):
- Lean specialization: 9 branch sites / 11 terminal outcomes
  (dispatch/fallback; arity precheck; immediate-shift range gate; `y` pop type;
   `w` pop type; `x` pop type; numeric-vs-invalid split; divisor-zero split;
   quotient push success-vs-`intOv` before remainder push).
- C++ specialization: 8 branch sites / 11 aligned terminal outcomes
  (`check_underflow(3)`; const-shift validity; `pop_int` order `y→w→x`;
   invalid-input funnel; divisor-zero split; quotient push fit-vs-overflow).

Key risk areas covered:
- ceil rounding for sign-mixed and near-zero inexact `(x << z) + w` over `y`;
- fixed immediate boundaries (`z = 1`, `z = 256`) plus hash decode correctness;
- explicit pop order (`y` first, then `w`, then `x`) and below-stack preservation;
- underflow/type/error ordering, including malformed-immediate range-gate
  precedence in direct-handler tests;
- non-quiet NaN/invalid funnels (`divzero`, NaN operands, overflowed quotient);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFT#ADDDIVMODC`.
-/

private def lshiftHashAddDivModcId : InstrId := { name := "LSHIFT#ADDDIVMODC" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkLshiftHashAddDivModcInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 3 1 true false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftHashAddDivModcId
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
  mkCase name stack #[mkLshiftHashAddDivModcInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkLshiftHashAddDivModcInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runLshiftHashAddDivModCDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashAddDivModcInstr shift) stack

private def runLshiftHashAddDivModCDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6622)) stack

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

private def lshiftHashAddDivModcGasProbeInstr : Instr :=
  mkLshiftHashAddDivModcInstr 7

private def lshiftHashAddDivModcSetGasExact : Int :=
  computeExactGasBudget lshiftHashAddDivModcGasProbeInstr

private def lshiftHashAddDivModcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashAddDivModcGasProbeInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def ceilXPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def addendPool : Array Int :=
  #[-5, -3, -1, 0, 1, 3, 5]

private def ceilYPool : Array Int :=
  #[-6, -5, -4, -3, -2, -1, 1, 2, 3, 4, 5, 6]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def classifyLshiftHashAddDivModc (x w y : Int) (shift : Nat) : String :=
  if y = 0 then
    "divzero"
  else
    let tmp := x * intPow2 shift + w
    let (q, r) := divModRound tmp y 1
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else
      "inexact"

private def mkFiniteFuzzCase
    (shape : Nat)
    (x w y : Int)
    (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashAddDivModc x w y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x, intV w, intV y]

private def genLshiftHashAddDivModCFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y0, r4) := pickInt257Boundary r3
      let y := if y0 = 0 then 1 else y0
      let (shift, r5) := pickShiftBoundary r4
      (mkFiniteFuzzCase shape x w y shift, r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftInRange r4
      (mkFiniteFuzzCase shape x w y shift, r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x w 0 shift, r4)
    else if shape = 3 then
      let (x, r2) := pickIntFromPool ceilXPool rng1
      let (w, r3) := pickIntFromPool addendPool r2
      (mkFiniteFuzzCase shape x w 3 1, r3)
    else if shape = 4 then
      let (x, r2) := pickIntFromPool ceilXPool rng1
      let (w, r3) := pickIntFromPool addendPool r2
      (mkFiniteFuzzCase shape x w (-3) 1, r3)
    else if shape = 5 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/overflow/max-shift1-add2-div1"
        1 #[.num maxInt257, .num 2, .num 1], rng1)
    else if shape = 6 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/overflow/min-shift1-add0-div1"
        1 #[.num minInt257, .num 0, .num 1], rng1)
    else if shape = 7 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/overflow/one-shift256-add1-div1"
        256 #[.num 1, .num 1, .num 1], rng1)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item" shift #[intV x], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/two-items" shift #[intV x, intV w], r4)
    else if shape = 11 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-two-non-int"
        shift #[.null, .cell Cell.empty], r2)
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
      let (wLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-w-when-both-non-int"
        shift #[intV x, wLike, .null], r4)
    else if shape = 16 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftBoundary r2
      let (xLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-x-when-y-int"
        shift #[xLike, .cell Cell.empty, intV y], r4)
    else if shape = 17 then
      let (x, r2) := pickIntFromPool ceilXPool rng1
      let (w, r3) := pickIntFromPool addendPool r2
      let (y, r4) := pickIntFromPool ceilYPool r3
      let y' := if y = 0 then 1 else y
      let (shift, r5) := randNat r4 1 4
      let (pickNull, r6) := randBool r5
      let below : Value := if pickNull then .null else .cell Cell.empty
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift #[below, intV x, intV w, intV y'], r6)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/y-via-program"
        shift #[.num x, .num w, .nan], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/w-via-program"
        shift #[.num x, .nan, .num y], r4)
    else if shape = 20 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/x-via-program"
        shift #[.nan, .num w, .num y], r4)
    else if shape = 21 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/all-via-program"
        shift #[.nan, .nan, .nan], r2)
    else if shape = 22 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xOut, .num w, .num y], r5)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        shift #[.num x, .num wOut, .num y], r5)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (yOut, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift #[.num x, .num w, .num yOut], r5)
    else if shape = 25 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/boundary/shift256"
        256 #[.num 1, .num 0, .num 2], rng1)
    else if shape = 26 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/divzero/shift256"
        256 #[.num 9, .num (-7), .num 0], rng1)
    else if shape = 27 then
      (mkShiftCase s!"/fuzz/shape-{shape}/range/shift0-before-pop"
        0 #[.null, .cell Cell.empty, intV 1], rng1)
    else if shape = 28 then
      (mkShiftCase s!"/fuzz/shape-{shape}/range/shift257-before-pop"
        257 #[.cell Cell.empty, .null, intV 1], rng1)
    else if shape = 29 then
      let (x, r2) := pickIntFromPool ceilXPool rng1
      let (w, r3) := pickIntFromPool addendPool r2
      let (y, r4) := pickIntFromPool ceilYPool r3
      let y' := if y = 0 then 1 else y
      let (shift, r5) := pickShiftBoundary r4
      (mkFiniteFuzzCase shape x w y' shift, r5)
    else if shape = 30 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (yOut, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        shift #[.num xOut, .num wOut, .num yOut], r5)
    else
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-range-shift0-empty"
        0 #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashAddDivModcId
  unit := #[
    { name := "/unit/direct/ceil-sign-shift-and-addend-invariants"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 5, 1, 4, -3),
            (-7, 3, 5, 1, -2, -1),
            (7, 3, -5, 1, -3, 2),
            (-7, -3, -5, 1, 4, 3),
            (1, 0, 3, 1, 1, -1),
            (-1, 0, 3, 1, 0, -2),
            (5, -3, 3, 2, 6, -1),
            (-5, 3, 3, 2, -5, -2),
            (5, 3, -3, 2, -7, 2),
            (-5, -3, -3, 2, 8, 1),
            (13, -7, 3, 2, 15, 0),
            (-13, 7, 3, 2, -15, 0),
            (0, 9, 7, 123, 2, -5)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/w={w}/y={y}/z={shift}"
                (runLshiftHashAddDivModCDirect shift #[intV x, intV w, intV y])
                #[intV q, intV r] }
    ,
    { name := "/unit/direct/boundary-success-and-pop-order"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 0, 2, 1, maxInt257, 0),
            (minInt257, 0, 2, 1, minInt257, 0),
            (minInt257 + 1, 0, -2, 1, maxInt257, 0),
            (maxInt257, -1, 2, 1, maxInt257, -1),
            (minInt257, 1, 2, 1, minInt257 + 1, -1),
            (maxInt257, 0, -2, 1, minInt257 + 1, 0),
            (1, 0, 2, 256, pow2 255, 0),
            (-1, 0, 2, 256, -(pow2 255), 0),
            (1, 1, 2, 256, (pow2 255) + 1, -1),
            (0, 5, 7, 256, 1, -2)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectOkStack s!"/unit/boundary/x={x}/w={w}/y={y}/z={shift}"
                (runLshiftHashAddDivModCDirect shift #[intV x, intV w, intV y])
                #[intV q, intV r]
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runLshiftHashAddDivModCDirect 1 #[.null, intV 7, intV 3, intV 5])
          #[.null, intV 4, intV (-3)]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runLshiftHashAddDivModCDirect 2 #[.cell Cell.empty, intV (-7), intV 2, intV 3])
          #[.cell Cell.empty, intV (-8), intV (-2)] }
    ,
    { name := "/unit/error/divzero-overflow-underflow-type-and-order"
      run := do
        expectErr "/unit/error/divzero/nonzero-over-zero"
          (runLshiftHashAddDivModCDirect 1 #[intV 7, intV 3, intV 0]) .intOv
        expectErr "/unit/error/overflow/max-shift1-add2-div1"
          (runLshiftHashAddDivModCDirect 1 #[intV maxInt257, intV 2, intV 1]) .intOv
        expectErr "/unit/error/overflow/min-shift1-add0-div1"
          (runLshiftHashAddDivModCDirect 1 #[intV minInt257, intV 0, intV 1]) .intOv
        expectErr "/unit/error/overflow/one-shift256-add1-div1"
          (runLshiftHashAddDivModCDirect 256 #[intV 1, intV 1, intV 1]) .intOv
        expectErr "/unit/error/underflow/empty"
          (runLshiftHashAddDivModCDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow/one-item"
          (runLshiftHashAddDivModCDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow/two-items"
          (runLshiftHashAddDivModCDirect 1 #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-two-non-int"
          (runLshiftHashAddDivModCDirect 1 #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/error/type/y-top-non-int"
          (runLshiftHashAddDivModCDirect 1 #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type/w-second-non-int"
          (runLshiftHashAddDivModCDirect 1 #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type/x-third-non-int"
          (runLshiftHashAddDivModCDirect 1 #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error-order/pop-y-before-w-when-both-non-int"
          (runLshiftHashAddDivModCDirect 1 #[intV 1, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-w-before-x-when-y-int"
          (runLshiftHashAddDivModCDirect 1 #[.null, .cell Cell.empty, intV 1]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-before-pop"
      run := do
        expectErr "/unit/error/range/shift0-before-y-pop"
          (runLshiftHashAddDivModCDirect 0 #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "/unit/error/range/shift257-before-y-pop"
          (runLshiftHashAddDivModCDirect 257 #[.cell Cell.empty, .null, intV 1]) .rangeChk
        expectErr "/unit/error/underflow/shift0-empty-before-range-gate"
          (runLshiftHashAddDivModCDirect 0 #[]) .stkUnd
        expectErr "/unit/error/underflow/shift257-one-item-before-range-gate"
          (runLshiftHashAddDivModCDirect 257 #[intV 1]) .stkUnd }
    ,
    { name := "/unit/opcode/decode-hash-sequence"
      run := do
        let instr1 := mkLshiftHashAddDivModcInstr 1
        let instr256 := mkLshiftHashAddDivModcInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-adddivmodc-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/lshift-hash-adddivmodc-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end-expected-exhausted-got-{s3.bitsRemaining}") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-adddivmodc-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashAddDivModCDispatchFallback #[]) #[intV 6622] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/ceil/sign/pos-pos-pos-z1" 1 #[.num 7, .num 3, .num 5],
    mkShiftInputCase "/ok/ceil/sign/neg-pos-pos-z1" 1 #[.num (-7), .num 3, .num 5],
    mkShiftInputCase "/ok/ceil/sign/pos-pos-negdiv-z1" 1 #[.num 7, .num 3, .num (-5)],
    mkShiftInputCase "/ok/ceil/sign/neg-neg-negdiv-z1" 1 #[.num (-7), .num (-3), .num (-5)],
    mkShiftInputCase "/ok/ceil/sign/near-zero-pos-divisor-z1" 1 #[.num 1, .num 0, .num 3],
    mkShiftInputCase "/ok/ceil/sign/near-zero-neg-x-pos-divisor-z1" 1 #[.num (-1), .num 0, .num 3],
    mkShiftInputCase "/ok/ceil/addend/cancel-positive-z2" 2 #[.num 13, .num (-7), .num 3],
    mkShiftInputCase "/ok/ceil/addend/cancel-negative-z2" 2 #[.num (-13), .num 7, .num 3],
    mkShiftInputCase "/ok/ceil/addend/positive-w-only-z123" 123 #[.num 0, .num 9, .num 7],
    mkShiftInputCase "/ok/ceil/addend/negative-w-only-z123" 123 #[.num 0, .num (-9), .num 7],
    mkShiftInputCase "/ok/exact/positive-z2" 2 #[.num 5, .num (-5), .num 3],
    mkShiftInputCase "/ok/exact/negative-z2" 2 #[.num (-5), .num 5, .num 3],
    mkShiftInputCase "/ok/boundary/max-shift1-div2" 1 #[.num maxInt257, .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/min-shift1-div2" 1 #[.num minInt257, .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift1-div-neg2"
      1 #[.num (minInt257 + 1), .num 0, .num (-2)],
    mkShiftInputCase "/ok/boundary/max-shift1-add-neg1-div2"
      1 #[.num maxInt257, .num (-1), .num 2],
    mkShiftInputCase "/ok/boundary/min-shift1-add-one-div2"
      1 #[.num minInt257, .num 1, .num 2],
    mkShiftInputCase "/ok/boundary/max-shift1-div-neg2"
      1 #[.num maxInt257, .num 0, .num (-2)],
    mkShiftInputCase "/ok/boundary/one-shift256-div2"
      256 #[.num 1, .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/negone-shift256-div2"
      256 #[.num (-1), .num 0, .num 2],
    mkShiftInputCase "/ok/boundary/one-shift256-add1-div2"
      256 #[.num 1, .num 1, .num 2],
    mkShiftCase "/ok/order/below-null-preserved"
      1 #[.null, intV 7, intV 3, intV 5],
    mkShiftCase "/ok/order/below-cell-preserved"
      2 #[.cell Cell.empty, intV (-7), intV 2, intV 3],
    mkShiftInputCase "/divzero/nonzero-over-zero" 1 #[.num 7, .num 3, .num 0],
    mkShiftInputCase "/divzero/zero-over-zero-shift256" 256 #[.num 0, .num 0, .num 0],
    mkShiftInputCase "/overflow/max-shift1-add2-div1"
      1 #[.num maxInt257, .num 2, .num 1],
    mkShiftInputCase "/overflow/min-shift1-add0-div1"
      1 #[.num minInt257, .num 0, .num 1],
    mkShiftInputCase "/overflow/one-shift256-add1-div1"
      256 #[.num 1, .num 1, .num 1],
    mkShiftInputCase "/overflow/max-shift1-add1-div2"
      1 #[.num maxInt257, .num 1, .num 2],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/underflow/two-items" 1 #[intV 1, intV 2],
    mkShiftCase "/error-order/underflow-before-type-two-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftCase "/type/y-top-non-int" 1 #[intV 1, intV 2, .null],
    mkShiftCase "/type/w-second-non-int" 1 #[intV 1, .null, intV 2],
    mkShiftCase "/type/x-third-non-int" 1 #[.null, intV 1, intV 2],
    mkShiftCase "/error-order/pop-y-before-w-when-both-non-int"
      1 #[intV 1, .cell Cell.empty, .null],
    mkShiftCase "/error-order/pop-w-before-x-when-y-int"
      1 #[.null, .cell Cell.empty, intV 1],
    mkShiftCase "/error-order/range-shift0-before-pop"
      0 #[.null, .cell Cell.empty, intV 1],
    mkShiftCase "/error-order/range-shift257-before-pop"
      257 #[.cell Cell.empty, .null, intV 1],
    mkShiftInputCase "/nan/y-via-program" 1 #[.num 7, .num 3, .nan],
    mkShiftInputCase "/nan/w-via-program" 1 #[.num 7, .nan, .num 5],
    mkShiftInputCase "/nan/x-via-program" 1 #[.nan, .num 3, .num 5],
    mkShiftInputCase "/nan/all-via-program" 1 #[.nan, .nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-high-before-op"
      1 #[.num (maxInt257 + 1), .num 2, .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-x-low-before-op"
      1 #[.num (minInt257 - 1), .num 2, .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-w-high-before-op"
      1 #[.num 2, .num (maxInt257 + 1), .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-y-low-before-op"
      1 #[.num 2, .num 3, .num (minInt257 - 1)],
    mkShiftInputCase "/error-order/pushint-overflow-all-before-op"
      1 #[.num (pow2 257), .num (-(pow2 257)), .num (maxInt257 + 2)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 5]
      #[.pushInt (.num lshiftHashAddDivModcSetGasExact),
        .tonEnvOp .setGasLimit,
        lshiftHashAddDivModcGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 5]
      #[.pushInt (.num lshiftHashAddDivModcSetGasExactMinusOne),
        .tonEnvOp .setGasLimit,
        lshiftHashAddDivModcGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020892
      count := 700
      gen := genLshiftHashAddDivModCFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_ADDDIVMODC
