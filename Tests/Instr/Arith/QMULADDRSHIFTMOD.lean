import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULADDRSHIFTMOD

/-
QMULADDRSHIFTMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true true 3 (-1) true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, stack underflow/type behavior)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-shrmod decode range `0xb7a9a0..0xb7a9a2`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (QMULADDRSHIFTMOD specialization):
- Lean: ~10 branch sites / ~18 terminal outcomes
  (dispatch fallback; arity precheck; runtime shift parse/type/range;
   pop order `shift→w→y→x`; quiet bad-shift NaN funnel; numeric-vs-invalid split;
   fixed floor round-mode path; fixed `d=3` two-result push; quiet fit overflow on `q`).
- C++: ~9 branch sites / ~16 aligned outcomes
  (`check_underflow`; runtime shift gate with quiet-range relaxation;
   ordered pops; GV13 invalid-input funnel; `tmp.add_mul + addend` path;
   quotient/remainder push order with quiet `push_int_quiet` overflow-to-NaN).

Key risk areas covered:
- floor quotient/remainder invariants for `(x * y + w) / 2^z`, including sign-mixed inputs;
- quiet runtime-shift behavior: out-of-range/NaN shift returns NaN-pair (no `rangeChk`);
- strict pop/error ordering (shift first, then `w`, then `y`, then `x`);
- quiet NaN funnel for invalid operands and bad shift;
- quiet overflow at `z=0` where `q` can become NaN while `r` remains numeric (`0` or `1`);
- oracle serialization safety: NaN and 257-bit-out-of-range integers injected via prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QMULADDRSHIFTMOD`.
-/

private def qmuladdrshiftmodId : InstrId := { name := "QMULADDRSHIFTMOD" }

private def qmuladdrshiftmodInstr : Instr :=
  .arithExt (.shrMod true true 3 (-1) true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmuladdrshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmuladdrshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmuladdrshiftmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def mkInputCase
    (name : String)
    (x y w shift : IntVal)
    (programSuffix : Array Instr := #[qmuladdrshiftmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCaseFromIntVals name #[x, y, w, shift] programSuffix below gasLimits fuel

private def mkShiftInjectedCase (name : String) (x y w : Int) (shift : IntVal) : OracleCase :=
  mkCase name #[intV x, intV y, intV w] #[.pushInt shift, qmuladdrshiftmodInstr]

private def runQMulAddRShiftModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmuladdrshiftmodInstr stack

private def runQMulAddRShiftModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9487)) stack

private def qmuladdrshiftmodSetGasExact : Int :=
  computeExactGasBudget qmuladdrshiftmodInstr

private def qmuladdrshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmuladdrshiftmodInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftValid (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickShiftBoundary rng1
  else
    let (shift, rng2) := randNat rng1 0 256
    (Int.ofNat shift, rng2)

private def pickShiftInvalid (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftInvalidPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQMulAddRShiftModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftBoundary r4
      (mkCase s!"/fuzz/shape-{shape}/ok/boundary-triplet"
        #[intV x, intV y, intV w, intV shift], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftValid r4
      (mkCase s!"/fuzz/shape-{shape}/ok/signed-random"
        #[intV x, intV y, intV w, intV shift], r5)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftValid r4
      (mkCase s!"/fuzz/shape-{shape}/ok/x-boundary"
        #[intV x, intV y, intV w, intV shift], r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftValid r4
      (mkCase s!"/fuzz/shape-{shape}/ok/y-boundary"
        #[intV x, intV y, intV w, intV shift], r5)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftValid r4
      (mkCase s!"/fuzz/shape-{shape}/ok/w-boundary"
        #[intV x, intV y, intV w, intV shift], r5)
    else if shape = 5 then
      let (x, r2) := pickFromPool smallSignedPool rng1
      let (y, r3) := pickFromPool smallSignedPool r2
      let (w, r4) := pickFromPool smallSignedPool r3
      let (shift, r5) := pickFromPool #[0, 1, 2, 3, 4, 5, 6, 7, 8] r4
      (mkCase s!"/fuzz/shape-{shape}/ok/small-signed"
        #[intV x, intV y, intV w, intV shift], r5)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-times-one-plus-one-shift0"
        #[intV maxInt257, intV 1, intV 1, intV 0], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-times-one-minus-one-shift0"
        #[intV minInt257, intV 1, intV (-1), intV 0], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-quotient-only-remainder-one"
        #[intV maxInt257, intV maxInt257, intV 0, intV 1], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInvalid r4
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/shift-invalid-via-program" x y w (.num shift), r5)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/shift-nan-via-program" x y w .nan, r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV y, intV w, nonInt], r5)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/w-second-after-shift"
        #[intV x, intV y, nonInt, intV shift], r5)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/y-third-after-shift"
        #[intV x, nonInt, intV w, intV shift], r5)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/x-fourth-after-shift"
        #[nonInt, intV y, intV w, intV shift], r5)
    else if shape = 15 then
      let (pick, r2) := randNat rng1 0 3
      let stack :=
        if pick = 0 then
          #[]
        else if pick = 1 then
          #[intV 1]
        else if pick = 2 then
          #[intV 1, intV 2]
        else
          #[intV 1, intV 2, intV 3]
      (mkCase s!"/fuzz/shape-{shape}/underflow" stack, r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-w-via-program"
        (.num x) (.num y) .nan (.num shift), r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-y-via-program"
        (.num x) .nan (.num w) (.num shift), r4)
    else if shape = 18 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-x-via-program"
        .nan (.num y) (.num w) (.num shift), r4)
    else if shape = 19 then
      let (shift, r2) := pickShiftValid rng1
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-all-operands-via-program"
        .nan .nan .nan (.num shift), r2)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-before-w-type-via-program"
        #[intV x, intV y, .null] #[.pushInt (.num 300), qmuladdrshiftmodInstr], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-before-y-type-via-program"
        #[intV x, .null, intV w] #[.pushInt (.num 300), qmuladdrshiftmodInstr], r3)
    else if shape = 22 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-before-x-type-via-program"
        #[.null, intV y, intV w] #[.pushInt (.num 300), qmuladdrshiftmodInstr], r3)
    else if shape = 23 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftValid r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num y) (.num w) (.num shift), r5)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftValid r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        (.num x) (.num yOut) (.num w) (.num shift), r5)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wOut, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftValid r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        (.num x) (.num y) (.num wOut) (.num shift), r5)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let shiftOut : Int := maxInt257 + 1
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        (.num x) (.num y) (.num w) (.num shiftOut), r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmuladdrshiftmodId
  unit := #[
    { name := "/unit/ok/floor-quot-rem-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 1, 2, 9, 0),
            (-7, 5, 1, 2, -9, 2),
            (7, -5, 1, 2, -9, 2),
            (-7, -5, 1, 2, 9, 0),
            (1, -2, 1, 1, -1, 1),
            (-1, 2, 1, 1, -1, 1),
            (9, 0, 5, 3, 0, 5),
            (0, 9, -3, 5, -1, 29),
            (5, 3, 0, 0, 15, 0),
            (-5, 3, 2, 0, -13, 0),
            (1, 1, 1, 256, 0, 2)
          ]
        for c in checks do
          let (x, y, w, shift, q, r) := c
          expectOkStack s!"/unit/ok/x={x}/y={y}/w={w}/shift={shift}"
            (runQMulAddRShiftModDirect #[intV x, intV y, intV w, intV shift])
            #[intV q, intV r]
        expectOkStack "/unit/ok/below-null-preserved"
          (runQMulAddRShiftModDirect #[.null, intV 7, intV 5, intV 1, intV 2])
          #[.null, intV 9, intV 0]
        expectOkStack "/unit/ok/below-cell-preserved"
          (runQMulAddRShiftModDirect #[.cell Cell.empty, intV (-7), intV 5, intV 1, intV 2])
          #[.cell Cell.empty, intV (-9), intV 2] }
    ,
    { name := "/unit/ok/boundary-shifts-and-extremes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 0, maxInt257, 0),
            (minInt257, 1, 0, 0, minInt257, 0),
            (maxInt257, 1, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 1, 0, minInt257 + 1, 0),
            (maxInt257, maxInt257, maxInt257, 256, maxInt257, 0),
            (minInt257, minInt257, minInt257, 256, maxInt257, 0),
            (minInt257, 1, 1, 256, -1, 1),
            (maxInt257, -1, -1, 256, -1, 0),
            (maxInt257, minInt257, maxInt257, 256, minInt257 + 1, maxInt257)
          ]
        for c in checks do
          let (x, y, w, shift, q, r) := c
          expectOkStack s!"/unit/ok/boundary/x={x}/y={y}/w={w}/shift={shift}"
            (runQMulAddRShiftModDirect #[intV x, intV y, intV w, intV shift])
            #[intV q, intV r] }
    ,
    { name := "/unit/quiet/nan-range-and-overflow-funnels"
      run := do
        expectOkStack "/unit/quiet/overflow-max-times-one-plus-one-shift0"
          (runQMulAddRShiftModDirect #[intV maxInt257, intV 1, intV 1, intV 0])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow-min-times-one-minus-one-shift0"
          (runQMulAddRShiftModDirect #[intV minInt257, intV 1, intV (-1), intV 0])
          #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow-quotient-only-remainder-one"
          (runQMulAddRShiftModDirect #[intV maxInt257, intV maxInt257, intV 0, intV 1])
          #[.int .nan, intV 1]
        expectOkStack "/unit/quiet/shift-negative-yields-nan-pair"
          (runQMulAddRShiftModDirect #[intV 7, intV 5, intV 3, intV (-1)])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/shift-over256-yields-nan-pair"
          (runQMulAddRShiftModDirect #[intV 7, intV 5, intV 3, intV 257])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/shift-nan-yields-nan-pair"
          (runQMulAddRShiftModDirect #[intV 7, intV 5, intV 3, .int .nan])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-w"
          (runQMulAddRShiftModDirect #[intV 7, intV 5, .int .nan, intV 4])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQMulAddRShiftModDirect #[intV 7, .int .nan, intV 3, intV 4])
          #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQMulAddRShiftModDirect #[.int .nan, intV 5, intV 3, intV 4])
          #[.int .nan, .int .nan] }
    ,
    { name := "/unit/error-order/underflow-and-type-precedence"
      run := do
        expectErr "/unit/error/underflow-empty" (runQMulAddRShiftModDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-one-arg" (runQMulAddRShiftModDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-args" (runQMulAddRShiftModDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow-three-args" (runQMulAddRShiftModDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/unit/error/underflow-before-shift-type-check"
          (runQMulAddRShiftModDirect #[intV 1, intV 2, .null]) .stkUnd
        expectErr "/unit/error/type-shift-top-null"
          (runQMulAddRShiftModDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/unit/error/type-shift-top-cell"
          (runQMulAddRShiftModDirect #[intV 1, intV 2, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type-w-after-shift"
          (runQMulAddRShiftModDirect #[intV 1, intV 2, .null, intV 4]) .typeChk
        expectErr "/unit/error/type-y-after-shift-and-w"
          (runQMulAddRShiftModDirect #[intV 1, .null, intV 3, intV 4]) .typeChk
        expectErr "/unit/error/type-x-last"
          (runQMulAddRShiftModDirect #[.null, intV 2, intV 3, intV 4]) .typeChk
        expectErr "/unit/error/order/bad-shift-does-not-mask-w-type"
          (runQMulAddRShiftModDirect #[intV 1, intV 2, .null, intV 300]) .typeChk
        expectErr "/unit/error/order/bad-shift-does-not-mask-y-type"
          (runQMulAddRShiftModDirect #[intV 1, .null, intV 3, intV 300]) .typeChk
        expectErr "/unit/error/order/bad-shift-does-not-mask-x-type"
          (runQMulAddRShiftModDirect #[.null, intV 2, intV 3, intV 300]) .typeChk }
    ,
    { name := "/unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQMulAddRShiftModDispatchFallback #[]) #[intV 9487] }
  ]
  oracle := #[
    mkCase "/ok/floor/basic-pos-pos" #[intV 7, intV 5, intV 1, intV 2],
    mkCase "/ok/floor/basic-neg-pos" #[intV (-7), intV 5, intV 1, intV 2],
    mkCase "/ok/floor/basic-pos-neg" #[intV 7, intV (-5), intV 1, intV 2],
    mkCase "/ok/floor/basic-neg-neg" #[intV (-7), intV (-5), intV 1, intV 2],
    mkCase "/ok/floor/shift-zero-pos" #[intV 5, intV 3, intV 0, intV 0],
    mkCase "/ok/floor/shift-zero-neg" #[intV (-5), intV 3, intV 2, intV 0],
    mkCase "/ok/floor/y-zero" #[intV 9, intV 0, intV 5, intV 3],
    mkCase "/ok/floor/x-zero-neg-addend" #[intV 0, intV 9, intV (-3), intV 5],
    mkCase "/ok/floor/shift-256-small" #[intV 1, intV 1, intV 1, intV 256],
    mkCase "/ok/boundary/max-times-one-shift0" #[intV maxInt257, intV 1, intV 0, intV 0],
    mkCase "/ok/boundary/min-times-one-shift0" #[intV minInt257, intV 1, intV 0, intV 0],
    mkCase "/ok/boundary/max-times-one-minus-one-shift0" #[intV maxInt257, intV 1, intV (-1), intV 0],
    mkCase "/ok/boundary/min-times-one-plus-one-shift0" #[intV minInt257, intV 1, intV 1, intV 0],
    mkCase "/ok/boundary/max-times-max-plus-max-shift256"
      #[intV maxInt257, intV maxInt257, intV maxInt257, intV 256],
    mkCase "/ok/boundary/min-times-min-plus-min-shift256"
      #[intV minInt257, intV minInt257, intV minInt257, intV 256],
    mkCase "/ok/boundary/min-times-one-plus-one-shift256"
      #[intV minInt257, intV 1, intV 1, intV 256],
    mkCase "/ok/boundary/max-times-neg1-plus-neg1-shift256"
      #[intV maxInt257, intV (-1), intV (-1), intV 256],
    mkCase "/ok/boundary/max-times-min-plus-max-shift256"
      #[intV maxInt257, intV minInt257, intV maxInt257, intV 256],
    mkCase "/quiet/overflow-max-times-one-plus-one-shift0"
      #[intV maxInt257, intV 1, intV 1, intV 0],
    mkCase "/quiet/overflow-min-times-one-minus-one-shift0"
      #[intV minInt257, intV 1, intV (-1), intV 0],
    mkCase "/quiet/overflow-quotient-only-remainder-one"
      #[intV maxInt257, intV maxInt257, intV 0, intV 1],
    mkCase "/quiet/shift-negative" #[intV 7, intV 5, intV 3, intV (-1)],
    mkCase "/quiet/shift-over256" #[intV 7, intV 5, intV 3, intV 257],
    mkShiftInjectedCase "/quiet/shift-nan-via-program" 7 5 3 .nan,
    mkInputCase "/quiet/nan-w-via-program" (.num 7) (.num 5) .nan (.num 4),
    mkInputCase "/quiet/nan-y-via-program" (.num 7) .nan (.num 3) (.num 4),
    mkInputCase "/quiet/nan-x-via-program" .nan (.num 5) (.num 3) (.num 4),
    mkInputCase "/quiet/nan-all-via-program" .nan .nan .nan (.num 4),
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-shift-type-three-args" #[intV 1, intV 2, .null],
    mkCase "/type/pop-shift-first-null" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 1, intV 2, intV 3, .cell Cell.empty],
    mkCase "/type/pop-w-second-null" #[intV 1, intV 2, .null, intV 4],
    mkCase "/type/pop-y-third-null" #[intV 1, .null, intV 3, intV 4],
    mkCase "/type/pop-x-fourth-null" #[.null, intV 2, intV 3, intV 4],
    mkCase "/error-order/bad-shift-before-w-type" #[intV 1, intV 2, .null, intV 300],
    mkCase "/error-order/bad-shift-before-y-type" #[intV 1, .null, intV 3, intV 300],
    mkCase "/error-order/bad-shift-before-x-type" #[.null, intV 2, intV 3, intV 300],
    mkCase "/error-order/bad-shift-before-w-type-via-program"
      #[intV 1, intV 2, .null] #[.pushInt (.num 300), qmuladdrshiftmodInstr],
    mkCase "/error-order/bad-shift-before-y-type-via-program"
      #[intV 1, .null, intV 3] #[.pushInt (.num 300), qmuladdrshiftmodInstr],
    mkCase "/error-order/bad-shift-before-x-type-via-program"
      #[.null, intV 2, intV 3] #[.pushInt (.num 300), qmuladdrshiftmodInstr],
    mkInputCase "/error-order/pushint-overflow-x-high-before-op"
      (.num (maxInt257 + 1)) (.num 5) (.num 3) (.num 2),
    mkInputCase "/error-order/pushint-overflow-x-low-before-op"
      (.num (minInt257 - 1)) (.num 5) (.num 3) (.num 2),
    mkInputCase "/error-order/pushint-overflow-y-high-before-op"
      (.num 5) (.num (maxInt257 + 1)) (.num 3) (.num 2),
    mkInputCase "/error-order/pushint-overflow-w-high-before-op"
      (.num 5) (.num 3) (.num (maxInt257 + 1)) (.num 2),
    mkInputCase "/error-order/pushint-overflow-shift-high-before-op"
      (.num 5) (.num 3) (.num 2) (.num (maxInt257 + 1)),
    mkInputCase "/error-order/pushint-overflow-shift-low-before-op"
      (.num 5) (.num 3) (.num 2) (.num (minInt257 - 1)),
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3, intV 2]
      #[.pushInt (.num qmuladdrshiftmodSetGasExact), .tonEnvOp .setGasLimit, qmuladdrshiftmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3, intV 2]
      #[.pushInt (.num qmuladdrshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmuladdrshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020860
      count := 700
      gen := genQMulAddRShiftModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULADDRSHIFTMOD
