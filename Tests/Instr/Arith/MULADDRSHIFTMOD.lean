import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULADDRSHIFTMOD

/-
MULADDRSHIFTMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true true 3 (-1) false none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, non-quiet `intOv` behavior)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (runtime-shift `MULADDRSHIFTMOD` decode in `0xa9b0..0xa9b2`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int`)

Branch counts used for this suite (MULADDRSHIFTMOD specialization):
- Lean: ~10 branch sites / ~18 terminal outcomes
  (arity precheck; runtime shift pop/range gate; ordered pops `shift→w→y→x`;
   numeric-vs-NaN path on `x,y,w`; floor round-mode path with `d=3`;
   non-quiet `pushIntQuiet` overflow gate on quotient).
- C++: ~9 branch sites / ~16 aligned outcomes
  (`check_underflow`; stack/runtime shift gate; ordered pops; invalid-input funnel;
   `tmp = x*y + w` combined-op path; quotient/remainder push with non-quiet overflow).

Key risk areas covered:
- combined-op boundaries for `(x * y + w) / 2^z`, including exact and near-exact pairs;
- intermediate precision cliffs where `x*y` exceeds 257 bits before shifting;
- strict error order: underflow, then shift range/type, then `w`, then `y`, then `x`;
- non-quiet NaN/out-of-range handling (`intOv`) with oracle/fuzz injection via prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; MULADDRSHIFTMOD`.
-/

private def muladdrshiftmodId : InstrId := { name := "MULADDRSHIFTMOD" }

private def muladdrshiftmodInstr : Instr :=
  .arithExt (.shrMod true true 3 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muladdrshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := muladdrshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[muladdrshiftmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def mkInputCase
    (name : String)
    (x y w shift : IntVal)
    (programSuffix : Array Instr := #[muladdrshiftmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCaseFromIntVals name #[x, y, w, shift] programSuffix below gasLimits fuel

private def mkShiftInjectedCase (name : String) (x y w : Int) (shift : IntVal) : OracleCase :=
  mkCase name #[intV x, intV y, intV w] #[.pushInt shift, muladdrshiftmodInstr]

private def runMulAddRShiftModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt muladdrshiftmodInstr stack

private def runMulAddRShiftModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9541)) stack

private def muladdrshiftmodSetGasExact : Int :=
  computeExactGasBudget muladdrshiftmodInstr

private def muladdrshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muladdrshiftmodInstr

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

private def genMulAddRShiftModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 31
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
      (mkCase s!"/fuzz/shape-{shape}/overflow/max-times-one-plus-one-shift0"
        #[intV maxInt257, intV 1, intV 1, intV 0], rng1)
    else if shape = 7 then
      (mkCase s!"/fuzz/shape-{shape}/overflow/min-times-one-minus-one-shift0"
        #[intV minInt257, intV 1, intV (-1), intV 0], rng1)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/overflow/intermediate-min-times-min-shift256"
        #[intV minInt257, intV minInt257, intV 0, intV 256], rng1)
    else if shape = 9 then
      (mkCase s!"/fuzz/shape-{shape}/ok/intermediate-max-times-max-plus-max-shift256"
        #[intV maxInt257, intV maxInt257, intV maxInt257, intV 256], rng1)
    else if shape = 10 then
      (mkCase s!"/fuzz/shape-{shape}/ok/intermediate-max-times-max-plus-zero-shift256"
        #[intV maxInt257, intV maxInt257, intV 0, intV 256], rng1)
    else if shape = 11 then
      (mkCase s!"/fuzz/shape-{shape}/ok/intermediate-min-times-min-plus-min-shift256"
        #[intV minInt257, intV minInt257, intV minInt257, intV 256], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftInvalid r4
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/range/shift-invalid-via-program" x y w (.num shift), r5)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/range/shift-nan-via-program" x y w .nan, r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV y, intV w, nonInt], r5)
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
          #[intV 1, intV 2, .null]
      (mkCase s!"/fuzz/shape-{shape}/underflow" stack, r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/w-second-after-shift"
        #[intV x, intV y, nonInt, intV shift], r5)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/y-third-after-shift"
        #[intV x, nonInt, intV w, intV shift], r5)
    else if shape = 18 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/x-fourth-after-shift"
        #[nonInt, intV y, intV w, intV shift], r5)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkInputCase s!"/fuzz/shape-{shape}/intov/nan-w-via-program"
        (.num x) (.num y) .nan (.num shift), r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        (.num x) .nan (.num w) (.num shift), r4)
    else if shape = 21 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        .nan (.num y) (.num w) (.num shift), r4)
    else if shape = 22 then
      let (shift, r2) := pickShiftValid rng1
      (mkInputCase s!"/fuzz/shape-{shape}/intov/nan-all-via-program"
        .nan .nan .nan (.num shift), r2)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-w-type-via-program"
        #[intV x, intV y, .null] #[.pushInt (.num 300), muladdrshiftmodInstr], r3)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-y-type-via-program"
        #[intV x, .null, intV w] #[.pushInt (.num 300), muladdrshiftmodInstr], r3)
    else if shape = 25 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-x-type-via-program"
        #[.null, intV y, intV w] #[.pushInt (.num 300), muladdrshiftmodInstr], r3)
    else if shape = 26 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftValid r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num y) (.num w) (.num shift), r5)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftValid r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        (.num x) (.num yOut) (.num w) (.num shift), r5)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wOut, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftValid r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        (.num x) (.num y) (.num wOut) (.num shift), r5)
    else if shape = 29 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (pickNeg, r5) := randBool r4
      let shiftOut : Int := if pickNeg then -1 else 257
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        (.num x) (.num y) (.num w) (.num shiftOut), r5)
    else if shape = 30 then
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        (.num (maxInt257 + 1)) (.num (minInt257 - 1)) (.num (maxInt257 + 1)) (.num 257), rng1)
    else
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftValid r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-y-when-both-non-int"
        #[intV x, .cell Cell.empty, .null, intV shift], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := muladdrshiftmodId
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
            (runMulAddRShiftModDirect #[intV x, intV y, intV w, intV shift])
            #[intV q, intV r]
        expectOkStack "/unit/ok/pop-order/below-null-preserved"
          (runMulAddRShiftModDirect #[.null, intV 7, intV 5, intV 1, intV 2])
          #[.null, intV 9, intV 0]
        expectOkStack "/unit/ok/pop-order/below-cell-preserved"
          (runMulAddRShiftModDirect #[.cell Cell.empty, intV (-7), intV 5, intV 1, intV 2])
          #[.cell Cell.empty, intV (-9), intV 2] }
    ,
    { name := "/unit/ok/combined-boundary-and-intermediate-precision"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, 0, maxInt257, 0),
            (minInt257, 1, 0, 0, minInt257, 0),
            (maxInt257, 1, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 1, 0, minInt257 + 1, 0),
            (maxInt257, maxInt257, maxInt257, 256, maxInt257, 0),
            (maxInt257, maxInt257, 0, 256, maxInt257 - 1, 1),
            (minInt257, minInt257, minInt257, 256, maxInt257, 0),
            (minInt257, 1, 1, 256, -1, 1),
            (maxInt257, -1, -1, 256, -1, 0),
            (maxInt257, minInt257, maxInt257, 256, minInt257 + 1, maxInt257)
          ]
        for c in checks do
          let (x, y, w, shift, q, r) := c
          expectOkStack s!"/unit/ok/intermediate/x={x}/y={y}/w={w}/shift={shift}"
            (runMulAddRShiftModDirect #[intV x, intV y, intV w, intV shift])
            #[intV q, intV r] }
    ,
    { name := "/unit/error/overflow-and-range"
      run := do
        expectErr "/unit/error/overflow/max-times-one-plus-one-shift0"
          (runMulAddRShiftModDirect #[intV maxInt257, intV 1, intV 1, intV 0]) .intOv
        expectErr "/unit/error/overflow/min-times-one-minus-one-shift0"
          (runMulAddRShiftModDirect #[intV minInt257, intV 1, intV (-1), intV 0]) .intOv
        expectErr "/unit/error/overflow/intermediate-min-times-min-shift256"
          (runMulAddRShiftModDirect #[intV minInt257, intV minInt257, intV 0, intV 256]) .intOv
        expectErr "/unit/error/range/shift-negative"
          (runMulAddRShiftModDirect #[intV 7, intV 5, intV 3, intV (-1)]) .rangeChk
        expectErr "/unit/error/range/shift-overmax"
          (runMulAddRShiftModDirect #[intV 7, intV 5, intV 3, intV 257]) .rangeChk }
    ,
    { name := "/unit/error-order/underflow-range-type-pop-order"
      run := do
        expectErr "/unit/error/underflow/empty" (runMulAddRShiftModDirect #[]) .stkUnd
        expectErr "/unit/error/underflow/one-arg" (runMulAddRShiftModDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow/two-args" (runMulAddRShiftModDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow/three-args" (runMulAddRShiftModDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/unit/error-order/underflow-before-shift-type"
          (runMulAddRShiftModDirect #[intV 1, intV 2, .null]) .stkUnd
        expectErr "/unit/error/type/shift-top-null"
          (runMulAddRShiftModDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/unit/error/type/shift-top-cell"
          (runMulAddRShiftModDirect #[intV 1, intV 2, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/range-before-w-type"
          (runMulAddRShiftModDirect #[intV 1, intV 2, .null, intV 300]) .rangeChk
        expectErr "/unit/error-order/range-before-y-type"
          (runMulAddRShiftModDirect #[intV 1, .null, intV 3, intV 300]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type"
          (runMulAddRShiftModDirect #[.null, intV 2, intV 3, intV 300]) .rangeChk
        expectErr "/unit/error/type/w-second-after-shift"
          (runMulAddRShiftModDirect #[intV 1, intV 2, .null, intV 4]) .typeChk
        expectErr "/unit/error/type/y-third-after-shift"
          (runMulAddRShiftModDirect #[intV 1, .null, intV 3, intV 4]) .typeChk
        expectErr "/unit/error/type/x-fourth-after-shift"
          (runMulAddRShiftModDirect #[.null, intV 2, intV 3, intV 4]) .typeChk
        expectErr "/unit/error-order/pop-w-before-y-when-both-non-int"
          (runMulAddRShiftModDirect #[intV 1, .cell Cell.empty, .null, intV 2]) .typeChk }
    ,
    { name := "/unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulAddRShiftModDispatchFallback #[]) #[intV 9541] }
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
    mkCase "/ok/intermediate/max-times-max-plus-max-shift256"
      #[intV maxInt257, intV maxInt257, intV maxInt257, intV 256],
    mkCase "/ok/intermediate/max-times-max-plus-zero-shift256"
      #[intV maxInt257, intV maxInt257, intV 0, intV 256],
    mkCase "/ok/intermediate/min-times-min-plus-min-shift256"
      #[intV minInt257, intV minInt257, intV minInt257, intV 256],
    mkCase "/ok/intermediate/min-times-one-plus-one-shift256"
      #[intV minInt257, intV 1, intV 1, intV 256],
    mkCase "/ok/intermediate/max-times-neg1-plus-neg1-shift256"
      #[intV maxInt257, intV (-1), intV (-1), intV 256],
    mkCase "/ok/intermediate/max-times-min-plus-max-shift256"
      #[intV maxInt257, intV minInt257, intV maxInt257, intV 256],
    mkCase "/overflow/max-times-one-plus-one-shift0"
      #[intV maxInt257, intV 1, intV 1, intV 0],
    mkCase "/overflow/min-times-one-minus-one-shift0"
      #[intV minInt257, intV 1, intV (-1), intV 0],
    mkCase "/overflow/intermediate/min-times-min-shift256"
      #[intV minInt257, intV minInt257, intV 0, intV 256],
    mkCase "/overflow/intermediate/max-times-max-plus-max-shift0"
      #[intV maxInt257, intV maxInt257, intV maxInt257, intV 0],
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
    mkCase "/error-order/pop-w-before-y-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null, intV 2],
    mkShiftInjectedCase "/range/shift-negative-via-program" 7 5 3 (.num (-1)),
    mkShiftInjectedCase "/range/shift-overmax-via-program" 7 5 3 (.num 257),
    mkShiftInjectedCase "/range/shift-nan-via-program" 7 5 3 .nan,
    mkCase "/error-order/range-before-w-type" #[intV 1, intV 2, .null, intV 300],
    mkCase "/error-order/range-before-y-type" #[intV 1, .null, intV 3, intV 300],
    mkCase "/error-order/range-before-x-type" #[.null, intV 2, intV 3, intV 300],
    mkCase "/error-order/range-before-w-type-via-program"
      #[intV 1, intV 2, .null] #[.pushInt (.num 300), muladdrshiftmodInstr],
    mkCase "/error-order/range-before-y-type-via-program"
      #[intV 1, .null, intV 3] #[.pushInt (.num 300), muladdrshiftmodInstr],
    mkCase "/error-order/range-before-x-type-via-program"
      #[.null, intV 2, intV 3] #[.pushInt (.num 300), muladdrshiftmodInstr],
    mkInputCase "/intov/nan-w-via-program" (.num 7) (.num 5) .nan (.num 4),
    mkInputCase "/intov/nan-y-via-program" (.num 7) .nan (.num 3) (.num 4),
    mkInputCase "/intov/nan-x-via-program" .nan (.num 5) (.num 3) (.num 4),
    mkInputCase "/intov/nan-all-via-program" .nan .nan .nan (.num 4),
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
      #[.pushInt (.num muladdrshiftmodSetGasExact), .tonEnvOp .setGasLimit, muladdrshiftmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3, intV 2]
      #[.pushInt (.num muladdrshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, muladdrshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020861
      count := 700
      gen := genMulAddRShiftModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFTMOD
