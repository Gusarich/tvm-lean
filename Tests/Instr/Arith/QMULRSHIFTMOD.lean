import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULRSHIFTMOD

/-
QMULRSHIFTMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 3 (-1) true none`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet encoding path `0xb7 ++ 0xa9ac..0xa9ae`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode path `0xb7a9ac..0xb7a9ae`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean (`execInstrArithExt` `.shrMod` generic helper): 9 branch sites / 20 terminal outcomes.
- Lean (QMULRSHIFTMOD specialization): 8 branch sites / 8 reachable terminal outcomes
  (finite-pair success; quiet overflow shape `q=NaN,r=0`; quiet NaN-pair funnel;
   `stkUnd`; shift `typeChk`; `y` `typeChk`; `x` `typeChk`; dispatch fallthrough).
- C++ (`exec_mulshrmod`, quiet runtime-shift mode): 8 branch sites / 14 aligned terminal outcomes
  (mode/decode gates; add-remap gate; underflow gate; shift source/range gate;
   operand pop/type gates; invalid-input quiet funnel for modern global-version path;
   fixed `d=3` dual-push shape).

Key risk areas covered:
- floor quotient/remainder invariants across sign combinations and shift boundaries (`0..256`);
- quiet overflow shape where quotient can quiet-fail but remainder still pushes;
- quiet bad-shift behavior for numeric operands vs shift/y/x type-pop precedence;
- strict pop ordering (`shift`, then `y`, then `x`) and underflow-before-type behavior;
- NaN/out-of-range serialization discipline (oracle/fuzz inject via `PUSHINT` prelude only);
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QMULRSHIFTMOD`.
-/

private def qmulrshiftmodId : InstrId := { name := "QMULRSHIFTMOD" }

private def qmulrshiftmodInstr : Instr :=
  .arithExt (.shrMod true false 3 (-1) true none)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulrshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulrshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulrshiftmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def runQMulRShiftModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulrshiftmodInstr stack

private def runQMulRShiftModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4683)) stack

private def qmulrshiftmodSetGasExact : Int :=
  computeExactGasBudget qmulrshiftmodInstr

private def qmulrshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulrshiftmodInstr

private def mkShiftInjectedCase (name : String) (x y : Int) (shift : IntVal) : OracleCase :=
  mkCase name #[intV x, intV y] #[.pushInt shift, qmulrshiftmodInstr]

private def mkYNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift] #[.pushInt .nan, .xchg0 1, qmulrshiftmodInstr]

private def mkXNanInjectedCase (name : String) (y shift : Int) : OracleCase :=
  mkCase name #[intV y, intV shift] #[.pushInt .nan, .xchg0 2, .xchg0 1, qmulrshiftmodInstr]

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-5, -2, -1, 257, 258, 300]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickFromPool validShiftBoundaryPool rng1
  else
    let (shift, rng2) := randNat rng1 0 256
    (Int.ofNat shift, rng2)

private def pickInvalidShift (rng : StdGen) : Int × StdGen :=
  pickFromPool invalidShiftPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQMulRShiftModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromPool validShiftBoundaryPool r3
      (mkCase s!"/fuzz/shape-{shape}/ok/boundary-triplet" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/ok/signed-triplet" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/ok/x-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/ok/y-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-max-times-two-shift0"
        #[intV maxInt257, intV 2, intV 0], rng1)
    else if shape = 5 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-times-neg-one-shift0"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/quiet/overflow-min-times-min-shift256"
        #[intV minInt257, intV minInt257, intV 256], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInvalidShift r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/shift-out-of-range-via-program"
        x y (.num shift), r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/shift-nan-via-program" x y .nan, r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/shift-top-non-int" #[intV x, intV y, shiftLike], r4)
    else if shape = 10 then
      let (pick, r2) := randNat rng1 0 2
      let stack :=
        if pick = 0 then
          #[]
        else if pick = 1 then
          #[intV 1]
        else
          #[intV 1, intV 2]
      (mkCase s!"/fuzz/shape-{shape}/underflow" stack, r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkYNanInjectedCase s!"/fuzz/shape-{shape}/quiet/nan-y-via-program" x shift, r3)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkXNanInjectedCase s!"/fuzz/shape-{shape}/quiet/nan-x-via-program" y shift, r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/y-second-non-int" #[intV x, yLike, intV shift], r4)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/x-third-non-int" #[xLike, intV y, intV shift], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftBad, r3) := pickInvalidShift r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-does-not-mask-y-type"
        #[intV x, .null] #[.pushInt (.num shiftBad), qmulrshiftmodInstr], r3)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (shiftBad, r3) := pickInvalidShift r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-does-not-mask-x-type"
        #[.null, intV y] #[.pushInt (.num shiftBad), qmulrshiftmodInstr], r3)
    else if shape = 17 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num shift], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num shift], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shiftOut], r4)
    else if shape = 20 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-both-operands-before-op"
        #[IntVal.num xOut, IntVal.num yOut, IntVal.num shift], r4)
    else
      let (x, r2) := pickFromPool smallSignedPool rng1
      let (y, r3) := pickFromPool smallSignedPool r2
      let (shift, r4) := pickFromPool #[0, 1, 2, 3, 4, 5, 6, 7, 8] r3
      (mkCase s!"/fuzz/shape-{shape}/ok/small-sign-mix" #[intV x, intV y, intV shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulrshiftmodId
  unit := #[
    { name := "/unit/direct/floor-quot-rem-sign-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 2, 8, 3),
            (-7, 5, 2, -9, 1),
            (7, -5, 2, -9, 1),
            (-7, -5, 2, 8, 3),
            (1, -2, 1, -1, 0),
            (-1, 2, 1, -1, 0),
            (9, 0, 5, 0, 0),
            (0, 9, 5, 0, 0),
            (5, 3, 0, 15, 0),
            (-5, 3, 0, -15, 0),
            (1, 1, 256, 0, 1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/shift={shift}"
                (runQMulRShiftModDirect #[intV x, intV y, intV shift]) #[intV q, intV r] }
    ,
    { name := "/unit/direct/quiet-nan-funnels-and-overflow-shapes"
      run := do
        expectOkStack "/unit/quiet/shift-negative"
          (runQMulRShiftModDirect #[intV 5, intV 7, intV (-1)]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/shift-overmax"
          (runQMulRShiftModDirect #[intV 5, intV 7, intV 257]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/shift-nan"
          (runQMulRShiftModDirect #[intV 5, intV 7, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-y"
          (runQMulRShiftModDirect #[intV 5, .int .nan, intV 4]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/nan-x"
          (runQMulRShiftModDirect #[.int .nan, intV 5, intV 4]) #[.int .nan, .int .nan]
        expectOkStack "/unit/quiet/overflow-max-times-two-shift0"
          (runQMulRShiftModDirect #[intV maxInt257, intV 2, intV 0]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow-min-times-neg-one-shift0"
          (runQMulRShiftModDirect #[intV minInt257, intV (-1), intV 0]) #[.int .nan, intV 0]
        expectOkStack "/unit/quiet/overflow-min-times-min-shift256"
          (runQMulRShiftModDirect #[intV minInt257, intV minInt257, intV 256]) #[.int .nan, intV 0] }
    ,
    { name := "/unit/error-order/underflow-and-type-precedence"
      run := do
        expectErr "/unit/error/underflow-empty" (runQMulRShiftModDirect #[]) .stkUnd
        expectErr "/unit/error/underflow-one-arg" (runQMulRShiftModDirect #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-args" (runQMulRShiftModDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow-before-type-with-two-items"
          (runQMulRShiftModDirect #[.null, intV 2]) .stkUnd
        expectErr "/unit/error/type-shift-top-null"
          (runQMulRShiftModDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type-shift-top-cell"
          (runQMulRShiftModDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type-y-second-null"
          (runQMulRShiftModDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "/unit/error/type-x-third-null"
          (runQMulRShiftModDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "/unit/error/order-bad-shift-does-not-mask-y-type"
          (runQMulRShiftModDirect #[intV 1, .null, intV 300]) .typeChk
        expectErr "/unit/error/order-bad-shift-does-not-mask-x-type"
          (runQMulRShiftModDirect #[.null, intV 1, intV 300]) .typeChk }
    ,
    { name := "/unit/direct/pop-order-top-three-consumed-below-preserved"
      run := do
        expectOkStack "/unit/pop-order/below-null"
          (runQMulRShiftModDirect #[.null, intV 7, intV 5, intV 2]) #[.null, intV 8, intV 3]
        expectOkStack "/unit/pop-order/below-cell-quiet-bad-shift"
          (runQMulRShiftModDirect #[.cell Cell.empty, intV 7, intV 5, intV 300])
          #[.cell Cell.empty, .int .nan, .int .nan] }
    ,
    { name := "/unit/dispatch/non-qmulrshiftmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQMulRShiftModDispatchFallback #[]) #[intV 4683] }
  ]
  oracle := #[
    mkCase "/ok/floor/basic/pos-pos" #[intV 7, intV 5, intV 2],
    mkCase "/ok/floor/basic/neg-pos" #[intV (-7), intV 5, intV 2],
    mkCase "/ok/floor/basic/pos-neg" #[intV 7, intV (-5), intV 2],
    mkCase "/ok/floor/basic/neg-neg" #[intV (-7), intV (-5), intV 2],
    mkCase "/ok/floor/shift-zero-pos" #[intV 5, intV 3, intV 0],
    mkCase "/ok/floor/shift-zero-neg" #[intV (-5), intV 3, intV 0],
    mkCase "/ok/floor/y-zero" #[intV 9, intV 0, intV 5],
    mkCase "/ok/floor/x-zero" #[intV 0, intV 9, intV 5],
    mkCase "/ok/floor/shift-256-small" #[intV 1, intV 1, intV 256],
    mkCase "/ok/boundary/max-times-one-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "/ok/boundary/min-times-one-shift0" #[intV minInt257, intV 1, intV 0],
    mkCase "/ok/boundary/max-times-neg1-shift0" #[intV maxInt257, intV (-1), intV 0],
    mkCase "/ok/boundary/min-times-neg1-shift256" #[intV minInt257, intV (-1), intV 256],
    mkCase "/ok/boundary/max-times-max-shift256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "/ok/boundary/min-plus1-times-min-plus1-shift256"
      #[intV (minInt257 + 1), intV (minInt257 + 1), intV 256],
    mkCase "/ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "/ok/boundary/max-times-min-shift256" #[intV maxInt257, intV minInt257, intV 256],
    mkCase "/quiet/overflow/max-times-two-shift0" #[intV maxInt257, intV 2, intV 0],
    mkCase "/quiet/overflow/min-times-neg1-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "/quiet/overflow/min-times-min-shift256" #[intV minInt257, intV minInt257, intV 256],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args-int" #[intV 1, intV 2],
    mkCase "/error-order/underflow-before-type-with-two-args" #[.null, intV 2],
    mkCase "/type/pop-shift-first-null" #[intV 1, intV 2, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "/type/pop-y-second-null" #[intV 1, .null, intV 1],
    mkCase "/type/pop-x-third-null" #[.null, intV 1, intV 1],
    mkCase "/error-order/pop-shift-before-y-when-both-non-int" #[intV 1, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-when-shift-valid" #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/bad-shift-does-not-mask-y-type" #[intV 1, .null]
      #[.pushInt (.num 300), qmulrshiftmodInstr],
    mkCase "/error-order/bad-shift-does-not-mask-x-type" #[.null, intV 1]
      #[.pushInt (.num 300), qmulrshiftmodInstr],
    mkShiftInjectedCase "/quiet/shift-negative-via-program" 5 7 (.num (-1)),
    mkShiftInjectedCase "/quiet/shift-overmax-via-program" 5 7 (.num 257),
    mkShiftInjectedCase "/quiet/shift-nan-via-program" 5 7 .nan,
    mkYNanInjectedCase "/quiet/nan-y-via-program" 5 4,
    mkXNanInjectedCase "/quiet/nan-x-via-program" 5 4,
    mkCaseFromIntVals "/error-order/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 7, IntVal.num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 7, IntVal.num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-high-before-op"
      #[IntVal.num 7, IntVal.num (maxInt257 + 1), IntVal.num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-low-before-op"
      #[IntVal.num 7, IntVal.num (minInt257 - 1), IntVal.num 3],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-high-before-op"
      #[IntVal.num 7, IntVal.num 5, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-low-before-op"
      #[IntVal.num 7, IntVal.num 5, IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "/error-order/pushint-overflow-all-before-op"
      #[IntVal.num (pow2 257), IntVal.num (-(pow2 257)), IntVal.num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulrshiftmodSetGasExact), .tonEnvOp .setGasLimit, qmulrshiftmodInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulrshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulrshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020849
      count := 700
      gen := genQMulRShiftModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTMOD
