import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMODPOW2

/-
QMODPOW2 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod` with
     `mulMode=false`, `addMode=false`, `d=2`, `roundMode=-1`, `quiet=true`, `zOpt=none`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.shrMod` quiet encoding via `0xb7 ++ 0xa928..0xa92a`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-shrmod decode for `0xb7a928..0xb7a92a`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean specialization: 6 branch sites / 7 terminal outcomes
  (dispatch; stack pre-underflow guard; shift pop `typeChk`/`rangeChk`/ok;
   x pop `typeChk`; finite-vs-NaN x split; quiet push terminal).
- C++ specialization: 5 branch sites / 7 aligned terminal outcomes
  (opcode guard; underflow guard; shift pop+range split; x pop type split;
   quiet result/NaN push behavior).

Key risk areas covered:
- powers `0/1/255/256` with floor-mod semantics across sign combinations;
- strict runtime shift validation (`0..256`) even on quiet opcode;
- error ordering: precheck `stkUnd`, shift errors before x-pop/type checks;
- quiet NaN path: NaN x must produce pushed NaN (not `intOv`);
- oracle serialization constraints (NaN/out-of-range fed via program, not `initStack`);
- exact gas boundary for `PUSHINT n; SETGASLIMIT; QMODPOW2`.
-/

private def qmodpow2Id : InstrId := { name := "QMODPOW2" }

private def qmodpow2Instr : Instr :=
  .arithExt (.shrMod false false 2 (-1) true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmodpow2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmodpow2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQModPow2InputCase
    (name : String)
    (x shift : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, shift]
  mkCase name (below ++ stack) (progPrefix.push qmodpow2Instr) gasLimits fuel

private def runQModPow2Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmodpow2Instr stack

private def runQModPow2DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5150)) stack

private def qmodpow2SetGasExact : Int :=
  computeExactGasBudget qmodpow2Instr

private def qmodpow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmodpow2Instr

private def validShiftPool : Array Int :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def smallXPool : Array Int :=
  #[-42, -13, -7, -1, 0, 1, 7, 13, 42]

private def outOfRangeXPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genQModPow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (caseOut, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickFromPool validShiftPool r2
      (mkCase "tmp" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftNat, r3) := randNat r2 0 256
      (mkCase "tmp" #[intV x, intV (Int.ofNat shiftNat)], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickFromPool invalidShiftPool r2
      (mkCase "tmp" #[intV x, intV shift], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool invalidShiftPool r2
      (mkCase "tmp" #[intV x, intV shift], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (useCell, r3) := randBool r2
      let shiftVal : Value := if useCell then .cell Cell.empty else .null
      (mkCase "tmp" #[intV x, shiftVal], r3)
    else if shape = 5 then
      let (shiftNat, r2) := randNat rng1 0 256
      let (useCell, r3) := randBool r2
      let xVal : Value := if useCell then .cell Cell.empty else .null
      (mkCase "tmp" #[xVal, intV (Int.ofNat shiftNat)], r3)
    else if shape = 6 then
      let (useIntArg, r2) := randBool rng1
      if useIntArg then
        let (x, r3) := pickSigned257ish r2
        (mkCase "tmp" #[intV x], r3)
      else
        (mkCase "tmp" #[.null], r2)
    else if shape = 7 then
      (mkCase "tmp" #[], rng1)
    else if shape = 8 then
      let (shiftNat, r2) := randNat rng1 0 256
      (mkQModPow2InputCase "tmp" .nan (.num (Int.ofNat shiftNat)), r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkQModPow2InputCase "tmp" (.num x) .nan, r2)
    else if shape = 10 then
      let (xHuge, r2) := pickFromPool outOfRangeXPool rng1
      let (shiftNat, r3) := randNat r2 0 256
      (mkQModPow2InputCase "tmp" (.num xHuge) (.num (Int.ofNat shiftNat)), r3)
    else if shape = 11 then
      let (badShift, r2) := pickFromPool invalidShiftPool rng1
      (mkCase "tmp" #[.null, intV badShift], r2)
    else
      let (x, r2) := pickFromPool smallXPool rng1
      let (shift, r3) := pickFromPool validShiftPool r2
      (mkCase "tmp" #[intV x, intV shift], r3)
  let kind :=
    if shape = 2 || shape = 3 || shape = 11 then
      "range"
    else if shape = 4 || shape = 5 then
      "type"
    else if shape = 6 || shape = 7 then
      "underflow"
    else if shape = 8 || shape = 9 then
      "nan-program"
    else if shape = 10 then
      "program-overflow"
    else
      "ok"
  let (tag, rng3) := randNat rng2 0 999_999
  ({ caseOut with name := s!"fuzz/shape-{shape}/{kind}-{tag}" }, rng3)

def suite : InstrSuite where
  id := qmodpow2Id
  unit := #[
    { name := "unit/floor-modpow2-sign-and-power-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 0, 0),
            (-7, 0, 0),
            (7, 1, 1),
            (-7, 1, 1),
            (13, 3, 5),
            (-13, 3, 3),
            (42, 6, 42),
            (-42, 6, 22),
            (maxInt257, 1, 1),
            (minInt257, 1, 0),
            (maxInt257, 255, (pow2 255) - 1),
            (minInt257, 255, 0),
            (maxInt257, 256, maxInt257),
            (minInt257, 256, 0),
            (minInt257 + 1, 256, 1),
            (-1, 256, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%2^{shift}" (runQModPow2Direct #[intV x, intV shift]) #[intV expected]
        expectOkStack "below-stack-preserved" (runQModPow2Direct #[.null, intV 13, intV 3]) #[.null, intV 5] }
    ,
    { name := "unit/error-ordering-and-quiet-nan-paths"
      run := do
        expectOkStack "quiet-nan/x-nan-valid-shift" (runQModPow2Direct #[.int .nan, intV 5]) #[.int .nan]
        expectErr "underflow/empty" (runQModPow2Direct #[]) .stkUnd
        expectErr "underflow/one-arg-int" (runQModPow2Direct #[intV 7]) .stkUnd
        expectErr "underflow/one-arg-non-int" (runQModPow2Direct #[.null]) .stkUnd
        expectErr "type/pop-shift-first-null" (runQModPow2Direct #[intV 7, .null]) .typeChk
        expectErr "type/pop-shift-first-cell" (runQModPow2Direct #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-null" (runQModPow2Direct #[.null, intV 7]) .typeChk
        expectErr "type/pop-x-second-cell" (runQModPow2Direct #[.cell Cell.empty, intV 7]) .typeChk
        expectErr "range/shift-negative" (runQModPow2Direct #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runQModPow2Direct #[intV 7, intV 257]) .rangeChk
        expectErr "range/shift-nan" (runQModPow2Direct #[intV 7, .int .nan]) .rangeChk
        expectErr "error-order/range-before-x-type-neg" (runQModPow2Direct #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-over" (runQModPow2Direct #[.cell Cell.empty, intV 257]) .rangeChk
        expectErr "error-order/type-on-shift-before-x" (runQModPow2Direct #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQModPow2DispatchFallback #[]) #[intV 5150] }
  ]
  oracle := #[
    mkCase "ok/shift0/zero" #[intV 0, intV 0],
    mkCase "ok/shift0/positive" #[intV 7, intV 0],
    mkCase "ok/shift0/negative" #[intV (-7), intV 0],
    mkCase "ok/shift1/positive" #[intV 7, intV 1],
    mkCase "ok/shift1/negative" #[intV (-7), intV 1],
    mkCase "ok/small/pos-shift3" #[intV 13, intV 3],
    mkCase "ok/small/neg-shift3" #[intV (-13), intV 3],
    mkCase "ok/small/pos-shift6" #[intV 42, intV 6],
    mkCase "ok/small/neg-shift6" #[intV (-42), intV 6],
    mkCase "ok/boundary/max-shift1" #[intV maxInt257, intV 1],
    mkCase "ok/boundary/min-shift1" #[intV minInt257, intV 1],
    mkCase "ok/boundary/max-shift255" #[intV maxInt257, intV 255],
    mkCase "ok/boundary/min-shift255" #[intV minInt257, intV 255],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 256],
    mkCase "ok/boundary/neg-one-shift256" #[intV (-1), intV 256],
    mkCase "ok/order/below-stack-preserved" #[.null, intV 13, intV 3],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-int" #[intV 7],
    mkCase "underflow/one-arg-non-int" #[.null],
    mkCase "type/pop-shift-first-null" #[intV 7, .null],
    mkCase "type/pop-shift-first-cell" #[intV 7, .cell Cell.empty],
    mkCase "type/pop-x-second-null" #[.null, intV 7],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 7],
    mkCase "range/shift-negative" #[intV 7, intV (-1)],
    mkCase "range/shift-over-256" #[intV 7, intV 257],
    mkCase "error-order/range-before-x-type-neg" #[.null, intV (-1)],
    mkCase "error-order/range-before-x-type-over" #[.cell Cell.empty, intV 257],
    mkCase "error-order/type-on-shift-before-x" #[.null, .cell Cell.empty],
    mkQModPow2InputCase "quiet-nan/x-via-program" .nan (.num 5),
    mkQModPow2InputCase "range/shift-nan-via-program" (.num 7) .nan,
    mkQModPow2InputCase "error-order/pushint-overflow-before-op-pos" (.num (maxInt257 + 1)) (.num 5),
    mkQModPow2InputCase "error-order/pushint-overflow-before-op-neg" (.num (minInt257 - 1)) (.num 5),
    mkCase "gas/exact-cost-succeeds" #[intV 37, intV 5]
      #[.pushInt (.num qmodpow2SetGasExact), .tonEnvOp .setGasLimit, qmodpow2Instr],
    mkCase "gas/exact-minus-one/out-of-gas" #[intV 37, intV 5]
      #[.pushInt (.num qmodpow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, qmodpow2Instr]
  ]
  fuzz := #[
    { seed := 2026020831
      count := 560
      gen := genQModPow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMODPOW2
