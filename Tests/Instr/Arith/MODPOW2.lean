import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODPOW2

/-
MODPOW2 branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod`)
  - `TvmLean/Model/Basics/Bytes.lean` (`modPow2Round`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xa928..0xa92a` decode to `.arithExt (.shrMod false false 2 ... false none)`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)

Branch counts used for this suite:
- Lean (`.shrMod` non-mul path): 7 branch sites / 12 terminal outcomes
  (dispatch; stack pre-underflow guard; runtime shift pop+range check;
   operand numeric-vs-NaN split; round-mode validity check; `d` switch;
   non-num NaN fanout split for `d=3` vs others).
- C++ (`exec_shrmod`, mode=0): 6 branch sites / 11 terminal outcomes
  (global-version `d==0` remap + invalid-op guard; underflow guard;
   `pop_smallint_range(256)` type/range checks; `y==0` round override;
   add-vs-non-add split; `d` switch with `push_int_quiet` overflow gate).

MODPOW2 specialization:
- fixed params: `mulMode=false`, `addMode=false`, `d=2`, `roundMode=-1`, `quiet=false`, `zOpt=none`.

Key risk areas covered:
- floor-mod remainder behavior for negative operands and `shift=0`;
- strict runtime shift validation (`0..256`) with `rangeChk` before `x` pop/type checks;
- pop/error order (`shift` is popped first, then `x`);
- non-quiet NaN path (`intOv`) injected via program only;
- exact gas and exact-minus-one gas boundaries via `SETGASLIMIT`.
-/

private def modpow2Id : InstrId := { name := "MODPOW2" }

private def modpow2Instr : Instr :=
  .arithExt (.shrMod false false 2 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modpow2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := modpow2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runModpow2Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt modpow2Instr stack

private def runModpow2DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4242)) stack

private def modpow2SetGasExact : Int :=
  computeExactGasBudget modpow2Instr

private def modpow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modpow2Instr

private def validShiftPool : Array Int :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def smallXPool : Array Int :=
  #[-13, -7, -1, 0, 1, 7, 13, 42, -42]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genModpow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
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
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool invalidShiftPool r2
      (mkCase "tmp" #[intV x, intV shift], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickFromPool invalidShiftPool r2
      (mkCase "tmp" #[intV x, intV shift], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (useCell, r3) := randBool r2
      let top : Value := if useCell then .cell Cell.empty else .null
      (mkCase "tmp" #[intV x, top], r3)
    else if shape = 5 then
      let (shift, r2) := pickFromPool validShiftPool rng1
      let (useCell, r3) := randBool r2
      let xVal : Value := if useCell then .cell Cell.empty else .null
      (mkCase "tmp" #[xVal, intV shift], r3)
    else if shape = 6 then
      let (useIntArg, r2) := randBool rng1
      if useIntArg then
        let (x, r3) := pickSigned257ish r2
        (mkCase "tmp" #[intV x], r3)
      else
        (mkCase "tmp" #[.null], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase "tmp" #[intV x] #[.pushInt .nan, modpow2Instr], r2)
    else if shape = 8 then
      let (shiftNat, r2) := randNat rng1 0 256
      (mkCase "tmp" #[intV (Int.ofNat shiftNat)] #[.pushInt .nan, .xchg0 1, modpow2Instr], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftNat, r3) := randNat r2 0 256
      (mkCase "tmp" #[intV x, intV (Int.ofNat shiftNat)]
        #[.pushInt (.num (pow2 256)), modpow2Instr], r3)
    else if shape = 10 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      (mkCase "tmp" #[intV x, intV 256], r2)
    else
      let (x, r2) := pickFromPool smallXPool rng1
      let (shift, r3) := pickFromPool validShiftPool r2
      (mkCase "tmp" #[intV x, intV shift], r3)
  let kind :=
    if shape = 2 || shape = 3 then
      "range"
    else if shape = 4 || shape = 5 then
      "type"
    else if shape = 6 then
      "underflow"
    else if shape = 7 || shape = 8 then
      "nan-program"
    else if shape = 9 then
      "program-overflow"
    else
      "ok"
  let (tag, rng3) := randNat rng2 0 999_999
  ({ caseOut with name := s!"fuzz/shape-{shape}/{kind}-{tag}" }, rng3)

def suite : InstrSuite where
  id := modpow2Id
  unit := #[
    { name := "unit/ok/floor-modpow2-sign-zero-and-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 0, 0),
            (-7, 0, 0),
            (13, 3, 5),
            (-13, 3, 3),
            (42, 6, 42),
            (-42, 6, 22),
            (-1, 1, 1),
            (-2, 1, 0),
            (maxInt257, 1, 1),
            (maxInt257, 255, (pow2 255) - 1),
            (maxInt257, 256, maxInt257),
            (minInt257, 1, 0),
            (minInt257, 255, 0),
            (minInt257, 256, 0),
            (minInt257 + 1, 256, 1),
            (-1, 256, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}%2^{shift}" (runModpow2Direct #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/error/range-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runModpow2Direct #[]) .stkUnd
        expectErr "underflow/one-arg-int" (runModpow2Direct #[intV 5]) .stkUnd
        expectErr "underflow/one-arg-non-int" (runModpow2Direct #[.null]) .stkUnd
        expectErr "type/pop-shift-first-null" (runModpow2Direct #[intV 5, .null]) .typeChk
        expectErr "type/pop-shift-first-cell" (runModpow2Direct #[intV 5, .cell Cell.empty]) .typeChk
        expectErr "type/pop-x-second-null" (runModpow2Direct #[.null, intV 5]) .typeChk
        expectErr "type/pop-x-second-cell" (runModpow2Direct #[.cell Cell.empty, intV 5]) .typeChk
        expectErr "range/shift-negative" (runModpow2Direct #[intV 5, intV (-1)]) .rangeChk
        expectErr "range/shift-over-256" (runModpow2Direct #[intV 5, intV 257]) .rangeChk
        expectErr "error-order/range-before-x-type-neg"
          (runModpow2Direct #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-over"
          (runModpow2Direct #[.cell Cell.empty, intV 257]) .rangeChk
        expectErr "error-order/type-on-shift-before-x"
          (runModpow2Direct #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runModpow2DispatchFallback #[]) #[intV 4242] }
  ]
  oracle := #[
    mkCase "ok/shift-zero/pos" #[intV 7, intV 0],
    mkCase "ok/shift-zero/neg" #[intV (-7), intV 0],
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
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-int" #[intV 5],
    mkCase "underflow/one-arg-non-int" #[.null],
    mkCase "type/pop-shift-first-null" #[intV 5, .null],
    mkCase "type/pop-shift-first-cell" #[intV 5, .cell Cell.empty],
    mkCase "type/pop-x-second-null" #[.null, intV 5],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 5],
    mkCase "range/shift-neg-one" #[intV 5, intV (-1)],
    mkCase "range/shift-neg-two" #[intV 5, intV (-2)],
    mkCase "range/shift-over-256" #[intV 5, intV 257],
    mkCase "range/shift-over-258" #[intV 5, intV 258],
    mkCase "error-order/range-before-x-type-neg" #[.null, intV (-1)],
    mkCase "error-order/range-before-x-type-over" #[.cell Cell.empty, intV 257],
    mkCase "error-order/type-on-shift-before-x" #[.null, .cell Cell.empty],
    mkCase "nan/shift-via-program" #[intV 5] #[.pushInt .nan, modpow2Instr],
    mkCase "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, modpow2Instr],
    mkCase "error-order/pushint-overflow-before-op" #[intV 7, intV 3]
      #[.pushInt (.num (pow2 256)), modpow2Instr],
    mkCase "gas/exact-cost-succeeds" #[intV 37, intV 5]
      #[.pushInt (.num modpow2SetGasExact), .tonEnvOp .setGasLimit, modpow2Instr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 37, intV 5]
      #[.pushInt (.num modpow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, modpow2Instr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genModpow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2
