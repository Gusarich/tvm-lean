import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFTMOD

/-
LSHIFTMOD branch-mapping notes (Lean + C++ reference):
- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 2 (-1) false false none`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)

Branch counts used for this suite:
- Lean (`.shlDivMod` generic path): 8 branch sites / 16 terminal outcomes
  (runtime-vs-const shift source; shift range gate; add-mode `w` pop gate;
   operand-shape split; divisor-zero split; round-mode validity; `d` switch;
   non-quiet `pushIntQuiet` success vs `intOv`).
- Lean (LSHIFTMOD specialization): 7 branch sites / 10 reachable outcomes
  (`ok`; `stkUnd`; `typeChk` on shift/y/x pop; `rangeChk` on shift;
   `intOv` via divisor-zero and NaN funnel).
- C++ (`exec_shldivmod`, non-quiet runtime-shift mode): 7 branch sites /
  12 aligned outcomes (invalid-op guard; underflow gate; shift range gate;
  operand-shape checks; divisor-zero path; `d` switch; non-quiet push funnels).

Key risk areas covered:
- strict pop/error order: shift pops first, then divisor `y`, then `x`;
- shift range boundary (`0..256`) and precedence over later type checks;
- floor remainder sign behavior across operand-sign combinations;
- large-shift (`256`) behavior near signed-257 boundaries;
- non-quiet NaN/out-of-range shift injection via program (`PUSHINT`) only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFTMOD`.
-/

private def lshiftmodId : InstrId := { name := "LSHIFTMOD" }

private def lshiftmodInstr : Instr :=
  .arithExt (.shlDivMod 2 (-1) false false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[lshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def mkShiftInjectedCase
    (name : String)
    (x : Int)
    (y : Int)
    (shift : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x, intV y] #[.pushInt shift, lshiftmodInstr] gasLimits fuel

private def runLshiftmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt lshiftmodInstr stack

private def runLshiftmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 8172)) stack

private def lshiftmodSetGasExact : Int :=
  computeExactGasBudget lshiftmodInstr

private def lshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftmodInstr

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def outOfRangeShiftPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromIntPool validShiftBoundaryPool rng1
  else
    let (n, rng2) := randNat rng1 0 256
    (Int.ofNat n, rng2)

private def pickOutOfRangeShift (rng : StdGen) : Int × StdGen :=
  pickFromIntPool outOfRangeShiftPool rng

private def pickNonZeroSigned257ish (rng : StdGen) : Int × StdGen :=
  let (n, rng') := pickSigned257ish rng
  (if n = 0 then 1 else n, rng')

private def genLshiftmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let y := if y0 = 0 then 1 else y0
      let (shift, r4) := pickFromIntPool validShiftBoundaryPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickFromIntPool validShiftBoundaryPool r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-with-boundary-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"fuzz/shape-{shape}/ok-random-shift" #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let y := if y0 = 0 then 1 else y0
      (mkCase s!"fuzz/shape-{shape}/ok-shift-256" #[intV x, intV y, intV 256], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCase s!"fuzz/shape-{shape}/divzero" #[intV x, intV 0, intV shift], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (badShift, r4) := pickOutOfRangeShift r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-out-of-range-shift" x y (.num badShift), r4)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" x y .nan, r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroSigned257ish r2
      let (pickNull, r4) := randBool r3
      let shiftLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-shift-top-non-int" #[intV x, intV y, shiftLike], r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (pickNull, r4) := randBool r3
      let yLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-y-second-non-int" #[intV x, yLike, intV shift], r4)
    else if shape = 9 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (pickNull, r4) := randBool r3
      let xLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-x-third-non-int" #[xLike, intV y, intV shift], r4)
    else if shape = 10 then
      let (kind, r2) := randNat rng1 0 2
      if kind = 0 then
        (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], r2)
      else if kind = 1 then
        let (shift, r3) := pickValidShift r2
        (mkCase s!"fuzz/shape-{shape}/underflow-only-shift" #[intV shift], r3)
      else
        let (x, r3) := pickSigned257ish r2
        let (shift, r4) := pickValidShift r3
        (mkCase s!"fuzz/shape-{shape}/underflow-missing-x-after-y-pop" #[intV x, intV shift], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num shift], r3)
    else if shape = 12 then
      let (y, r2) := pickNonZeroSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num shift], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-y-type"
        #[intV x, .null] #[.pushInt (.num 257), lshiftmodInstr], r2)
    else
      let (x0, r2) := pickInt257Boundary rng1
      let x := if x0 = minInt257 then minInt257 + 1 else x0
      (mkCase s!"fuzz/shape-{shape}/ok-canceling-divisor"
        #[intV x, intV (-x), intV 1], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftmodId
  unit := #[
    { name := "unit/direct/floor-remainder-sign-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 2),
            (-7, 3, 1, 1),
            (7, -3, 1, -1),
            (-7, -3, 1, -2),
            (5, 7, 0, 5),
            (-5, 7, 0, 2),
            (1, 2, 8, 0),
            (-1, 2, 8, 0),
            (maxInt257, maxInt257, 0, 0),
            (minInt257, maxInt257, 0, maxInt257 - 1),
            (maxInt257 - 1, maxInt257, 256, maxInt257 - 1),
            (maxInt257, maxInt257, 256, 0),
            (minInt257, 1, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"x={x}/y={y}/z={shift}"
            (runLshiftmodDirect #[intV x, intV y, intV shift]) #[intV r] }
    ,
    { name := "unit/pop-order/top-three-consumed-below-preserved"
      run := do
        expectOkStack "below-null"
          (runLshiftmodDirect #[.null, intV 7, intV 3, intV 1]) #[.null, intV 2]
        expectOkStack "below-cell"
          (runLshiftmodDirect #[.cell Cell.empty, intV (-7), intV 3, intV 1]) #[.cell Cell.empty, intV 1] }
    ,
    { name := "unit/error/underflow-type-range-divzero-ordering"
      run := do
        expectErr "underflow/empty" (runLshiftmodDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runLshiftmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/missing-x-after-y-pop" (runLshiftmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "type/shift-top-null" (runLshiftmodDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/y-second-null" (runLshiftmodDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/x-third-null" (runLshiftmodDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "range/shift-negative" (runLshiftmodDirect #[intV 5, intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax" (runLshiftmodDirect #[intV 5, intV 7, intV 257]) .rangeChk
        expectErr "error-order/range-before-y-type" (runLshiftmodDirect #[intV 5, .null, intV 257]) .rangeChk
        expectErr "divzero/nonzero-over-zero" (runLshiftmodDirect #[intV 5, intV 0, intV 3]) .intOv }
    ,
    { name := "unit/dispatch/non-shldivmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runLshiftmodDispatchFallback #[]) #[intV 8172] }
  ]
  oracle := #[
    mkCase "ok/floor/pos-pos-shift1" #[intV 7, intV 3, intV 1],
    mkCase "ok/floor/neg-pos-shift1" #[intV (-7), intV 3, intV 1],
    mkCase "ok/floor/pos-neg-shift1" #[intV 7, intV (-3), intV 1],
    mkCase "ok/floor/neg-neg-shift1" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/floor/shift-zero-pos" #[intV 5, intV 7, intV 0],
    mkCase "ok/floor/shift-zero-neg" #[intV (-5), intV 7, intV 0],
    mkCase "ok/floor/large-shift-pos" #[intV 1, intV 2, intV 8],
    mkCase "ok/floor/large-shift-neg" #[intV (-1), intV 2, intV 8],
    mkCase "ok/boundary/max-mod-self-shift0" #[intV maxInt257, intV maxInt257, intV 0],
    mkCase "ok/boundary/min-mod-max-shift0" #[intV minInt257, intV maxInt257, intV 0],
    mkCase "ok/boundary/max-minus-one-mod-max-shift256"
      #[intV (maxInt257 - 1), intV maxInt257, intV 256],
    mkCase "ok/boundary/max-mod-max-shift256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/boundary/min-mod-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "divzero/nonzero-over-zero" #[intV 5, intV 0, intV 3],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/missing-x-after-y-pop" #[intV 1, intV 2],
    mkCase "type/shift-top-null" #[intV 1, intV 2, .null],
    mkCase "type/y-second-null" #[intV 1, .null, intV 2],
    mkCase "type/x-third-null" #[.null, intV 1, intV 2],
    mkCase "type/error-order-both-non-int-shift-first" #[.cell Cell.empty, .null, intV 1],
    mkShiftInjectedCase "range/shift-negative-via-program" 5 7 (.num (-1)),
    mkShiftInjectedCase "range/shift-overmax-via-program" 5 7 (.num 257),
    mkShiftInjectedCase "range/shift-nan-via-program" 5 7 .nan,
    mkCase "error-order/range-before-y-type-via-program"
      #[intV 5, .null] #[.pushInt (.num 257), lshiftmodInstr],
    mkCaseFromIntVals "nan/y-via-program" #[IntVal.num 5, IntVal.nan, IntVal.num 3],
    mkCaseFromIntVals "nan/x-via-program" #[IntVal.nan, IntVal.num 5, IntVal.num 3],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftmodSetGasExact), .tonEnvOp .setGasLimit, lshiftmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num lshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020812
      count := 700
      gen := genLshiftmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTMOD
