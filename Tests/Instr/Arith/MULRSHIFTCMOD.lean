import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTCMOD

/-
MULRSHIFTCMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 3 1 false none` path)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round` used by the `d=3` result pair)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xa9a` + args4 decode wiring)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode registration in `register_div_ops`)

Branch/terminal counts used for this suite:
- Lean (`.shrMod` generic helper): 9 branch sites / 20 terminal outcomes
  (mul-vs-non-mul split; explicit underflow precheck; runtime-vs-const shift source;
   bad-shift guard; operand-shape split; round-mode validity split; `d` switch;
   NaN fallback arity split; non-quiet `pushIntQuiet` overflow funnel).
- Lean specialization (`mul=true, add=false, d=3, round=1, quiet=false, zOpt=none`):
  reachable outcomes covered here: `ok`, `stkUnd`, `typeChk` (shift/y/x pop order),
  `rangeChk` (shift), `intOv` (NaN funnel), `intOv` (result overflow).
- C++ (`exec_mulshrmod` runtime-shift, non-quiet): 8 branch sites / 17 aligned outcomes
  (add-mode remap gate; invalid-opcode guard; underflow guard; runtime shift range guard;
   shift-zero round-mode normalization; global-version NaN/invalid short-circuit;
   `d` switch; non-quiet push overflow/NaN throw funnel).

Key risk areas covered:
- ceil quotient/remainder semantics for mixed signs and half-like residues;
- stack pop/error order (`z` shift first, then `y`, then `x`);
- shift domain boundaries (`0..256`) with `rangeChk` precedence over later type checks;
- non-quiet NaN and out-of-range-int inputs injected via `PUSHINT` program prefixes only;
- signed-257 boundary/overflow behavior from large products and narrow shifts;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; MULRSHIFTCMOD`.
-/

private def mulrshiftcmodId : InstrId := { name := "MULRSHIFTCMOD" }

private def mulrshiftcmodInstr : Instr :=
  .arithExt (.shrMod true false 3 1 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftcmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulrshiftcmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[mulrshiftcmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runMulrshiftcmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftcmodInstr stack

private def runMulrshiftcmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4303)) stack

private def mulrshiftcmodSetGasExact : Int :=
  computeExactGasBudget mulrshiftcmodInstr

private def mulrshiftcmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftcmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def outOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def classifyMulrshiftcmod (x y : Int) (shift : Nat) : String :=
  let roundMode : Int := if shift = 0 then (-1) else 1
  let tmp : Int := x * y
  let q := rshiftPow2Round tmp shift roundMode
  let r := modPow2Round tmp shift roundMode
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "overflow"
  else if tmp = 0 then
    "zero"
  else if r = 0 then
    "exact"
  else
    "inexact"

private def genMulrshiftcmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-boundary-shift-boundary"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-random-shift-random"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-boundary-shift-boundary"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-random-shift-random"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyMulrshiftcmod 0 y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-left-factor"
        #[intV 0, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyMulrshiftcmod x 0 shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/zero-right-factor"
        #[intV x, intV 0, intV (Int.ofNat shift)], r3)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let (useNegY, r3) := randBool r2
      let x := if useMax then maxInt257 else minInt257
      let y := if useNegY then (-1) else 1
      let shift := 256
      let kind := classifyMulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/extreme-x-shift256"
        #[intV x, intV y, intV 256], r3)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/overflow/max-max-shift0"
        #[intV maxInt257, intV maxInt257, intV 0], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/overflow/min-neg1-shift0"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-one-item" #[intV x], r2)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/underflow-two-non-int-items"
        #[.cell Cell.empty, .null], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (pickNull, r4) := randBool r3
      let shiftLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-shift-pop-first"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (pickNull, r4) := randBool r3
      let yLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-y-pop-second"
        #[intV x, yLike, intV (Int.ofNat shift)], r4)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (pickNull, r4) := randBool r3
      let xLike : Value := if pickNull then .null else .cell Cell.empty
      (mkCase s!"fuzz/shape-{shape}/type-x-pop-third"
        #[xLike, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-shift-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-negative"
        #[intV x, intV y, intV (-1)], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-overmax"
        #[intV x, intV y, intV 257], r3)
    else if shape = 20 then
      let (oor, r2) := pickFromPool outOfRangePool rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-x-via-program"
        #[IntVal.num oor, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else
      let (x, r2) := pickSigned257ish rng1
      let (oor, r3) := pickFromPool outOfRangePool r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/range-y-via-program"
        #[IntVal.num x, IntVal.num oor, IntVal.num (Int.ofNat shift)], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftcmodId
  unit := #[
    { name := "unit/direct/ceil-sign-zero-and-shift-boundaries"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 11, -1),
            (-7, 3, 1, -10, -1),
            (7, -3, 1, -10, -1),
            (-7, -3, 1, 11, -1),
            (5, 5, 2, 7, -3),
            (-5, 5, 2, -6, -1),
            (5, -5, 2, -6, -1),
            (-5, -5, 2, 7, -3),
            (0, 9, 5, 0, 0),
            (9, 0, 5, 0, 0),
            (7, 3, 0, 21, 0),
            (-7, 3, 0, -21, 0),
            (maxInt257, 1, 256, 1, -1),
            (minInt257, 1, 256, -1, 0),
            (minInt257 + 1, 1, 256, 0, minInt257 + 1),
            (minInt257, -1, 1, pow2 255, 0),
            (maxInt257, -1, 1, 1 - (pow2 255), -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"({x}*{y})>>{shift}"
            (runMulrshiftcmodDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/pop-order/top-three-consumed-below-preserved"
      run := do
        expectOkStack "below-null-preserved"
          (runMulrshiftcmodDirect #[.null, intV 7, intV 3, intV 1])
          #[.null, intV 11, intV (-1)]
        expectOkStack "below-cell-preserved"
          (runMulrshiftcmodDirect #[.cell Cell.empty, intV (-7), intV 3, intV 1])
          #[.cell Cell.empty, intV (-10), intV (-1)] }
    ,
    { name := "unit/error/intov-range-type-underflow-ordering"
      run := do
        expectErr "underflow/empty" (runMulrshiftcmodDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runMulrshiftcmodDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-non-int-items" (runMulrshiftcmodDirect #[.cell Cell.empty, .null]) .stkUnd
        expectErr "type/shift-pop-first-null"
          (runMulrshiftcmodDirect #[intV 5, intV 3, .null]) .typeChk
        expectErr "type/y-pop-second-null"
          (runMulrshiftcmodDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/x-pop-third-null"
          (runMulrshiftcmodDirect #[.null, intV 3, intV 1]) .typeChk
        expectErr "error-order/y-before-x-after-shift"
          (runMulrshiftcmodDirect #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "range/shift-negative"
          (runMulrshiftcmodDirect #[intV 5, intV 3, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax"
          (runMulrshiftcmodDirect #[intV 5, intV 3, intV 257]) .rangeChk
        expectErr "error-order/range-before-y-type"
          (runMulrshiftcmodDirect #[intV 5, .null, intV 257]) .rangeChk
        expectErr "overflow/min-times-neg-one-shift0"
          (runMulrshiftcmodDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "overflow/max-times-max-shift0"
          (runMulrshiftcmodDirect #[intV maxInt257, intV maxInt257, intV 0]) .intOv
        expectErr "overflow/max-times-max-shift1"
          (runMulrshiftcmodDirect #[intV maxInt257, intV maxInt257, intV 1]) .intOv }
    ,
    { name := "unit/dispatch/non-mulrshiftcmod-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runMulrshiftcmodDispatchFallback #[]) #[intV 4303] }
  ]
  oracle := #[
    mkCase "ok/ceil/sign/pos-pos-shift1" #[intV 7, intV 3, intV 1],
    mkCase "ok/ceil/sign/neg-pos-shift1" #[intV (-7), intV 3, intV 1],
    mkCase "ok/ceil/sign/pos-neg-shift1" #[intV 7, intV (-3), intV 1],
    mkCase "ok/ceil/sign/neg-neg-shift1" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/ceil/sign/pos-pos-shift2" #[intV 5, intV 5, intV 2],
    mkCase "ok/ceil/sign/neg-pos-shift2" #[intV (-5), intV 5, intV 2],
    mkCase "ok/ceil/sign/pos-neg-shift2" #[intV 5, intV (-5), intV 2],
    mkCase "ok/ceil/sign/neg-neg-shift2" #[intV (-5), intV (-5), intV 2],
    mkCase "ok/exact/shift-zero-pos" #[intV 7, intV 3, intV 0],
    mkCase "ok/exact/shift-zero-neg" #[intV (-7), intV 3, intV 0],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 9, intV 5],
    mkCase "ok/exact/zero-right-factor" #[intV 9, intV 0, intV 5],
    mkCase "ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-plus-one-times-one-shift256" #[intV (minInt257 + 1), intV 1, intV 256],
    mkCase "ok/boundary/min-times-neg-one-shift1" #[intV minInt257, intV (-1), intV 1],
    mkCase "ok/boundary/max-times-neg-one-shift1" #[intV maxInt257, intV (-1), intV 1],
    mkCase "overflow/min-times-neg-one-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "overflow/max-times-max-shift0" #[intV maxInt257, intV maxInt257, intV 0],
    mkCase "overflow/max-times-max-shift1" #[intV maxInt257, intV maxInt257, intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-with-two-non-int"
      #[.cell Cell.empty, .null],
    mkCase "type/shift-pop-first-null" #[intV 5, intV 3, .null],
    mkCase "type/shift-pop-first-cell" #[intV 5, intV 3, .cell Cell.empty],
    mkCase "type/y-pop-second-null" #[intV 5, .null, intV 1],
    mkCase "type/y-pop-second-cell" #[intV 5, .cell Cell.empty, intV 1],
    mkCase "type/x-pop-third-null" #[.null, intV 3, intV 1],
    mkCase "type/x-pop-third-cell" #[.cell Cell.empty, intV 3, intV 1],
    mkCase "error-order/y-before-x-after-shift"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "range/shift-negative" #[intV 5, intV 3, intV (-1)],
    mkCase "range/shift-overmax" #[intV 5, intV 3, intV 257],
    mkCase "error-order/range-before-y-type"
      #[intV 5, .null, intV 257],
    mkCaseFromIntVals "nan/x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "nan/y-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "nan/shift-via-program"
      #[IntVal.num 5, IntVal.num 3, IntVal.nan],
    mkCaseFromIntVals "range/x-high-via-program"
      #[IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "range/x-low-via-program"
      #[IntVal.num (minInt257 - 1), IntVal.num 3, IntVal.num 1],
    mkCaseFromIntVals "range/y-high-via-program"
      #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "range/y-low-via-program"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftcmodSetGasExact), .tonEnvOp .setGasLimit, mulrshiftcmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftcmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftcmodInstr]
  ]
  fuzz := #[
    { seed := 2026020826
      count := 700
      gen := genMulrshiftcmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTCMOD
