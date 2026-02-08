import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULRSHIFTCMOD

/-
QMULRSHIFTCMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 3 1 true none)` path)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`; runtime `shift=0` rewrite to floor)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xb7a9ac..0xb7a9ae` quiet decode for `QMULRSHIFT{,MOD}`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch/outcome counts used for this suite:
- Lean (`.shrMod` generic helper): 9 branch sites / 20 terminal outcomes.
- Lean specialization (`mul=true`, `add=false`, `d=3`, `round=1`, `quiet=true`, runtime shift):
  reachable outcomes covered here:
  `ok` numeric pair, `ok` quiet NaN pair, `ok` quiet mixed `[NaN, int]`,
  `stkUnd`, `typeChk`.
- C++ (`exec_mulshrmod`, quiet runtime-shift mode): 8 branch sites / 17 aligned outcomes
  (underflow gate, range behavior in quiet mode, `shift=0` round rewrite,
   invalid-int/shift quiet fallback, `d` switch, quiet push outcomes).

Key risk areas covered:
- ceil quotient/remainder behavior across sign mixes and shift boundaries;
- runtime `shift=0` rewrite to floor mode (even for `...C` flavor);
- quiet handling for bad shifts and NaN operands (NaN pair, not throw);
- quiet partial-overflow behavior where quotient becomes NaN but remainder stays exact;
- strict pop/error ordering (`shift`, then `y`, then `x`) under underflow/type interactions;
- NaN/out-of-range oracle inputs injected only through `PUSHINT` prelude helpers;
- exact gas cliff via `PUSHINT n; SETGASLIMIT; QMULRSHIFTCMOD`.
-/

private def qmulrshiftcmodId : InstrId := { name := "QMULRSHIFTCMOD" }

private def qmulrshiftcmodInstr : Instr :=
  .arithExt (.shrMod true false 3 1 true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulrshiftcmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qmulrshiftcmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulrshiftcmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix ++ programSuffix) gasLimits fuel

private def runQmulrshiftcmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulrshiftcmodInstr stack

private def runQmulrshiftcmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4703)) stack

private def qmulrshiftcmodSetGasExact : Int :=
  computeExactGasBudget qmulrshiftcmodInstr

private def qmulrshiftcmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulrshiftcmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 7
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyQmulrshiftcmod (x y : Int) (shift : Nat) : String :=
  let roundMode : Int := if shift = 0 then -1 else 1
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

private def genQmulrshiftcmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 26
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyQmulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-boundary-shift-boundary"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyQmulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/boundary-random-shift-random"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyQmulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/random-boundary-shift-boundary"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyQmulrshiftcmod x y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/random-random-shift-random"
        #[intV x, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyQmulrshiftcmod 0 y shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/zero-left-factor"
        #[intV 0, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyQmulrshiftcmod x 0 shift
      (mkCase s!"fuzz/shape-{shape}/ok/{kind}/zero-right-factor"
        #[intV x, intV 0, intV (Int.ofNat shift)], r3)
    else if shape = 6 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/shift0-floor-rewrite"
        #[intV x, intV y, intV 0], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/shift256-boundary"
        #[intV x, intV y, intV 256], r3)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/ok/quiet-overflow-q-nan-r-zero-maxmax"
        #[intV maxInt257, intV maxInt257, intV 0], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/ok/quiet-overflow-q-nan-r-zero-minneg1"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 10 then
      (mkCase s!"fuzz/shape-{shape}/error/underflow-empty-stack" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/error/underflow-one-item" #[intV x], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/error/underflow-two-items" #[intV x, intV y], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error/type-shift-pop-first"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error/type-y-pop-second"
        #[intV x, yLike, intV (Int.ofNat shift)], r4)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/error/type-x-pop-third"
        #[xLike, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/quiet-bad-shift-negative-to-nan-pair"
        #[intV x, intV y, intV (-1)], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCase s!"fuzz/shape-{shape}/ok/quiet-bad-shift-overmax-to-nan-pair"
        #[intV x, intV y, intV 257], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error/type-bad-shift-does-not-mask-y-type"
        #[intV x, yLike, intV 257], r3)
    else if shape = 19 then
      let (y, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error/type-bad-shift-does-not-mask-x-type"
        #[xLike, intV y, intV (-1)], r3)
    else if shape = 20 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/quiet-nan-x-via-program"
        #[IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/quiet-nan-y-via-program"
        #[IntVal.num x, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/ok/quiet-nan-shift-via-program"
        #[IntVal.num x, IntVal.num y, IntVal.nan], r3)
    else if shape = 23 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error/pushint-overflow-x-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftInRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num yOut, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num y, IntVal.num shiftOut], r4)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error/pushint-overflow-both-before-op"
        #[IntVal.num xOut, IntVal.num y, IntVal.num shiftOut], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulrshiftcmodId
  unit := #[
    { name := "unit/direct/ceil-round-sign-zero-and-shift-boundaries"
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
            (maxInt257, -1, 1, 1 - (pow2 255), -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"unit/check/{x}/{y}/{shift}"
            (runQmulrshiftcmodDirect #[intV x, intV y, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/quiet/nan-range-and-overflow-yield-quiet-results"
      run := do
        expectOkStack "unit/quiet/shift-negative"
          (runQmulrshiftcmodDirect #[intV 5, intV 3, intV (-1)])
          #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/shift-overmax"
          (runQmulrshiftcmodDirect #[intV 5, intV 3, intV 257])
          #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/shift-nan"
          (runQmulrshiftcmodDirect #[intV 5, intV 3, .int .nan])
          #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/nan-x"
          (runQmulrshiftcmodDirect #[.int .nan, intV 3, intV 1])
          #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/nan-y"
          (runQmulrshiftcmodDirect #[intV 3, .int .nan, intV 1])
          #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/overflow-maxmax-shift0-qnan-r0"
          (runQmulrshiftcmodDirect #[intV maxInt257, intV maxInt257, intV 0])
          #[.int .nan, intV 0]
        expectOkStack "unit/quiet/overflow-minneg1-shift0-qnan-r0"
          (runQmulrshiftcmodDirect #[intV minInt257, intV (-1), intV 0])
          #[.int .nan, intV 0] }
    ,
    { name := "unit/error/pop-order-underflow-and-type-precedence"
      run := do
        expectErr "unit/error/underflow-empty"
          (runQmulrshiftcmodDirect #[]) .stkUnd
        expectErr "unit/error/underflow-one-item"
          (runQmulrshiftcmodDirect #[intV 1]) .stkUnd
        expectErr "unit/error/underflow-two-items"
          (runQmulrshiftcmodDirect #[intV 1, intV 2]) .stkUnd
        expectErr "unit/error/underflow-two-non-int-items"
          (runQmulrshiftcmodDirect #[.cell Cell.empty, .null]) .stkUnd
        expectErr "unit/error/type-shift-pop-first-null"
          (runQmulrshiftcmodDirect #[intV 5, intV 3, .null]) .typeChk
        expectErr "unit/error/type-shift-pop-first-cell"
          (runQmulrshiftcmodDirect #[intV 5, intV 3, .cell Cell.empty]) .typeChk
        expectErr "unit/error/type-y-pop-second"
          (runQmulrshiftcmodDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "unit/error/type-x-pop-third"
          (runQmulrshiftcmodDirect #[.null, intV 3, intV 1]) .typeChk
        expectErr "unit/error/type-bad-shift-does-not-mask-y-type"
          (runQmulrshiftcmodDirect #[intV 5, .null, intV 257]) .typeChk
        expectErr "unit/error/type-bad-shift-does-not-mask-x-type"
          (runQmulrshiftcmodDirect #[.null, intV 3, intV (-1)]) .typeChk }
    ,
    { name := "unit/pop-order/top-three-consumed-below-preserved"
      run := do
        expectOkStack "unit/order/below-null"
          (runQmulrshiftcmodDirect #[.null, intV 7, intV 3, intV 1])
          #[.null, intV 11, intV (-1)]
        expectOkStack "unit/order/below-cell"
          (runQmulrshiftcmodDirect #[.cell Cell.empty, intV (-7), intV 3, intV 1])
          #[.cell Cell.empty, intV (-10), intV (-1)] }
    ,
    { name := "unit/dispatch/non-qmulrshiftcmod-falls-through"
      run := do
        expectOkStack "unit/dispatch/fallback"
          (runQmulrshiftcmodDispatchFallback #[]) #[intV 4703] }
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
    mkCase "ok/exact/shift0-positive" #[intV 7, intV 3, intV 0],
    mkCase "ok/exact/shift0-negative" #[intV (-7), intV 3, intV 0],
    mkCase "ok/exact/zero-left-factor" #[intV 0, intV 9, intV 5],
    mkCase "ok/exact/zero-right-factor" #[intV 9, intV 0, intV 5],
    mkCase "ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/min-plus-one-shift256" #[intV (minInt257 + 1), intV 1, intV 256],
    mkCase "ok/boundary/max-times-neg-one-shift1" #[intV maxInt257, intV (-1), intV 1],
    mkCase "ok/order/below-null-preserved" #[.null, intV 7, intV 3, intV 1],
    mkCase "ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-7), intV 3, intV 1],
    mkCase "ok/quiet/overflow-maxmax-shift0-qnan-r0" #[intV maxInt257, intV maxInt257, intV 0],
    mkCase "ok/quiet/overflow-minneg1-shift0-qnan-r0" #[intV minInt257, intV (-1), intV 0],
    mkCase "ok/quiet/shift-negative-yields-nan-pair" #[intV 5, intV 3, intV (-1)],
    mkCase "ok/quiet/shift-overmax-yields-nan-pair" #[intV 5, intV 3, intV 257],
    mkCaseFromIntVals "ok/quiet/nan-x-via-program"
      #[IntVal.nan, IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "ok/quiet/nan-y-via-program"
      #[IntVal.num 5, IntVal.nan, IntVal.num 1],
    mkCaseFromIntVals "ok/quiet/nan-shift-via-program"
      #[IntVal.num 5, IntVal.num 3, IntVal.nan],
    mkCase "error/underflow/empty-stack" #[],
    mkCase "error/underflow/one-item" #[intV 1],
    mkCase "error/underflow/two-items" #[intV 1, intV 2],
    mkCase "error/underflow/two-non-int-items" #[.cell Cell.empty, .null],
    mkCase "error/type/shift-pop-first-null" #[intV 5, intV 3, .null],
    mkCase "error/type/shift-pop-first-cell" #[intV 5, intV 3, .cell Cell.empty],
    mkCase "error/type/y-pop-second-null" #[intV 5, .null, intV 1],
    mkCase "error/type/x-pop-third-null" #[.null, intV 3, intV 1],
    mkCase "error/type/bad-shift-does-not-mask-y-type" #[intV 5, .null, intV 257],
    mkCase "error/type/bad-shift-does-not-mask-x-type" #[.null, intV 3, intV (-1)],
    mkCaseFromIntVals "error/pushint-overflow-x-high-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "error/pushint-overflow-x-low-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 5, IntVal.num 1],
    mkCaseFromIntVals "error/pushint-overflow-y-high-before-op"
      #[IntVal.num 5, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkCaseFromIntVals "error/pushint-overflow-y-low-before-op"
      #[IntVal.num 5, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkCaseFromIntVals "error/pushint-overflow-shift-high-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num (maxInt257 + 1)],
    mkCaseFromIntVals "error/pushint-overflow-shift-low-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num (minInt257 - 1)],
    mkCaseFromIntVals "error/pushint-overflow-both-before-op"
      #[IntVal.num (pow2 257), IntVal.num 3, IntVal.num (-(pow2 257))],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num qmulrshiftcmodSetGasExact), .tonEnvOp .setGasLimit, qmulrshiftcmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num qmulrshiftcmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulrshiftcmodInstr]
  ]
  fuzz := #[
    { seed := 2026020839
      count := 700
      gen := genQmulrshiftcmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTCMOD
