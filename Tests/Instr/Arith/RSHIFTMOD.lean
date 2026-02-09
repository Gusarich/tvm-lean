import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTMOD

/-
RSHIFTMOD branch-mapping notes (Lean + C++ reference):
- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_add_mul_ops`)

Branch/terminal counts covered by this suite:
- Lean (`.shrMod` general helper): 9 branch points / 20 terminal outcomes
  (mul-vs-non-mul split; stack precheck; runtime-vs-immediate shift source;
   operand-shape split; round-mode validity; `d` switch; NaN fallback arity).
- Lean (RSHIFTMOD specialization `mul=false, add=false, d=3, round=-1, quiet=false`):
  6 reachable terminal outcomes (`ok`, `stkUnd`, `typeChk` on shift pop,
   `typeChk` on `x` pop, `rangeChk` on shift, `intOv` via NaN funnel).
- C++ (`exec_shrmod` + registration): 7 branch points / 14 terminal outcomes
  (mode/immediate gate, add remap gate, invalid-opcode guard, underflow guard,
   zero-shift round-mode normalization, add-vs-non-add split, `d` switch).

Key risk areas covered:
- strict pop/error order: shift pops first, then `x`;
- shift range boundaries (`0..256`) and `rangeChk` precedence over later type checks;
- quotient/remainder sign behavior for negative operands at small and extreme shifts;
- signed-257 boundary behavior at shift `0` and `256`;
- non-quiet NaN funnel to `intOv` (injected via program, never via `initStack`);
- exact gas boundary (`PUSHINT n; SETGASLIMIT; RSHIFTMOD`) with exact and minus-one budgets.
-/

private def rshiftmodId : InstrId := { name := "RSHIFTMOD" }

private def rshiftmodInstr : Instr := .arithExt (.shrMod false false 3 (-1) false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRshiftmodDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt rshiftmodInstr stack

private def runRshiftmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 606)) stack

private def rshiftmodSetGasExact : Int :=
  computeExactGasBudget rshiftmodInstr

private def rshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftmodInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 7, 8, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def genRshiftmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (x, rng2) := pickInt257Boundary rng1
    let (shift, rng3) := pickShiftBoundary rng2
    let (tag, rng4) := randNat rng3 0 999_999
    (mkCase s!"fuzz/ok/boundary-x-boundary-shift-{tag}" #[intV x, intV (Int.ofNat shift)], rng4)
  else if shape = 1 then
    let (x, rng2) := pickSigned257ish rng1
    let (shift, rng3) := pickShiftBoundary rng2
    let (tag, rng4) := randNat rng3 0 999_999
    (mkCase s!"fuzz/ok/random-x-boundary-shift-{tag}" #[intV x, intV (Int.ofNat shift)], rng4)
  else if shape = 2 then
    let (x, rng2) := pickInt257Boundary rng1
    let (shift, rng3) := pickShiftMixed rng2
    let (tag, rng4) := randNat rng3 0 999_999
    (mkCase s!"fuzz/ok/boundary-x-random-shift-{tag}" #[intV x, intV (Int.ofNat shift)], rng4)
  else if shape = 3 then
    let (x, rng2) := pickSigned257ish rng1
    let (shift, rng3) := pickShiftMixed rng2
    let (tag, rng4) := randNat rng3 0 999_999
    (mkCase s!"fuzz/ok/random-x-random-shift-{tag}" #[intV x, intV (Int.ofNat shift)], rng4)
  else if shape = 4 then
    let (x, rng2) := pickSigned257ish rng1
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/range/shift-gt-256-{tag}" #[intV x, intV 257], rng3)
  else if shape = 5 then
    let (x, rng2) := pickSigned257ish rng1
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/range/shift-negative-{tag}" #[intV x, intV (-1)], rng3)
  else if shape = 6 then
    let (x, rng2) := pickSigned257ish rng1
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/type/shift-top-null-{tag}" #[intV x, .null], rng3)
  else if shape = 7 then
    let (shift, rng2) := pickShiftMixed rng1
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/type/x-second-null-{tag}" #[.null, intV (Int.ofNat shift)], rng3)
  else if shape = 8 then
    let (shift, rng2) := pickShiftMixed rng1
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/underflow/missing-x-after-shift-pop-{tag}" #[intV (Int.ofNat shift)], rng3)
  else if shape = 9 then
    let (x, rng2) := pickSigned257ish rng1
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/nan/shift-via-program-{tag}" #[intV x] #[.pushInt .nan, rshiftmodInstr], rng3)
  else if shape = 10 then
    let (shift, rng2) := pickShiftMixed rng1
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/nan/x-via-program-{tag}" #[intV (Int.ofNat shift)]
      #[.pushInt .nan, .xchg0 1, rshiftmodInstr], rng3)
  else
    let (tag, rng2) := randNat rng1 0 999_999
    let (useMin, rng3) := randBool rng2
    let x := if useMin then minInt257 else maxInt257
    (mkCase s!"fuzz/ok/extreme-shift-256-{tag}" #[intV x, intV 256], rng3)

def suite : InstrSuite where
  id := rshiftmodId
  unit := #[
    { name := "unit/direct/quot-rem-sign-and-zero-invariants"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (13, 2, 3, 1),
            (-13, 2, -4, 3),
            (7, 3, 0, 7),
            (-7, 3, -1, 1),
            (1, 1, 0, 1),
            (-1, 1, -1, 1),
            (0, 7, 0, 0),
            (5, 0, 5, 0),
            (-5, 0, -5, 0),
            (maxInt257, 1, (pow2 255) - 1, 1),
            (minInt257, 1, -(pow2 255), 0)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"{x}>>{shift}" (runRshiftmodDirect #[intV x, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/direct/shift-boundary-successes"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (maxInt257, 0, maxInt257, 0),
            (minInt257, 0, minInt257, 0),
            (maxInt257, 256, 0, maxInt257),
            (maxInt257 - 1, 256, 0, maxInt257 - 1),
            (minInt257, 256, -1, 0),
            (minInt257 + 1, 256, -1, 1),
            (pow2 255, 255, 1, 0),
            (-(pow2 255), 255, -1, 0)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"{x}>>{shift}" (runRshiftmodDirect #[intV x, intV (Int.ofNat shift)])
            #[intV q, intV r] }
    ,
    { name := "unit/error/range-type-underflow-and-pop-order"
      run := do
        expectErr "empty" (runRshiftmodDirect #[]) .stkUnd
        expectErr "missing-x-after-shift-pop" (runRshiftmodDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow-before-type" (runRshiftmodDirect #[.null]) .stkUnd
        expectErr "shift-top-null" (runRshiftmodDirect #[intV 1, .null]) .typeChk
        expectErr "x-second-null" (runRshiftmodDirect #[.null, intV 1]) .typeChk
        expectErr "shift-negative-range" (runRshiftmodDirect #[intV 5, intV (-1)]) .rangeChk
        expectErr "shift-too-large-range" (runRshiftmodDirect #[intV 5, intV 257]) .rangeChk
        expectErr "pop-order-shift-range-before-x-type" (runRshiftmodDirect #[.null, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "fallback" (runRshiftmodDispatchFallback #[]) #[intV 606] }
  ]
  oracle := #[
    mkCase "ok/basic/pos-shift-two" #[intV 13, intV 2],
    mkCase "ok/basic/neg-shift-two" #[intV (-13), intV 2],
    mkCase "ok/basic/small-pos-shift-three" #[intV 7, intV 3],
    mkCase "ok/basic/small-neg-shift-three" #[intV (-7), intV 3],
    mkCase "ok/basic/shift-zero-pos" #[intV 9, intV 0],
    mkCase "ok/basic/shift-zero-neg" #[intV (-9), intV 0],
    mkCase "ok/basic/neg-near-zero" #[intV (-1), intV 1],
    mkCase "ok/basic/zero-value" #[intV 0, intV 200],
    mkCase "boundary/max-shift-zero" #[intV maxInt257, intV 0],
    mkCase "boundary/min-shift-zero" #[intV minInt257, intV 0],
    mkCase "boundary/max-shift-256" #[intV maxInt257, intV 256],
    mkCase "boundary/max-minus-one-shift-256" #[intV (maxInt257 - 1), intV 256],
    mkCase "boundary/min-shift-256" #[intV minInt257, intV 256],
    mkCase "boundary/min-plus-one-shift-256" #[intV (minInt257 + 1), intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 1],
    mkCase "error-order/single-non-int-underflow-before-type" #[.null],
    mkCase "type/shift-top-null" #[intV 1, .null],
    mkCase "type/x-second-null" #[.null, intV 1],
    mkCase "type/error-order-both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative" #[intV 5, intV (-1)],
    mkCase "range/shift-gt-256" #[intV 5, intV 257],
    mkCase "error-order/shift-range-before-x-type" #[.null, intV 257],
    mkCase "nan/shift-via-program" #[intV 5] #[.pushInt .nan, rshiftmodInstr],
    mkCase "nan/x-via-program" #[intV 5] #[.pushInt .nan, .xchg0 1, rshiftmodInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 13, intV 2]
      #[.pushInt (.num rshiftmodSetGasExact), .tonEnvOp .setGasLimit, rshiftmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 13, intV 2]
      #[.pushInt (.num rshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020808
      count := 700
      gen := genRshiftmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTMOD
