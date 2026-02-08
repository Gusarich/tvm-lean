import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTMODC

/- 
RSHIFTMODC branch-mapping notes (Lean + C++ reference):

- Lean analyzed file:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 3 1 false (some z)` path)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, opcode wiring in `register_div_ops`)

Branch counts used for this suite:
- Lean (RSHIFTMODC specialization): 6 branch sites / 8 terminal outcomes
  (dispatch/fallback; explicit underflow gate for const-shift mode; `popInt`
   type check; numeric-vs-NaN split; fixed `d=3` two-result path; non-quiet
   `pushIntQuiet` success vs `intOv`).
- C++ (`exec_shrmod` const-shift form): 5 branch sites / 8 aligned outcomes
  (invalid-opcode guard; `check_underflow(1)`; `pop_int` type gate; `d` switch
   selecting `RSHIFTMOD`; two `push_int_quiet` overflow/NaN throw funnels).

Key risk areas covered:
- ceil quotient/remainder semantics for mixed signs (`z=1`, `z=2`, `z=256`);
- output order (`q` then `r`) and single-pop stack discipline (top consumed,
  below preserved);
- strict error ordering (empty stack underflow before type path; non-empty
  non-int hits `typeChk`);
- non-quiet NaN and out-of-range numeric inputs (injected via program only);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; RSHIFTMODC`.
-/

private def rshiftmodcId : InstrId := { name := "RSHIFTMODC" }

private def mkRshiftmodcInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 3 1 false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rshiftmodcId
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
  mkCase name stack #[mkRshiftmodcInstr shift] gasLimits fuel

private def mkShiftCaseFromIntVals
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkRshiftmodcInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runRshiftmodcDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkRshiftmodcInstr shift) stack

private def runRshiftmodcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4040)) stack

private def rshiftmodcGasProbeInstr : Instr :=
  mkRshiftmodcInstr 7

private def rshiftmodcSetGasExact : Int :=
  computeExactGasBudget rshiftmodcGasProbeInstr

private def rshiftmodcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftmodcGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def genRshiftmodcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"fuzz/shape-{shape}/ok-boundary" shift #[intV x], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"fuzz/shape-{shape}/ok-boundary-signed" shift #[intV x], r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"fuzz/shape-{shape}/ok-random-shift" shift #[intV x], r3)
    else if shape = 3 then
      let (shift, r2) := pickShiftInRange rng1
      let (pickNull, r3) := randBool r2
      let below : Value := if pickNull then .null else .cell Cell.empty
      let (x, r4) := pickSigned257ish r3
      (mkShiftCase s!"fuzz/shape-{shape}/pop-order-below-preserved" shift #[below, intV x], r4)
    else if shape = 4 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"fuzz/shape-{shape}/underflow-empty" shift #[], r2)
    else if shape = 5 then
      let (shift, r2) := pickShiftBoundary rng1
      let (pickNull, r3) := randBool r2
      let xLike : Value := if pickNull then .null else .cell Cell.empty
      (mkShiftCase s!"fuzz/shape-{shape}/type-top-non-int" shift #[xLike], r3)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCaseFromIntVals s!"fuzz/shape-{shape}/nan-via-program" shift #[IntVal.nan], r2)
    else if shape = 7 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCaseFromIntVals s!"fuzz/shape-{shape}/nan-via-program-alt" shift #[IntVal.nan], r2)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"fuzz/shape-{shape}/ok-max-boundary" shift #[intV maxInt257], r2)
    else
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"fuzz/shape-{shape}/ok-min-boundary" shift #[intV minInt257], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftmodcId
  unit := #[
    { name := "unit/direct/ceil-quotient-remainder-and-output-order"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (7, 1, 4, -1),
            (-7, 1, -3, -1),
            (7, 2, 2, -1),
            (-7, 2, -1, -3),
            (1, 1, 1, -1),
            (-1, 1, 0, -1),
            (8, 3, 1, 0),
            (-8, 3, -1, 0),
            (maxInt257, 256, 1, -1),
            (minInt257, 256, -1, 0),
            (minInt257 + 1, 256, 0, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"x={x}/z={shift}" (runRshiftmodcDirect shift #[intV x]) #[intV q, intV r] }
    ,
    { name := "unit/pop-order/top-consumed-and-below-preserved"
      run := do
        expectOkStack "below-null" (runRshiftmodcDirect 1 #[.null, intV 7]) #[.null, intV 4, intV (-1)]
        expectOkStack "below-cell" (runRshiftmodcDirect 2 #[.cell Cell.empty, intV (-7)])
          #[.cell Cell.empty, intV (-1), intV (-3)] }
    ,
    { name := "unit/error-order/underflow-and-type-paths"
      run := do
        expectErr "underflow/empty" (runRshiftmodcDirect 1 #[]) .stkUnd
        expectErr "type/top-null" (runRshiftmodcDirect 1 #[.null]) .typeChk
        expectErr "type/top-cell" (runRshiftmodcDirect 1 #[.cell Cell.empty]) .typeChk }
    ,
    { name := "unit/dispatch/non-rshiftmodc-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runRshiftmodcDispatchFallback #[]) #[intV 4040] }
  ]
  oracle := #[
    mkShiftCase "ok/ceil/pos-odd-shift1" 1 #[intV 7],
    mkShiftCase "ok/ceil/neg-odd-shift1" 1 #[intV (-7)],
    mkShiftCase "ok/ceil/pos-odd-shift2" 2 #[intV 7],
    mkShiftCase "ok/ceil/neg-odd-shift2" 2 #[intV (-7)],
    mkShiftCase "ok/ceil/pos-half-shift1" 1 #[intV 1],
    mkShiftCase "ok/ceil/neg-half-shift1" 1 #[intV (-1)],
    mkShiftCase "ok/exact/divisible-pos" 3 #[intV 8],
    mkShiftCase "ok/exact/divisible-neg" 3 #[intV (-8)],
    mkShiftCase "ok/boundary/max-shift256" 256 #[intV maxInt257],
    mkShiftCase "ok/boundary/min-shift256" 256 #[intV minInt257],
    mkShiftCase "ok/boundary/min-plus-one-shift256" 256 #[intV (minInt257 + 1)],
    mkShiftCase "pop-order/below-preserved-null" 1 #[.null, intV 7],
    mkShiftCase "pop-order/below-preserved-cell" 2 #[.cell Cell.empty, intV (-7)],
    mkShiftCase "underflow/empty-stack" 1 #[],
    mkShiftCase "type/top-null" 1 #[.null],
    mkShiftCase "type/top-cell" 1 #[.cell Cell.empty],
    mkShiftCase "error-order/empty-underflow-before-type-path" 256 #[],
    mkShiftCase "error-order/non-empty-type-after-underflow-gate" 1 #[.null],
    mkShiftCaseFromIntVals "nan/x-via-program" 1 #[IntVal.nan],
    mkShiftCaseFromIntVals "nan/x-via-program-shift256" 256 #[IntVal.nan],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num rshiftmodcSetGasExact), .tonEnvOp .setGasLimit, rshiftmodcGasProbeInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num rshiftmodcSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftmodcGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020811
      count := 500
      gen := genRshiftmodcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTMODC
