import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_VAR

/-
LSHIFT_VAR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Lshift.lean` (`execInstrArithLshift`, opcode `.lshift`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popNatUpTo`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xac` decode, 8-bit `LSHIFT_VAR`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_lshift`, opcode wiring in `register_add_mul_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `push_int_quiet`)

Branch counts used for this suite (`LSHIFT_VAR`, non-quiet):
- Lean: 7 branch sites / 10 terminal outcomes
  (dispatch/fallback; pre-pop underflow gate; shift pop type/range split;
   `x` pop type split; finite-vs-NaN `x`; non-quiet push success vs `intOv`).
- C++: 6 branch sites / 10 aligned terminal outcomes
  (`check_underflow(2)`; `pop_long` type/range path; strict range gate;
   `pop_int` type split; finite-vs-invalid `x`; non-quiet `push_int_quiet` overflow/NaN throw).

Key risk areas covered:
- strict pop/error ordering: underflow before shift-type/range checks for short stacks;
- runtime shift bounds `[0, 1023]` and the `>=260` overflow/NaN cliff;
- shift is popped before `x`, so shift range/type can mask `x`-side type errors;
- signed-257 boundary cliffs around `255/256/259/260/1023` exponents;
- non-quiet NaN and out-of-range integer injection only through program `PUSHINT`;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFT_VAR` (exact vs exact-minus-one).
-/

private def lshiftVarId : InstrId := { name := "LSHIFT_VAR" }

private def lshiftVarInstr : Instr := .lshift

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftVarId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[lshiftVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def mkShiftInjectedCase
    (name : String)
    (x : Value)
    (shift : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[x] #[.pushInt shift, lshiftVarInstr] gasLimits fuel

private def runLshiftVarDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithLshift lshiftVarInstr stack

private def runLshiftVarDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithLshift .add (VM.push (intV 3417)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def lshiftVarSetGasExact : Int :=
  computeExactGasBudget lshiftVarInstr

private def lshiftVarSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftVarInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 259, 260, 511, 1023]

private def shiftNegativePool : Array Int :=
  #[-1, -2, -7, -128, -1024]

private def shiftOvermaxPool : Array Int :=
  #[1024, 1025, 2048, 4096]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftInRange (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromPool shiftBoundaryPool rng1
  else
    let (n, rng2) := randNat rng1 0 1023
    (Int.ofNat n, rng2)

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def genLshiftVarFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickFromPool shiftBoundaryPool r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-x-boundary-shift" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-x-random-shift" #[intV x, intV shift], r3)
    else if shape = 2 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok-zero-stable-large-shift" #[intV 0, intV shift], r2)
    else if shape = 3 then
      let (variant, r2) := randNat rng1 0 3
      let x :=
        if variant = 0 then
          (pow2 255) - 1
        else if variant = 1 then
          -(pow2 255)
        else if variant = 2 then
          (-1 : Int)
        else
          (1 : Int)
      let shift := if variant = 3 then 255 else 1
      (mkCase s!"fuzz/shape-{shape}/ok-near-boundary" #[intV x, intV shift], r2)
    else if shape = 4 then
      (mkCase s!"fuzz/shape-{shape}/overflow-max-shift1" #[intV maxInt257, intV 1], rng1)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/overflow-min-shift1" #[intV minInt257, intV 1], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/overflow-one-shift256" #[intV 1, intV 256], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool shiftNegativePool r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-negative" #[intV x, intV shift], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool shiftOvermaxPool r2
      (mkCase s!"fuzz/shape-{shape}/range-shift-overmax" #[intV x, intV shift], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" (intV x) .nan, r2)
    else if shape = 10 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program" #[.nan, .num shift], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftLike, r3) := pickNonIntLike r2
      (mkCase s!"fuzz/shape-{shape}/type-shift-top-non-int" #[intV x, shiftLike], r3)
    else if shape = 12 then
      let (xLike, r2) := pickNonIntLike rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/type-x-second-non-int" #[xLike, intV shift], r3)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-int" #[intV x], r2)
    else if shape = 15 then
      let (v, r2) := pickNonIntLike rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-before-shift-type-single-item" #[v], r2)
    else if shape = 16 then
      let (xLike, r2) := pickNonIntLike rng1
      let (shift, r3) := pickFromPool shiftNegativePool r2
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-x-type-negative" #[xLike, intV shift], r3)
    else if shape = 17 then
      let (shift, r2) := pickFromPool shiftOvermaxPool rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-before-shift-range-via-program"
        #[] #[.pushInt (.num shift), lshiftVarInstr], r2)
    else if shape = 18 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/pushint-overflow-x-before-op"
        #[.num xo, .num shift], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/pushint-overflow-shift-before-op"
        #[.num x, .num yo], r3)
    else if shape = 20 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/pushint-overflow-both-before-op"
        #[.num xo, .num yo], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (below, r4) := pickNonIntLike r3
      (mkCase s!"fuzz/shape-{shape}/ok-below-preserved" #[below, intV x, intV shift], r4)
    else
      let (xLike, r2) := pickNonIntLike rng1
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order-range-before-x-type-nan-shift-via-program"
        xLike .nan, r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftVarId
  unit := #[
    { name := "unit/direct/success-near-boundary-and-below-preservation"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 0, 7),
            (7, 1, 14),
            (-7, 1, -14),
            (3, 4, 48),
            (1, 255, pow2 255),
            (-1, 255, -(pow2 255)),
            (-1, 256, minInt257),
            ((pow2 255) - 1, 1, maxInt257 - 1),
            (-(pow2 255), 1, minInt257),
            (maxInt257, 0, maxInt257),
            (minInt257, 0, minInt257),
            (0, 259, 0)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}<<{shift}" (runLshiftVarDirect #[intV x, intV shift]) #[intV expected]
        expectOkStack "ok/below-preserved"
          (runLshiftVarDirect #[.null, intV 7, intV 3]) #[.null, intV 56] }
    ,
    { name := "unit/direct/error-intov-overflow-cliff"
      run := do
        expectErr "overflow/max-shift1" (runLshiftVarDirect #[intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-shift1" (runLshiftVarDirect #[intV minInt257, intV 1]) .intOv
        expectErr "overflow/one-shift256" (runLshiftVarDirect #[intV 1, intV 256]) .intOv
        expectErr "overflow/zero-shift260" (runLshiftVarDirect #[intV 0, intV 260]) .intOv
        expectErr "overflow/max-shift1023" (runLshiftVarDirect #[intV maxInt257, intV 1023]) .intOv }
    ,
    { name := "unit/direct/error-underflow-range-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runLshiftVarDirect #[]) .stkUnd
        expectErr "underflow/single-int" (runLshiftVarDirect #[intV 1]) .stkUnd
        expectErr "underflow/single-non-int" (runLshiftVarDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runLshiftVarDirect #[intV 7, .null]) .typeChk
        expectErr "type/shift-top-cell" (runLshiftVarDirect #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "type/x-second-null" (runLshiftVarDirect #[.null, intV 1]) .typeChk
        expectErr "type/x-second-cell" (runLshiftVarDirect #[.cell Cell.empty, intV 1]) .typeChk
        expectErr "type/error-order-shift-type-before-x-type"
          (runLshiftVarDirect #[.null, .cell Cell.empty]) .typeChk
        expectErr "range/shift-negative" (runLshiftVarDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-overmax" (runLshiftVarDirect #[intV 7, intV 1024]) .rangeChk
        expectErr "error-order/range-before-x-type-negative"
          (runLshiftVarDirect #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-overmax"
          (runLshiftVarDirect #[.cell Cell.empty, intV 1024]) .rangeChk }
    ,
    { name := "unit/opcode/decode-lshift-var-sequence"
      run := do
        let program : Array Instr := #[lshiftVarInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/lshift-var" s0 lshiftVarInstr 8
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-lshift-var-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runLshiftVarDispatchFallback #[]) #[intV 3417] }
  ]
  oracle := #[
    mkCase "ok/shift-zero/zero" #[intV 0, intV 0],
    mkCase "ok/shift-zero/pos" #[intV 7, intV 0],
    mkCase "ok/shift-zero/neg" #[intV (-7), intV 0],
    mkCase "ok/shift-one/pos" #[intV 7, intV 1],
    mkCase "ok/shift-one/neg" #[intV (-7), intV 1],
    mkCase "ok/shift-four/pos" #[intV 3, intV 4],
    mkCase "ok/boundary/max-shift-zero" #[intV maxInt257, intV 0],
    mkCase "ok/boundary/min-shift-zero" #[intV minInt257, intV 0],
    mkCase "ok/boundary/pos-near-max-shift-one" #[intV ((pow2 255) - 1), intV 1],
    mkCase "ok/boundary/neg-pow2-255-shift-one" #[intV (-(pow2 255)), intV 1],
    mkCase "ok/boundary/one-shift-255" #[intV 1, intV 255],
    mkCase "ok/boundary/neg-one-shift-256" #[intV (-1), intV 256],
    mkCase "ok/boundary/zero-shift-259" #[intV 0, intV 259],
    mkCase "ok/top-order/below-preserved" #[.null, intV 7, intV 3],
    mkCase "overflow/max-shift-one" #[intV maxInt257, intV 1],
    mkCase "overflow/min-shift-one" #[intV minInt257, intV 1],
    mkCase "overflow/one-shift-256" #[intV 1, intV 256],
    mkCase "overflow/zero-shift-260" #[intV 0, intV 260],
    mkCase "overflow/max-shift-1023" #[intV maxInt257, intV 1023],
    mkCase "range/shift-negative" #[intV 7, intV (-1)],
    mkCase "range/shift-overmax" #[intV 7, intV 1024],
    mkShiftInjectedCase "range/shift-nan-via-program" (intV 7) .nan,
    mkShiftInjectedCase "error-order/range-before-x-type-negative-via-program" .null (.num (-1)),
    mkShiftInjectedCase "error-order/range-before-x-type-overmax-via-program"
      (.cell Cell.empty) (.num 1024),
    mkShiftInjectedCase "error-order/range-before-x-type-nan-shift-via-program"
      .null .nan,
    mkCaseFromIntVals "nan/x-via-program" #[.nan, .num 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/single-int" #[intV 1],
    mkCase "underflow/single-non-int" #[.null],
    mkCase "type/shift-top-null" #[intV 7, .null],
    mkCase "type/shift-top-cell" #[intV 7, .cell Cell.empty],
    mkCase "type/x-second-null" #[.null, intV 1],
    mkCase "type/x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/shift-type-before-x-type" #[.null, .cell Cell.empty],
    mkCaseFromIntVals "error-order/pushint-overflow-x-before-op"
      #[.num (maxInt257 + 1), .num 1],
    mkCaseFromIntVals "error-order/pushint-underflow-x-before-op"
      #[.num (minInt257 - 1), .num 1],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-before-op"
      #[.num 7, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-underflow-shift-before-op"
      #[.num 7, .num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-both-before-op"
      #[.num (pow2 257), .num (-(pow2 257))],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num lshiftVarSetGasExact), .tonEnvOp .setGasLimit, lshiftVarInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num lshiftVarSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftVarInstr]
  ]
  fuzz := #[
    { seed := 2026020837
      count := 700
      gen := genLshiftVarFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_VAR
