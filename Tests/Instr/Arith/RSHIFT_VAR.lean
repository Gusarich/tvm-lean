import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFT_VAR

/-
RSHIFT_VAR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Rshift.lean`
    (`execInstrArithRshift`, `.rshift` runtime-shift path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popNatUpTo`, `popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_rshift`, opcode wiring in `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean specialization: 6 branch sites / 11 terminal outcomes
  (dispatch/fallback; `popNatUpTo` underflow/type/range/ok; `x` pop underflow/type/ok;
   NaN-vs-num; non-quiet `pushIntQuiet` fit-vs-`intOv` for oversized numeric results).
- C++ specialization: 6 branch sites / 10 aligned terminal outcomes
  (`check_underflow`; `pop_long` type/range gate; `pop_int` type path;
   invalid-`x` (`!is_valid`) path; `push_int_quiet` fit-vs-`int_ov` in non-quiet mode).

Key risk areas covered:
- strict runtime shift bounds `0..1023` (including out-of-immediate-range `257..1023`);
- error precedence: bad shift (`rangeChk`) must happen before `x` type checks;
- pop order (`shift` first, then `x`) with underflow/type combinations;
- arithmetic sign-extension across sign combinations and boundary/near-boundary values;
- NaN and out-of-range integer injection via program prelude only (serialization-safe);
- deterministic gas edge for `PUSHINT n; SETGASLIMIT; RSHIFT_VAR`.
-/

private def rshiftVarId : InstrId := { name := "RSHIFT_VAR" }

private def rshiftVarInstr : Instr := .rshift

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rshiftVarId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[rshiftVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runRshiftVarDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithRshift rshiftVarInstr stack

private def runRshiftVarDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithRshift .add (VM.push (intV 953)) stack

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

private def rshiftVarSetGasExact : Int :=
  computeExactGasBudget rshiftVarInstr

private def rshiftVarSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftVarInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 511, 512, 1022, 1023]

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (Int.ofNat shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 0 1023
  (Int.ofNat n, rng')

private def pickShiftOutOfImmediateRange (rng : StdGen) : Int × StdGen :=
  let (n, rng') := randNat rng 257 1023
  (Int.ofNat n, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  ((if pick = 0 then .null else .cell Cell.empty), rng')

private def genRshiftVarFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-x-boundary-shift" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-x-boundary-shift" #[intV x, intV shift], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-boundary-x-random-shift" #[intV x, intV shift], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-x-random-shift" #[intV x, intV shift], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftOutOfImmediateRange r2
      (mkCase s!"fuzz/shape-{shape}/ok-random-x-out-of-immediate-range-shift" #[intV x, intV shift], r3)
    else if shape = 5 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok-sign-minus-one" #[intV (-1), intV shift], r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok-sign-plus-one" #[intV 1, intV shift], r2)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/ok-near-boundary-max-minus-one-shift1"
        #[intV (maxInt257 - 1), intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/ok-near-boundary-min-plus-one-shift1"
        #[intV (minInt257 + 1), intV 1], rng1)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty-stack" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-missing-x-after-shift-pop" #[intV x], r2)
    else if shape = 11 then
      let (top, r2) := pickNonInt rng1
      (mkCase s!"fuzz/shape-{shape}/type-shift-pop-first" #[intV 7, top], r2)
    else if shape = 12 then
      let (shift, r2) := pickShiftInRange rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/type-x-pop-second" #[xLike, intV shift], r3)
    else if shape = 13 then
      let (xLike, r2) := pickNonInt rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order-both-non-int-shift-first" #[xLike, shiftLike], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (amt, r3) := randNat r2 1 16
      let shift := -Int.ofNat amt
      (mkCase s!"fuzz/shape-{shape}/range-negative-shift" #[intV x, intV shift], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftN, r3) := randNat r2 1024 4096
      (mkCase s!"fuzz/shape-{shape}/range-overmax-shift" #[intV x, intV (Int.ofNat shiftN)], r3)
    else if shape = 16 then
      let (useOver, r2) := randBool rng1
      let badShift : Int := if useOver then 1024 else -1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order-range-before-x-type" #[xLike, intV badShift], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-shift-via-program" #[.num x, .nan], r2)
    else if shape = 18 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/nan-x-via-program" #[.nan, .num shift], r2)
    else if shape = 19 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/out-of-range-x-via-program" #[.num xo, .num shift], r3)
    else if shape = 20 then
      let (pickPos, r2) := randBool rng1
      let vals : Array IntVal :=
        if pickPos then
          #[.num (pow2 257), .num 2]
        else
          #[.num (-(pow2 257)), .num 1]
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/out-of-range-x-fold-finite-via-program" vals, r2)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order-pushint-overflow-shift-before-op"
        #[.num x, .num yo], r3)
    else
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order-pushint-overflow-both-before-op"
        #[.num xo, .num yo], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftVarId
  unit := #[
    { name := "unit/direct/floor-sign-boundary-and-near-boundary-shifts"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (7, 1, 3),
            (-7, 1, -4),
            (7, 2, 1),
            (-7, 2, -2),
            (0, 0, 0),
            (123, 0, 123),
            (-123, 0, -123),
            (maxInt257, 255, 1),
            (minInt257, 255, -2),
            (maxInt257, 256, 0),
            (minInt257, 256, -1),
            (maxInt257, 257, 0),
            (minInt257, 257, -1),
            (maxInt257, 1023, 0),
            (minInt257, 1023, -1),
            (maxInt257 - 1, 1, (pow2 255) - 1),
            (minInt257 + 1, 1, -(pow2 255)),
            (1, 1023, 0),
            (-1, 1023, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>{shift}" (runRshiftVarDirect #[intV x, intV shift]) #[intV expected] }
    ,
    { name := "unit/direct/range-checks-and-range-before-x-precedence"
      run := do
        expectErr "range/shift-negative" (runRshiftVarDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/shift-over-1023" (runRshiftVarDirect #[intV 7, intV 1024]) .rangeChk
        expectErr "range/shift-way-over-1023" (runRshiftVarDirect #[intV 7, intV 4096]) .rangeChk
        expectErr "error-order/range-before-x-type-negative"
          (runRshiftVarDirect #[.null, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-x-type-overmax"
          (runRshiftVarDirect #[.cell Cell.empty, intV 1024]) .rangeChk }
    ,
    { name := "unit/direct/underflow-type-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runRshiftVarDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runRshiftVarDirect #[intV 7]) .stkUnd
        expectErr "type/single-non-int-shift-pop" (runRshiftVarDirect #[.null]) .typeChk
        expectErr "type/shift-top-null" (runRshiftVarDirect #[intV 7, .null]) .typeChk
        expectErr "type/shift-top-cell" (runRshiftVarDirect #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "type/x-second-null" (runRshiftVarDirect #[.null, intV 7]) .typeChk
        expectErr "type/x-second-cell" (runRshiftVarDirect #[.cell Cell.empty, intV 7]) .typeChk
        expectErr "type/both-non-int-shift-first"
          (runRshiftVarDirect #[.cell Cell.empty, .null]) .typeChk
        expectOkStack "ok/top-only-consumed/lower-preserved"
          (runRshiftVarDirect #[.null, intV (-8), intV 1]) #[.null, intV (-4)] }
    ,
    { name := "unit/opcode/decode-rshift-var-sequence"
      run := do
        let program : Array Instr := #[rshiftVarInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/rshift-var" s0 rshiftVarInstr 8
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-rshift-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runRshiftVarDispatchFallback #[]) #[intV 953] }
  ]
  oracle := #[
    mkCase "ok/floor/pos-shift1" #[intV 7, intV 1],
    mkCase "ok/floor/neg-shift1" #[intV (-7), intV 1],
    mkCase "ok/floor/pos-shift2" #[intV 7, intV 2],
    mkCase "ok/floor/neg-shift2" #[intV (-7), intV 2],
    mkCase "ok/identity/shift0-pos" #[intV 12345, intV 0],
    mkCase "ok/identity/shift0-neg" #[intV (-12345), intV 0],
    mkCase "ok/sign/one-shift1023" #[intV 1, intV 1023],
    mkCase "ok/sign/minus-one-shift1023" #[intV (-1), intV 1023],
    mkCase "ok/boundary/max-shift255" #[intV maxInt257, intV 255],
    mkCase "ok/boundary/min-shift255" #[intV minInt257, intV 255],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/near-boundary/max-minus-one-shift1" #[intV (maxInt257 - 1), intV 1],
    mkCase "ok/near-boundary/min-plus-one-shift1" #[intV (minInt257 + 1), intV 1],
    mkCase "ok/out-of-immediate/max-shift257" #[intV maxInt257, intV 257],
    mkCase "ok/out-of-immediate/min-shift257" #[intV minInt257, intV 257],
    mkCase "ok/out-of-immediate/max-shift511" #[intV maxInt257, intV 511],
    mkCase "ok/out-of-immediate/min-shift511" #[intV minInt257, intV 511],
    mkCase "ok/out-of-immediate/max-shift1023" #[intV maxInt257, intV 1023],
    mkCase "ok/out-of-immediate/min-shift1023" #[intV minInt257, intV 1023],
    mkCase "ok/pop-order/lower-preserved" #[.null, intV (-8), intV 1],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/missing-x-after-shift-pop" #[intV 7],
    mkCase "type/single-non-int-shift-pop" #[.null],
    mkCase "type/shift-top-null" #[intV 7, .null],
    mkCase "type/shift-top-cell" #[intV 7, .cell Cell.empty],
    mkCase "type/x-second-null" #[.null, intV 7],
    mkCase "type/x-second-cell" #[.cell Cell.empty, intV 7],
    mkCase "error-order/both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "range/shift-negative" #[intV 7, intV (-1)],
    mkCase "range/shift-over-1023" #[intV 7, intV 1024],
    mkCase "range/shift-way-over-1023" #[intV 7, intV 4096],
    mkCase "error-order/range-before-x-type-negative-shift" #[.null, intV (-1)],
    mkCase "error-order/range-before-x-type-overmax-shift" #[.null, intV 1024],
    mkCaseFromIntVals "nan/shift-via-program" #[.num 7, .nan],
    mkCaseFromIntVals "nan/x-via-program-shift0" #[.nan, .num 0],
    mkCaseFromIntVals "nan/x-via-program-shift300" #[.nan, .num 300],
    mkCaseFromIntVals "nan/both-via-program-shift-first-range" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-overflow-x-before-rshift-var"
      #[.num (maxInt257 + 1), .num 0],
    mkCaseFromIntVals "error-order/pushint-underflow-x-before-rshift-var"
      #[.num (minInt257 - 1), .num 0],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-before-rshift-var"
      #[.num 7, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-underflow-shift-before-rshift-var"
      #[.num 7, .num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-both-before-rshift-var"
      #[.num (pow2 257), .num (-(pow2 257))],
    mkCaseFromIntVals "range/out-of-range-x-still-overflow-via-program-pos"
      #[.num (pow2 257), .num 1],
    mkCaseFromIntVals "range/out-of-range-x-still-overflow-via-program-neg"
      #[.num (-(pow2 257)), .num 0],
    mkCaseFromIntVals "range/out-of-range-x-folds-finite-via-program-pos"
      #[.num (pow2 257), .num 2],
    mkCaseFromIntVals "range/out-of-range-x-folds-finite-via-program-neg"
      #[.num (-(pow2 257)), .num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 300]
      #[.pushInt (.num rshiftVarSetGasExact), .tonEnvOp .setGasLimit, rshiftVarInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 300]
      #[.pushInt (.num rshiftVarSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftVarInstr]
  ]
  fuzz := #[
    { seed := 2026020832
      count := 700
      gen := genRshiftVarFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFT_VAR
