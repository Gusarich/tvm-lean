import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFT_VAR

/-
QLSHIFT_VAR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.lshiftVar true)` path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, quiet signed-257 funnel)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_lshift`, opcode wiring in `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`)

Branch counts used for this suite:
- Lean specialization: 6 branch sites / 10 terminal outcomes
  (dispatch/fallback; shift pop underflow/type/ok; bad-shift gate;
   x pop underflow/type/ok; x NaN-vs-num split; quiet push finite-vs-NaN).
- C++ specialization: 5 branch sites / 9 aligned terminal outcomes
  (`check_underflow`; `pop_long` type path; range gate;
   `pop_int` type path; quiet result split for bad-shift or invalid `x`).

Key risk areas covered:
- runtime shift bounds `0..1023` with out-of-immediate-range coverage (`257..1023`);
- quiet bad-shift behavior (`shift < 0` / `shift > 1023`) must produce NaN, not throw;
- pop order (`shift` consumed first, then `x`) including bad-shift + `x` type precedence;
- quiet signed-257 funnel for overflowed left-shift results;
- NaN handling for both `shift` and `x`, including oracle-safe program injection;
- exact gas cliff (`PUSHINT n; SETGASLIMIT; QLSHIFT_VAR`) exact vs exact-minus-one.
-/

private def qlshiftVarId : InstrId := { name := "QLSHIFT_VAR" }

private def qlshiftVarInstr : Instr :=
  .arithExt (.lshiftVar true)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftVarId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qlshiftVarInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQlshiftVarDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftVarInstr stack

private def runQlshiftVarDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 947)) stack

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

private def qlshiftVarSetGasExact : Int :=
  computeExactGasBudget qlshiftVarInstr

private def qlshiftVarSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftVarInstr

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

private def genQlshiftVarFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-x/boundary-shift" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-x/boundary-shift" #[intV x, intV shift], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-x/random-shift" #[intV x, intV shift], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-x/random-shift" #[intV x, intV shift], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftOutOfImmediateRange r2
      (mkCase s!"fuzz/shape-{shape}/ok/random-x/out-of-immediate-range-shift" #[intV x, intV shift], r3)
    else if shape = 5 then
      let (shift, r2) := pickShiftOutOfImmediateRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok/zero-stable/huge-shift" #[intV 0, intV shift], r2)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow/max-shift1" #[intV maxInt257, intV 1], rng1)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow/min-shift1" #[intV minInt257, intV 1], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow/one-shift256" #[intV 1, intV 256], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (amt, r3) := randNat r2 1 16
      let shift := -Int.ofNat amt
      (mkCase s!"fuzz/shape-{shape}/quiet/range/bad-negative-shift" #[intV x, intV shift], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftN, r3) := randNat r2 1024 4096
      (mkCase s!"fuzz/shape-{shape}/quiet/range/bad-overmax-shift" #[intV x, intV (Int.ofNat shiftN)], r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/error/underflow/empty-stack" #[], rng1)
    else if shape = 12 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"fuzz/shape-{shape}/error/underflow/missing-x-after-shift-pop" #[intV shift], r2)
    else if shape = 13 then
      let (top, r2) := pickNonInt rng1
      (mkCase s!"fuzz/shape-{shape}/error/type/shift-pop-first" #[intV 7, top], r2)
    else if shape = 14 then
      let (shift, r2) := pickShiftInRange rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error/type/x-pop-second" #[xLike, intV shift], r3)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      let (shiftLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error/order/both-non-int-shift-first" #[xLike, shiftLike], r3)
    else if shape = 16 then
      let (pickOver, r2) := randBool rng1
      let shift : Int := if pickOver then 1024 else -1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/type-x-on-bad-shift" #[xLike, intV shift], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/shift-via-program" #[.num x, .nan], r2)
    else if shape = 18 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/x-via-program" #[.nan, .num shift], r2)
    else if shape = 19 then
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan/both-via-program" #[.nan, .nan], rng1)
    else if shape = 20 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[.num xo, .num shift], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[.num x, .num yo], r3)
    else
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        #[.num xo, .num yo], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftVarId
  unit := #[
    { name := "unit/direct/finite-boundaries-and-quiet-overflow-funnel"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 1, 14),
            (-7, 1, -14),
            (7, 2, 28),
            (-7, 2, -28),
            (1, 255, pow2 255),
            (-1, 255, -(pow2 255)),
            (-1, 256, minInt257),
            (maxInt257, 0, maxInt257),
            (minInt257, 0, minInt257),
            (-(pow2 255), 1, minInt257)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"ok/{x}-shift-{shift}" (runQlshiftVarDirect #[intV x, intV shift]) #[intV expected]
        expectOkStack "ok/0-shift-1023"
          (runQlshiftVarDirect #[intV 0, intV 1023]) #[.int .nan]
        let quietNanChecks : Array (Int × Int) :=
          #[
            (maxInt257, 1),
            (minInt257, 1),
            (1, 256),
            (1, 257),
            (-1, 257),
            (pow2 255, 1),
            (pow2 257, 0),
            (-(pow2 257), 0)
          ]
        for c in quietNanChecks do
          let x := c.1
          let shift := c.2
          expectOkStack s!"quiet/overflow/{x}-shift-{shift}"
            (runQlshiftVarDirect #[intV x, intV shift]) #[.int .nan]
        expectOkStack "ok/lower-stack-preserved"
          (runQlshiftVarDirect #[.null, intV 7, intV 1]) #[.null, intV 14] }
    ,
    { name := "unit/direct/quiet-range-and-nan-funnel"
      run := do
        expectOkStack "quiet/range/shift-negative" (runQlshiftVarDirect #[intV 7, intV (-1)]) #[.int .nan]
        expectOkStack "quiet/range/shift-over-1023" (runQlshiftVarDirect #[intV 7, intV 1024]) #[.int .nan]
        expectOkStack "quiet/range/shift-way-over-1023" (runQlshiftVarDirect #[intV 7, intV 4096]) #[.int .nan]
        expectOkStack "quiet/nan/shift-nan" (runQlshiftVarDirect #[intV 7, .int .nan]) #[.int .nan]
        expectOkStack "quiet/nan/x-nan-shift0" (runQlshiftVarDirect #[.int .nan, intV 0]) #[.int .nan]
        expectOkStack "quiet/nan/x-nan-shift300" (runQlshiftVarDirect #[.int .nan, intV 300]) #[.int .nan]
        expectOkStack "quiet/overflow/x-overflow-shift0"
          (runQlshiftVarDirect #[intV (pow2 257), intV 0]) #[.int .nan]
        expectOkStack "quiet/overflow/x-underflow-shift0"
          (runQlshiftVarDirect #[intV (-(pow2 257)), intV 0]) #[.int .nan] }
    ,
    { name := "unit/direct/underflow-type-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runQlshiftVarDirect #[]) .stkUnd
        expectErr "underflow/missing-x-after-shift-pop" (runQlshiftVarDirect #[intV 7]) .stkUnd
        expectErr "type/single-non-int-shift-pop" (runQlshiftVarDirect #[.null]) .stkUnd
        expectErr "type/shift-top-null" (runQlshiftVarDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second-null" (runQlshiftVarDirect #[.null, intV 7]) .typeChk
        expectErr "type/both-non-int-shift-first"
          (runQlshiftVarDirect #[.cell Cell.empty, .null]) .typeChk
        expectErr "error-order/type-x-on-shift-nan"
          (runQlshiftVarDirect #[.null, .int .nan]) .typeChk
        expectErr "error-order/type-x-on-bad-shift-negative"
          (runQlshiftVarDirect #[.null, intV (-1)]) .typeChk
        expectErr "error-order/type-x-on-bad-shift-overmax"
          (runQlshiftVarDirect #[.null, intV 1024]) .typeChk }
    ,
    { name := "unit/opcode/decode-qlshift-var-sequence"
      run := do
        let program : Array Instr := #[qlshiftVarInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qlshift-var" s0 qlshiftVarInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQlshiftVarDispatchFallback #[]) #[intV 947] }
  ]
  oracle := #[
    mkCase "ok/finite/shift0-pos" #[intV 12345, intV 0],
    mkCase "ok/finite/shift0-neg" #[intV (-12345), intV 0],
    mkCase "ok/finite/shift1-pos" #[intV 7, intV 1],
    mkCase "ok/finite/shift1-neg" #[intV (-7), intV 1],
    mkCase "ok/finite/shift2-pos" #[intV 7, intV 2],
    mkCase "ok/finite/shift2-neg" #[intV (-7), intV 2],
    mkCase "ok/finite/one-shift255" #[intV 1, intV 255],
    mkCase "ok/finite/neg-one-shift255" #[intV (-1), intV 255],
    mkCase "ok/finite/neg-one-shift256" #[intV (-1), intV 256],
    mkCase "ok/finite/zero-shift1023" #[intV 0, intV 1023],
    mkCase "ok/finite/min-edge-shift1" #[intV (-(pow2 255)), intV 1],
    mkCase "ok/out-of-immediate/zero-shift257" #[intV 0, intV 257],
    mkCase "ok/out-of-immediate/zero-shift511" #[intV 0, intV 511],
    mkCase "ok/out-of-immediate/zero-shift1023" #[intV 0, intV 1023],
    mkCase "quiet/overflow/max-shift1" #[intV maxInt257, intV 1],
    mkCase "quiet/overflow/min-shift1" #[intV minInt257, intV 1],
    mkCase "quiet/overflow/one-shift256" #[intV 1, intV 256],
    mkCase "quiet/overflow/one-shift257" #[intV 1, intV 257],
    mkCase "quiet/overflow/neg-one-shift257" #[intV (-1), intV 257],
    mkCase "quiet/overflow/pow2-255-shift1" #[intV (pow2 255), intV 1],
    mkCase "error/underflow/empty-stack" #[],
    mkCase "error/underflow/missing-x-after-shift-pop" #[intV 1],
    mkCase "error/type/shift-top-null" #[intV 7, .null],
    mkCase "error/type/shift-top-cell" #[intV 7, .cell Cell.empty],
    mkCase "error/type/x-second-null" #[.null, intV 7],
    mkCase "error/type/x-second-cell" #[.cell Cell.empty, intV 7],
    mkCase "error/order/both-non-int-shift-first" #[.cell Cell.empty, .null],
    mkCase "quiet/range/shift-negative" #[intV 7, intV (-1)],
    mkCase "quiet/range/shift-over-1023" #[intV 7, intV 1024],
    mkCase "quiet/range/shift-way-over-1023" #[intV 7, intV 4096],
    mkCase "error-order/type-x-on-bad-shift-negative" #[.null, intV (-1)],
    mkCase "error-order/type-x-on-bad-shift-overmax" #[.null, intV 1024],
    mkCaseFromIntVals "quiet/nan/shift-via-program" #[.num 7, .nan],
    mkCaseFromIntVals "quiet/nan/x-via-program-shift0" #[.nan, .num 0],
    mkCaseFromIntVals "quiet/nan/x-via-program-shift300" #[.nan, .num 300],
    mkCaseFromIntVals "quiet/nan/both-via-program" #[.nan, .nan],
    mkCaseFromIntVals "error-order/pushint-overflow-x-before-qlshift-var"
      #[.num (maxInt257 + 1), .num 0],
    mkCaseFromIntVals "error-order/pushint-underflow-x-before-qlshift-var"
      #[.num (minInt257 - 1), .num 0],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-before-qlshift-var"
      #[.num 7, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-underflow-shift-before-qlshift-var"
      #[.num 7, .num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-both-before-qlshift-var"
      #[.num (pow2 257), .num (-(pow2 257))],
    mkCase "gas/exact-cost-succeeds" #[intV 0, intV 300]
      #[.pushInt (.num qlshiftVarSetGasExact), .tonEnvOp .setGasLimit, qlshiftVarInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 0, intV 300]
      #[.pushInt (.num qlshiftVarSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftVarInstr]
  ]
  fuzz := #[
    { seed := 2026020833
      count := 700
      gen := genQlshiftVarFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFT_VAR
