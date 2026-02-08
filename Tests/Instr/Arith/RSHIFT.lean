import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFT

/-
RSHIFT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Rshift.lean` (`execInstrArithRshift`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popNatUpTo`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode/dispatch for stack `RSHIFT`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp` (`exec_rshift`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`check_underflow`, `pop_long`, `push_int_quiet`)

Branch counts used for this suite (`RSHIFT`, non-quiet):
- Lean: ~7 branch sites / ~10 terminal outcomes
  (dispatch/fallback; underflow gate; shift pop type/range split; `x` pop type split;
   finite-vs-NaN `x`; non-quiet push success vs `intOv`).
- C++: ~6 branch sites / ~10 aligned terminal outcomes
  (`check_underflow(2)`; shift parse/range gate; `x` parse/type gate;
   arithmetic right-shift success path; NaN/invalid funnel; non-quiet push behavior).

Key risk areas covered:
- pop-order and error-order (`shift` popped before `x`);
- runtime shift bounds `[0, 1023]` with negative/over-max/NaN shift probes;
- arithmetic sign extension for negative operands;
- underflow before any type/range checks on short stacks;
- oracle serialization constraints: NaN and non-serializable integers only via prelude program;
- exact gas cliff (`PUSHINT n; SETGASLIMIT; RSHIFT`).
-/

private def rshiftId : InstrId := { name := "RSHIFT" }

private def rshiftInstr : Instr := .rshift

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := rshiftId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[rshiftInstr])
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
  mkCase name #[x] #[.pushInt shift, rshiftInstr] gasLimits fuel

private def runRshiftDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithRshift rshiftInstr stack

private def runRshiftDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithRshift .add (VM.push (intV 3412)) stack

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

private def rshiftSetGasExact : Int :=
  computeExactGasBudget rshiftInstr

private def rshiftSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftInstr

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 1023]

private def shiftNegativePool : Array Int :=
  #[-1, -2, -7, -128, -1024]

private def shiftOvermaxPool : Array Int :=
  #[1024, 1025, 2048, 4096]

private def pushIntOverflowPool : Array Int :=
  #[pow2 256, minInt257 - 1, maxInt257 + 1, -(pow2 257)]

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

private def classifyRshift (x shift : Int) : String :=
  if shift = 0 then
    "ok-identity"
  else if x = 0 then
    "ok-zero"
  else if x < 0 then
    "ok-neg"
  else
    "ok-pos"

private def genRshiftFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickFromPool shiftBoundaryPool r2
      let kind := classifyRshift x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-shift-boundary" #[intV x, intV shift], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyRshift x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/random-inrange" #[intV x, intV shift], r3)
    else if shape = 2 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok-zero-with-shift" #[intV 0, intV shift], r2)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool shiftNegativePool r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-negative-shift-via-program" (intV x) (.num shift), r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool shiftOvermaxPool r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-overmax-shift-via-program" (intV x) (.num shift), r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range-shift-nan-via-program" (intV x) .nan, r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftInRange rng1
      (mkCase s!"fuzz/shape-{shape}/intov-nan-x-via-program" #[intV shift]
        #[.pushInt .nan, .xchg0 1, rshiftInstr], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shiftLike, r3) := pickNonIntLike r2
      (mkCase s!"fuzz/shape-{shape}/type-shift-top-non-int" #[intV x, shiftLike], r3)
    else if shape = 8 then
      let (xLike, r2) := pickNonIntLike rng1
      let (shift, r3) := pickShiftInRange r2
      (mkCase s!"fuzz/shape-{shape}/type-x-second-non-int" #[xLike, intV shift], r3)
    else if shape = 9 then
      (mkCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-int" #[intV x], r2)
    else if shape = 11 then
      let (v, r2) := pickNonIntLike rng1
      (mkCase s!"fuzz/shape-{shape}/underflow-single-non-int" #[v], r2)
    else if shape = 12 then
      let (xLike, r2) := pickNonIntLike rng1
      let (shift, r3) := pickFromPool shiftNegativePool r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/error-order-range-before-x-type" xLike (.num shift), r3)
    else if shape = 13 then
      let (big, r2) := pickFromPool pushIntOverflowPool rng1
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order-pushint-overflow-before-op"
        #[.num big, .num 1], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickFromPool shiftBoundaryPool r2
      let (below, r4) := pickNonIntLike r3
      let kind := classifyRshift x shift
      (mkCase s!"fuzz/shape-{shape}/{kind}/below-preserved" #[below, intV x, intV shift], r4)
    else if shape = 15 then
      (mkCase s!"fuzz/shape-{shape}/ok-max-shift1023" #[intV maxInt257, intV 1023], rng1)
    else
      (mkCase s!"fuzz/shape-{shape}/ok-min-shift1023" #[intV minInt257, intV 1023], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftId
  unit := #[
    { name := "unit/direct/success-sign-extension-and-boundaries"
      run := do
        let checks : Array (Int × Nat) :=
          #[
            (0, 0),
            (7, 0),
            (7, 1),
            (-7, 1),
            (17, 3),
            (-17, 3),
            (maxInt257, 1),
            (minInt257, 1),
            (maxInt257, 256),
            (minInt257, 256),
            (maxInt257, 1023),
            (minInt257, 1023)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2
          let expected := floorDivPow2 x shift
          expectOkStack s!"{x}>>{shift}" (runRshiftDirect #[intV x, intV shift]) #[intV expected]
        expectOkStack "below-preserved"
          (runRshiftDirect #[.null, intV (-17), intV 3]) #[.null, intV (floorDivPow2 (-17) 3)] }
    ,
    { name := "unit/error/underflow-range-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runRshiftDirect #[]) .stkUnd
        expectErr "underflow/single-int-before-range" (runRshiftDirect #[intV 257]) .stkUnd
        expectErr "underflow/single-non-int-before-type" (runRshiftDirect #[.null]) .typeChk
        expectErr "range/negative-shift" (runRshiftDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "range/overmax-shift" (runRshiftDirect #[intV 7, intV 1024]) .rangeChk
        expectErr "error-order/range-before-x-type" (runRshiftDirect #[.null, intV (-1)]) .rangeChk
        expectErr "type/shift-top-non-int" (runRshiftDirect #[intV 7, .null]) .typeChk
        expectErr "type/x-second-non-int" (runRshiftDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/error/nan-x-and-dispatch"
      run := do
        expectErr "intov/nan-x" (runRshiftDirect #[.int .nan, intV 1]) .intOv
        expectOkStack "dispatch/fallback" (runRshiftDispatchFallback #[]) #[intV 3412] }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[rshiftInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/rshift" s0 rshiftInstr 8
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
  ]
  oracle := #[
    mkCase "ok/identity/shift-zero-pos" #[intV 123456789, intV 0],
    mkCase "ok/identity/shift-zero-neg" #[intV (-123456789), intV 0],
    mkCase "ok/sign/pos-shift1" #[intV 7, intV 1],
    mkCase "ok/sign/neg-shift1" #[intV (-7), intV 1],
    mkCase "ok/sign/pos-shift3" #[intV 17, intV 3],
    mkCase "ok/sign/neg-shift3" #[intV (-17), intV 3],
    mkCase "ok/boundary/max-shift256" #[intV maxInt257, intV 256],
    mkCase "ok/boundary/min-shift256" #[intV minInt257, intV 256],
    mkCase "ok/boundary/max-shift1023" #[intV maxInt257, intV 1023],
    mkCase "ok/boundary/min-shift1023" #[intV minInt257, intV 1023],
    mkCase "ok/pop-order/below-preserved" #[.null, intV 19, intV 2],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/one-non-int-before-type" #[.null],
    mkCase "type/shift-top-non-int" #[intV 7, .null],
    mkCase "type/x-second-non-int" #[.null, intV 1],
    mkCase "range/shift-negative" #[intV 7, intV (-1)],
    mkCase "range/shift-overmax" #[intV 7, intV 1024],
    mkShiftInjectedCase "range/shift-nan-via-program" (intV 7) .nan,
    mkCase "error-order/range-before-x-type" #[.null, intV (-1)],
    mkCase "intov/nan-x-direct" #[.int .nan, intV 1],
    mkCase "intov/nan-shift-and-x-via-program" #[] #[.pushInt .nan, .pushInt .nan, rshiftInstr],
    mkCaseFromIntVals "error-order/pushint-overflow-before-op" #[.num (maxInt257 + 1), .num 1],
    mkCase "gas/exact-cost-succeeds" #[intV 1, intV 1]
      #[.pushInt (.num rshiftSetGasExact), .tonEnvOp .setGasLimit, rshiftInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 1, intV 1]
      #[.pushInt (.num rshiftSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftInstr]
  ]
  fuzz := #[
    { seed := 0x52534846
      count := 700
      gen := genRshiftFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFT
