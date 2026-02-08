import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QFITSX

/-
QFITSX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.qfitsx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`QFITSX` opcode encode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7b600` decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_fits(..., quiet=true)`, opcode wiring in `register_shift_logic_ops`)

Branch/terminal outcomes covered by this suite:
- dispatch to `QFITSX` vs fallback;
- width pop (`pop_smallint_range(1023)` / `VM.popNatUpTo 1023`):
  underflow, type, range, success;
- value pop (`pop_int`): underflow, type, success;
- signed-fit predicate pass/fail with quiet result conversion;
- quiet behavior: non-fitting values and NaN inputs yield NaN on stack (no `intOv`).

Key risk areas:
- width is stack-sourced (`[0, 1023]`), including width `0` (`x = 0` only);
- signed threshold edges (`-2^(bits-1)` and `2^(bits-1)-1`) across boundary widths;
- error ordering: width range/type checks happen before `x` pop/type;
- fixed 24-bit opcode decode (`0xb7b600`) and tail decode alignment;
- precise gas cliff for `PUSHINT n; SETGASLIMIT; QFITSX` (exact vs exact-1).
-/

private def qfitsxId : InstrId := { name := "QFITSX" }

private def qfitsxInstr : Instr := .contExt .qfitsx

private def widthV (bits : Nat) : Value :=
  intV (Int.ofNat bits)

private def mkQFitsXCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qfitsxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qfitsxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runQFitsXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qfitsxInstr stack

private def runQFitsXDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt .add (VM.push (intV 909)) stack

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

private def qfitsxGasProbeWidth : Nat := 8

private def qfitsxSetGasExact : Int :=
  computeExactGasBudget qfitsxInstr

private def qfitsxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qfitsxInstr

private def qfitsxWidthBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023]

private def qfitsxWidthThresholdPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickQFitsXWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (qfitsxWidthBoundaryPool.size - 1)
  (qfitsxWidthBoundaryPool[idx]!, rng')

private def pickQFitsXWidthThreshold (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (qfitsxWidthThresholdPool.size - 1)
  (qfitsxWidthThresholdPool[idx]!, rng')

private def pickQFitsXWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 5
  if mode = 0 then
    pickQFitsXWidthBoundary rng1
  else
    randNat rng1 0 1023

private def pickSignedBoundaryForWidth (bits : Nat) (rng0 : StdGen) : Int × StdGen :=
  if bits = 0 then
    let (pick, rng1) := randNat rng0 0 2
    let x : Int :=
      if pick = 0 then
        0
      else if pick = 1 then
        1
      else
        -1
    (x, rng1)
  else
    let half := intPow2 (bits - 1)
    let (pick, rng1) := randNat rng0 0 3
    let x : Int :=
      if pick = 0 then
        half - 1
      else if pick = 1 then
        -half
      else if pick = 2 then
        half
      else
        -half - 1
    (x, rng1)

private def genQFitsXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (case0, rng2) :=
    if shape = 0 then
      let (bits, r2) := pickQFitsXWidthBoundary rng1
      let (x, r3) := pickInt257Boundary r2
      (mkQFitsXCase s!"fuzz/shape-{shape}/ok-boundary" #[intV x, widthV bits], r3)
    else if shape = 1 then
      let (bits, r2) := pickQFitsXWidthMixed rng1
      let (x, r3) := pickSigned257ish r2
      (mkQFitsXCase s!"fuzz/shape-{shape}/ok-mixed" #[intV x, widthV bits], r3)
    else if shape = 2 then
      let (bits, r2) := pickQFitsXWidthThreshold rng1
      let (x, r3) := pickSignedBoundaryForWidth bits r2
      (mkQFitsXCase s!"fuzz/shape-{shape}/edge-threshold" #[intV x, widthV bits], r3)
    else if shape = 3 then
      let (bits, r2) := pickQFitsXWidthMixed rng1
      let (tag, r3) := randNat r2 0 6
      let x : Int :=
        if tag = 0 then
          -3
        else if tag = 1 then
          -2
        else if tag = 2 then
          -1
        else if tag = 3 then
          0
        else if tag = 4 then
          1
        else if tag = 5 then
          2
        else
          3
      (mkQFitsXCase s!"fuzz/shape-{shape}/ok-small-ints" #[intV x, widthV bits], r3)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      (mkQFitsXCase s!"fuzz/shape-{shape}/ok-width-1023" #[intV x, widthV 1023], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkQFitsXCase s!"fuzz/shape-{shape}/range-width-negative" #[intV x, intV (-1)], r2)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkQFitsXCase s!"fuzz/shape-{shape}/range-width-overmax" #[intV x, intV 1024], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.nan]
      (mkQFitsXCase s!"fuzz/shape-{shape}/range-width-nan" stack (progPrefix.push qfitsxInstr), r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (pick, r3) := randNat r2 0 1
      let widthLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkQFitsXCase s!"fuzz/shape-{shape}/type-width-non-int" #[intV x, widthLike], r3)
    else if shape = 9 then
      let (bits, r2) := pickQFitsXWidthMixed rng1
      let (pick, r3) := randNat r2 0 1
      let xLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkQFitsXCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, widthV bits], r3)
    else if shape = 10 then
      (mkQFitsXCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 11 then
      let (pick, r2) := randNat rng1 0 1
      let stack : Array Value :=
        if pick = 0 then
          #[intV 1]
        else
          #[.null]
      (mkQFitsXCase s!"fuzz/shape-{shape}/underflow-single" stack, r2)
    else if shape = 12 then
      let (bits, r2) := pickQFitsXWidthMixed rng1
      let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.nan, IntVal.num bits]
      (mkQFitsXCase s!"fuzz/shape-{shape}/quiet-nan-x" stack (progPrefix.push qfitsxInstr), r2)
    else
      let (pick, r2) := randNat rng1 0 1
      let xLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkQFitsXCase s!"fuzz/shape-{shape}/error-order-range-before-x-type" #[xLike, intV (-1)], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qfitsxId
  unit := #[
    { name := "unit/direct/width-boundary-successes"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (0, 0),
            (1, 0),
            (1, -1),
            (2, 1),
            (2, -2),
            (8, 127),
            (8, -128),
            (16, 32767),
            (16, -32768),
            (256, (pow2 255) - 1),
            (256, -(pow2 255)),
            (1023, maxInt257),
            (1023, minInt257)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          expectOkStack s!"bits={bits}/x={x}" (runQFitsXDirect #[intV x, widthV bits]) #[intV x] }
    ,
    { name := "unit/direct/quiet-overflow-and-nan-to-nan"
      run := do
        expectOkStack "width0/plus-one" (runQFitsXDirect #[intV 1, widthV 0]) #[.int .nan]
        expectOkStack "width0/minus-one" (runQFitsXDirect #[intV (-1), widthV 0]) #[.int .nan]
        expectOkStack "width1/plus-one" (runQFitsXDirect #[intV 1, widthV 1]) #[.int .nan]
        expectOkStack "width1/minus-two" (runQFitsXDirect #[intV (-2), widthV 1]) #[.int .nan]
        expectOkStack "width8/plus-128" (runQFitsXDirect #[intV 128, widthV 8]) #[.int .nan]
        expectOkStack "width8/minus-129" (runQFitsXDirect #[intV (-129), widthV 8]) #[.int .nan]
        expectOkStack "width256/plus-2pow255" (runQFitsXDirect #[intV (pow2 255), widthV 256]) #[.int .nan]
        expectOkStack "width256/minus-2pow255-minus-one"
          (runQFitsXDirect #[intV (-(pow2 255) - 1), widthV 256]) #[.int .nan]
        expectOkStack "x-nan" (runQFitsXDirect #[.int .nan, widthV 64]) #[.int .nan] }
    ,
    { name := "unit/width/range-and-type-checks"
      run := do
        expectErr "width-negative" (runQFitsXDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "width-overmax" (runQFitsXDirect #[intV 7, intV 1024]) .rangeChk
        expectErr "width-nan" (runQFitsXDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "width-non-int" (runQFitsXDirect #[intV 7, .null]) .typeChk
        expectErr "x-non-int-after-valid-width" (runQFitsXDirect #[.null, widthV 8]) .typeChk }
    ,
    { name := "unit/error-order/underflow-range-type"
      run := do
        expectErr "empty-underflow" (runQFitsXDirect #[]) .stkUnd
        expectErr "single-int-underflow" (runQFitsXDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow" (runQFitsXDirect #[.null]) .stkUnd
        expectErr "range-before-x-type-negative" (runQFitsXDirect #[.null, intV (-1)]) .rangeChk
        expectErr "range-before-x-type-overmax" (runQFitsXDirect #[.null, intV 1024]) .rangeChk
        expectErr "type-width-before-x" (runQFitsXDirect #[intV 9, .cell Cell.empty]) .typeChk
        expectErr "type-x-after-valid-width" (runQFitsXDirect #[.cell Cell.empty, widthV 8]) .typeChk
        expectOkStack "below-stack-preserved" (runQFitsXDirect #[.null, intV 7, widthV 8]) #[.null, intV 7] }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[qfitsxInstr, .add, qfitsxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qfitsx-1" s0 qfitsxInstr 24
        let s2 ← expectDecodeStep "decode/tail-add-1" s1 .add 8
        let s3 ← expectDecodeStep "decode/qfitsx-2" s2 qfitsxInstr 24
        let s4 ← expectDecodeStep "decode/tail-add-2" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-qfitsx-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQFitsXDispatchFallback #[]) #[intV 909] }
  ]
  oracle := #[
    mkQFitsXCase "ok/width-0/zero" #[intV 0, widthV 0],
    mkQFitsXCase "ok/width-1/zero" #[intV 0, widthV 1],
    mkQFitsXCase "ok/width-1/minus-one" #[intV (-1), widthV 1],
    mkQFitsXCase "ok/width-2/plus-one" #[intV 1, widthV 2],
    mkQFitsXCase "ok/width-2/minus-two" #[intV (-2), widthV 2],
    mkQFitsXCase "ok/width-8/plus-127" #[intV 127, widthV 8],
    mkQFitsXCase "ok/width-8/minus-128" #[intV (-128), widthV 8],
    mkQFitsXCase "ok/width-256/plus-max" #[intV ((pow2 255) - 1), widthV 256],
    mkQFitsXCase "ok/width-256/minus-min" #[intV (-(pow2 255)), widthV 256],
    mkQFitsXCase "ok/width-1023/max-int257" #[intV maxInt257, widthV 1023],
    mkQFitsXCase "ok/width-1023/min-int257" #[intV minInt257, widthV 1023],
    mkQFitsXCase "ok/order/below-preserved" #[.null, intV 7, widthV 8],
    mkQFitsXCase "quiet-nan/overflow/width-0-plus-one" #[intV 1, widthV 0],
    mkQFitsXCase "quiet-nan/overflow/width-1-minus-two" #[intV (-2), widthV 1],
    mkQFitsXCase "quiet-nan/overflow/width-8-plus-128" #[intV 128, widthV 8],
    mkQFitsXCase "quiet-nan/overflow/width-8-minus-129" #[intV (-129), widthV 8],
    mkQFitsXCase "quiet-nan/overflow/width-256-plus-2pow255" #[intV (pow2 255), widthV 256],
    mkQFitsXCase "quiet-nan/overflow/width-256-minus-2pow255-minus-one" #[intV (-(pow2 255) - 1), widthV 256],
    mkQFitsXCase "quiet-nan/overflow/width-0-minus-one" #[intV (-1), widthV 0],
    mkQFitsXCase "quiet-nan/overflow/width-255-max-int257" #[intV maxInt257, widthV 255],
    mkQFitsXCase "quiet-nan/x-via-program" #[] #[.pushInt .nan, .pushInt (.num 8), qfitsxInstr],
    mkQFitsXCase "range/width-negative" #[intV 7, intV (-1)],
    mkQFitsXCase "range/width-overmax" #[intV 7, intV 1024],
    mkQFitsXCase "range/width-nan-via-program" #[intV 7] #[.pushInt .nan, qfitsxInstr],
    mkQFitsXCase "underflow/empty-stack" #[],
    mkQFitsXCase "underflow/single-int" #[intV 1],
    mkQFitsXCase "underflow/single-non-int" #[.null],
    mkQFitsXCase "type/width-top-non-int" #[intV 1, .null],
    mkQFitsXCase "type/x-after-valid-width" #[.null, widthV 8],
    mkQFitsXCase "error-order/range-before-x-type-negative" #[.null, intV (-1)],
    mkQFitsXCase "error-order/range-before-x-type-overmax" #[.cell Cell.empty, intV 1024],
    mkQFitsXCase "gas/exact-cost-succeeds" #[intV 7, widthV qfitsxGasProbeWidth]
      #[.pushInt (.num qfitsxSetGasExact), .tonEnvOp .setGasLimit, qfitsxInstr],
    mkQFitsXCase "gas/exact-minus-one-out-of-gas" #[intV 7, widthV qfitsxGasProbeWidth]
      #[.pushInt (.num qfitsxSetGasExactMinusOne), .tonEnvOp .setGasLimit, qfitsxInstr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 650
      gen := genQFitsXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QFITSX
