import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.FITSX

/-
FITSX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.fitsx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (opcode encode for `FITSX`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (opcode decode for `FITSX`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_fits`, opcode wiring in `register_shift_logic_ops`)

Branch/terminal outcomes covered by this suite:
- dispatch to FITSX vs fallback;
- stack-width pop (`pop_smallint_range(1023)` / `VM.popNatUpTo 1023`):
  underflow, type, range, success;
- value pop (`pop_int`): underflow, type, success;
- signed-fit predicate pass/fail;
- non-quiet failure paths (`NaN` / non-fitting) to `.intOv`.

Key risk areas:
- width comes from stack (not opcode immediate): boundary widths `0`, `1`, `256`, `1023`;
- signed range edges (`[-2^(bits-1), 2^(bits-1)-1]`) plus width-`0` special case (`0` only);
- error ordering across underflow/type/range with mixed stacks;
- fixed opcode decode length (`0xb600`, 16 bits);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; FITSX`.
-/

private def fitsxId : InstrId := { name := "FITSX" }

private def fitsxInstr : Instr := .contExt .fitsx

private def widthV (bits : Nat) : Value :=
  intV (Int.ofNat bits)

private def mkFitsXCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[fitsxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := fitsxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runFitsXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt fitsxInstr stack

private def runFitsXDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt .add (VM.push (intV 606)) stack

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

private def fitsxGasProbeWidth : Nat := 8

private def fitsxSetGasExact : Int :=
  computeExactGasBudget fitsxInstr

private def fitsxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne fitsxInstr

private def fitsxWidthBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023]

private def fitsxWidthThresholdPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickFitsXWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (fitsxWidthBoundaryPool.size - 1)
  (fitsxWidthBoundaryPool[idx]!, rng')

private def pickFitsXWidthThreshold (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (fitsxWidthThresholdPool.size - 1)
  (fitsxWidthThresholdPool[idx]!, rng')

private def pickFitsXWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 5
  if mode = 0 then
    pickFitsXWidthBoundary rng1
  else
    randNat rng1 0 1023

private def pickSignedBoundaryForWidth (bits : Nat) (rng0 : StdGen) : Int × StdGen :=
  if bits = 0 then
    let (pick, rng1) := randNat rng0 0 2
    let x : Int := if pick = 0 then 0 else if pick = 1 then 1 else -1
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

private def genFitsXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng2) :=
    if shape = 0 then
      let (bits, r2) := pickFitsXWidthBoundary rng1
      let (x, r3) := pickInt257Boundary r2
      (mkFitsXCase s!"fuzz/shape-{shape}/valid-boundary" #[intV x, widthV bits], r3)
    else if shape = 1 then
      let (bits, r2) := pickFitsXWidthMixed rng1
      let (x, r3) := pickSigned257ish r2
      (mkFitsXCase s!"fuzz/shape-{shape}/valid-mixed" #[intV x, widthV bits], r3)
    else if shape = 2 then
      let (bits, r2) := pickFitsXWidthThreshold rng1
      let (x, r3) := pickSignedBoundaryForWidth bits r2
      (mkFitsXCase s!"fuzz/shape-{shape}/signed-threshold" #[intV x, widthV bits], r3)
    else if shape = 3 then
      let (bits, r2) := pickFitsXWidthMixed rng1
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
      (mkFitsXCase s!"fuzz/shape-{shape}/small-ints" #[intV x, widthV bits], r3)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      (mkFitsXCase s!"fuzz/shape-{shape}/width-1023" #[intV x, widthV 1023], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      (mkFitsXCase s!"fuzz/shape-{shape}/range-negative-width" #[intV x, intV (-1)], r2)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkFitsXCase s!"fuzz/shape-{shape}/range-width-1024" #[intV x, intV 1024], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.nan]
      (mkFitsXCase s!"fuzz/shape-{shape}/range-width-nan" stack (progPrefix.push fitsxInstr), r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (pick, r3) := randNat r2 0 1
      let widthLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkFitsXCase s!"fuzz/shape-{shape}/type-width-non-int" #[intV x, widthLike], r3)
    else if shape = 9 then
      let (bits, r2) := pickFitsXWidthMixed rng1
      let (pick, r3) := randNat r2 0 1
      let xLike : Value := if pick = 0 then .null else .cell Cell.empty
      (mkFitsXCase s!"fuzz/shape-{shape}/type-x-non-int" #[xLike, widthV bits], r3)
    else if shape = 10 then
      (mkFitsXCase s!"fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else
      let (pick, r2) := randNat rng1 0 1
      let stack : Array Value :=
        if pick = 0 then
          #[intV 1]
        else
          #[.null]
      (mkFitsXCase s!"fuzz/shape-{shape}/underflow-single" stack, r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := fitsxId
  unit := #[
    { name := "unit/direct/width-from-stack-boundary-successes"
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
          expectOkStack s!"bits={bits}/x={x}" (runFitsXDirect #[intV x, widthV bits]) #[intV x] }
    ,
    { name := "unit/direct/intov-from-overflow-and-nan"
      run := do
        expectErr "width0/plus-one" (runFitsXDirect #[intV 1, widthV 0]) .intOv
        expectErr "width0/minus-one" (runFitsXDirect #[intV (-1), widthV 0]) .intOv
        expectErr "width1/plus-one" (runFitsXDirect #[intV 1, widthV 1]) .intOv
        expectErr "width1/minus-two" (runFitsXDirect #[intV (-2), widthV 1]) .intOv
        expectErr "width8/plus-128" (runFitsXDirect #[intV 128, widthV 8]) .intOv
        expectErr "width8/minus-129" (runFitsXDirect #[intV (-129), widthV 8]) .intOv
        expectErr "width256/plus-2pow255" (runFitsXDirect #[intV (pow2 255), widthV 256]) .intOv
        expectErr "width256/minus-2pow255-minus-one"
          (runFitsXDirect #[intV (-(pow2 255) - 1), widthV 256]) .intOv
        expectErr "x-nan" (runFitsXDirect #[.int .nan, widthV 64]) .intOv }
    ,
    { name := "unit/width/range-and-type-checks"
      run := do
        expectErr "width-negative" (runFitsXDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "width-overmax" (runFitsXDirect #[intV 7, intV 1024]) .rangeChk
        expectErr "width-nan" (runFitsXDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "width-non-int" (runFitsXDirect #[intV 7, .null]) .typeChk
        expectErr "x-non-int-after-valid-width" (runFitsXDirect #[.null, widthV 8]) .typeChk }
    ,
    { name := "unit/error-order/underflow-range-type"
      run := do
        expectErr "empty-underflow" (runFitsXDirect #[]) .stkUnd
        expectErr "single-int-underflow" (runFitsXDirect #[intV 1]) .stkUnd
        expectErr "single-non-int-underflow" (runFitsXDirect #[.null]) .stkUnd
        expectErr "range-before-x-type-negative" (runFitsXDirect #[.null, intV (-1)]) .rangeChk
        expectErr "range-before-x-type-overmax" (runFitsXDirect #[.null, intV 1024]) .rangeChk
        expectErr "type-width-before-x" (runFitsXDirect #[intV 9, .cell Cell.empty]) .typeChk
        expectErr "type-x-after-valid-width" (runFitsXDirect #[.cell Cell.empty, widthV 8]) .typeChk
        expectOkStack "below-stack-preserved" (runFitsXDirect #[.null, intV 7, widthV 8]) #[.null, intV 7] }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[fitsxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/fitsx" s0 fitsxInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-fitsx-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runFitsXDispatchFallback #[]) #[intV 606] }
  ]
  oracle := #[
    mkFitsXCase "ok/width-0/zero" #[intV 0, widthV 0],
    mkFitsXCase "ok/width-1/zero" #[intV 0, widthV 1],
    mkFitsXCase "ok/width-1/minus-one" #[intV (-1), widthV 1],
    mkFitsXCase "ok/width-2/plus-one" #[intV 1, widthV 2],
    mkFitsXCase "ok/width-2/minus-two" #[intV (-2), widthV 2],
    mkFitsXCase "ok/width-8/plus-127" #[intV 127, widthV 8],
    mkFitsXCase "ok/width-8/minus-128" #[intV (-128), widthV 8],
    mkFitsXCase "ok/width-256/plus-max" #[intV ((pow2 255) - 1), widthV 256],
    mkFitsXCase "ok/width-256/minus-min" #[intV (-(pow2 255)), widthV 256],
    mkFitsXCase "ok/width-1023/max-int257" #[intV maxInt257, widthV 1023],
    mkFitsXCase "ok/width-1023/min-int257" #[intV minInt257, widthV 1023],
    mkFitsXCase "ok/top-order/below-preserved" #[.null, intV 7, widthV 8],
    mkFitsXCase "overflow/width-0/plus-one" #[intV 1, widthV 0],
    mkFitsXCase "overflow/width-1/minus-two" #[intV (-2), widthV 1],
    mkFitsXCase "overflow/width-8/plus-128" #[intV 128, widthV 8],
    mkFitsXCase "overflow/width-8/minus-129" #[intV (-129), widthV 8],
    mkFitsXCase "overflow/width-256/plus-2pow255" #[intV (pow2 255), widthV 256],
    mkFitsXCase "overflow/width-256/minus-2pow255-minus-one" #[intV (-(pow2 255) - 1), widthV 256],
    mkFitsXCase "overflow/width-0/minus-one" #[intV (-1), widthV 0],
    mkFitsXCase "nan/x-via-program" #[widthV 8] #[.pushInt .nan, .xchg0 1, fitsxInstr],
    mkFitsXCase "range/width-negative" #[intV 7, intV (-1)],
    mkFitsXCase "range/width-overmax" #[intV 7, intV 1024],
    mkFitsXCase "range/width-nan" #[intV 7] #[.pushInt .nan, fitsxInstr],
    mkFitsXCase "underflow/empty-stack" #[],
    mkFitsXCase "underflow/single-int" #[intV 1],
    mkFitsXCase "underflow/single-non-int" #[.null],
    mkFitsXCase "type/width-top-non-int" #[intV 1, .null],
    mkFitsXCase "type/x-after-valid-width" #[.null, widthV 8],
    mkFitsXCase "error-order/range-before-x-type-negative" #[.null, intV (-1)],
    mkFitsXCase "error-order/range-before-x-type-overmax" #[.cell Cell.empty, intV 1024],
    mkFitsXCase "gas/exact-succeeds" #[intV 7, widthV fitsxGasProbeWidth]
      #[.pushInt (.num fitsxSetGasExact), .tonEnvOp .setGasLimit, fitsxInstr],
    mkFitsXCase "gas/exact-minus-one-out-of-gas" #[intV 7, widthV fitsxGasProbeWidth]
      #[.pushInt (.num fitsxSetGasExactMinusOne), .tonEnvOp .setGasLimit, fitsxInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 650
      gen := genFitsXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.FITSX
