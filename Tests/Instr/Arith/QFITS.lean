import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QFITS

/-
QFITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.fitsConst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`QFITS` encode: `0xb7b4 + imm8`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`QFITS` decode, `bits = imm + 1`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_fits_tinyint8(..., quiet=true)`, opcode wiring in `register_shift_logic_ops`)

Branch map used for this suite:
- Lean QFITS path: 5 branch sites / 6 terminal outcomes
  (dispatch; `popInt` underflow/type/success; NaN-vs-num split; signed-fit pass/fail;
   quiet conversion for overflow/NaN outcomes).
- C++ QFITS path: 4 branch sites / 6 aligned terminal outcomes
  (`check_underflow`; `pop_int` type check; `signed_fits_bits` pass/fail;
   `push_int_quiet(..., quiet=true)` success-vs-NaN conversion).

Key risk areas:
- tinyint8 immediate decode (`bits = imm + 1`) must preserve width endpoints `1` and `256`;
- signed boundary edges are off-by-one sensitive (`[-2^(bits-1), 2^(bits-1)-1]`);
- quiet behavior must yield NaN (not `intOv`) for both NaN input and non-fitting values;
- error ordering for unary pop: underflow (`stkUnd`) before type (`typeChk`);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QFITS bits` (exact vs exact-1).
-/

private def qfitsId : InstrId := { name := "QFITS" }

private def qfitsInstr (bits : Nat) : Instr :=
  .arithExt (.fitsConst false true bits)

private def mkQFitsCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[qfitsInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qfitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQFitsProgramCase
    (name : String)
    (bits : Nat)
    (x : IntVal) : OracleCase :=
  mkQFitsCase name bits #[] #[.pushInt x, qfitsInstr bits]

private def runQFitsDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (qfitsInstr bits) stack

private def runQFitsDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 717)) stack

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

private def qfitsGasProbeBits : Nat := 8

private def qfitsSetGasExact : Int :=
  computeExactGasBudget (qfitsInstr qfitsGasProbeBits)

private def qfitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (qfitsInstr qfitsGasProbeBits)

private def qfitsBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickQFitsBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (qfitsBitsBoundaryPool.size - 1)
  (qfitsBitsBoundaryPool[idx]!, rng')

private def pickQFitsBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickQFitsBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickSignedBoundaryForBits (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let half := intPow2 (bits - 1)
  let (pick, rng') := randNat rng 0 3
  let x : Int :=
    if pick = 0 then
      half - 1
    else if pick = 1 then
      -half
    else if pick = 2 then
      half
    else
      -half - 1
  (x, rng')

private def pickSignedOverflowForBits (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let half := intPow2 (bits - 1)
  let (pick, rng') := randNat rng 0 1
  ((if pick = 0 then half else -half - 1), rng')

private def pickQFitsNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  ((if pick = 0 then .null else .cell Cell.empty), rng')

private def expectQFitsDirectOk (checks : Array (Nat × Int)) : IO Unit := do
  for c in checks do
    let bits := c.1
    let x := c.2
    expectOkStack s!"ok/bits-{bits}/x-{x}" (runQFitsDirect bits #[intV x]) #[intV x]

private def expectQFitsDirectQuietNan (checks : Array (Nat × Int)) : IO Unit := do
  for c in checks do
    let bits := c.1
    let x := c.2
    expectOkStack s!"quiet-nan/bits-{bits}/x-{x}" (runQFitsDirect bits #[intV x]) #[.int .nan]

private def genQFitsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (case0, rng2) :=
    if shape = 0 then
      let (bits, r2) := pickQFitsBitsBoundary rng1
      let (x, r3) := pickSignedBoundaryForBits bits r2
      (mkQFitsCase s!"fuzz/shape-{shape}/edge-threshold" bits #[intV x], r3)
    else if shape = 1 then
      let (bits, r2) := pickQFitsBitsMixed rng1
      let (x, r3) := pickSigned257ish r2
      (mkQFitsCase s!"fuzz/shape-{shape}/mixed-signed" bits #[intV x], r3)
    else if shape = 2 then
      let (bits, r2) := pickQFitsBitsBoundary rng1
      let (x, r3) := pickInt257Boundary r2
      (mkQFitsCase s!"fuzz/shape-{shape}/int257-boundary" bits #[intV x], r3)
    else if shape = 3 then
      let (bits, r2) := pickQFitsBitsMixed rng1
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
      (mkQFitsCase s!"fuzz/shape-{shape}/small-ints" bits #[intV x], r3)
    else if shape = 4 then
      let (bits, r2) := pickQFitsBitsBoundary rng1
      let (x, r3) := pickSignedOverflowForBits bits r2
      (mkQFitsCase s!"fuzz/shape-{shape}/overflow-direct" bits #[intV x], r3)
    else if shape = 5 then
      let (bits, r2) := pickQFitsBitsMixed rng1
      let (xLike, r3) := pickQFitsNonInt r2
      (mkQFitsCase s!"fuzz/shape-{shape}/type-top-non-int" bits #[xLike], r3)
    else if shape = 6 then
      let (bits, r2) := pickQFitsBitsMixed rng1
      (mkQFitsCase s!"fuzz/shape-{shape}/underflow-empty" bits #[], r2)
    else if shape = 7 then
      let (bits, r2) := pickQFitsBitsMixed rng1
      let (xLike, r3) := pickQFitsNonInt r2
      (mkQFitsCase s!"fuzz/shape-{shape}/error-order-top-type" bits #[intV 1, xLike], r3)
    else if shape = 8 then
      let (bits, r2) := pickQFitsBitsMixed rng1
      let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.nan]
      (mkQFitsCase s!"fuzz/shape-{shape}/quiet-nan-via-program" bits stack (progPrefix.push (qfitsInstr bits)), r2)
    else if shape = 9 then
      let (bits, r2) := pickQFitsBitsBoundary rng1
      let (x, r3) := pickSignedOverflowForBits bits r2
      (mkQFitsCase
        s!"fuzz/shape-{shape}/overflow-via-program"
        bits
        #[]
        #[.pushInt (.num x), qfitsInstr bits], r3)
    else if shape = 10 then
      let (pick, r2) := randNat rng1 0 1
      let x : Int := if pick = 0 then (pow2 255) else (-(pow2 255) - 1)
      (mkQFitsCase
        s!"fuzz/shape-{shape}/overflow-256-via-program"
        256
        #[]
        #[.pushInt (.num x), qfitsInstr 256], r2)
    else if shape = 11 then
      let (bits, r2) := pickQFitsBitsMixed rng1
      let (x, r3) := pickSigned257ish r2
      (mkQFitsCase s!"fuzz/shape-{shape}/below-preserved" bits #[.null, intV x], r3)
    else
      let (bits, r2) := pickQFitsBitsBoundary rng1
      let (x0, r3) := pickSignedBoundaryForBits bits r2
      let (delta, r4) := randNat r3 0 1
      let x := if delta = 0 then x0 - 1 else x0 + 1
      (mkQFitsCase s!"fuzz/shape-{shape}/edge-plus-minus-one" bits #[intV x], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qfitsId
  unit := #[
    { name := "unit/direct/signed-fit-boundary-successes"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, 0),
            (1, -1),
            (2, 1),
            (2, -2),
            (8, 127),
            (8, -128),
            (16, 32767),
            (16, -32768),
            (255, (pow2 254) - 1),
            (255, -(pow2 254)),
            (256, (pow2 255) - 1),
            (256, -(pow2 255))
          ]
        expectQFitsDirectOk checks }
    ,
    { name := "unit/direct/quiet-nan-from-overflow-and-nan"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, 1),
            (1, -2),
            (8, 128),
            (8, -129),
            (255, pow2 254),
            (255, -(pow2 254) - 1),
            (256, pow2 255),
            (256, -(pow2 255) - 1),
            (255, maxInt257),
            (255, minInt257)
          ]
        expectQFitsDirectQuietNan checks
        expectOkStack "quiet-nan/x-nan-direct" (runQFitsDirect 8 #[.int .nan]) #[.int .nan] }
    ,
    { name := "unit/direct/error-order-underflow-and-type"
      run := do
        expectErr "underflow/empty-stack" (runQFitsDirect 8 #[]) .stkUnd
        expectErr "type/top-null" (runQFitsDirect 8 #[.null]) .typeChk
        expectErr "type/top-cell" (runQFitsDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "error-order/top-non-int-before-below-int" (runQFitsDirect 8 #[intV 1, .null]) .typeChk
        expectOkStack "order/below-stack-preserved" (runQFitsDirect 8 #[.null, intV 7]) #[.null, intV 7] }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr := #[qfitsInstr 1, qfitsInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qfits-1" s0 (qfitsInstr 1) 24
        let s2 ← expectDecodeStep "decode/qfits-256" s1 (qfitsInstr 256) 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        match assembleCp0 [qfitsInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"qfits/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "qfits/0: expected assemble rangeChk, got success")
        match assembleCp0 [qfitsInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"qfits/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "qfits/257: expected assemble rangeChk, got success") }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQFitsDispatchFallback #[]) #[intV 717] }
  ]
  oracle := #[
    mkQFitsCase "ok/bits-1/zero" 1 #[intV 0],
    mkQFitsCase "ok/bits-1/minus-one" 1 #[intV (-1)],
    mkQFitsCase "ok/bits-2/plus-one" 2 #[intV 1],
    mkQFitsCase "ok/bits-2/minus-two" 2 #[intV (-2)],
    mkQFitsCase "ok/bits-8/plus-127" 8 #[intV 127],
    mkQFitsCase "ok/bits-8/minus-128" 8 #[intV (-128)],
    mkQFitsCase "ok/bits-16/plus-32767" 16 #[intV 32767],
    mkQFitsCase "ok/bits-16/minus-32768" 16 #[intV (-32768)],
    mkQFitsCase "ok/bits-255/plus-max" 255 #[intV ((pow2 254) - 1)],
    mkQFitsCase "ok/bits-255/minus-min" 255 #[intV (-(pow2 254))],
    mkQFitsCase "ok/bits-256/plus-max" 256 #[intV ((pow2 255) - 1)],
    mkQFitsCase "ok/bits-256/minus-min" 256 #[intV (-(pow2 255))],
    mkQFitsCase "ok/order/below-preserved" 8 #[.null, intV 7],
    mkQFitsCase "quiet-nan/overflow/bits-1/plus-one" 1 #[intV 1],
    mkQFitsCase "quiet-nan/overflow/bits-1/minus-two" 1 #[intV (-2)],
    mkQFitsCase "quiet-nan/overflow/bits-8/plus-128" 8 #[intV 128],
    mkQFitsCase "quiet-nan/overflow/bits-8/minus-129" 8 #[intV (-129)],
    mkQFitsCase "quiet-nan/overflow/bits-255/plus-2pow254" 255 #[intV (pow2 254)],
    mkQFitsCase "quiet-nan/overflow/bits-255/minus-2pow254-minus-one" 255 #[intV (-(pow2 254) - 1)],
    mkQFitsCase "quiet-nan/overflow/bits-256/plus-2pow255" 256 #[intV (pow2 255)],
    mkQFitsCase "quiet-nan/overflow/bits-256/minus-2pow255-minus-one" 256 #[intV (-(pow2 255) - 1)],
    mkQFitsCase "quiet-nan/overflow/bits-255/max-int257" 255 #[intV maxInt257],
    mkQFitsCase "quiet-nan/overflow/bits-255/min-int257" 255 #[intV minInt257],
    mkQFitsCase "underflow/empty-stack" 8 #[],
    mkQFitsCase "type/top-null" 8 #[.null],
    mkQFitsCase "type/top-cell" 8 #[.cell Cell.empty],
    mkQFitsCase "error-order/top-non-int-before-below-int" 8 #[intV 1, .null],
    mkQFitsProgramCase "quiet-nan/x-via-program" 8 .nan,
    mkQFitsProgramCase "quiet-nan/out-of-range-via-program-positive" 256 (.num (pow2 255)),
    mkQFitsProgramCase "quiet-nan/out-of-range-via-program-negative" 256 (.num (-(pow2 255) - 1)),
    mkQFitsCase "gas/exact-cost-succeeds" qfitsGasProbeBits #[intV 7]
      #[.pushInt (.num qfitsSetGasExact), .tonEnvOp .setGasLimit, qfitsInstr qfitsGasProbeBits],
    mkQFitsCase "gas/exact-minus-one/out-of-gas" qfitsGasProbeBits #[intV 7]
      #[.pushInt (.num qfitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, qfitsInstr qfitsGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026020829
      count := 620
      gen := genQFitsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QFITS
