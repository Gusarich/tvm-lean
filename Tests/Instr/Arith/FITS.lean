import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.FITS

/-
FITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.fitsConst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`encodeArithExtInstr`, `FITS` range check)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb4 + imm8`, decoded as `bits = imm + 1`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_fits_tinyint8`, opcode registration in `register_shift_logic_ops`)

Branch map used for this suite:
- Lean FITS execution path: 5 branch points / 6 terminal outcomes
  (dispatch; `popInt` underflow/type/success; NaN-vs-num split; signed-fit pass/fail;
   non-quiet overflow handling).
- C++ FITS execution path: 4 branch points / 6 aligned terminal outcomes
  (`check_underflow`; `pop_int` type check; `signed_fits_bits` pass/fail;
   `push_int_quiet(..., quiet=false)` success-vs-`int_ov`).

Key risk areas:
- tinyint8 immediate decode (`bits = imm + 1`) must preserve width endpoints 1 and 256;
- signed fit boundaries are off-by-one sensitive (`[-2^(bits-1), 2^(bits-1)-1]`);
- non-quiet FITS must throw `intOv` for NaN and non-fitting values;
- error ordering for unary pop: empty stack (`stkUnd`) vs non-int top (`typeChk`);
- exact gas threshold for `PUSHINT n; SETGASLIMIT; FITS bits`.
-/

private def fitsId : InstrId := { name := "FITS" }

private def fitsInstr (bits : Nat) : Instr :=
  .arithExt (.fitsConst false false bits)

private def mkFitsCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[fitsInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := fitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runFitsDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (fitsInstr bits) stack

private def fitsGasProbeBits : Nat := 8

private def fitsSetGasExact : Int :=
  computeExactGasBudget (fitsInstr fitsGasProbeBits)

private def fitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (fitsInstr fitsGasProbeBits)

private def fitsBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickFitsBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (fitsBitsBoundaryPool.size - 1)
  (fitsBitsBoundaryPool[idx]!, rng')

private def pickFitsBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickFitsBitsBoundary rng1
  else
    randNat rng1 1 256

private def genFitsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  let (bits, rng2) := pickFitsBitsMixed rng1
  let (x, rng3) :=
    if shape = 0 then
      let half := intPow2 (bits - 1)
      let (pick, r3) := randNat rng2 0 3
      let x' : Int :=
        if pick = 0 then
          half - 1
        else if pick = 1 then
          -half
        else if pick = 2 then
          half
        else
          -half - 1
      (x', r3)
    else if shape = 1 then
      pickInt257Boundary rng2
    else if shape = 2 then
      pickSigned257ish rng2
    else if shape = 3 then
      let (x0, r3) := pickInt257Boundary rng2
      let (delta, r4) := randNat r3 0 1
      let x' :=
        if x0 = minInt257 then
          minInt257 + 1
        else if x0 = maxInt257 then
          maxInt257 - 1
        else if delta = 0 then
          x0 - 1
        else
          x0 + 1
      (x', r4)
    else if shape = 4 then
      let (tag, r3) := randNat rng2 0 5
      let x' : Int :=
        if tag = 0 then
          -2
        else if tag = 1 then
          -1
        else if tag = 2 then
          0
        else if tag = 3 then
          1
        else if tag = 4 then
          2
        else
          3
      (x', r3)
    else
      let (useMax, r3) := randBool rng2
      ((if useMax then maxInt257 else minInt257), r3)
  let (tag, rng4) := randNat rng3 0 999_999
  (mkFitsCase s!"fuzz/shape-{shape}-bits-{bits}-{tag}" bits #[intV x], rng4)

def suite : InstrSuite where
  id := fitsId
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
            (256, (pow2 255) - 1),
            (256, -(pow2 255))
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          expectOkStack s!"fits/{bits}/{x}" (runFitsDirect bits #[intV x]) #[intV x] }
    ,
    { name := "unit/direct/intov-from-overflow-and-nan"
      run := do
        expectErr "bits1/+1" (runFitsDirect 1 #[intV 1]) .intOv
        expectErr "bits1/-2" (runFitsDirect 1 #[intV (-2)]) .intOv
        expectErr "bits8/+128" (runFitsDirect 8 #[intV 128]) .intOv
        expectErr "bits8/-129" (runFitsDirect 8 #[intV (-129)]) .intOv
        expectErr "bits256/+2^255" (runFitsDirect 256 #[intV (pow2 255)]) .intOv
        expectErr "bits256/-(2^255+1)" (runFitsDirect 256 #[intV (-(pow2 255) - 1)]) .intOv
        expectErr "nan" (runFitsDirect 8 #[.int .nan]) .intOv }
    ,
    { name := "unit/direct/underflow-and-type-ordering"
      run := do
        expectErr "empty-underflow" (runFitsDirect 8 #[]) .stkUnd
        expectErr "top-null-typechk" (runFitsDirect 8 #[.null]) .typeChk
        expectErr "top-cell-typechk" (runFitsDirect 8 #[.cell Cell.empty]) .typeChk }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr := #[fitsInstr 1, fitsInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let decodeOne
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
        let s0 := Slice.ofCell code
        let s1 ← decodeOne "decode/fits-1" s0 (fitsInstr 1) 16
        let s2 ← decodeOne "decode/fits-256" s1 (fitsInstr 256) 16
        let s3 ← decodeOne "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        match assembleCp0 [fitsInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"fits/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "fits/0: expected assemble rangeChk, got success")
        match assembleCp0 [fitsInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"fits/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "fits/257: expected assemble rangeChk, got success") }
  ]
  oracle := #[
    mkFitsCase "ok/bits-1-zero" 1 #[intV 0],
    mkFitsCase "ok/bits-1-minus-one" 1 #[intV (-1)],
    mkFitsCase "ok/bits-2-plus-one" 2 #[intV 1],
    mkFitsCase "ok/bits-2-minus-two" 2 #[intV (-2)],
    mkFitsCase "ok/bits-8-plus-127" 8 #[intV 127],
    mkFitsCase "ok/bits-8-minus-128" 8 #[intV (-128)],
    mkFitsCase "ok/bits-16-plus-32767" 16 #[intV 32767],
    mkFitsCase "ok/bits-16-minus-32768" 16 #[intV (-32768)],
    mkFitsCase "ok/bits-255-plus-max" 255 #[intV ((pow2 254) - 1)],
    mkFitsCase "ok/bits-255-minus-min" 255 #[intV (-(pow2 254))],
    mkFitsCase "ok/bits-256-plus-max" 256 #[intV ((pow2 255) - 1)],
    mkFitsCase "ok/bits-256-minus-min" 256 #[intV (-(pow2 255))],
    mkFitsCase "overflow/bits-1-plus-one" 1 #[intV 1],
    mkFitsCase "overflow/bits-1-minus-two" 1 #[intV (-2)],
    mkFitsCase "overflow/bits-8-plus-128" 8 #[intV 128],
    mkFitsCase "overflow/bits-8-minus-129" 8 #[intV (-129)],
    mkFitsCase "overflow/bits-256-plus-2pow255" 256 #[intV (pow2 255)],
    mkFitsCase "overflow/bits-256-minus-2pow255-minus-one" 256 #[intV (-(pow2 255) - 1)],
    mkFitsCase "overflow/bits-256-max-int257" 256 #[intV maxInt257],
    mkFitsCase "overflow/bits-256-min-int257" 256 #[intV minInt257],
    mkFitsCase "underflow/empty-stack" 8 #[],
    mkFitsCase "type/top-null" 8 #[.null],
    mkFitsCase "type/top-cell" 8 #[.cell Cell.empty],
    mkFitsCase "error-order/non-empty-non-int-before-underflow" 1 #[.null],
    mkFitsCase "nan/pushnan-propagates-intov" 8 #[] #[.pushInt .nan, fitsInstr 8],
    mkFitsCase "gas/exact-cost-succeeds" fitsGasProbeBits #[intV 7]
      #[.pushInt (.num fitsSetGasExact), .tonEnvOp .setGasLimit, fitsInstr fitsGasProbeBits],
    mkFitsCase "gas/exact-minus-one-out-of-gas" fitsGasProbeBits #[intV 7]
      #[.pushInt (.num fitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, fitsInstr fitsGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 600
      gen := genFitsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.FITS
