import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.UFITS

/-
UFITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Ext.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_ufits_tinyint8`, opcode wiring in `register_shift_logic_ops`).

Branch/terminal outcomes covered by this suite:
- Lean: 5 branch sites / 6 terminal outcomes for the UFITS execution path
  (opcode dispatch; `VM.popInt` underflow/type/success; `IntVal` nan-vs-num;
   unsigned-fit predicate; non-quiet fail path to `.intOv`).
- C++: 4 aligned branch sites / 5 aligned terminal outcomes
  (underflow check; `pop_int` type check; `unsigned_fits_bits`; non-quiet
   `push_int_quiet` success vs `int_ov`).

Key divergence risk areas:
- unsigned width boundary decode/encode (`bits = imm8 + 1`, legal range `[1, 256]`);
- unsigned-fit thresholds (`2^k - 1` fits, `2^k` fails) across multiple `k`;
- negative operands must always fail UFITS in non-quiet mode;
- NaN propagation must throw `.intOv` in non-quiet UFITS;
- top-of-stack error ordering (top non-int fails even when below is int);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; UFITS bits` with exact vs exact-1 budgets.
-/

private def ufitsId : InstrId := { name := "UFITS" }

private def ufitsInstr (bits : Nat) : Instr :=
  .arithExt (.fitsConst true false bits)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ufitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkUFITSCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[ufitsInstr bits] gasLimits fuel

private def runUFITSDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (ufitsInstr bits) stack

private def runUFITSDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 777)) stack

private def expectAssembleErr
    (label : String)
    (program : List Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

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

private def ufitsGasProbeBits : Nat := 17

private def ufitsSetGasExact : Int :=
  computeExactGasBudget (ufitsInstr ufitsGasProbeBits)

private def ufitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (ufitsInstr ufitsGasProbeBits)

private def ufitsBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickUFITSBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ufitsBitsBoundaryPool.size - 1)
  (ufitsBitsBoundaryPool[idx]!, rng')

private def pickUFITSBitsUniform (rng : StdGen) : Nat × StdGen :=
  let (bits, rng') := randNat rng 1 256
  (bits, rng')

private def pickUFITSBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickUFITSBitsBoundary rng1
  else
    pickUFITSBitsUniform rng1

private def genUFITSFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  let ((x, bits), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (bits0, r3) := pickUFITSBitsBoundary r2
      ((x0, bits0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (bits0, r3) := pickUFITSBitsBoundary r2
      ((x0, bits0), r3)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (bits0, r3) := pickUFITSBitsUniform r2
      ((x0, bits0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (bits0, r3) := pickUFITSBitsUniform r2
      ((x0, bits0), r3)
    else if shape = 4 then
      let (bits0, r2) := pickUFITSBitsMixed rng1
      ((pow2 bits0 - 1, bits0), r2)
    else if shape = 5 then
      let (bits0, r2) := pickUFITSBitsMixed rng1
      let bits1 := if bits0 = 256 then 255 else bits0
      ((pow2 bits1, bits1), r2)
    else if shape = 6 then
      let (bits0, r2) := pickUFITSBitsMixed rng1
      ((-1, bits0), r2)
    else
      let (bits0, r2) := pickUFITSBitsMixed rng1
      ((0, bits0), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkUFITSCase s!"fuzz/shape-{shape}-{tag}" bits #[intV x], rng3)

def suite : InstrSuite where
  id := ufitsId
  unit := #[
    { name := "unit/direct/unsigned-fit-success-boundaries"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, 0),
            (1, 1),
            (2, 3),
            (8, 255),
            (128, pow2 127),
            (255, (pow2 255) - 1),
            (256, maxInt257)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          expectOkStack s!"bits={bits} x={x}" (runUFITSDirect bits #[intV x]) #[intV x] }
    ,
    { name := "unit/direct/non-fitting-and-nan-intov"
      run := do
        expectErr "2-in-1-bit" (runUFITSDirect 1 #[intV 2]) .intOv
        expectErr "pow2-8-in-8-bits" (runUFITSDirect 8 #[intV (pow2 8)]) .intOv
        expectErr "max-in-255-bits" (runUFITSDirect 255 #[intV maxInt257]) .intOv
        expectErr "pow2-256-in-256-bits" (runUFITSDirect 256 #[intV (pow2 256)]) .intOv
        expectErr "negative-in-unsigned" (runUFITSDirect 256 #[intV (-1)]) .intOv
        expectErr "nan-propagates-intov" (runUFITSDirect 32 #[.int .nan]) .intOv }
    ,
    { name := "unit/error/underflow-type-and-top-ordering"
      run := do
        expectErr "empty-underflow" (runUFITSDirect 8 #[]) .stkUnd
        expectErr "top-null" (runUFITSDirect 8 #[.null]) .typeChk
        expectErr "top-cell" (runUFITSDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-before-below-int" (runUFITSDirect 8 #[intV 1, .null]) .typeChk
        expectOkStack "top-int-keeps-below" (runUFITSDirect 8 #[.null, intV 7]) #[.null, intV 7] }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr :=
          #[ufitsInstr 1, ufitsInstr 2, ufitsInstr 255, ufitsInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ufits-1" s0 (ufitsInstr 1) 16
        let s2 ← expectDecodeStep "decode/ufits-2" s1 (ufitsInstr 2) 16
        let s3 ← expectDecodeStep "decode/ufits-255" s2 (ufitsInstr 255) 16
        let s4 ← expectDecodeStep "decode/ufits-256" s3 (ufitsInstr 256) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "ufits/0" [ufitsInstr 0] .rangeChk
        expectAssembleErr "ufits/257" [ufitsInstr 257] .rangeChk }
    ,
    { name := "unit/dispatch/non-ufits-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runUFITSDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkUFITSCase "ok/bit1/zero" 1 #[intV 0],
    mkUFITSCase "ok/bit1/one" 1 #[intV 1],
    mkUFITSCase "ok/bit2/max" 2 #[intV 3],
    mkUFITSCase "ok/bit8/max" 8 #[intV 255],
    mkUFITSCase "ok/bit128/high-boundary" 128 #[intV (pow2 127)],
    mkUFITSCase "ok/bit255/max" 255 #[intV ((pow2 255) - 1)],
    mkUFITSCase "ok/bit256/max-int257" 256 #[intV maxInt257],
    mkUFITSCase "ok/top-order/below-kept" 8 #[.null, intV 7],
    mkUFITSCase "overflow/bit1/two" 1 #[intV 2],
    mkUFITSCase "overflow/bit8/pow2" 8 #[intV (pow2 8)],
    mkUFITSCase "overflow/bit255/max-int257" 255 #[intV maxInt257],
    mkUFITSCase "overflow/bit256/negative-one" 256 #[intV (-1)],
    mkUFITSCase "overflow/negative/minus-one" 8 #[intV (-1)],
    mkUFITSCase "overflow/negative/min-int257" 256 #[intV minInt257],
    mkUFITSCase "underflow/empty-stack" 64 #[],
    mkUFITSCase "type/top-null" 64 #[.null],
    mkUFITSCase "type/top-cell" 64 #[.cell Cell.empty],
    mkUFITSCase "error-order/top-non-int-before-below-int" 64 #[intV 1, .null],
    mkUFITSCase "error-order/underflow-before-any-type-check" 64 #[],
    mkCase "nan/pushnan-propagates-intov" #[intV 42] #[.pushInt .nan, ufitsInstr 64],
    mkCase "gas/exact-cost-succeeds" #[intV 255]
      #[.pushInt (.num ufitsSetGasExact), .tonEnvOp .setGasLimit, ufitsInstr ufitsGasProbeBits],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 255]
      #[.pushInt (.num ufitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, ufitsInstr ufitsGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 500
      gen := genUFITSFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.UFITS
