import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QUFITS

/-
QUFITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`.fitsConst unsigned=true quiet=true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`QUFITS` immediate encode: `0xb7b5`, 24-bit)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7b5` decode)
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_ufits_tinyint8(..., quiet=true)`, shift/logic opcode wiring).

Branch/terminal outcomes covered by this suite:
- Lean: 5 branch sites / 5 terminal outcomes for QUFITS
  (opcode dispatch; `VM.popInt` underflow/type/success; NaN-vs-num path;
   unsigned-fit predicate; quiet fail path to pushed NaN).
- C++: aligned tinyint UFITS quiet path
  (`check_underflow`; `pop_int`; `unsigned_fits_bits`; `push_int_quiet(..., true)`).

Key divergence risk areas:
- immediate-width encoding/decoding (`bits = imm8 + 1`) over full `[1, 256]` domain;
- quiet semantics: overflow / negative / NaN produce NaN (never `.intOv`);
- top-of-stack error ordering (top non-int checked before below values);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QUFITS` (exact vs exact-1).
-/

private def qufitsId : InstrId := { name := "QUFITS" }

private def qufitsInstr (bits : Nat) : Instr :=
  .arithExt (.fitsConst true true bits)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qufitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQUFITSCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[qufitsInstr bits] gasLimits fuel

private def mkQUFITSInputCase
    (name : String)
    (bits : Nat)
    (x : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stack) (progPrefix.push (qufitsInstr bits)) gasLimits fuel

private def runQUFITSDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (qufitsInstr bits) stack

private def runQUFITSDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 919)) stack

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

private def qufitsGasProbeBits : Nat := 17

private def qufitsSetGasExact : Int :=
  computeExactGasBudget (qufitsInstr qufitsGasProbeBits)

private def qufitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (qufitsInstr qufitsGasProbeBits)

private def qufitsBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickQUFITSBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (qufitsBitsBoundaryPool.size - 1)
  (qufitsBitsBoundaryPool[idx]!, rng')

private def pickQUFITSBitsUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickQUFITSBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickQUFITSBitsBoundary rng1
  else
    pickQUFITSBitsUniform rng1

private def qufitsOverflowBitsPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickQUFITSOverflowBits (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (qufitsOverflowBitsPool.size - 1)
  (qufitsOverflowBitsPool[idx]!, rng')

private def pickQUFITSNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def qufitsOutOfRangePool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1]

private def pickQUFITSOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qufitsOutOfRangePool.size - 1)
  (qufitsOutOfRangePool[idx]!, rng')

private def genQUFITSFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, r3) := pickInt257Boundary rng2
    let (bits, r4) := pickQUFITSBitsBoundary r3
    (mkQUFITSCase s!"fuzz/shape-{shape}/tag-{tag}" bits #[intV x], r4)
  else if shape = 1 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickQUFITSBitsBoundary r3
    (mkQUFITSInputCase s!"fuzz/shape-{shape}/tag-{tag}" bits (.num x), r4)
  else if shape = 2 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickQUFITSBitsUniform r3
    (mkQUFITSInputCase s!"fuzz/shape-{shape}/tag-{tag}" bits (.num x), r4)
  else if shape = 3 then
    let (bits, r3) := pickQUFITSBitsMixed rng2
    let x := pow2 bits - 1
    (mkQUFITSCase s!"fuzz/shape-{shape}/tag-{tag}" bits #[intV x], r3)
  else if shape = 4 then
    let (bits, r3) := pickQUFITSOverflowBits rng2
    let x := pow2 bits
    (mkQUFITSInputCase s!"fuzz/shape-{shape}/tag-{tag}" bits (.num x), r3)
  else if shape = 5 then
    let (bits, r3) := pickQUFITSBitsMixed rng2
    let (which, r4) := randNat r3 0 2
    let x : Int :=
      if which = 0 then
        -1
      else if which = 1 then
        -2
      else
        minInt257
    (mkQUFITSCase s!"fuzz/shape-{shape}/tag-{tag}" bits #[intV x], r4)
  else if shape = 6 then
    let (bits, r3) := pickQUFITSBitsMixed rng2
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.nan]
    (mkCase s!"fuzz/shape-{shape}/tag-{tag}" stack (progPrefix.push (qufitsInstr bits)), r3)
  else if shape = 7 then
    let (bits, r3) := pickQUFITSBitsMixed rng2
    let (huge, r4) := pickQUFITSOutOfRange r3
    (mkQUFITSInputCase s!"fuzz/shape-{shape}/tag-{tag}" bits (.num huge), r4)
  else if shape = 8 then
    let (xNonInt, r3) := pickQUFITSNonInt rng2
    let (bits, r4) := pickQUFITSBitsMixed r3
    (mkQUFITSCase s!"fuzz/shape-{shape}/tag-{tag}" bits #[xNonInt], r4)
  else if shape = 9 then
    let (xNonInt, r3) := pickQUFITSNonInt rng2
    let (bits, r4) := pickQUFITSBitsMixed r3
    (mkQUFITSCase s!"fuzz/shape-{shape}/tag-{tag}" bits #[intV 1, xNonInt], r4)
  else
    let (bits, r3) := pickQUFITSBitsMixed rng2
    (mkQUFITSCase s!"fuzz/shape-{shape}/tag-{tag}" bits #[], r3)

def suite : InstrSuite where
  id := qufitsId
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
          expectOkStack s!"bits={bits}/x={x}" (runQUFITSDirect bits #[intV x]) #[intV x] }
    ,
    { name := "unit/direct/quiet-nan-for-overflow-negative-and-nan"
      run := do
        expectOkStack "bit1/two" (runQUFITSDirect 1 #[intV 2]) #[.int .nan]
        expectOkStack "bit8/pow2" (runQUFITSDirect 8 #[intV (pow2 8)]) #[.int .nan]
        expectOkStack "bit255/max-int257" (runQUFITSDirect 255 #[intV maxInt257]) #[.int .nan]
        expectOkStack "bit256/pow2" (runQUFITSDirect 256 #[intV (pow2 256)]) #[.int .nan]
        expectOkStack "negative-in-unsigned" (runQUFITSDirect 256 #[intV (-1)]) #[.int .nan]
        expectOkStack "nan-propagates" (runQUFITSDirect 64 #[.int .nan]) #[.int .nan]
        expectOkStack "out-of-range-via-direct-number" (runQUFITSDirect 256 #[intV (pow2 300)]) #[.int .nan] }
    ,
    { name := "unit/error/underflow-type-and-top-ordering"
      run := do
        expectErr "empty-underflow" (runQUFITSDirect 8 #[]) .stkUnd
        expectErr "top-null" (runQUFITSDirect 8 #[.null]) .typeChk
        expectErr "top-cell" (runQUFITSDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-before-below-int" (runQUFITSDirect 8 #[intV 1, .null]) .typeChk
        expectOkStack "top-int-keeps-below" (runQUFITSDirect 8 #[.null, intV 7]) #[.null, intV 7] }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr :=
          #[qufitsInstr 1, qufitsInstr 2, qufitsInstr 255, qufitsInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qufits-1" s0 (qufitsInstr 1) 24
        let s2 ← expectDecodeStep "decode/qufits-2" s1 (qufitsInstr 2) 24
        let s3 ← expectDecodeStep "decode/qufits-255" s2 (qufitsInstr 255) 24
        let s4 ← expectDecodeStep "decode/qufits-256" s3 (qufitsInstr 256) 24
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "qufits/0" [qufitsInstr 0] .rangeChk
        expectAssembleErr "qufits/257" [qufitsInstr 257] .rangeChk }
    ,
    { name := "unit/dispatch/non-qufits-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQUFITSDispatchFallback #[]) #[intV 919] }
  ]
  oracle := #[
    mkQUFITSCase "ok/bit1/zero" 1 #[intV 0],
    mkQUFITSCase "ok/bit1/one" 1 #[intV 1],
    mkQUFITSCase "ok/bit2/max" 2 #[intV 3],
    mkQUFITSCase "ok/bit8/max" 8 #[intV 255],
    mkQUFITSCase "ok/bit128/high-boundary" 128 #[intV (pow2 127)],
    mkQUFITSCase "ok/bit255/max" 255 #[intV ((pow2 255) - 1)],
    mkQUFITSCase "ok/bit256/max-int257" 256 #[intV maxInt257],
    mkQUFITSCase "ok/order/below-kept" 8 #[.null, intV 7],
    mkQUFITSCase "nan/overflow/bit1/two" 1 #[intV 2],
    mkQUFITSCase "nan/overflow/bit8/pow2" 8 #[intV (pow2 8)],
    mkQUFITSCase "nan/overflow/bit255/max-int257" 255 #[intV maxInt257],
    mkQUFITSInputCase "nan/overflow/bit256/max-plus-one-via-program" 256 (.num (maxInt257 + 1)),
    mkQUFITSCase "nan/negative/minus-one" 256 #[intV (-1)],
    mkQUFITSCase "nan/negative/min-int257" 256 #[intV minInt257],
    mkCase "nan/x-nan-via-program" #[] #[.pushInt .nan, qufitsInstr 64],
    mkQUFITSInputCase "nan/out-of-range-via-program" 256 (.num (maxInt257 + 1)),
    mkQUFITSCase "underflow/empty-stack" 64 #[],
    mkQUFITSCase "type/top-null" 64 #[.null],
    mkQUFITSCase "type/top-cell" 64 #[.cell Cell.empty],
    mkQUFITSCase "error-order/top-non-int-before-below-int" 64 #[intV 1, .null],
    mkQUFITSCase "error-order/underflow-before-any-type-check" 64 #[],
    mkCase "gas/exact-cost-succeeds" #[intV 255]
      #[.pushInt (.num qufitsSetGasExact), .tonEnvOp .setGasLimit, qufitsInstr qufitsGasProbeBits],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 255]
      #[.pushInt (.num qufitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, qufitsInstr qufitsGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026020807
      count := 620
      gen := genQUFITSFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QUFITS
