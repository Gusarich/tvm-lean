import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QUFITSX

/-
QUFITSX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qufitsx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`QUFITSX` opcode encode: `0xb7b601`, 24-bit)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb7b601` decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_ufits(..., quiet=true)`, `register_shift_logic_ops` wiring for `QUFITSX`).

Branch/terminal outcomes covered by this suite:
- Lean: 8 branch sites / 9 terminal outcomes for `.qufitsx`
  (dispatch; upfront underflow check; width pop type/range/success;
   value pop type/success; NaN-vs-num; unsigned-fit predicate;
   quiet push path where non-257 numerics collapse to NaN).
- C++: aligned `exec_ufits` path for quiet mode
  (`check_underflow(2)`; `pop_smallint_range(1023)`; `pop_int`;
   `unsigned_fits_bits` pass/fail; `push_int_quiet(..., true)`).

Key risk areas:
- quiet semantics: overflow / negative / NaN must return NaN (not throw `intOv`);
- width domain is runtime stack value in `[0, 1023]`; width `0` accepts only `x = 0`;
- pop order is width first, then value (`range/type` ordering depends on this);
- 24-bit opcode decode/dispatch (`0xb7b601`) must stay aligned;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QUFITSX` (exact vs exact-1).
-/

private def qufitsxId : InstrId := { name := "QUFITSX" }

private def qufitsxInstr : Instr := .contExt .qufitsx

private def bitsV (bits : Nat) : Value :=
  intV (Int.ofNat bits)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qufitsxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qufitsxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQUFITSXCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[qufitsxInstr] gasLimits fuel

private def runQUFITSXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qufitsxInstr stack

private def runQUFITSXDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt .add (VM.push (intV 919)) stack

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

private def qufitsxGasProbeBits : Nat := 17

private def qufitsxSetGasExact : Int :=
  computeExactGasBudget qufitsxInstr

private def qufitsxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qufitsxInstr

private def qufitsxBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 511, 512, 1023]

private def pickQUFITSXBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (qufitsxBitsBoundaryPool.size - 1)
  (qufitsxBitsBoundaryPool[idx]!, rng')

private def pickQUFITSXBitsUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 1023

private def pickQUFITSXBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickQUFITSXBitsBoundary rng1
  else
    pickQUFITSXBitsUniform rng1

private def qufitsxOverflowBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255]

private def pickQUFITSXOverflowBits (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (qufitsxOverflowBitsPool.size - 1)
  (qufitsxOverflowBitsPool[idx]!, rng')

private def qufitsxInvalidNegativeBitsPool : Array Int :=
  #[-1, -2, -17, -256]

private def pickQUFITSXInvalidNegativeBits (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qufitsxInvalidNegativeBitsPool.size - 1)
  (qufitsxInvalidNegativeBitsPool[idx]!, rng')

private def qufitsxInvalidHighBitsPool : Array Int :=
  #[1024, 1025, 1536, 2048]

private def pickQUFITSXInvalidHighBits (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qufitsxInvalidHighBitsPool.size - 1)
  (qufitsxInvalidHighBitsPool[idx]!, rng')

private def pickQUFITSXNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genQUFITSXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, r3) := pickInt257Boundary rng2
    let (bits, r4) := pickQUFITSXBitsBoundary r3
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsV bits], r4)
  else if shape = 1 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickQUFITSXBitsMixed r3
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsV bits], r4)
  else if shape = 2 then
    let (bits, r3) := pickQUFITSXBitsMixed rng2
    let x :=
      if bits = 0 then
        0
      else if bits ≤ 256 then
        pow2 bits - 1
      else
        maxInt257
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.num bits]
    (mkCase s!"fuzz/shape-{shape}-{tag}" stack (progPrefix.push qufitsxInstr), r3)
  else if shape = 3 then
    let (bits, r3) := pickQUFITSXOverflowBits rng2
    let x := if bits = 0 then 1 else pow2 bits
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.num bits]
    (mkCase s!"fuzz/shape-{shape}-{tag}" stack (progPrefix.push qufitsxInstr), r3)
  else if shape = 4 then
    let (bits, r3) := pickQUFITSXBitsMixed rng2
    let (which, r4) := randNat r3 0 2
    let x : Int :=
      if which = 0 then
        -1
      else if which = 1 then
        -2
      else
        minInt257
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsV bits], r4)
  else if shape = 5 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickQUFITSXInvalidNegativeBits r3
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV bits], r4)
  else if shape = 6 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickQUFITSXInvalidHighBits r3
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV bits], r4)
  else if shape = 7 then
    let (x, r3) := pickInt257Boundary rng2
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.nan]
    (mkCase s!"fuzz/shape-{shape}-{tag}" stack (progPrefix.push qufitsxInstr), r3)
  else if shape = 8 then
    let (x, r3) := pickSigned257ish rng2
    let (bitsNonInt, r4) := pickQUFITSXNonInt r3
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsNonInt], r4)
  else if shape = 9 then
    let (xNonInt, r3) := pickQUFITSXNonInt rng2
    let (bits, r4) := pickQUFITSXBitsMixed r3
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[xNonInt, bitsV bits], r4)
  else if shape = 10 then
    let (bits, r3) := pickQUFITSXBitsMixed rng2
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.nan, IntVal.num bits]
    (mkCase s!"fuzz/shape-{shape}-{tag}" stack (progPrefix.push qufitsxInstr), r3)
  else
    let (pick, r3) := randNat rng2 0 1
    let stack :=
      if pick = 0 then
        #[]
      else
        #[bitsV 8]
    (mkQUFITSXCase s!"fuzz/shape-{shape}-{tag}" stack, r3)

def suite : InstrSuite where
  id := qufitsxId
  unit := #[
    { name := "unit/direct/width-boundary-successes"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (0, 0),
            (1, 0),
            (1, 1),
            (2, 3),
            (8, 255),
            (256, maxInt257),
            (257, maxInt257),
            (1023, maxInt257)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          expectOkStack s!"bits={bits}/x={x}" (runQUFITSXDirect #[intV x, bitsV bits]) #[intV x] }
    ,
    { name := "unit/direct/quiet-nan-for-overflow-negative-and-nan"
      run := do
        expectOkStack "bit0/one" (runQUFITSXDirect #[intV 1, bitsV 0]) #[.int .nan]
        expectOkStack "bit1/two" (runQUFITSXDirect #[intV 2, bitsV 1]) #[.int .nan]
        expectOkStack "bit8/pow2" (runQUFITSXDirect #[intV (pow2 8), bitsV 8]) #[.int .nan]
        expectOkStack "bit255/max-int257" (runQUFITSXDirect #[intV maxInt257, bitsV 255]) #[.int .nan]
        expectOkStack "negative-in-unsigned" (runQUFITSXDirect #[intV (-1), bitsV 1023]) #[.int .nan]
        expectOkStack "nan-propagates" (runQUFITSXDirect #[.int .nan, bitsV 32]) #[.int .nan]
        expectOkStack "fit-unsigned-but-not-signed257-pushed-as-nan"
          (runQUFITSXDirect #[intV (pow2 300), bitsV 1023]) #[.int .nan] }
    ,
    { name := "unit/error/width-range-type-and-ordering"
      run := do
        expectErr "empty-underflow" (runQUFITSXDirect #[]) .stkUnd
        expectErr "width-only-underflow" (runQUFITSXDirect #[bitsV 8]) .stkUnd
        expectErr "top-width-null" (runQUFITSXDirect #[intV 7, .null]) .typeChk
        expectErr "top-width-cell" (runQUFITSXDirect #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "width-negative-rangechk" (runQUFITSXDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "width-too-large-rangechk" (runQUFITSXDirect #[intV 7, intV 1024]) .rangeChk
        expectErr "width-nan-rangechk" (runQUFITSXDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "range-before-x-type" (runQUFITSXDirect #[.null, intV (-1)]) .rangeChk
        expectErr "x-null-after-valid-width" (runQUFITSXDirect #[.null, bitsV 8]) .typeChk
        expectOkStack "top-width-valid-keeps-below"
          (runQUFITSXDirect #[.null, intV 7, bitsV 8])
          #[.null, intV 7] }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[qufitsxInstr, .add, qufitsxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qufitsx-1" s0 qufitsxInstr 24
        let s2 ← expectDecodeStep "decode/tail-add-1" s1 .add 8
        let s3 ← expectDecodeStep "decode/qufitsx-2" s2 qufitsxInstr 24
        let s4 ← expectDecodeStep "decode/tail-add-2" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add-2: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-qufitsx-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQUFITSXDispatchFallback #[]) #[intV 919] }
  ]
  oracle := #[
    mkQUFITSXCase "ok/bit0/zero" #[intV 0, bitsV 0],
    mkQUFITSXCase "ok/bit1/one" #[intV 1, bitsV 1],
    mkQUFITSXCase "ok/bit2/max" #[intV 3, bitsV 2],
    mkQUFITSXCase "ok/bit8/max" #[intV 255, bitsV 8],
    mkQUFITSXCase "ok/bit255/max" #[intV ((pow2 255) - 1), bitsV 255],
    mkQUFITSXCase "ok/bit256/max-int257" #[intV maxInt257, bitsV 256],
    mkQUFITSXCase "ok/bit257/max-int257" #[intV maxInt257, bitsV 257],
    mkQUFITSXCase "ok/bit1023/max-int257" #[intV maxInt257, bitsV 1023],
    mkQUFITSXCase "ok/order/below-kept" #[.null, intV 7, bitsV 8],
    mkQUFITSXCase "nan/overflow/bit0/one" #[intV 1, bitsV 0],
    mkQUFITSXCase "nan/overflow/bit1/two" #[intV 2, bitsV 1],
    mkQUFITSXCase "nan/overflow/bit8/pow2" #[intV (pow2 8), bitsV 8],
    mkQUFITSXCase "nan/overflow/bit255/max-int257" #[intV maxInt257, bitsV 255],
    mkQUFITSXCase "nan/negative/minus-one" #[intV (-1), bitsV 1023],
    mkQUFITSXCase "nan/negative/min-int257" #[intV minInt257, bitsV 1023],
    mkCase "nan/x-nan-via-program" #[] #[.pushInt .nan, .pushInt (.num 64), qufitsxInstr],
    mkQUFITSXCase "underflow/empty-stack" #[],
    mkQUFITSXCase "underflow/width-only" #[bitsV 8],
    mkQUFITSXCase "type/top-width-null" #[intV 1, .null],
    mkQUFITSXCase "type/top-width-cell" #[intV 1, .cell Cell.empty],
    mkQUFITSXCase "type/x-null-after-valid-width" #[.null, bitsV 8],
    mkQUFITSXCase "range/width-negative" #[intV 1, intV (-1)],
    mkQUFITSXCase "range/width-too-large" #[intV 1, intV 1024],
    mkCase "range/width-nan" #[] #[.pushInt (.num 1), .pushInt .nan, qufitsxInstr],
    mkQUFITSXCase "error-order/range-before-x-type" #[.null, intV (-1)],
    mkCase "gas/exact-cost-succeeds" #[intV 255, bitsV qufitsxGasProbeBits]
      #[.pushInt (.num qufitsxSetGasExact), .tonEnvOp .setGasLimit, qufitsxInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 255, bitsV qufitsxGasProbeBits]
      #[.pushInt (.num qufitsxSetGasExactMinusOne), .tonEnvOp .setGasLimit, qufitsxInstr]
  ]
  fuzz := #[
    { seed := 2026020806
      count := 650
      gen := genQUFITSXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QUFITSX
