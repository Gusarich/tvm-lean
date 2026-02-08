import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.UFITSX

/-
UFITSX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.ufitsx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`UFITSX` opcode encode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xb601` decode)
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (stack-width FITSX/UFITSX handlers, opcode wiring in shift/logic registration).

Branch/terminal outcomes covered by this suite:
- Lean: 7 branch sites / 9 terminal outcomes for UFITSX
  (opcode dispatch; `popNatUpTo 1023` underflow/type/range/success;
   second-pop underflow/type/success for `x`; `IntVal` nan-vs-num;
   unsigned-fit predicate; non-quiet fail path to `.intOv`).
- C++: aligned stack-width fit path branches
  (width pop/check; operand pop/type; unsigned-fit success vs overflow throw).

Key divergence risk areas:
- width source is stack, not immediate: legal runtime domain is `[0, 1023]`;
- width `0` is valid and only accepts `x = 0`;
- pop order is `width` first, then `x` (range/type ordering depends on this);
- non-quiet UFITSX must throw `.intOv` for NaN `x` and non-fitting values;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; UFITSX` (exact vs exact-1).
-/

private def ufitsxId : InstrId := { name := "UFITSX" }

private def ufitsxInstr : Instr := .contExt .ufitsx

private def bitsV (bits : Nat) : Value :=
  intV (Int.ofNat bits)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ufitsxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ufitsxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkUFITSXCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[ufitsxInstr] gasLimits fuel

private def runUFITSXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt ufitsxInstr stack

private def runUFITSXDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt .add (VM.push (intV 777)) stack

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

private def ufitsxGasProbeBits : Nat := 17

private def ufitsxSetGasExact : Int :=
  computeExactGasBudget ufitsxInstr

private def ufitsxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ufitsxInstr

private def ufitsxBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 511, 512, 1023]

private def pickUFITSXBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ufitsxBitsBoundaryPool.size - 1)
  (ufitsxBitsBoundaryPool[idx]!, rng')

private def pickUFITSXBitsUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 1023

private def pickUFITSXBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickUFITSXBitsBoundary rng1
  else
    pickUFITSXBitsUniform rng1

private def ufitsxOverflowBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255]

private def pickUFITSXOverflowBits (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ufitsxOverflowBitsPool.size - 1)
  (ufitsxOverflowBitsPool[idx]!, rng')

private def ufitsxInvalidNegativeBitsPool : Array Int :=
  #[-1, -2, -17, -256]

private def pickUFITSXInvalidNegativeBits (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (ufitsxInvalidNegativeBitsPool.size - 1)
  (ufitsxInvalidNegativeBitsPool[idx]!, rng')

private def ufitsxInvalidHighBitsPool : Array Int :=
  #[1024, 1025, 1536, 2048]

private def pickUFITSXInvalidHighBits (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (ufitsxInvalidHighBitsPool.size - 1)
  (ufitsxInvalidHighBitsPool[idx]!, rng')

private def pickUFITSXNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genUFITSXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, r3) := pickInt257Boundary rng2
    let (bits, r4) := pickUFITSXBitsBoundary r3
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsV bits], r4)
  else if shape = 1 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickUFITSXBitsMixed r3
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsV bits], r4)
  else if shape = 2 then
    let (bits, r3) := pickUFITSXBitsMixed rng2
    let x :=
      if bits = 0 then
        0
      else if bits ≤ 256 then
        pow2 bits - 1
      else
        maxInt257
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.num bits]
    (mkCase s!"fuzz/shape-{shape}-{tag}" stack (progPrefix.push ufitsxInstr), r3)
  else if shape = 3 then
    let (bits, r3) := pickUFITSXOverflowBits rng2
    let x := if bits = 0 then 1 else pow2 bits
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.num bits]
    (mkCase s!"fuzz/shape-{shape}-{tag}" stack (progPrefix.push ufitsxInstr), r3)
  else if shape = 4 then
    let (bits, r3) := pickUFITSXBitsMixed rng2
    let (which, r4) := randNat r3 0 2
    let x : Int :=
      if which = 0 then
        -1
      else if which = 1 then
        -2
      else
        minInt257
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsV bits], r4)
  else if shape = 5 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickUFITSXInvalidNegativeBits r3
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV bits], r4)
  else if shape = 6 then
    let (x, r3) := pickSigned257ish rng2
    let (bits, r4) := pickUFITSXInvalidHighBits r3
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV bits], r4)
  else if shape = 7 then
    let (x, r3) := pickInt257Boundary rng2
    let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.num x, IntVal.nan]
    (mkCase s!"fuzz/shape-{shape}-{tag}" stack (progPrefix.push ufitsxInstr), r3)
  else if shape = 8 then
    let (x, r3) := pickSigned257ish rng2
    let (bitsNonInt, r4) := pickUFITSXNonInt r3
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[intV x, bitsNonInt], r4)
  else if shape = 9 then
    let (xNonInt, r3) := pickUFITSXNonInt rng2
    let (bits, r4) := pickUFITSXBitsMixed r3
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[xNonInt, bitsV bits], r4)
  else
    let (bits, r3) := pickUFITSXBitsMixed rng2
    (mkUFITSXCase s!"fuzz/shape-{shape}-{tag}" #[bitsV bits], r3)

def suite : InstrSuite where
  id := ufitsxId
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
          expectOkStack s!"bits={bits}/x={x}" (runUFITSXDirect #[intV x, bitsV bits]) #[intV x] }
    ,
    { name := "unit/direct/non-fitting-and-nan-intov"
      run := do
        expectErr "bit0/one" (runUFITSXDirect #[intV 1, bitsV 0]) .intOv
        expectErr "bit1/two" (runUFITSXDirect #[intV 2, bitsV 1]) .intOv
        expectErr "bit8/pow2" (runUFITSXDirect #[intV (pow2 8), bitsV 8]) .intOv
        expectErr "bit255/max-int257" (runUFITSXDirect #[intV maxInt257, bitsV 255]) .intOv
        expectErr "negative-in-unsigned" (runUFITSXDirect #[intV (-1), bitsV 1023]) .intOv
        expectErr "nan-propagates-intov" (runUFITSXDirect #[.int .nan, bitsV 32]) .intOv }
    ,
    { name := "unit/error/width-range-type-and-ordering"
      run := do
        expectErr "empty-underflow" (runUFITSXDirect #[]) .stkUnd
        expectErr "width-only-underflow" (runUFITSXDirect #[bitsV 8]) .stkUnd
        expectErr "top-width-null" (runUFITSXDirect #[intV 7, .null]) .typeChk
        expectErr "top-width-cell" (runUFITSXDirect #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "width-negative-rangechk" (runUFITSXDirect #[intV 7, intV (-1)]) .rangeChk
        expectErr "width-too-large-rangechk" (runUFITSXDirect #[intV 7, intV 1024]) .rangeChk
        expectErr "width-nan-rangechk" (runUFITSXDirect #[intV 7, .int .nan]) .rangeChk
        expectErr "range-before-x-type" (runUFITSXDirect #[.null, intV (-1)]) .rangeChk
        expectErr "x-null-after-valid-width" (runUFITSXDirect #[.null, bitsV 8]) .typeChk
        expectOkStack "top-width-valid-keeps-below"
          (runUFITSXDirect #[.null, intV 7, bitsV 8])
          #[.null, intV 7] }
    ,
    { name := "unit/opcode/decode-sequence"
      run := do
        let program : Array Instr := #[ufitsxInstr, .add, ufitsxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ufitsx-1" s0 ufitsxInstr 16
        let s2 ← expectDecodeStep "decode/tail-add-1" s1 .add 8
        let s3 ← expectDecodeStep "decode/ufitsx-2" s2 ufitsxInstr 16
        let s4 ← expectDecodeStep "decode/tail-add-2" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add-2: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-ufitsx-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runUFITSXDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkUFITSXCase "ok/bit0/zero" #[intV 0, bitsV 0],
    mkUFITSXCase "ok/bit1/one" #[intV 1, bitsV 1],
    mkUFITSXCase "ok/bit2/max" #[intV 3, bitsV 2],
    mkUFITSXCase "ok/bit8/max" #[intV 255, bitsV 8],
    mkUFITSXCase "ok/bit255/max" #[intV ((pow2 255) - 1), bitsV 255],
    mkUFITSXCase "ok/bit256/max-int257" #[intV maxInt257, bitsV 256],
    mkUFITSXCase "ok/bit257/max-int257" #[intV maxInt257, bitsV 257],
    mkUFITSXCase "ok/bit1023/max-int257" #[intV maxInt257, bitsV 1023],
    mkUFITSXCase "ok/order/below-kept" #[.null, intV 7, bitsV 8],
    mkUFITSXCase "overflow/bit0/one" #[intV 1, bitsV 0],
    mkUFITSXCase "overflow/bit1/two" #[intV 2, bitsV 1],
    mkUFITSXCase "overflow/bit8/pow2" #[intV (pow2 8), bitsV 8],
    mkUFITSXCase "overflow/bit255/max-int257" #[intV maxInt257, bitsV 255],
    mkUFITSXCase "overflow/negative/minus-one" #[intV (-1), bitsV 1023],
    mkUFITSXCase "overflow/negative/min-int257" #[intV minInt257, bitsV 1023],
    mkUFITSXCase "underflow/empty-stack" #[],
    mkUFITSXCase "underflow/width-only" #[bitsV 8],
    mkUFITSXCase "type/top-width-null" #[intV 1, .null],
    mkUFITSXCase "type/top-width-cell" #[intV 1, .cell Cell.empty],
    mkUFITSXCase "type/x-null-after-valid-width" #[.null, bitsV 8],
    mkUFITSXCase "range/width-negative" #[intV 1, intV (-1)],
    mkUFITSXCase "range/width-too-large" #[intV 1, intV 1024],
    mkCase "range/width-nan" #[intV 1] #[.pushInt .nan, ufitsxInstr],
    mkUFITSXCase "error-order/range-before-x-type" #[.null, intV (-1)],
    mkCase "nan/x-nan-propagates-intov" #[bitsV 64] #[.pushInt .nan, .xchg0 1, ufitsxInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 255, bitsV ufitsxGasProbeBits]
      #[.pushInt (.num ufitsxSetGasExact), .tonEnvOp .setGasLimit, ufitsxInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 255, bitsV ufitsxGasProbeBits]
      #[.pushInt (.num ufitsxSetGasExactMinusOne), .tonEnvOp .setGasLimit, ufitsxInstr]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 600
      gen := genUFITSXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.UFITSX
