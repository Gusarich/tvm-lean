import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFT

/-
QLSHIFT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/LshiftConst.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (24-bit `QLSHIFT <imm8+1>` encoding)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (24-bit `0xb7aa` decode)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, quiet `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_lshift_tinyint8`, `register_div_ops` wiring for `QLSHIFT`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean specialization: 4 branch points / 7 terminal outcomes
  (dispatch/fallback; unary pop underflow/type/success; NaN-vs-num split;
   quiet push finite-vs-overflow-to-NaN on numeric results).
- C++ specialization: 4 branch points / 7 aligned terminal outcomes
  (opcode binds to quiet tinyint left shift; underflow check;
   `pop_int` type check; quiet push finite-vs-NaN split).

Mapped terminal outcomes covered:
- finite success for signed operands and immediate boundaries (`bits ∈ [1, 256]`);
- invalid-input compatibility split from C++ (`NaN` preserved for `bits < 64`,
  normalized to integer zero for `bits ≥ 64`);
- quiet NaN funnel for numeric overflow and oversized injected values;
- `stkUnd`;
- `typeChk`;
- assembler `rangeChk` for invalid immediate (`bits = 0` or `bits > 256`).

Key divergence risk areas covered:
- two's-complement sign behavior at `255/256` shift boundaries;
- signed-257 fit cliff (`[-2^256, 2^256-1]`) in quiet mode (NaN, not throw);
- unary pop/error ordering (underflow on empty, type check on non-empty top);
- top-only consumption with lower-stack preservation;
- oracle serialization constraints (`NaN` / out-of-range only via program injection);
- exact gas edge for `PUSHINT n; SETGASLIMIT; QLSHIFT bits`.
-/

private def qlshiftId : InstrId := { name := "QLSHIFT" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQlshiftCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[.lshiftConst true bits] gasLimits fuel

private def mkInputCase
    (name : String)
    (bits : Nat)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (programPrefix ++ #[.lshiftConst true bits])

private def runQlshiftDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithLshiftConst (.lshiftConst true bits) stack

private def runQlshiftDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithLshiftConst .add (VM.push (intV 919)) stack

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

private def qlshiftGasProbeBits : Nat := 13

private def qlshiftSetGasExact : Int :=
  computeExactGasBudget (.lshiftConst true qlshiftGasProbeBits)

private def qlshiftSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.lshiftConst true qlshiftGasProbeBits)

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def nanCompatShiftPool : Array Nat :=
  #[1, 2, 3, 8, 16, 32, 64, 128, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickNanCompatShift (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (nanCompatShiftPool.size - 1)
  (nanCompatShiftPool[idx]!, rng')

private def hugeOutOfRangePos : Int := pow2 300

private def hugeOutOfRangeNeg : Int := -(pow2 300)

private def genQlshiftFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok/boundary-x-boundary-shift" bits #[intV x], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok/signed-x-boundary-shift" bits #[intV x], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (bits, r3) := pickShiftInRange r2
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok/boundary-x-random-shift" bits #[intV x], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (bits, r3) := pickShiftInRange r2
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok/signed-x-random-shift" bits #[intV x], r3)
    else if shape = 4 then
      let (bits, r2) := pickShiftInRange rng1
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok/zero-stable" bits #[intV 0], r2)
    else if shape = 5 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok-or-nan/minus-one-boundary-shifts" bits #[intV (-1)], r2)
    else if shape = 6 then
      (mkQlshiftCase s!"fuzz/shape-{shape}/quiet/overflow-max-shift1" 1 #[intV maxInt257], rng1)
    else if shape = 7 then
      (mkQlshiftCase s!"fuzz/shape-{shape}/quiet/overflow-min-shift1" 1 #[intV minInt257], rng1)
    else if shape = 8 then
      (mkQlshiftCase s!"fuzz/shape-{shape}/quiet/overflow-one-shift256" 256 #[intV 1], rng1)
    else if shape = 9 then
      let (pickEdge, r2) := randBool rng1
      let bits := if pickEdge then 1 else 256
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok/immediate/boundary-edge" bits #[intV 7], r2)
    else if shape = 10 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkQlshiftCase s!"fuzz/shape-{shape}/error/underflow-empty" bits #[], r2)
    else if shape = 11 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkQlshiftCase s!"fuzz/shape-{shape}/error/type-top-null" bits #[.null], r2)
    else if shape = 12 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkQlshiftCase s!"fuzz/shape-{shape}/error/type-top-cell" bits #[.cell Cell.empty], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkQlshiftCase s!"fuzz/shape-{shape}/error/order/type-top-before-lower-int" bits #[intV x, .null], r3)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkQlshiftCase s!"fuzz/shape-{shape}/ok/top-only-consumed-lower-preserved"
        bits #[.null, intV x], r3)
    else if shape = 15 then
      let (bits, r2) := pickNanCompatShift rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-via-program" bits .nan, r2)
    else if shape = 16 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-before-op" bits (.num x), r3)
    else if shape = 17 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-high-before-op-with-tail"
        bits (.num (maxInt257 + 1)) #[.null], r2)
    else if shape = 18 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-low-before-op-with-tail"
        bits (.num (minInt257 - 1)) #[intV 11], r2)
    else
      let (bits, r2) := pickNanCompatShift rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-via-program-with-tail" bits .nan #[intV 11], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftId
  unit := #[
    { name := "unit/direct/finite-boundaries-and-quiet-overflow-funnel"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (0, 1, 0),
            (7, 1, 14),
            (-7, 1, -14),
            (1, 255, pow2 255),
            (-1, 255, -(pow2 255)),
            (-1, 256, minInt257),
            ((pow2 255) - 1, 1, maxInt257 - 1),
            (-(pow2 255), 1, minInt257),
            (0, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let bits := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}<<{bits}" (runQlshiftDirect bits #[intV x]) #[intV expected]
        let quietNanChecks : Array (Int × Nat) :=
          #[
            (maxInt257, 1),
            (minInt257, 1),
            (1, 256),
            (pow2 255, 1),
            (pow2 257, 1),
            (-(pow2 257), 1)
          ]
        for c in quietNanChecks do
          let x := c.1
          let bits := c.2
          expectOkStack s!"quiet-nan/{x}<<{bits}"
            (runQlshiftDirect bits #[intV x]) #[.int .nan]
        expectOkStack "quiet/nan-direct"
          (runQlshiftDirect 13 #[.int .nan]) #[.int .nan]
        expectOkStack "quiet/nan-wordshift64-normalizes-zero"
          (runQlshiftDirect 64 #[.int .nan]) #[intV 0]
        expectOkStack "quiet/nan-wordshift128-normalizes-zero"
          (runQlshiftDirect 128 #[.int .nan]) #[intV 0]
        expectOkStack "quiet/range-huge-high-direct"
          (runQlshiftDirect 1 #[intV hugeOutOfRangePos]) #[.int .nan]
        expectOkStack "quiet/range-huge-low-direct"
          (runQlshiftDirect 1 #[intV hugeOutOfRangeNeg]) #[.int .nan] }
    ,
    { name := "unit/immediate/decode-boundary-sequence-24bit"
      run := do
        let program : Array Instr :=
          #[.lshiftConst true 1, .lshiftConst true 2, .lshiftConst true 255, .lshiftConst true 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/1" s0 (.lshiftConst true 1) 24
        let s2 ← expectDecodeStep "decode/2" s1 (.lshiftConst true 2) 24
        let s3 ← expectDecodeStep "decode/255" s2 (.lshiftConst true 255) 24
        let s4 ← expectDecodeStep "decode/256" s3 (.lshiftConst true 256) 24
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "qlshift/0" [.lshiftConst true 0] .rangeChk
        expectAssembleErr "qlshift/257" [.lshiftConst true 257] .rangeChk }
    ,
    { name := "unit/error-order/underflow-before-type-and-top-pop"
      run := do
        expectErr "underflow/empty" (runQlshiftDirect 1 #[]) .stkUnd
        expectErr "type/top-null" (runQlshiftDirect 1 #[.null]) .typeChk
        expectErr "type/top-cell" (runQlshiftDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "error-order/type-top-before-lower-int"
          (runQlshiftDirect 1 #[intV 7, .null]) .typeChk
        expectOkStack "ok/top-only-consumed/lower-preserved"
          (runQlshiftDirect 1 #[.null, intV 7]) #[.null, intV 14]
        expectOkStack "ok/top-only-consumed/lower-preserved-nan"
          (runQlshiftDirect 13 #[.null, .int .nan]) #[.null, .int .nan] }
    ,
    { name := "unit/dispatch/non-qlshift-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQlshiftDispatchFallback #[]) #[intV 919] }
  ]
  oracle := #[
    mkQlshiftCase "ok/finite/pos-shift1" 1 #[intV 7],
    mkQlshiftCase "ok/finite/neg-shift1" 1 #[intV (-7)],
    mkQlshiftCase "ok/finite/pos-shift2" 2 #[intV 7],
    mkQlshiftCase "ok/finite/neg-shift2" 2 #[intV (-7)],
    mkQlshiftCase "ok/finite/one-shift255" 255 #[intV 1],
    mkQlshiftCase "ok/finite/neg-one-shift255" 255 #[intV (-1)],
    mkQlshiftCase "ok/finite/neg-one-shift256" 256 #[intV (-1)],
    mkQlshiftCase "ok/finite/zero-shift256" 256 #[intV 0],
    mkQlshiftCase "ok/boundary/near-max-safe-shift1" 1 #[intV ((pow2 255) - 1)],
    mkQlshiftCase "ok/boundary/neg-pow2-255-shift1" 1 #[intV (-(pow2 255))],
    mkQlshiftCase "ok/top-only-consumed/lower-preserved" 1 #[.null, intV 7],
    mkQlshiftCase "quiet/overflow/max-shift1" 1 #[intV maxInt257],
    mkQlshiftCase "quiet/overflow/min-shift1" 1 #[intV minInt257],
    mkQlshiftCase "quiet/overflow/one-shift256" 256 #[intV 1],
    mkQlshiftCase "quiet/overflow/pow2-255-shift1" 1 #[intV (pow2 255)],
    mkInputCase "quiet/nan/via-program" 13 .nan,
    mkInputCase "regression/quiet/nan-wordshift64-normalizes-zero" 64 .nan,
    mkInputCase "regression/quiet/nan-wordshift128-normalizes-zero" 128 .nan,
    mkInputCase "quiet/nan/via-program-with-tail" 7 .nan #[intV 11],
    mkQlshiftCase "error/underflow/empty-stack" 1 #[],
    mkQlshiftCase "error/type/top-null" 1 #[.null],
    mkQlshiftCase "error/type/top-cell" 1 #[.cell Cell.empty],
    mkQlshiftCase "error/order/type-top-before-lower-int" 1 #[intV 7, .null],
    mkInputCase "error-order/pushint-overflow-before-op-high" 1 (.num (maxInt257 + 1)),
    mkInputCase "error-order/pushint-overflow-before-op-low" 1 (.num (minInt257 - 1)),
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num qlshiftSetGasExact), .tonEnvOp .setGasLimit, .lshiftConst true qlshiftGasProbeBits],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num qlshiftSetGasExactMinusOne), .tonEnvOp .setGasLimit, .lshiftConst true qlshiftGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026020832
      count := 700
      gen := genQlshiftFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFT
