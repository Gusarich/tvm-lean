import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QRSHIFT

/-
QRSHIFT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/RshiftConst.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (24-bit `QRSHIFT <imm8+1>` encoding)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (24-bit `0xb7ab` decode)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_rshift_tinyint8`, `register_div_ops` wiring for `QRSHIFT`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/refint.cpp`
    (`operator>>`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`)

Branch counts used for this suite:
- Lean (QRSHIFT specialization): 4 branch points / 6 terminal outcomes
  (dispatch/fallback; `popInt` underflow/type/success; NaN-vs-num split;
   quiet `pushIntQuiet` fit-vs-overflow-to-NaN split for numeric results).
- C++ (QRSHIFT specialization): 4 branch points / 6 aligned outcomes
  (opcode binds to `exec_rshift_tinyint8(..., quiet=true)`; underflow check;
   `pop_int` type check; `push_int_quiet` fit-vs-quiet-NaN for oversized results).

Mapped terminal outcomes covered:
- finite success with arithmetic sign-extension for `bits ∈ [1, 256]`;
- quiet NaN passthrough from NaN input;
- quiet NaN from oversized numeric results;
- finite fold from oversized inputs when shift count makes result fit;
- `stkUnd`;
- `typeChk`;
- assembler `rangeChk` for invalid immediate (`bits = 0` or `bits > 256`).

Key divergence risk areas covered:
- arithmetic right-shift sign-extension on negative values (`-1`, `minInt257`, odd negatives);
- immediate encoding/decoding boundaries (`1`, `2`, `255`, `256`) in 24-bit form;
- unary pop error ordering (underflow before type; top-only consumption on success);
- quiet NaN/out-of-range behavior with serialization-safe program injection only;
- deterministic gas edge for `PUSHINT n; SETGASLIMIT; QRSHIFT bits`
  at exact and exact-minus-one budgets.
-/

private def qrshiftId : InstrId := { name := "QRSHIFT" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qrshiftId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQrshiftCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[.rshiftConst true bits] gasLimits fuel

private def mkInputCase
    (name : String)
    (bits : Nat)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (programPrefix ++ #[.rshiftConst true bits])

private def runQrshiftDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithRshiftConst (.rshiftConst true bits) stack

private def runQrshiftDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithRshiftConst .add (VM.push (intV 917)) stack

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

private def qrshiftGasProbeBits : Nat := 13

private def qrshiftSetGasExact : Int :=
  computeExactGasBudget (.rshiftConst true qrshiftGasProbeBits)

private def qrshiftSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.rshiftConst true qrshiftGasProbeBits)

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

private def hugeOutOfRangePos : Int := (maxInt257 + 1) * 2

private def hugeOutOfRangeNeg : Int := -((maxInt257 + 1) * 2) - 1

private def genQrshiftFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkQrshiftCase s!"fuzz/shape-{shape}/ok/boundary-x-boundary-shift" bits #[intV x], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkQrshiftCase s!"fuzz/shape-{shape}/ok/signed-x-boundary-shift" bits #[intV x], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (bits, r3) := pickShiftInRange r2
      (mkQrshiftCase s!"fuzz/shape-{shape}/ok/boundary-x-random-shift" bits #[intV x], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (bits, r3) := pickShiftInRange r2
      (mkQrshiftCase s!"fuzz/shape-{shape}/ok/signed-x-random-shift" bits #[intV x], r3)
    else if shape = 4 then
      let (bits, r2) := pickShiftInRange rng1
      (mkQrshiftCase s!"fuzz/shape-{shape}/ok/sign-extension-minus-one" bits #[intV (-1)], r2)
    else if shape = 5 then
      let (useMin, r2) := randBool rng1
      let x := if useMin then minInt257 else maxInt257
      let (bits, r3) := pickShiftBoundary r2
      (mkQrshiftCase s!"fuzz/shape-{shape}/ok/extreme-endpoints" bits #[intV x], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      (mkQrshiftCase s!"fuzz/shape-{shape}/ok/shift-256-sign-extension" 256 #[intV x], r2)
    else if shape = 7 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkQrshiftCase s!"fuzz/shape-{shape}/error/underflow-empty" bits #[], r2)
    else if shape = 8 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkQrshiftCase s!"fuzz/shape-{shape}/error/type-top-null" bits #[.null], r2)
    else if shape = 9 then
      let (bits, r2) := pickShiftBoundary rng1
      (mkQrshiftCase s!"fuzz/shape-{shape}/error/type-top-cell" bits #[.cell Cell.empty], r2)
    else if shape = 10 then
      let (bits, r2) := pickNanCompatShift rng1
      (mkInputCase s!"fuzz/shape-{shape}/quiet/nan-via-program" bits .nan, r2)
    else if shape = 11 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (bits, r3) := pickShiftBoundary r2
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-helper-via-program" bits (.num x), r3)
    else if shape = 12 then
      let (bitsRaw, r2) := pickNanCompatShift rng1
      let bits := if bitsRaw = 256 then 1 else bitsRaw
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-huge-high-to-nan-via-program"
        bits (.num hugeOutOfRangePos), r2)
    else if shape = 13 then
      let (bitsRaw, r2) := pickNanCompatShift rng1
      let bits := if bitsRaw = 256 then 1 else bitsRaw
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-huge-low-to-nan-via-program"
        bits (.num hugeOutOfRangeNeg), r2)
    else if shape = 14 then
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-huge-high-fold-finite-via-program"
        256 (.num hugeOutOfRangePos), rng1)
    else
      (mkInputCase s!"fuzz/shape-{shape}/quiet/range-huge-low-fold-finite-via-program"
        256 (.num hugeOutOfRangeNeg), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qrshiftId
  unit := #[
    { name := "unit/direct/floor-sign-extension-and-boundary-shifts"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (7, 1, 3),
            (7, 2, 1),
            (-7, 1, -4),
            (-7, 2, -2),
            (1, 256, 0),
            (-1, 1, -1),
            (-1, 256, -1),
            (maxInt257, 255, 1),
            (minInt257, 255, -2),
            (maxInt257, 256, 0),
            (minInt257, 256, -1)
          ]
        for c in checks do
          let x := c.1
          let bits := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>>{bits}" (runQrshiftDirect bits #[intV x]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-and-range-folding"
      run := do
        expectOkStack "quiet/nan-direct" (runQrshiftDirect 13 #[.int .nan]) #[intV (-1)]
        expectOkStack "quiet/range-high-to-nan" (runQrshiftDirect 1 #[intV hugeOutOfRangePos]) #[.int .nan]
        expectOkStack "quiet/range-low-to-nan" (runQrshiftDirect 1 #[intV hugeOutOfRangeNeg]) #[.int .nan]
        expectOkStack "quiet/range-high-fold-finite"
          (runQrshiftDirect 256 #[intV hugeOutOfRangePos]) #[intV 2]
        expectOkStack "quiet/range-low-fold-finite"
          (runQrshiftDirect 256 #[intV hugeOutOfRangeNeg]) #[intV (-3)] }
    ,
    { name := "unit/immediate/decode-boundary-sequence-24bit"
      run := do
        let program : Array Instr :=
          #[.rshiftConst true 1, .rshiftConst true 2, .rshiftConst true 255, .rshiftConst true 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/1" s0 (.rshiftConst true 1) 24
        let s2 ← expectDecodeStep "decode/2" s1 (.rshiftConst true 2) 24
        let s3 ← expectDecodeStep "decode/255" s2 (.rshiftConst true 255) 24
        let s4 ← expectDecodeStep "decode/256" s3 (.rshiftConst true 256) 24
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "qrshift/0" [.rshiftConst true 0] .rangeChk
        expectAssembleErr "qrshift/257" [.rshiftConst true 257] .rangeChk }
    ,
    { name := "unit/error-order/underflow-before-type-and-top-pop"
      run := do
        expectErr "underflow/empty" (runQrshiftDirect 1 #[]) .stkUnd
        expectErr "type/top-null" (runQrshiftDirect 1 #[.null]) .typeChk
        expectErr "type/top-cell" (runQrshiftDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-null-before-lower-int" (runQrshiftDirect 1 #[intV 7, .null]) .typeChk
        expectOkStack "ok/top-only-consumed/lower-preserved"
          (runQrshiftDirect 1 #[.null, intV (-8)]) #[.null, intV (-4)] }
    ,
    { name := "unit/dispatch/non-qrshift-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQrshiftDispatchFallback #[]) #[intV 917] }
  ]
  oracle := #[
    mkQrshiftCase "ok/floor/pos-shift1" 1 #[intV 7],
    mkQrshiftCase "ok/floor/neg-shift1-sign-extend" 1 #[intV (-7)],
    mkQrshiftCase "ok/floor/pos-shift2" 2 #[intV 7],
    mkQrshiftCase "ok/floor/neg-shift2-sign-extend" 2 #[intV (-7)],
    mkQrshiftCase "ok/floor/minus-one-stable" 256 #[intV (-1)],
    mkQrshiftCase "ok/floor/zero-stable" 128 #[intV 0],
    mkQrshiftCase "ok/boundary/max-shift255" 255 #[intV maxInt257],
    mkQrshiftCase "ok/boundary/min-shift255" 255 #[intV minInt257],
    mkQrshiftCase "ok/boundary/max-shift256" 256 #[intV maxInt257],
    mkQrshiftCase "ok/boundary/min-shift256" 256 #[intV minInt257],
    mkQrshiftCase "ok/top-only-consumed/lower-preserved" 1 #[.null, intV (-8)],
    mkInputCase "quiet/nan-via-program" 13 .nan,
    mkInputCase "quiet/nan-via-program-with-tail" 7 .nan #[intV 11],
    mkInputCase "quiet/range-helper-via-program-high" 1 (.num (maxInt257 + 1)),
    mkInputCase "quiet/range-helper-via-program-low" 1 (.num (minInt257 - 1)),
    mkInputCase "quiet/range-huge-high-to-nan-via-program" 1 (.num (maxInt257 + 1)),
    mkInputCase "quiet/range-huge-low-to-nan-via-program" 1 (.num (minInt257 - 1)),
    mkInputCase "quiet/range-huge-high-fold-finite-via-program" 256 (.num (maxInt257 + 1)),
    mkInputCase "quiet/range-huge-low-fold-finite-via-program" 256 (.num (minInt257 - 1)),
    mkQrshiftCase "error/underflow/empty-stack" 1 #[],
    mkQrshiftCase "error/type/top-null" 1 #[.null],
    mkQrshiftCase "error/type/top-cell" 1 #[.cell Cell.empty],
    mkQrshiftCase "error/order/type-top-null-before-lower-int" 1 #[intV 7, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num qrshiftSetGasExact), .tonEnvOp .setGasLimit, .rshiftConst true qrshiftGasProbeBits],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num qrshiftSetGasExactMinusOne), .tonEnvOp .setGasLimit, .rshiftConst true qrshiftGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026020831
      count := 600
      gen := genQrshiftFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFT
