import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHPOW2

/-
PUSHPOW2 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Stack/PushPow2.lean`
    (`execInstrStackPushPow2`, runtime push path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.pushPow2` assembler range gate)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0x8300..0x83fe => PUSHPOW2`, `0x83ff => PUSHNAN`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_push_pow2`, `exec_push_nan`, opcode wiring in `register_int_const_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/opctable.cpp`
    (`mkfixedrange` uses half-open `[min,max)`, preserving `0x83ff` for PUSHNAN)

Branch map and terminal outcomes covered:
- Lean runtime: 2 branch outcomes
  - dispatch `.pushPow2 exponent` vs `next` passthrough;
  - matched path performs raw `VM.push` (no `intOv`/range/type checks).
- Lean codec: 5 branch outcomes
  - assemble immediate guard: `1..255` ok vs out-of-range `rangeChk`;
  - decode `0x83**` split: `0x83ff` aliases to `.pushInt .nan`, otherwise `.pushPow2`.
- C++ alignment: 4 branch outcomes
  - opcode table split `0x8300..0x83fe` (PUSHPOW2) vs `0x83ff` (PUSHNAN);
  - `exec_push_pow2` always succeeds and pushes raw integer `2^x`.

Shared helper usage:
- `Tests.Harness.Gen.Arith`:
  - `pow2` / `intV` utilities;
  - `oracleIntInputsToStackOrProgram` for prelude-only NaN/out-of-range injection;
  - exact-gas fixed-point helpers (`computeExactGasBudget*`).

Key risk areas covered:
- opcode boundary split (`PUSHPOW2 255` vs `PUSHNAN` alias at `0x83ff`);
- push ordering: existing stack entries preserved, new power value appended;
- raw-push behavior (no signed-257 overflow rejection in direct handler path);
- prelude injection discipline for oracle/fuzz (NaN/out-of-range never in oracle `initStack`);
- exact gas cliff (`exact` succeeds, `exact-minus-one` fails).
-/

private def pushpow2Id : InstrId := { name := "PUSHPOW2" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def pushpow2Instr (exponent : Nat) : Instr :=
  .pushPow2 exponent

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := pushpow2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkExpCase
    (name : String)
    (exponent : Nat)
    (stack : Array Value := #[])
    (programPrefix : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (programPrefix ++ #[pushpow2Instr exponent]) gasLimits fuel

private def mkExpCaseFromIntVals
    (name : String)
    (exponent : Nat)
    (tailVals : Array IntVal)
    (programPrefix : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, preludeProgram) := oracleIntInputsToStackOrProgram tailVals
  mkExpCase name exponent stack (programPrefix ++ preludeProgram) gasLimits fuel

private def runPushpow2Direct (exponent : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushPow2 (pushpow2Instr exponent) stack

private def runPushpow2DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushPow2 (.pushPow2Dec 7) (VM.push (intV 8301)) stack

private def expectDecodeStep
    (label : String)
    (slice : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits slice with
  | .error decodeError =>
      throw (IO.userError s!"{label}: decode failed with {decodeError}")
  | .ok (decodedInstr, decodedBits, nextSlice) =>
      if decodedInstr != expectedInstr then
        throw (IO.userError
          s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr decodedInstr}")
      else if decodedBits != expectedBits then
        throw (IO.userError
          s!"{label}: expected bits {expectedBits}, got {decodedBits}")
      else
        pure nextSlice

private def pushpow2GasProbeExponent : Nat := 255

private def pushpow2GasProbeInstr : Instr :=
  pushpow2Instr pushpow2GasProbeExponent

private def pushpow2SetGasExact : Int :=
  computeExactGasBudget pushpow2GasProbeInstr

private def pushpow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pushpow2GasProbeInstr

private def exponentBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 31, 63, 127, 191, 254, 255]

private def preludeOutOfRangePool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1, pow2 257, -(pow2 257)]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (index, nextRng) := randNat rng 0 (pool.size - 1)
  (pool[index]!, nextRng)

private def pickBoundaryExponent (rng : StdGen) : Nat × StdGen :=
  pickFromPool exponentBoundaryPool rng

private def pickRandomExponent (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 255

private def pickMixedExponent (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickBoundaryExponent rng1
  else
    pickRandomExponent rng1

private def pickNonIntTailValue (rng : StdGen) : Value × StdGen :=
  let (useCell, nextRng) := randBool rng
  ((if useCell then .cell Cell.empty else .null), nextRng)

private def genPushpow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (baseCase, rng2) :=
    if shape = 0 then
      let (exponent, rng2) := pickBoundaryExponent rng1
      (mkExpCase s!"/fuzz/shape-{shape}/ok/empty/boundary-exp-{exponent}" exponent, rng2)
    else if shape = 1 then
      let (exponent, rng2) := pickRandomExponent rng1
      (mkExpCase s!"/fuzz/shape-{shape}/ok/empty/random-exp-{exponent}" exponent, rng2)
    else if shape = 2 then
      let (exponent, rng2) := pickMixedExponent rng1
      let (tailInt, rng3) := pickSigned257ish rng2
      (mkExpCase s!"/fuzz/shape-{shape}/ok/tail/finite-int" exponent #[intV tailInt], rng3)
    else if shape = 3 then
      let (exponent, rng2) := pickMixedExponent rng1
      let (tailValue, rng3) := pickNonIntTailValue rng2
      (mkExpCase s!"/fuzz/shape-{shape}/ok/tail/non-int" exponent #[tailValue], rng3)
    else if shape = 4 then
      let (exponent, rng2) := pickMixedExponent rng1
      let (tailIntA, rng3) := pickSigned257ish rng2
      let (tailIntB, rng4) := pickSigned257ish rng3
      (mkExpCase s!"/fuzz/shape-{shape}/ok/tail/deep" exponent #[.null, intV tailIntA, intV tailIntB], rng4)
    else if shape = 5 then
      let (exponent, rng2) := pickMixedExponent rng1
      (mkExpCaseFromIntVals s!"/fuzz/shape-{shape}/prelude/nan-tail-via-program" exponent #[.nan], rng2)
    else if shape = 6 then
      let (exponent, rng2) := pickMixedExponent rng1
      let (finiteTail, rng3) := pickSigned257ish rng2
      (mkExpCaseFromIntVals
        s!"/fuzz/shape-{shape}/prelude/finite-then-nan-tail-via-program"
        exponent #[.num finiteTail, .nan], rng3)
    else if shape = 7 then
      let (exponent, rng2) := pickMixedExponent rng1
      let (hugeTail, rng3) := pickFromPool preludeOutOfRangePool rng2
      (mkExpCaseFromIntVals
        s!"/fuzz/shape-{shape}/prelude/out-of-range-tail-via-program"
        exponent #[.num hugeTail], rng3)
    else if shape = 8 then
      let (exponent, rng2) := pickMixedExponent rng1
      let (finiteTail, rng3) := pickSigned257ish rng2
      let (hugeTail, rng4) := pickFromPool preludeOutOfRangePool rng3
      (mkExpCaseFromIntVals
        s!"/fuzz/shape-{shape}/error-order/prelude-range-before-op"
        exponent #[.num finiteTail, .num hugeTail], rng4)
    else if shape = 9 then
      let (exponent, rng2) := pickMixedExponent rng1
      (mkCase s!"/fuzz/shape-{shape}/ok/pushnan-alias-before-op"
        #[] #[.pushInt .nan, pushpow2Instr exponent], rng2)
    else if shape = 10 then
      (mkCase s!"/fuzz/shape-{shape}/gas/exact"
        #[] #[.pushInt (.num pushpow2SetGasExact), .tonEnvOp .setGasLimit, pushpow2GasProbeInstr], rng1)
    else if shape = 11 then
      (mkCase s!"/fuzz/shape-{shape}/gas/exact-minus-one"
        #[] #[.pushInt (.num pushpow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, pushpow2GasProbeInstr], rng1)
    else if shape = 12 then
      let (firstExponent, rng2) := pickMixedExponent rng1
      let (secondExponent, rng3) := pickMixedExponent rng2
      (mkCase s!"/fuzz/shape-{shape}/ok/two-pushpow2-program"
        #[] #[pushpow2Instr firstExponent, pushpow2Instr secondExponent], rng3)
    else
      let (exponent, rng2) := pickMixedExponent rng1
      (mkExpCase s!"/fuzz/shape-{shape}/ok/fallback-exp-{exponent}" exponent, rng2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pushpow2Id
  unit := #[
    { name := "/unit/direct/push-values-and-tail-preservation"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, pow2 1),
            (2, pow2 2),
            (8, pow2 8),
            (127, pow2 127),
            (255, pow2 255)
          ]
        for entry in checks do
          let exponent := entry.1
          let expected := entry.2
          expectOkStack s!"pushpow2/{exponent}"
            (runPushpow2Direct exponent #[]) #[intV expected]
        expectOkStack "tail/null-preserved"
          (runPushpow2Direct 8 #[.null]) #[.null, intV (pow2 8)]
        expectOkStack "tail/cell-preserved"
          (runPushpow2Direct 15 #[.cell Cell.empty]) #[.cell Cell.empty, intV (pow2 15)]
        expectOkStack "tail/nan-preserved"
          (runPushpow2Direct 7 #[.int .nan]) #[.int .nan, intV (pow2 7)] }
    ,
    { name := "/unit/direct/raw-push-allows-manual-exp-256"
      run := do
        expectOkStack "manual-exp-256"
          (runPushpow2Direct 256 #[]) #[intV (pow2 256)] }
    ,
    { name := "/unit/immediate/decode-boundary-and-pushnan-alias"
      run := do
        let program : Array Instr := #[pushpow2Instr 1, pushpow2Instr 255, .pushInt .nan, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error encodeError => throw (IO.userError s!"assemble failed: {encodeError}")
        let slice0 := Slice.ofCell code
        let slice1 ← expectDecodeStep "decode/pushpow2-exp1" slice0 (pushpow2Instr 1) 16
        let slice2 ← expectDecodeStep "decode/pushpow2-exp255" slice1 (pushpow2Instr 255) 16
        let slice3 ← expectDecodeStep "decode/pushnan-alias-83ff" slice2 (.pushInt .nan) 16
        let slice4 ← expectDecodeStep "decode/tail-add" slice3 .add 8
        if slice4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/end: expected exhausted slice, got {slice4.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/immediate/assembler-range-check"
      run := do
        match assembleCp0 [pushpow2Instr 0] with
        | .error .rangeChk => pure ()
        | .error encodeError =>
            throw (IO.userError s!"pushpow2/0: expected rangeChk, got {encodeError}")
        | .ok _ =>
            throw (IO.userError "pushpow2/0: expected assemble rangeChk, got success")
        match assembleCp0 [pushpow2Instr 256] with
        | .error .rangeChk => pure ()
        | .error encodeError =>
            throw (IO.userError s!"pushpow2/256: expected rangeChk, got {encodeError}")
        | .ok _ =>
            throw (IO.userError "pushpow2/256: expected assemble rangeChk, got success") }
    ,
    { name := "/unit/dispatch/non-pushpow2-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runPushpow2DispatchFallback #[]) #[intV 8301] }
  ]
  oracle := #[
    mkExpCase "ok/exp-1" 1,
    mkExpCase "ok/exp-2" 2,
    mkExpCase "ok/exp-8" 8,
    mkExpCase "ok/exp-31" 31,
    mkExpCase "ok/exp-127" 127,
    mkExpCase "ok/exp-255" 255,
    mkExpCase "ok/tail/null-preserved" 8 #[.null],
    mkExpCase "ok/tail/cell-preserved" 16 #[.cell Cell.empty],
    mkExpCase "ok/tail/int-preserved" 31 #[intV 99],
    mkExpCase "ok/pushnan-alias-before-op" 7 #[] #[.pushInt .nan],
    mkCase "ok/two-pushpow2-program"
      #[] #[pushpow2Instr 3, pushpow2Instr 5],
    mkExpCaseFromIntVals "prelude/nan-tail-via-program" 8 #[.nan],
    mkExpCaseFromIntVals "prelude/nan-with-finite-tail-via-program" 8 #[.num 42, .nan],
    mkExpCaseFromIntVals "prelude/range-positive-tail-via-program" 8 #[.num (pow2 257)],
    mkExpCaseFromIntVals "prelude/range-negative-tail-via-program" 8 #[.num (-(pow2 257))],
    mkExpCaseFromIntVals "error-order/prelude-range-before-op" 8 #[.num (maxInt257 + 1)],
    mkCase "gas/exact-cost-succeeds"
      #[] #[.pushInt (.num pushpow2SetGasExact), .tonEnvOp .setGasLimit, pushpow2GasProbeInstr],
    mkCase "gas/exact-minus-one-out-of-gas"
      #[] #[.pushInt (.num pushpow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, pushpow2GasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020842
      count := 620
      gen := genPushpow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHPOW2
