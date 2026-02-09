import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QPOW2

/-
QPOW2 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Qpow2.lean` (`execInstrArithQpow2`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popNatUpTo`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` / `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (opcode encode/decode for `QPOW2`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_pow2`, `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (dispatch to `.qpow2`; pop underflow/type; `popNatUpTo 1023`
   NaN/negative/over-max range gates; quiet `pushIntQuiet` fit-vs-overflow).
- C++: 6 branch points / 8 aligned terminal outcomes
  (`QPOW2` opcode wiring to `exec_pow2(..., quiet=true)`;
   `check_underflow`; `pop_int` type check; `pop_smallint_range(0..1023)` range gate;
   `set_pow2` magnitude path; `push_int_quiet` fit-vs-quiet-NaN behavior).

Key risk areas covered:
- quiet overflow split: `256..1023` must succeed and push NaN (not `intOv`);
- range/type/underflow ordering (`stkUnd` → `typeChk`/`rangeChk` as applicable);
- range gate precedence over quiet overflow (`1024` => `rangeChk`, `256` => NaN);
- top-of-stack operand consumption with below-stack preservation;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QPOW2`.
-/

private def qpow2Id : InstrId := { name := "QPOW2" }

private def qpow2Instr : Instr := .qpow2

private def mkQpow2Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qpow2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qpow2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQpow2CaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qpow2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkQpow2Case name stack (progPrefix ++ programSuffix) gasLimits fuel

private def runQpow2Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithQpow2 qpow2Instr stack

private def runQpow2DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithQpow2 .add (VM.push (intV 907)) stack

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

private def qpow2GasProbeExp : Int := 8

private def qpow2SetGasExact : Int :=
  computeExactGasBudget qpow2Instr

private def qpow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qpow2Instr

private def qpow2OkExpPool : Array Int :=
  #[0, 1, 2, 7, 8, 15, 31, 63, 127, 255]

private def qpow2OverflowExpPool : Array Int :=
  #[256, 257, 511, 1023]

private def qpow2RangeNegPool : Array Int :=
  #[-1, -2, -255, -1024]

private def qpow2RangeHighPool : Array Int :=
  #[1024, 1025, 2048, 4096]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genQpow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng2) :=
    if shape = 0 then
      let (exp, r2) := pickFromIntPool qpow2OkExpPool rng1
      (mkQpow2Case s!"fuzz/ok/exp-{exp}" #[intV exp], r2)
    else if shape = 1 then
      let (exp, r2) := pickFromIntPool qpow2OverflowExpPool rng1
      (mkQpow2Case s!"fuzz/quiet-overflow/exp-{exp}" #[intV exp], r2)
    else if shape = 2 then
      let (exp, r2) := pickFromIntPool qpow2RangeNegPool rng1
      (mkQpow2Case s!"fuzz/range/negative-{exp}" #[intV exp], r2)
    else if shape = 3 then
      let (exp, r2) := pickFromIntPool qpow2RangeHighPool rng1
      (mkQpow2Case s!"fuzz/range/overmax-{exp}" #[intV exp], r2)
    else if shape = 4 then
      (mkQpow2Case "fuzz/underflow/empty" #[], rng1)
    else if shape = 5 then
      let (pick, r2) := randNat rng1 0 1
      let top : Value := if pick = 0 then .null else .cell Cell.empty
      (mkQpow2Case s!"fuzz/type/top-non-int-{pick}" #[top], r2)
    else if shape = 6 then
      (mkQpow2CaseFromIntVals "fuzz/range/nan-via-program" #[IntVal.nan], rng1)
    else if shape = 7 then
      let (exp, r2) := pickFromIntPool qpow2OkExpPool rng1
      let (pick, r3) := randNat r2 0 1
      let below : Value := if pick = 0 then .null else intV 999
      (mkQpow2Case s!"fuzz/ok/top-order-below-{pick}" #[below, intV exp], r3)
    else if shape = 8 then
      let (exp, r2) := pickFromIntPool qpow2OverflowExpPool rng1
      let (pick, r3) := randNat r2 0 1
      let below : Value := if pick = 0 then .null else intV 777
      (mkQpow2Case s!"fuzz/quiet-overflow/top-order-below-{pick}" #[below, intV exp], r3)
    else if shape = 9 then
      (mkQpow2Case "fuzz/error-order/range-before-overflow" #[intV 1024], rng1)
    else if shape = 10 then
      (mkQpow2Case "fuzz/error-order/overflow-after-range-pass" #[intV 256], rng1)
    else
      let (u, r2) := randNat rng1 0 255
      let exp : Int := Int.ofNat u
      (mkQpow2Case s!"fuzz/ok/random-small-{u}" #[intV exp], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qpow2Id
  unit := #[
    { name := "unit/direct/success-and-quiet-overflow-boundaries"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, 1),
            (1, 2),
            (8, pow2 8),
            (31, pow2 31),
            (127, pow2 127),
            (255, pow2 255)
          ]
        for c in checks do
          let exp := c.1
          let expected := c.2
          expectOkStack s!"2^{exp}" (runQpow2Direct #[intV exp]) #[intV expected]
        expectOkStack "exp-256-quiet-overflow" (runQpow2Direct #[intV 256]) #[.int .nan]
        expectOkStack "exp-1023-quiet-overflow" (runQpow2Direct #[intV 1023]) #[.int .nan] }
    ,
    { name := "unit/range-type-underflow-errors"
      run := do
        expectErr "range/negative" (runQpow2Direct #[intV (-1)]) .rangeChk
        expectErr "range/overmax" (runQpow2Direct #[intV 1024]) .rangeChk
        expectErr "range/nan" (runQpow2Direct #[.int .nan]) .rangeChk
        expectErr "type/null" (runQpow2Direct #[.null]) .typeChk
        expectErr "type/cell" (runQpow2Direct #[.cell Cell.empty]) .typeChk
        expectErr "underflow/empty" (runQpow2Direct #[]) .stkUnd }
    ,
    { name := "unit/error-order-and-top-order"
      run := do
        expectErr "range-before-overflow" (runQpow2Direct #[intV 1024]) .rangeChk
        expectOkStack "overflow-after-range-pass"
          (runQpow2Direct #[intV 256]) #[.int .nan]
        expectErr "type-before-range" (runQpow2Direct #[.null]) .typeChk
        expectOkStack "top-order/below-preserved-success"
          (runQpow2Direct #[.null, intV 8]) #[.null, intV (pow2 8)]
        expectOkStack "top-order/below-preserved-quiet-overflow"
          (runQpow2Direct #[intV 77, intV 256]) #[intV 77, .int .nan] }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[qpow2Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qpow2" s0 qpow2Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-qpow2-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQpow2DispatchFallback #[]) #[intV 907] }
  ]
  oracle := #[
    mkQpow2Case "ok/exp-0" #[intV 0],
    mkQpow2Case "ok/exp-1" #[intV 1],
    mkQpow2Case "ok/exp-8" #[intV 8],
    mkQpow2Case "ok/exp-31" #[intV 31],
    mkQpow2Case "ok/exp-127" #[intV 127],
    mkQpow2Case "ok/exp-255" #[intV 255],
    mkQpow2Case "ok/top-order/below-preserved" #[.null, intV 8],
    mkQpow2Case "quiet-overflow/exp-256" #[intV 256],
    mkQpow2Case "quiet-overflow/exp-257" #[intV 257],
    mkQpow2Case "quiet-overflow/exp-511" #[intV 511],
    mkQpow2Case "quiet-overflow/exp-1023" #[intV 1023],
    mkQpow2Case "range/negative-minus-one" #[intV (-1)],
    mkQpow2Case "range/negative-minus-1024" #[intV (-1024)],
    mkQpow2Case "range/overmax-1024" #[intV 1024],
    mkQpow2Case "range/overmax-2048" #[intV 2048],
    mkQpow2CaseFromIntVals "range/nan-via-program" #[IntVal.nan],
    mkQpow2Case "underflow/empty-stack" #[],
    mkQpow2Case "type/top-null" #[.null],
    mkQpow2Case "type/top-cell" #[.cell Cell.empty],
    mkQpow2Case "error-order/range-before-overflow" #[intV 1024],
    mkQpow2Case "error-order/overflow-after-range-pass" #[intV 256],
    mkQpow2Case "gas/exact-cost-succeeds" #[intV qpow2GasProbeExp]
      #[.pushInt (.num qpow2SetGasExact), .tonEnvOp .setGasLimit, qpow2Instr],
    mkQpow2Case "gas/exact-minus-one-out-of-gas" #[intV qpow2GasProbeExp]
      #[.pushInt (.num qpow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, qpow2Instr]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 600
      gen := genQpow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QPOW2
