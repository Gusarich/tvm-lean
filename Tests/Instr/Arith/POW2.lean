import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.POW2

/-
POW2 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.pow2`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popNatUpTo`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` / `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (opcode encode/decode for `POW2`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_pow2`, `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (dispatch to `.contExt .pow2`; pop underflow/type; `popNatUpTo 1023`
   NaN/negative/over-max checks; signed-257 fit check in non-quiet `pushIntQuiet`).
- C++: 5 branch points / 8 aligned terminal outcomes
  (opcode registration binds `POW2` to `exec_pow2(..., quiet=false)`;
   `check_underflow`; `pop_int` type check; `pop_long_range(0..1023)` range gate;
   `push_int_quiet` signed-257 overflow gate).

Key risk areas covered:
- exponent boundary split: `255` succeeds but `256` overflows (`intOv`);
- in-range-but-large exponents (`257..1023`) must stay `intOv` (not `rangeChk`);
- range/type/underflow ordering (`stkUnd` → `typeChk`/`rangeChk` as applicable);
- top-of-stack operand use with below-stack preservation on success;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; POW2`.
-/

private def pow2Id : InstrId := { name := "POW2" }

private def pow2Instr : Instr := .contExt .pow2

private def mkPow2Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pow2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pow2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPow2Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt pow2Instr stack

private def runPow2DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt .add (VM.push (intV 505)) stack

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

private def pow2GasProbeExp : Int := 8

private def pow2SetGasExact : Int :=
  computeExactGasBudget pow2Instr

private def pow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pow2Instr

private def pow2OkExpPool : Array Int :=
  #[0, 1, 2, 7, 8, 15, 31, 63, 127, 255]

private def pow2OverflowExpPool : Array Int :=
  #[256, 257, 511, 1023]

private def pow2RangeNegPool : Array Int :=
  #[-1, -2, -255, -1024]

private def pow2RangeHighPool : Array Int :=
  #[1024, 1025, 2048, 4096]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genPow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (case0, rng2) :=
    if shape = 0 then
      let (exp, r2) := pickFromIntPool pow2OkExpPool rng1
      (mkPow2Case s!"fuzz/ok/exp-{exp}" #[intV exp], r2)
    else if shape = 1 then
      let (exp, r2) := pickFromIntPool pow2OverflowExpPool rng1
      (mkPow2Case s!"fuzz/overflow/exp-{exp}" #[intV exp], r2)
    else if shape = 2 then
      let (exp, r2) := pickFromIntPool pow2RangeNegPool rng1
      (mkPow2Case s!"fuzz/range/negative-{exp}" #[intV exp], r2)
    else if shape = 3 then
      let (exp, r2) := pickFromIntPool pow2RangeHighPool rng1
      (mkPow2Case s!"fuzz/range/overmax-{exp}" #[intV exp], r2)
    else if shape = 4 then
      (mkPow2Case "fuzz/underflow/empty" #[], rng1)
    else if shape = 5 then
      let (pick, r2) := randNat rng1 0 1
      let top : Value := if pick = 0 then .null else .cell Cell.empty
      (mkPow2Case s!"fuzz/type/top-non-int-{pick}" #[top], r2)
    else if shape = 6 then
      let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[IntVal.nan]
      (mkPow2Case "fuzz/range/nan-via-program" stack (progPrefix.push pow2Instr), rng1)
    else if shape = 7 then
      let (exp, r2) := pickFromIntPool pow2OkExpPool rng1
      let (pick, r3) := randNat r2 0 1
      let below : Value := if pick = 0 then .null else intV 999
      (mkPow2Case s!"fuzz/ok/top-order-below-{pick}" #[below, intV exp], r3)
    else if shape = 8 then
      (mkPow2Case "fuzz/error-order/range-before-overflow" #[intV 1024], rng1)
    else if shape = 9 then
      (mkPow2Case "fuzz/error-order/overflow-after-range-pass" #[intV 256], rng1)
    else
      let (u, r2) := randNat rng1 0 255
      let exp : Int := Int.ofNat u
      (mkPow2Case s!"fuzz/ok/random-small-{u}" #[intV exp], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pow2Id
  unit := #[
    { name := "unit/direct/success-and-overflow-boundaries"
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
          expectOkStack s!"2^{exp}" (runPow2Direct #[intV exp]) #[intV expected]
        expectErr "exp-256-overflow" (runPow2Direct #[intV 256]) .intOv
        expectErr "exp-1023-overflow" (runPow2Direct #[intV 1023]) .intOv }
    ,
    { name := "unit/range-type-underflow-errors"
      run := do
        expectErr "range/negative" (runPow2Direct #[intV (-1)]) .rangeChk
        expectErr "range/overmax" (runPow2Direct #[intV 1024]) .rangeChk
        expectErr "range/nan" (runPow2Direct #[.int .nan]) .rangeChk
        expectErr "type/null" (runPow2Direct #[.null]) .typeChk
        expectErr "type/cell" (runPow2Direct #[.cell Cell.empty]) .typeChk
        expectErr "underflow/empty" (runPow2Direct #[]) .stkUnd }
    ,
    { name := "unit/error-order-and-top-order"
      run := do
        expectErr "range-before-overflow" (runPow2Direct #[intV 1024]) .rangeChk
        expectErr "overflow-after-range-pass" (runPow2Direct #[intV 256]) .intOv
        expectErr "type-before-range" (runPow2Direct #[.null]) .typeChk
        expectOkStack "top-order/below-preserved"
          (runPow2Direct #[.null, intV 8]) #[.null, intV (pow2 8)] }
    ,
    { name := "unit/opcode/decode-fixed-sequence"
      run := do
        let program : Array Instr := #[pow2Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/pow2" s0 pow2Instr 8
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-pow2-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runPow2DispatchFallback #[]) #[intV 505] }
  ]
  oracle := #[
    mkPow2Case "ok/exp-0" #[intV 0],
    mkPow2Case "ok/exp-1" #[intV 1],
    mkPow2Case "ok/exp-8" #[intV 8],
    mkPow2Case "ok/exp-31" #[intV 31],
    mkPow2Case "ok/exp-127" #[intV 127],
    mkPow2Case "ok/exp-255" #[intV 255],
    mkPow2Case "ok/top-order/below-preserved" #[.null, intV 8],
    mkPow2Case "overflow/exp-256" #[intV 256],
    mkPow2Case "overflow/exp-257" #[intV 257],
    mkPow2Case "overflow/exp-511" #[intV 511],
    mkPow2Case "overflow/exp-1023" #[intV 1023],
    mkPow2Case "range/negative-minus-one" #[intV (-1)],
    mkPow2Case "range/negative-minus-1024" #[intV (-1024)],
    mkPow2Case "range/overmax-1024" #[intV 1024],
    mkPow2Case "range/overmax-2048" #[intV 2048],
    mkPow2Case "range/nan-via-program" #[] #[.pushInt .nan, pow2Instr],
    mkPow2Case "underflow/empty-stack" #[],
    mkPow2Case "type/top-null" #[.null],
    mkPow2Case "type/top-cell" #[.cell Cell.empty],
    mkPow2Case "error-order/range-before-overflow" #[intV 1024],
    mkPow2Case "error-order/overflow-after-range-pass" #[intV 256],
    mkPow2Case "gas/exact-cost-succeeds" #[intV pow2GasProbeExp]
      #[.pushInt (.num pow2SetGasExact), .tonEnvOp .setGasLimit, pow2Instr],
    mkPow2Case "gas/exact-minus-one-out-of-gas" #[intV pow2GasProbeExp]
      #[.pushInt (.num pow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, pow2Instr]
  ]
  fuzz := #[
    { seed := 2026020806
      count := 600
      gen := genPow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.POW2
