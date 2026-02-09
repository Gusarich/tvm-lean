import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHNEGPOW2

/-
PUSHNEGPOW2 branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Stack/PushNegPow2.lean`
    (`execInstrStackPushNegPow2`, pushes `-2^exp` via `pushIntQuiet`)
  - `TvmLean/Semantics/Exec/Stack.lean`
    (dispatch chain includes `execInstrStackPushNegPow2`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.pushNegPow2 exp` encoding, `exp ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0x85 <arg8>` decode, `exp = arg + 1`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_push_negpow2`, `register_int_const_ops` for opcode `0x85`)

Branch/terminal counts used for this suite:
- Lean execution path: 3 branch sites / 4 terminal outcomes
  (handler dispatch vs fallback; fixed-constant push success;
   prelude error before op via injected `PUSHINT`; out-of-gas gate).
- C++ execution path: 3 aligned branch sites / 4 aligned outcomes
  (opcode wiring; constant push path; prelude failure before target op; gas exhaustion).

Key risk areas covered:
- exponent boundaries (`exp=1`, `exp=255`, `exp=256`) and signed-257 minimum (`-2^256`);
- stack preservation (instruction pushes and never consumes existing stack);
- encoding/decoding range and fixed-width behavior (`0x85`, 16-bit total);
- deterministic gas cliff (`PUSHINT n; SETGASLIMIT; PUSHNEGPOW2`);
- oracle/fuzz serialization hygiene: NaN/out-of-range integer setup is injected
  through program prelude helper (`oracleIntInputsToStackOrProgram`) only.
-/

private def pushNegPow2Id : InstrId := { name := "PUSHNEGPOW2" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkPushNegPow2Instr (exp : Nat) : Instr :=
  .pushNegPow2 exp

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := pushNegPow2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkExpCase
    (name : String)
    (exp : Nat)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkPushNegPow2Instr exp] gasLimits fuel

private def mkPreludeCase
    (name : String)
    (preludeVals : Array IntVal)
    (exp : Nat)
    (stackPrefix : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkPushNegPow2Instr exp
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram preludeVals
  mkCase name (stackPrefix ++ stackOrEmpty) (programPrefix.push instr) gasLimits fuel

private def runPushNegPow2Direct
    (exp : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushNegPow2 (mkPushNegPow2Instr exp) stack

private def runPushNegPow2DispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushNegPow2 .add (VM.push (intV 4202)) stack

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

private def pushNegPow2GasProbeExp : Nat := 256

private def pushNegPow2GasProbeInstr : Instr :=
  mkPushNegPow2Instr pushNegPow2GasProbeExp

private def pushNegPow2SetGasExact : Int :=
  computeExactGasBudget pushNegPow2GasProbeInstr

private def pushNegPow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pushNegPow2GasProbeInstr

private def expBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 31, 63, 127, 128, 255, 256]

private def pickBoundaryExp (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (expBoundaryPool.size - 1)
  (expBoundaryPool[idx]!, rng')

private def genPushNegPow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (baseCase, rng2) :=
    if shape = 0 then
      let (exp, r2) := pickBoundaryExp rng1
      (mkExpCase s!"/fuzz/shape-{shape}/ok/boundary-exp-{exp}" exp, r2)
    else if shape = 1 then
      let (exp, r2) := randNat rng1 1 256
      (mkExpCase s!"/fuzz/shape-{shape}/ok/random-exp-{exp}" exp, r2)
    else if shape = 2 then
      let (exp, r2) := pickBoundaryExp rng1
      (mkExpCase s!"/fuzz/shape-{shape}/ok/stack-preserve-null" exp #[.null], r2)
    else if shape = 3 then
      let (exp, r2) := pickBoundaryExp rng1
      (mkExpCase s!"/fuzz/shape-{shape}/ok/stack-preserve-cell-and-int"
        exp #[.cell Cell.empty, intV 17], r2)
    else if shape = 4 then
      let (exp, r2) := pickBoundaryExp rng1
      (mkPreludeCase s!"/fuzz/shape-{shape}/ok/prelude-nan-via-program" #[.nan] exp, r2)
    else if shape = 5 then
      let (exp, r2) := pickBoundaryExp rng1
      (mkPreludeCase s!"/fuzz/shape-{shape}/ok/prelude-nan-with-tail-via-program"
        #[.num 77, .nan] exp, r2)
    else if shape = 6 then
      let (exp, r2) := pickBoundaryExp rng1
      let (x, r3) := pickSigned257ish r2
      (mkPreludeCase s!"/fuzz/shape-{shape}/ok/prelude-serializable-int"
        #[.num x] exp #[.null], r3)
    else if shape = 7 then
      let (exp, r2) := pickBoundaryExp rng1
      let (delta, r3) := randNat r2 1 64
      let n := maxInt257 + Int.ofNat delta
      (mkPreludeCase s!"/fuzz/shape-{shape}/error-order/prelude-overflow-high-before-op"
        #[.num n] exp, r3)
    else if shape = 8 then
      let (exp, r2) := pickBoundaryExp rng1
      let (delta, r3) := randNat r2 1 64
      let n := minInt257 - Int.ofNat delta
      (mkPreludeCase s!"/fuzz/shape-{shape}/error-order/prelude-overflow-low-before-op"
        #[.num n] exp, r3)
    else if shape = 9 then
      let (exp, r2) := pickBoundaryExp rng1
      (mkExpCase s!"/fuzz/shape-{shape}/ok/stack-preserve-two-values"
        exp #[intV (-1), .null], r2)
    else if shape = 10 then
      (mkExpCase s!"/fuzz/shape-{shape}/ok/max-exp-256" 256 #[intV 5], rng1)
    else
      (mkExpCase s!"/fuzz/shape-{shape}/ok/min-exp-1" 1 #[.cell Cell.empty], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pushNegPow2Id
  unit := #[
    { name := "/unit/direct/ok-boundaries-and-stack-preservation"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, -2),
            (2, -4),
            (8, -(pow2 8)),
            (31, -(pow2 31)),
            (255, -(pow2 255)),
            (256, minInt257)
          ]
        for c in checks do
          let exp := c.1
          let expected := c.2
          expectOkStack s!"/unit/direct/exp-{exp}"
            (runPushNegPow2Direct exp #[]) #[intV expected]
        expectOkStack "/unit/top-order/below-null-preserved"
          (runPushNegPow2Direct 8 #[.null]) #[.null, intV (-(pow2 8))]
        expectOkStack "/unit/top-order/below-cell-and-int-preserved"
          (runPushNegPow2Direct 256 #[.cell Cell.empty, intV 5])
          #[.cell Cell.empty, intV 5, intV minInt257] }
    ,
    { name := "/unit/opcode/decode-fixed-sequence"
      run := do
        let instr1 := mkPushNegPow2Instr 1
        let instr256 := mkPushNegPow2Instr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/opcode/decode: assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/pushnegpow2-exp-1" s0 instr1 16
        let s2 ← expectDecodeStep "/unit/decode/pushnegpow2-exp-256" s1 instr256 16
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-invalid-immediate-range"
      run := do
        expectAssembleErr "/unit/encode/range/exp-0" [mkPushNegPow2Instr 0] .rangeChk
        expectAssembleErr "/unit/encode/range/exp-257" [mkPushNegPow2Instr 257] .rangeChk }
    ,
    { name := "/unit/dispatch/non-pushnegpow2-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runPushNegPow2DispatchFallback #[.null]) #[.null, intV 4202] }
  ]
  oracle := #[
    mkExpCase "/ok/exp-1" 1,
    mkExpCase "/ok/exp-8" 8,
    mkExpCase "/ok/exp-255" 255,
    mkExpCase "/ok/boundary/exp-256-min-int257" 256,
    mkExpCase "/ok/stack-preserve/below-null" 8 #[.null],
    mkExpCase "/ok/stack-preserve/below-cell-and-int" 256 #[.cell Cell.empty, intV 7],
    mkPreludeCase "/ok/prelude/nan-via-program-before-op" #[.nan] 8,
    mkPreludeCase "/ok/prelude/nan-with-tail-via-program" #[.num 77, .nan] 1,
    mkPreludeCase "/ok/prelude/serializable-int-stays-in-stack" #[.num (-11)] 31,
    mkPreludeCase "/error-order/prelude-pushint-overflow-high-before-op"
      #[.num (maxInt257 + 1)] 8,
    mkPreludeCase "/error-order/prelude-pushint-overflow-low-before-op"
      #[.num (minInt257 - 1)] 8,
    mkCase "/gas/exact-cost-succeeds" #[]
      #[.pushInt (.num pushNegPow2SetGasExact), .tonEnvOp .setGasLimit, pushNegPow2GasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[]
      #[.pushInt (.num pushNegPow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, pushNegPow2GasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020892
      count := 620
      gen := genPushNegPow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHNEGPOW2
