import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHINT_8

/-
PUSHINT_8 branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeCp0`, canonical tinyint4/tinyint8/tinyint16 selection)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0x80` tinyint8 two's-complement decode path)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean`
    (`execInstrStackPushInt`, pushInt dispatch and fallback behavior)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.pushIntQuiet`, signed-257 non-quiet guard for generic PUSHINT execution)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_push_tinyint8`, opcode wiring in `register_int_const_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::push_smallint`, generic `push_int_quiet` overflow behavior)

Branch map and terminal outcomes used by this suite:
- Tinyint8 opcode decode path:
  `0x80` dispatch + 8-bit signed two's-complement decode (`-128..127`) with 16-bit length.
- Execution path specialization:
  `.pushInt (.num n)` pushes `n` (no pops); non-`pushInt` opcodes fall through to `next`.
- Generic PUSHINT guard path exercised via prelude:
  out-of-range `PUSHINT` prelude values fail with `intOv` before the target tinyint8 op.

Mapped risk areas:
- signed decode boundaries and canonical frontier with PUSHINT_4 (`-6/11` vs `-5/10`);
- stack-growth-only behavior (existing stack elements preserved);
- slash-named oracle/fuzz cases with program-prelude injection for non-serializable values
  (`NaN` / signed-257 out-of-range), never direct oracle stack tokens;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one) for a tinyint8 payload.
-/

private def pushInt8Id : InstrId := { name := "PUSHINT_8" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkPushInt8Instr (imm : Int) : Instr :=
  .pushInt (.num imm)

private def pushInt8DefaultImm : Int := 11

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mkPushInt8Instr pushInt8DefaultImm])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := pushInt8Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPushInt8Case
    (name : String)
    (imm : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkPushInt8Instr imm] gasLimits fuel

/--
For oracle/fuzz cases, NaN and signed-257-out-of-range values must be injected
through program prelude `PUSHINT`, not `initStack`, because stack tokens are
intentionally serialization-safe.
-/
private def mkPushInt8CaseFromBelowVals
    (name : String)
    (imm : Int)
    (belowVals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram belowVals
  mkCase name stack (progPrefix.push (mkPushInt8Instr imm)) gasLimits fuel

private def runPushIntDirect
    (arg : IntVal)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushInt (.pushInt arg) stack

private def runPushInt8Direct
    (imm : Int)
    (stack : Array Value) : Except Excno (Array Value) :=
  runPushIntDirect (.num imm) stack

private def runPushIntDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushInt .add (VM.push (intV 9081)) stack

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

private def pushInt8GasProbeImm : Int := 11

private def pushInt8GasProbeInstr : Instr :=
  mkPushInt8Instr pushInt8GasProbeImm

private def pushInt8SetGasExact : Int :=
  computeExactGasBudget pushInt8GasProbeInstr

private def pushInt8SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pushInt8GasProbeInstr

private def pushInt8BoundaryPool : Array Int :=
  #[-128, -127, -120, -64, -11, -6, 11, 12, 63, 64, 120, 126, 127]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickPushInt8Boundary (rng : StdGen) : Int × StdGen :=
  pickFromIntPool pushInt8BoundaryPool rng

private def pickPushInt8Uniform (rng0 : StdGen) : Int × StdGen :=
  let (pickNeg, rng1) := randBool rng0
  if pickNeg then
    let (u, rng2) := randNat rng1 0 122
    (Int.ofNat u - 128, rng2)
  else
    let (u, rng2) := randNat rng1 0 116
    (Int.ofNat u + 11, rng2)

private def pickPushInt8Mixed (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then pickPushInt8Boundary rng1 else pickPushInt8Uniform rng1

private def pickNonInt (rng0 : StdGen) : Value × StdGen :=
  let (pickCell, rng1) := randBool rng0
  (if pickCell then .cell Cell.empty else .null, rng1)

private def genPushInt8FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng2) :=
    if shape = 0 then
      let (imm, r2) := pickPushInt8Boundary rng1
      (mkPushInt8Case s!"/fuzz/shape-{shape}/ok/empty-boundary" imm #[], r2)
    else if shape = 1 then
      let (imm, r2) := pickPushInt8Uniform rng1
      (mkPushInt8Case s!"/fuzz/shape-{shape}/ok/empty-uniform" imm #[], r2)
    else if shape = 2 then
      let (imm, r2) := pickPushInt8Boundary rng1
      let (below, r3) := pickInt257Boundary r2
      (mkPushInt8Case s!"/fuzz/shape-{shape}/ok/preserve-below-int"
        imm #[intV below], r3)
    else if shape = 3 then
      let (imm, r2) := pickPushInt8Uniform rng1
      let (below, r3) := pickNonInt r2
      (mkPushInt8Case s!"/fuzz/shape-{shape}/ok/preserve-below-nonint"
        imm #[below], r3)
    else if shape = 4 then
      let (imm, r2) := pickPushInt8Mixed rng1
      let (x, r3) := pickInt257Boundary r2
      let (y, r4) := pickInt257Boundary r3
      (mkPushInt8Case s!"/fuzz/shape-{shape}/ok/preserve-two-below-values"
        imm #[intV x, intV y], r4)
    else if shape = 5 then
      let (imm, r2) := pickFromIntPool #[-128, -6, 11, 127] rng1
      (mkPushInt8Case s!"/fuzz/shape-{shape}/ok/canonical-frontier-values"
        imm #[], r2)
    else if shape = 6 then
      let (imm, r2) := pickPushInt8Mixed rng1
      (mkPushInt8CaseFromBelowVals
        s!"/fuzz/shape-{shape}/ok/prelude-nan-below-via-program"
        imm #[.nan], r2)
    else if shape = 7 then
      let (imm, r2) := pickPushInt8Mixed rng1
      (mkPushInt8CaseFromBelowVals
        s!"/fuzz/shape-{shape}/error-order/prelude-overflow-high-before-target"
        imm #[.num (maxInt257 + 1)], r2)
    else if shape = 8 then
      let (imm, r2) := pickPushInt8Mixed rng1
      (mkPushInt8CaseFromBelowVals
        s!"/fuzz/shape-{shape}/error-order/prelude-overflow-low-before-target"
        imm #[.num (minInt257 - 1)], r2)
    else if shape = 9 then
      let (imm, r2) := pickPushInt8Mixed rng1
      let (x, r3) := pickInt257Boundary r2
      (mkPushInt8CaseFromBelowVals
        s!"/fuzz/shape-{shape}/ok/prelude-mixed-finite-and-nan"
        imm #[.num x, .nan], r3)
    else if shape = 10 then
      let (imm, r2) := pickPushInt8Mixed rng1
      (mkPushInt8CaseFromBelowVals
        s!"/fuzz/shape-{shape}/error-order/prelude-overflow-first-in-multi-prefix"
        imm #[.num (maxInt257 + 1), .num 7], r2)
    else
      let (imm, r2) := pickPushInt8Boundary rng1
      let (below, r3) := pickNonInt r2
      (mkPushInt8Case s!"/fuzz/shape-{shape}/ok/preserve-nonint-and-immediate-boundary"
        imm #[intV maxInt257, below], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pushInt8Id
  unit := #[
    { name := "/unit/direct/pushes-imm8-boundaries-and-preserves-below"
      run := do
        let checks : Array (Int × Array Value × Array Value) :=
          #[
            (-128, #[], #[intV (-128)]),
            (-6, #[.null], #[.null, intV (-6)]),
            (11, #[.cell Cell.empty], #[.cell Cell.empty, intV 11]),
            (127, #[intV 5, .null], #[intV 5, .null, intV 127]),
            (-127, #[intV maxInt257], #[intV maxInt257, intV (-127)])
          ]
        for c in checks do
          let imm := c.1
          let stack := c.2.1
          let expected := c.2.2
          expectOkStack s!"/unit/direct/imm={imm}"
            (runPushInt8Direct imm stack) expected }
    ,
    { name := "/unit/opcode/decode-pushint8-sequence"
      run := do
        let i1 := mkPushInt8Instr (-128)
        let i2 := mkPushInt8Instr (-6)
        let i3 := mkPushInt8Instr 11
        let i4 := mkPushInt8Instr 127
        let program : Array Instr := #[i1, i2, i3, i4, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"/unit/opcode/decode: assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode/-128" s0 i1 16
        let s2 ← expectDecodeStep "/unit/opcode/decode/-6" s1 i2 16
        let s3 ← expectDecodeStep "/unit/opcode/decode/11" s2 i3 16
        let s4 ← expectDecodeStep "/unit/opcode/decode/127" s3 i4 16
        let s5 ← expectDecodeStep "/unit/opcode/decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"/unit/opcode/decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/canonical-frontier-between-pushint4-8-16"
      run := do
        let n5 : Instr := .pushInt (.num (-5))
        let n6 : Instr := .pushInt (.num (-6))
        let p10 : Instr := .pushInt (.num 10)
        let p11 : Instr := .pushInt (.num 11)
        let n129 : Instr := .pushInt (.num (-129))
        let p128 : Instr := .pushInt (.num 128)
        let program : Array Instr := #[n5, n6, p10, p11, n129, p128]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"/unit/opcode/frontier: assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/frontier/-5-tiny4" s0 n5 8
        let s2 ← expectDecodeStep "/unit/opcode/frontier/-6-tiny8" s1 n6 16
        let s3 ← expectDecodeStep "/unit/opcode/frontier/10-tiny4" s2 p10 8
        let s4 ← expectDecodeStep "/unit/opcode/frontier/11-tiny8" s3 p11 16
        let s5 ← expectDecodeStep "/unit/opcode/frontier/-129-tiny16" s4 n129 24
        let s6 ← expectDecodeStep "/unit/opcode/frontier/128-tiny16" s5 p128 24
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"/unit/opcode/frontier/end: expected exhausted slice, got {s6.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/direct/generic-pushint-nan-and-range-branches"
      run := do
        expectOkStack "/unit/direct/pushnan-branch" (runPushIntDirect .nan #[]) #[.int .nan]
        expectErr "/unit/direct/range-overflow-high-intov"
          (runPushIntDirect (.num (maxInt257 + 1)) #[]) .intOv
        expectErr "/unit/direct/range-overflow-low-intov"
          (runPushIntDirect (.num (minInt257 - 1)) #[]) .intOv }
    ,
    { name := "/unit/dispatch/non-pushint-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runPushIntDispatchFallback #[]) #[intV 9081] }
  ]
  oracle := #[
    mkPushInt8Case "/ok/min-neg128-empty" (-128) #[],
    mkPushInt8Case "/ok/max-pos127-empty" 127 #[],
    mkPushInt8Case "/ok/near-tiny4-lower-neg6" (-6) #[],
    mkPushInt8Case "/ok/near-tiny4-upper-pos11" 11 #[],
    mkPushInt8Case "/ok/stack-growth-preserves-below-null" 11 #[.null],
    mkPushInt8Case "/ok/stack-growth-preserves-below-cell" (-6) #[.cell Cell.empty],
    mkPushInt8Case "/ok/stack-growth-preserves-below-int" 127 #[intV minInt257],
    mkPushInt8Case "/ok/stack-growth-preserves-two-below-values" (-128)
      #[intV 5, .null],
    mkPushInt8CaseFromBelowVals "/ok/prelude-nan-below-via-program" 11 #[.nan],
    mkPushInt8CaseFromBelowVals "/ok/prelude-mixed-finite-and-nan-via-program" (-6)
      #[.num 7, .nan],
    mkPushInt8CaseFromBelowVals "/error-order/prelude-overflow-high-before-target" 11
      #[.num (maxInt257 + 1)],
    mkPushInt8CaseFromBelowVals "/error-order/prelude-overflow-low-before-target" (-6)
      #[.num (minInt257 - 1)],
    mkCase "/gas/exact-cost-succeeds" #[]
      #[.pushInt (.num pushInt8SetGasExact), .tonEnvOp .setGasLimit, pushInt8GasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[]
      #[.pushInt (.num pushInt8SetGasExactMinusOne), .tonEnvOp .setGasLimit, pushInt8GasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020808
      count := 600
      gen := genPushInt8FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHINT_8
