import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QEQINT

/-
QEQINT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`.arithExt (.qeqInt imm)` quiet path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (24-bit `0xb7c0 + imm8` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`QEQINT` immediate encoding)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_cmp_int`, `register_int_cmp_ops`, mode `0x878`, `quiet=true`)

Branch counts used for this suite:
- Lean: 4 branch points / 6 terminal outcomes
  (opcode dispatch; `popInt` underflow/type/success split; finite-vs-NaN split;
   equality predicate for finite integers).
- C++: 4 branch points / 6 aligned terminal outcomes
  (`check_underflow`; `pop_int` type guard; valid-vs-NaN split via `is_valid`;
   EQ-mode result mapping to `-1` for equal and `0` otherwise).

Mapped terminal outcomes covered:
- success (`-1` when `x = imm`, `0` otherwise);
- `stkUnd`;
- `typeChk`;
- quiet NaN propagation (returns NaN, never `intOv`).

Key divergence risk areas:
- tinyint8 two's-complement immediate decode boundaries (`-128`, `-1`, `0`, `127`);
- 24-bit encoding/decoding of `QEQINT` (`0xb7c0 + imm8`) and range guard (`[-128, 127]`);
- quiet NaN path must preserve NaN instead of throwing `intOv`;
- equality truth-value mapping must stay TVM-boolean (`-1`) not `1`;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QEQINT imm`;
- oracle serialization safety: NaN/out-of-range inputs are injected via program, not `initStack`.
-/

private def qeqIntId : InstrId := { name := "QEQINT" }

private def qeqIntInstr (imm : Int) : Instr :=
  .arithExt (.qeqInt imm)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qeqIntId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQeqIntCase
    (name : String)
    (imm : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[qeqIntInstr imm] gasLimits fuel

private def mkInputCase
    (name : String)
    (imm : Int)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (programPrefix ++ #[qeqIntInstr imm])

private def runQeqIntDirect (imm : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (qeqIntInstr imm) stack

private def runQeqIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 515)) stack

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

private def qeqIntGasProbeImm : Int := 7

private def qeqIntSetGasExact : Int :=
  computeExactGasBudget (qeqIntInstr qeqIntGasProbeImm)

private def qeqIntSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (qeqIntInstr qeqIntGasProbeImm)

private def genQeqIntFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (imm, r3) := pickTinyInt8Boundary r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/boundary-x-boundary-imm" imm (.num x), r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (imm, r3) := pickTinyInt8Boundary r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/signed-x-boundary-imm" imm (.num x), r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (imm, r3) := pickTinyInt8Mixed r2
      (mkInputCase s!"fuzz/shape-{shape}/ok/signed-x-mixed-imm" imm (.num x), r3)
    else if shape = 3 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/equal" imm (.num imm), r2)
    else if shape = 4 then
      let (imm, r2) := pickTinyInt8Boundary rng1
      let (deltaIdx, r3) := randNat r2 0 4
      let delta : Int :=
        if deltaIdx = 0 then -2
        else if deltaIdx = 1 then -1
        else if deltaIdx = 2 then 0
        else if deltaIdx = 3 then 1
        else 2
      (mkInputCase s!"fuzz/shape-{shape}/ok/neighbor" imm (.num (imm + delta)), r3)
    else if shape = 5 then
      let (imm, r2) := pickTinyInt8Boundary rng1
      (mkQeqIntCase s!"fuzz/shape-{shape}/error/underflow-empty" imm #[], r2)
    else if shape = 6 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkQeqIntCase s!"fuzz/shape-{shape}/error/type-top-non-int" imm #[.null], r2)
    else if shape = 7 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkInputCase s!"fuzz/shape-{shape}/nan/via-program" imm .nan, r2)
    else if shape = 8 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      let (x, r3) := pickInt257OutOfRange r2
      (mkInputCase s!"fuzz/shape-{shape}/range/via-program" imm (.num x), r3)
    else if shape = 9 then
      let (imm, r2) := pickTinyInt8Boundary rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/max-int257" imm (.num maxInt257), r2)
    else if shape = 10 then
      let (imm, r2) := pickTinyInt8Boundary rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/min-int257" imm (.num minInt257), r2)
    else
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"fuzz/shape-{shape}/ok/zero-imm" 0 (.num x), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qeqIntId
  unit := #[
    { name := "unit/direct/finite-eq-results-and-immediate-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, -1),
            (17, 17, -1),
            (17, 25, 0),
            (-17, -17, -1),
            (-17, 5, 0),
            (-128, -128, -1),
            (127, 127, -1),
            (5, -128, 0),
            (5, 127, 0),
            (maxInt257, 127, 0),
            (minInt257, -128, 0)
          ]
        for c in checks do
          let x := c.1
          let imm := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}=={imm}" (runQeqIntDirect imm #[intV x]) #[intV expected] }
    ,
    { name := "unit/direct/quiet-nan-propagates"
      run := do
        expectOkStack "nan/top" (runQeqIntDirect 1 #[.int .nan]) #[.int .nan] }
    ,
    { name := "unit/immediate/encode-decode-boundary-sequence-24bit"
      run := do
        let program : Array Instr :=
          #[qeqIntInstr (-128), qeqIntInstr (-1), qeqIntInstr 0, qeqIntInstr 1, qeqIntInstr 127, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/failed/{e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/-128" s0 (qeqIntInstr (-128)) 24
        let s2 ← expectDecodeStep "decode/-1" s1 (qeqIntInstr (-1)) 24
        let s3 ← expectDecodeStep "decode/0" s2 (qeqIntInstr 0) 24
        let s4 ← expectDecodeStep "decode/1" s3 (qeqIntInstr 1) 24
        let s5 ← expectDecodeStep "decode/127" s4 (qeqIntInstr 127) 24
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add/non-empty/{s6.bitsRemaining}") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "qeqint/128" [qeqIntInstr 128] .rangeChk
        expectAssembleErr "qeqint/-129" [qeqIntInstr (-129)] .rangeChk }
    ,
    { name := "unit/error-order/underflow-before-type-and-stack-shape"
      run := do
        expectErr "error/underflow/empty" (runQeqIntDirect 0 #[]) .stkUnd
        expectErr "error/type/top-null" (runQeqIntDirect 0 #[.null]) .typeChk
        expectErr "error/type/top-cell" (runQeqIntDirect 0 #[.cell Cell.empty]) .typeChk
        expectOkStack "ok/top-only-consumed/lower-preserved"
          (runQeqIntDirect 8 #[.null, intV 8]) #[.null, intV (-1)] }
    ,
    { name := "unit/dispatch/non-qeqint-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQeqIntDispatchFallback #[]) #[intV 515] }
  ]
  oracle := #[
    mkInputCase "ok/equal/zero" 0 (.num 0),
    mkInputCase "ok/equal/positive" 17 (.num 17),
    mkInputCase "ok/equal/negative" (-17) (.num (-17)),
    mkInputCase "ok/not-equal/positive" 25 (.num 17),
    mkInputCase "ok/not-equal/negative" (-25) (.num (-17)),
    mkInputCase "immediate/min-neg128-match" (-128) (.num (-128)),
    mkInputCase "immediate/max-pos127-match" 127 (.num 127),
    mkInputCase "immediate/min-neg128-mismatch" (-128) (.num 127),
    mkInputCase "immediate/max-pos127-mismatch" 127 (.num (-128)),
    mkInputCase "boundary/max-int-never-eq-tiny" 127 (.num maxInt257),
    mkInputCase "boundary/min-int-never-eq-tiny" (-128) (.num minInt257),
    mkInputCase "boundary/near-max-mismatch" 126 (.num (maxInt257 - 1)),
    mkInputCase "boundary/near-min-mismatch" (-127) (.num (minInt257 + 1)),
    mkQeqIntCase "underflow/empty-stack" 0 #[],
    mkQeqIntCase "type/top-null" 0 #[.null],
    mkQeqIntCase "type/top-cell" 0 #[.cell Cell.empty],
    mkQeqIntCase "error-order/empty-underflow-before-type" 127 #[],
    mkQeqIntCase "error-order/non-empty-type-check" (-128) #[.null],
    mkInputCase "nan/via-program/pushnan-before-qeqint" 1 .nan,
    mkInputCase "range/via-program/high-before-qeqint" 7 (.num (maxInt257 + 1)),
    mkInputCase "range/via-program/low-before-qeqint" 7 (.num (minInt257 - 1)),
    mkCase "gas/exact/succeeds" #[intV qeqIntGasProbeImm]
      #[.pushInt (.num qeqIntSetGasExact), .tonEnvOp .setGasLimit, qeqIntInstr qeqIntGasProbeImm],
    mkCase "gas/exact-minus-one/out-of-gas" #[intV qeqIntGasProbeImm]
      #[.pushInt (.num qeqIntSetGasExactMinusOne), .tonEnvOp .setGasLimit, qeqIntInstr qeqIntGasProbeImm]
  ]
  fuzz := #[
    { seed := 2026020826
      count := 600
      gen := genQeqIntFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QEQINT
