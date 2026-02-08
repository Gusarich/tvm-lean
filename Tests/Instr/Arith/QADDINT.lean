import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADDINT

/-
QADDINT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`.arithExt (.qaddInt imm)` quiet path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (24-bit `0xb7a6 + imm8` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`QADDINT` immediate encode/range guard)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_add_tinyint8`, `register_add_mul_ops`, `QADDINT` opcode wiring)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::check_underflow`, `Stack::pop_int`, `Stack::push_int_quiet`)

Branch counts used for this suite:
- Lean: 6 branch points / 7 terminal outcomes
  (opcode dispatch; `arithExt` op dispatch; `popInt` underflow/type/success split;
   finite-vs-NaN split; quiet `pushIntQuiet` in-range-vs-overflow-to-NaN split).
- C++: 5 branch points / 7 aligned terminal outcomes
  (`QADDINT` opcode wiring; `check_underflow(1)`; `pop_int` type guard;
   finite-vs-NaN arithmetic input; `push_int_quiet` in-range vs overflow/NaN).

Mapped terminal outcomes covered:
- success with finite result,
- success with quiet NaN result from overflow,
- success with NaN propagation from NaN input,
- `stkUnd`,
- `typeChk`,
- fallback-to-`next` dispatch for non-`QADDINT` opcodes.

Key divergence risk areas:
- tinyint8 two's-complement immediate boundaries (`-128`, `-1`, `0`, `127`);
- 24-bit `QADDINT` decode/encode and assembler range guard (`[-128, 127]`);
- quiet overflow must push NaN (never throw `intOv`);
- unary pop order: top consumed, lower stack tail preserved on success;
- error ordering: underflow on empty stack before type-check path;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QADDINT imm`;
- NaN/out-of-range inputs in oracle/fuzz are injected via `PUSHINT` prelude,
  never serialized in `initStack`.
-/

private def qaddIntId : InstrId := { name := "QADDINT" }

private def qaddIntInstr (imm : Int) : Instr :=
  .arithExt (.qaddInt imm)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qaddIntId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQaddIntCase
    (name : String)
    (imm : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[qaddIntInstr imm] gasLimits fuel

private def mkInputCase
    (name : String)
    (imm : Int)
    (x : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (programPrefix ++ #[qaddIntInstr imm]) gasLimits fuel

private def runQaddIntDirect (imm : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (qaddIntInstr imm) stack

private def runQaddIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 411)) stack

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

private def qaddIntGasProbeImm : Int := 7

private def qaddIntSetGasExact : Int :=
  computeExactGasBudget (qaddIntInstr qaddIntGasProbeImm)

private def qaddIntSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (qaddIntInstr qaddIntGasProbeImm)

private def genQaddIntFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (imm, r3) := pickTinyInt8Boundary r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok/boundary-x-boundary-imm" imm (.num x), r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (imm, r3) := pickTinyInt8Boundary r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok/signed-x-boundary-imm" imm (.num x), r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (imm, r3) := pickTinyInt8Mixed r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok/signed-x-mixed-imm" imm (.num x), r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"/fuzz/shape-{shape}/ok/zero-imm-noop" 0 (.num x), r2)
    else if shape = 4 then
      let (hi, r2) := randBool rng1
      let imm : Int := if hi then 127 else 1
      (mkQaddIntCase s!"/fuzz/shape-{shape}/quiet-overflow/max-plus-pos-imm" imm #[intV maxInt257], r2)
    else if shape = 5 then
      let (lo, r2) := randBool rng1
      let imm : Int := if lo then -128 else -1
      (mkQaddIntCase s!"/fuzz/shape-{shape}/quiet-overflow/min-plus-neg-imm" imm #[intV minInt257], r2)
    else if shape = 6 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkQaddIntCase s!"/fuzz/shape-{shape}/error/underflow-empty" imm #[], r2)
    else if shape = 7 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkQaddIntCase s!"/fuzz/shape-{shape}/error/type-top-null" imm #[.null], r2)
    else if shape = 8 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkQaddIntCase s!"/fuzz/shape-{shape}/error/type-top-cell" imm #[.cell Cell.empty], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (imm, r3) := pickTinyInt8Mixed r2
      (mkInputCase s!"/fuzz/shape-{shape}/pop-order/top-consumed-tail-kept" imm (.num x) #[intV 9], r3)
    else if shape = 10 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkQaddIntCase s!"/fuzz/shape-{shape}/error-order/type-before-tail" imm #[intV 9, .null], r2)
    else if shape = 11 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkInputCase s!"/fuzz/shape-{shape}/nan/via-program" imm .nan, r2)
    else if shape = 12 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkInputCase s!"/fuzz/shape-{shape}/range/via-program/high" imm (.num (maxInt257 + 1)), r2)
    else
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkInputCase s!"/fuzz/shape-{shape}/range/via-program/low" imm (.num (minInt257 - 1)), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qaddIntId
  unit := #[
    { name := "/unit/direct/finite-sign-zero-and-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (17, 25, 42),
            (17, -5, 12),
            (-17, 5, -12),
            (-17, -5, -22),
            (123, 0, 123),
            (5, -128, -123),
            (5, 127, 132),
            (maxInt257, -1, maxInt257 - 1),
            (minInt257, 1, minInt257 + 1),
            (maxInt257 - 127, 127, maxInt257),
            (minInt257 + 128, -128, minInt257)
          ]
        for c in checks do
          let x := c.1
          let imm := c.2.1
          let expected := c.2.2
          expectOkStack s!"/direct/{x}+{imm}" (runQaddIntDirect imm #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/quiet-overflow-and-nan-propagation"
      run := do
        expectOkStack "/quiet-overflow/max-plus-one" (runQaddIntDirect 1 #[intV maxInt257]) #[.int .nan]
        expectOkStack "/quiet-overflow/max-plus-127" (runQaddIntDirect 127 #[intV maxInt257]) #[.int .nan]
        expectOkStack "/quiet-overflow/min-minus-one" (runQaddIntDirect (-1) #[intV minInt257]) #[.int .nan]
        expectOkStack "/quiet-overflow/min-minus-128" (runQaddIntDirect (-128) #[intV minInt257]) #[.int .nan]
        expectOkStack "/quiet-nan-input" (runQaddIntDirect 1 #[.int .nan]) #[.int .nan] }
    ,
    { name := "/unit/immediate/encode-decode-boundary-sequence-24bit"
      run := do
        let program : Array Instr :=
          #[qaddIntInstr (-128), qaddIntInstr (-1), qaddIntInstr 0, qaddIntInstr 1, qaddIntInstr 127, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/assemble/failed/{e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/decode/-128" s0 (qaddIntInstr (-128)) 24
        let s2 ← expectDecodeStep "/decode/-1" s1 (qaddIntInstr (-1)) 24
        let s3 ← expectDecodeStep "/decode/0" s2 (qaddIntInstr 0) 24
        let s4 ← expectDecodeStep "/decode/1" s3 (qaddIntInstr 1) 24
        let s5 ← expectDecodeStep "/decode/127" s4 (qaddIntInstr 127) 24
        let s6 ← expectDecodeStep "/decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/decode/non-empty-tail/{s6.bitsRemaining}") }
    ,
    { name := "/unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "/qaddint/128" [qaddIntInstr 128] .rangeChk
        expectAssembleErr "/qaddint/-129" [qaddIntInstr (-129)] .rangeChk }
    ,
    { name := "/unit/pop-order-and-error-order"
      run := do
        expectOkStack "/pop-order/top-consumed-tail-preserved"
          (runQaddIntDirect 5 #[intV 99, intV 7]) #[intV 99, intV 12]
        expectErr "/error-order/underflow-empty" (runQaddIntDirect 0 #[]) .stkUnd
        expectErr "/error-order/type-top-null" (runQaddIntDirect 0 #[.null]) .typeChk
        expectErr "/error-order/type-top-cell" (runQaddIntDirect 0 #[.cell Cell.empty]) .typeChk
        expectErr "/error-order/type-before-tail" (runQaddIntDirect 3 #[intV 11, .null]) .typeChk }
    ,
    { name := "/unit/dispatch/non-qaddint-falls-through"
      run := do
        expectOkStack "/dispatch/fallback" (runQaddIntDispatchFallback #[]) #[intV 411] }
  ]
  oracle := #[
    mkInputCase "/ok/zero/x-zero-imm-zero" 0 (.num 0),
    mkInputCase "/ok/sign/pos-plus-pos-imm" 25 (.num 17),
    mkInputCase "/ok/sign/pos-plus-neg-imm" (-5) (.num 17),
    mkInputCase "/ok/sign/neg-plus-pos-imm" 5 (.num (-17)),
    mkInputCase "/ok/sign/neg-plus-neg-imm" (-5) (.num (-17)),
    mkInputCase "/ok/zero/imm-zero-noop" 0 (.num 123),
    mkInputCase "/immediate/min-neg128" (-128) (.num 5),
    mkInputCase "/immediate/max-pos127" 127 (.num 5),
    mkCase "/immediate/decode-sequence-min-max" #[intV 1]
      #[qaddIntInstr (-128), qaddIntInstr 127],
    mkInputCase "/boundary/max-plus-zero-imm" 0 (.num maxInt257),
    mkInputCase "/boundary/min-plus-zero-imm" 0 (.num minInt257),
    mkInputCase "/boundary/max-plus-neg-one" (-1) (.num maxInt257),
    mkInputCase "/boundary/min-plus-one" 1 (.num minInt257),
    mkInputCase "/boundary/near-max-plus-one-no-overflow" 1 (.num (maxInt257 - 1)),
    mkInputCase "/boundary/near-min-minus-one-no-overflow" (-1) (.num (minInt257 + 1)),
    mkInputCase "/quiet-overflow/max-plus-one-to-nan" 1 (.num maxInt257),
    mkInputCase "/quiet-overflow/max-plus-127-to-nan" 127 (.num maxInt257),
    mkInputCase "/quiet-overflow/min-minus-one-to-nan" (-1) (.num minInt257),
    mkInputCase "/quiet-overflow/min-minus-128-to-nan" (-128) (.num minInt257),
    mkInputCase "/pop-order/top-consumed-tail-preserved" 5 (.num 7) #[intV 99],
    mkQaddIntCase "/underflow/empty-stack" 0 #[],
    mkQaddIntCase "/type/top-null" 0 #[.null],
    mkQaddIntCase "/type/top-cell" 0 #[.cell Cell.empty],
    mkQaddIntCase "/error-order/empty-underflow-before-type" 127 #[],
    mkQaddIntCase "/error-order/type-before-tail-null" (-128) #[intV 11, .null],
    mkQaddIntCase "/error-order/type-before-tail-cell" 3 #[intV 11, .cell Cell.empty],
    mkInputCase "/nan/via-program/pushnan-before-qaddint" 1 .nan,
    mkInputCase "/range/via-program/high-before-qaddint" 7 (.num (maxInt257 + 1)),
    mkInputCase "/range/via-program/low-before-qaddint" 7 (.num (minInt257 - 1)),
    mkCase "/gas/exact/succeeds" #[intV 7]
      #[.pushInt (.num qaddIntSetGasExact), .tonEnvOp .setGasLimit, qaddIntInstr qaddIntGasProbeImm],
    mkCase "/gas/exact-minus-one/out-of-gas" #[intV 7]
      #[.pushInt (.num qaddIntSetGasExactMinusOne), .tonEnvOp .setGasLimit, qaddIntInstr qaddIntGasProbeImm]
  ]
  fuzz := #[
    { seed := 2026020831
      count := 600
      gen := genQaddIntFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADDINT
