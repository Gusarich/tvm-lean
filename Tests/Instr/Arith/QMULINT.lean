import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULINT

/-
QMULINT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`.arithExt (.qmulInt imm)` quiet path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popInt`, `VM.pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (24-bit `0xb7a7 + imm8` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`QMULINT` immediate encoding/range guard)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mul_tinyint8`, `register_add_mul_ops` for `MULINT` / `QMULINT`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.hpp` (`check_underflow`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean: 5 branch points / 6 terminal outcomes
  (opcode dispatch; `popInt` underflow/type/success; `.nan` vs `.num`;
   quiet `pushIntQuiet` NaN path; signed-257 fit check on finite product).
- C++: 4 branch points / 6 aligned terminal outcomes
  (`check_underflow`; `pop_int` type/success; multiply NaN-vs-finite;
   quiet `push_int_quiet` finite fit vs NaN funnel on overflow).

Key risk areas covered:
- tinyint8 two's-complement immediate boundaries (`-128`, `-1`, `0`, `127`);
- quiet NaN semantics (`QMULINT` must never throw `intOv`);
- signed-257 overflow/underflow at `±2^256` (quietly returns NaN);
- single-pop error ordering (top-of-stack type error masks lower entries);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QMULINT k`;
- oracle-serialization hygiene: NaN/out-of-range inputs injected via program prelude.
-/

private def qmulIntId : InstrId := { name := "QMULINT" }

private def qmulIntInstr (imm : Int) : Instr :=
  .arithExt (.qmulInt imm)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulIntId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkQmulIntCase
    (name : String)
    (imm : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[qmulIntInstr imm] gasLimits fuel

private def mkInputCase
    (name : String)
    (imm : Int)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (programPrefix ++ #[qmulIntInstr imm])

private def runQmulIntDirect (imm : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (qmulIntInstr imm) stack

private def runQmulIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 672)) stack

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

private def qmulIntGasProbeImm : Int := 7

private def qmulIntSetGasExact : Int :=
  computeExactGasBudget (qmulIntInstr qmulIntGasProbeImm)

private def qmulIntSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (qmulIntInstr qmulIntGasProbeImm)

private def pickNonIntLike (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def overflowPairPool : Array (Int × Int) :=
  #[
    (maxInt257, 2),
    (maxInt257, -2),
    (maxInt257, 127),
    (minInt257, -1),
    (minInt257, 2),
    (minInt257, -128)
  ]

private def pickOverflowPair (rng : StdGen) : (Int × Int) × StdGen :=
  let (idx, rng') := randNat rng 0 (overflowPairPool.size - 1)
  (overflowPairPool[idx]!, rng')

private def genQmulIntFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (imm, r3) := pickTinyInt8Boundary r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok-or-quiet/boundary-x-boundary-imm" imm (.num x), r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (imm, r3) := pickTinyInt8Boundary r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok-or-quiet/signed-x-boundary-imm" imm (.num x), r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (imm, r3) := pickTinyInt8Mixed r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok-or-quiet/signed-x-mixed-imm" imm (.num x), r3)
    else if shape = 3 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkInputCase s!"/fuzz/shape-{shape}/ok/zero-x" imm (.num 0), r2)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      (mkInputCase s!"/fuzz/shape-{shape}/ok/zero-imm" 0 (.num x), r2)
    else if shape = 5 then
      let ((x, imm), r2) := pickOverflowPair rng1
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/overflow" imm (.num x), r2)
    else if shape = 6 then
      let (imm, r2) := pickTinyInt8Boundary rng1
      (mkQmulIntCase s!"/fuzz/shape-{shape}/error/underflow-empty" imm #[], r2)
    else if shape = 7 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      let (bad, r3) := pickNonIntLike r2
      (mkQmulIntCase s!"/fuzz/shape-{shape}/error/type-top-non-int" imm #[bad], r3)
    else if shape = 8 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      let (x, r3) := pickSigned257ish r2
      let (bad, r4) := pickNonIntLike r3
      (mkQmulIntCase s!"/fuzz/shape-{shape}/error-order/top-non-int-before-lower-int"
        imm #[intV x, bad], r4)
    else if shape = 9 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      let (x, r3) := pickSigned257ish r2
      let (bad, r4) := pickNonIntLike r3
      (mkQmulIntCase s!"/fuzz/shape-{shape}/pop-order/top-int-over-lower-non-int"
        imm #[bad, intV x], r4)
    else if shape = 10 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      (mkInputCase s!"/fuzz/shape-{shape}/quiet/nan-via-program" imm .nan, r2)
    else if shape = 11 then
      let (imm, r2) := pickTinyInt8Mixed rng1
      let (xOut, r3) := pickInt257OutOfRange r2
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-range-before-op" imm (.num xOut), r3)
    else if shape = 12 then
      let (imm, r2) := pickTinyInt8Boundary rng1
      let (pickMax, r3) := randBool r2
      let x := if pickMax then maxInt257 else minInt257
      (mkInputCase s!"/fuzz/shape-{shape}/ok-or-quiet/extreme-x" imm (.num x), r3)
    else
      let (x, r2) := pickInt257Boundary rng1
      let (imm, r3) := pickTinyInt8Boundary r2
      (mkInputCase s!"/fuzz/shape-{shape}/ok-or-quiet/boundary-regression" imm (.num x), r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulIntId
  unit := #[
    { name := "/unit/direct/finite-sign-zero-and-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 21),
            (7, -3, -21),
            (-7, 3, -21),
            (-7, -3, 21),
            (maxInt257, 0, 0),
            (maxInt257, 1, maxInt257),
            (minInt257, 1, minInt257),
            (maxInt257, -1, -maxInt257),
            (minInt257 + 1, -1, maxInt257),
            (1, 127, 127),
            (1, -128, -128),
            (-1, -128, 128)
          ]
        for c in checks do
          let x := c.1
          let imm := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}*{imm}" (runQmulIntDirect imm #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/quiet-nan-and-overflow-yield-nan"
      run := do
        expectOkStack "nan/input" (runQmulIntDirect 5 #[.int .nan]) #[.int .nan]
        let overflowChecks : Array (Int × Int) :=
          #[
            (maxInt257, 2),
            (maxInt257, 127),
            (minInt257, -1),
            (minInt257, 2)
          ]
        for c in overflowChecks do
          let x := c.1
          let imm := c.2
          expectOkStack s!"overflow/{x}*{imm}" (runQmulIntDirect imm #[intV x]) #[.int .nan] }
    ,
    { name := "/unit/immediate/decode-boundary-sequence-24bit"
      run := do
        let program : Array Instr :=
          #[qmulIntInstr (-128), qmulIntInstr (-1), qmulIntInstr 0, qmulIntInstr 1, qmulIntInstr 127, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/failed/{e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/-128" s0 (qmulIntInstr (-128)) 24
        let s2 ← expectDecodeStep "decode/-1" s1 (qmulIntInstr (-1)) 24
        let s3 ← expectDecodeStep "decode/0" s2 (qmulIntInstr 0) 24
        let s4 ← expectDecodeStep "decode/1" s3 (qmulIntInstr 1) 24
        let s5 ← expectDecodeStep "decode/127" s4 (qmulIntInstr 127) 24
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add/non-empty/{s6.bitsRemaining}") }
    ,
    { name := "/unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "qmulint/128" [qmulIntInstr 128] .rangeChk
        expectAssembleErr "qmulint/-129" [qmulIntInstr (-129)] .rangeChk }
    ,
    { name := "/unit/error-order/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQmulIntDirect 0 #[]) .stkUnd
        expectErr "type/top-null" (runQmulIntDirect 0 #[.null]) .typeChk
        expectErr "type/top-cell" (runQmulIntDirect 0 #[.cell Cell.empty]) .typeChk
        expectErr "error-order/top-non-int-before-lower-int"
          (runQmulIntDirect 5 #[intV 9, .null]) .typeChk
        expectOkStack "pop-order/top-int-over-lower-non-int"
          (runQmulIntDirect 5 #[.null, intV 9]) #[.null, intV 45] }
    ,
    { name := "/unit/dispatch/non-qmulint-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQmulIntDispatchFallback #[]) #[intV 672] }
  ]
  oracle := #[
    mkInputCase "/ok/zero-x-zero-imm" 0 (.num 0),
    mkInputCase "/ok/sign/pos-pos" 3 (.num 7),
    mkInputCase "/ok/sign/pos-neg" (-3) (.num 7),
    mkInputCase "/ok/sign/neg-pos" 3 (.num (-7)),
    mkInputCase "/ok/sign/neg-neg" (-3) (.num (-7)),
    mkInputCase "/ok/boundary/max-times-one" 1 (.num maxInt257),
    mkInputCase "/ok/boundary/min-times-one" 1 (.num minInt257),
    mkInputCase "/ok/boundary/max-times-neg-one" (-1) (.num maxInt257),
    mkInputCase "/ok/boundary/min-plus-one-times-neg-one" (-1) (.num (minInt257 + 1)),
    mkInputCase "/ok/immediate/min-neg128-times-one" (-128) (.num 1),
    mkInputCase "/ok/immediate/max-pos127-times-one" 127 (.num 1),
    mkInputCase "/quiet/overflow/max-times-two" 2 (.num maxInt257),
    mkInputCase "/quiet/overflow/max-times-127" 127 (.num maxInt257),
    mkInputCase "/quiet/overflow/min-times-neg-one" (-1) (.num minInt257),
    mkInputCase "/quiet/overflow/min-times-two" 2 (.num minInt257),
    mkQmulIntCase "/error/underflow/empty-stack" 0 #[],
    mkQmulIntCase "/error/type/top-null" 0 #[.null],
    mkQmulIntCase "/error/type/top-cell" 0 #[.cell Cell.empty],
    mkQmulIntCase "/error/order/top-non-int-before-lower-int" 5 #[intV 9, .null],
    mkQmulIntCase "/pop-order/top-int-over-lower-non-int" 5 #[.null, intV 9],
    mkInputCase "/quiet/nan/via-program/pushnan-before-qmulint" 5 .nan,
    mkInputCase "/error/order/pushint-range-high-before-op" 7 (.num (maxInt257 + 1)),
    mkInputCase "/error/order/pushint-range-low-before-op" 7 (.num (minInt257 - 1)),
    mkCase "/gas/exact/succeeds" #[intV 11]
      #[.pushInt (.num qmulIntSetGasExact), .tonEnvOp .setGasLimit, qmulIntInstr qmulIntGasProbeImm],
    mkCase "/gas/exact-minus-one/out-of-gas" #[intV 11]
      #[.pushInt (.num qmulIntSetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulIntInstr qmulIntGasProbeImm]
  ]
  fuzz := #[
    { seed := 2026020830
      count := 600
      gen := genQmulIntFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULINT
