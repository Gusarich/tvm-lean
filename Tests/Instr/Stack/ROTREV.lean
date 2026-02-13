import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.ROTREV

/-
INSTRUCTION: ROTREV

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Normal path, runtime] — valid stack depth >=3, no stack underflow check failure, values are rotated by index swaps.
2. [Edge case, runtime] — empty stack triggers `stkUnd` from `stack.size < 3` check.
3. [Edge case, runtime] — one-item stack triggers `stkUnd` from `stack.size < 3` check.
4. [Edge case, runtime] — two-item stack triggers `stkUnd` from `stack.size < 3` check.
5. [Runtime property] — for depth >3, elements above the selected triple keep their relative order after rotation.
6. [Runtime property] — no type checks; all `Value` variants pass through unchanged if depth is sufficient.
7. [Assembler encoding] — fixed-form opcode with no parameters (`[.rotRev]`), no range-check branch because there are no immediate arguments.
8. [Decoder behavior] — decode of bits `0x59` yields `.rotRev` and consumes 8 bits.
9. [Decoder behavior] — opcode aliasing boundaries: `0x58` decodes to `.rot`, `0x5a` decodes to `.twoSwap`.
10. [Decoder behavior] — decode of truncated bitstreams (e.g. `<8` bits) must fail with `invOpcode`.
11. [Gas accounting] — fixed base gas path: exact gas budget succeeds.
12. [Gas accounting] — out-of-gas boundary: exact-1 budget fails before/at execution.

Gas accounting note: no additional runtime-variable gas penalty in Lean/C++ for `.rotRev` (base cost + implicit return gas only).
TOTAL BRANCHES: 12

Each branch above is represented by the tagged tests below in `unit`, `oracle`, or `fuzz`.
-/

private def rotRevId : InstrId := { name := "ROTREV" }

private def rotRevInstr : Instr := .rotRev

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rotRevInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rotRevId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runRotRevDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackRotRev rotRevInstr stack

private def expectedRotRev (stack : Array Value) : Array Value :=
  match stack[0]?, stack[1]?, stack[2]? with
  | some x0, some x1, some x2 =>
      if stack.size = 3 then
        #[x1, x2, x0]
      else
        #[x1, x2, x0] ++ stack.extract 3 stack.size
  | _, _, _ => stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error decodeError =>
      throw (IO.userError s!"{label}: decode failed with {decodeError}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def expectDecodeErr (label : String) (bits : BitString) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary bits #[])) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, decodedBits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={decodedBits}")

private def rotrevSetGasExact : Int :=
  computeExactGasBudget rotRevInstr

private def rotrevSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rotRevInstr

private def gasProgram (limit : Int) : Array Instr :=
  #[.pushInt (.num limit), .tonEnvOp .setGasLimit, rotRevInstr]

private def genRotRevFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (case, rng2) :=
    if shape = 0 then
      (mkCase "/fuzz/shape-0/ok/depth3-small" #[intV 7, intV (-7), intV 12], rng1)
    else if shape = 1 then
      (mkCase "/fuzz/shape-1/ok/depth3-boundary" #[intV maxInt257, intV 0, intV minInt257], rng1)
    else if shape = 2 then
      let (x, rng2) := pickInt257Boundary rng1
      let (y, rng3) := pickInt257Boundary rng2
      let (z, rng4) := pickInt257Boundary rng3
      (mkCase "/fuzz/shape-2/ok/depth3-boundary-pool" #[intV x, intV y, intV z], rng4)
    else if shape = 3 then
      let (x, rng2) := pickSigned257ish rng1
      let (y, rng3) := pickSigned257ish rng2
      let (z, rng4) := pickSigned257ish rng3
      (mkCase "/fuzz/shape-3/ok/depth4-mixed" #[intV x, intV y, intV z, .null], rng4)
    else if shape = 4 then
      (mkCase "/fuzz/shape-4/ok/depth5-mixed" #[intV 1, .cell Cell.empty, intV 2, .null, intV 3], rng1)
    else if shape = 5 then
      (mkCase "/fuzz/shape-5/ok/tail-non-int" #[.null, .cell Cell.empty, intV 42], rng1)
    else if shape = 6 then
      (mkCase "/fuzz/shape-6/ok/depth3-nan" #[.int .nan, intV 9, intV 11], rng1)
    else if shape = 7 then
      (mkCase "/fuzz/shape-7/error/underflow-empty" #[], rng1)
    else if shape = 8 then
      (mkCase "/fuzz/shape-8/error/underflow-one" #[intV 1], rng1)
    else if shape = 9 then
      ( (mkCase "/fuzz/shape-9/gas/exact" #[])
          |> fun c => { c with initStack := #[intV 11, intV 12, intV 13], program := gasProgram rotrevSetGasExact }
      , rng1)
    else
      ( (mkCase "/fuzz/shape-10/gas/exact-minus-one" #[])
          |> fun c => { c with initStack := #[intV 11, intV 12, intV 13], program := gasProgram rotrevSetGasExactMinusOne }
      , rng1)

  (case, rng2)

def suite : InstrSuite where
  id := rotRevId
  unit := #[
    { name := "unit/ok/depth3-rotation"
      run := do
        let input := #[intV 1, intV 2, intV 3]
        expectOkStack "unit/ok/depth3-rotation"
          (runRotRevDirect input)
          (expectedRotRev input) }
    ,
    { name := "unit/ok/depth3-mixed-types"
      run := do
        let input := #[.null, .cell Cell.empty, intV 7]
        expectOkStack "unit/ok/depth3-mixed-types"
          (runRotRevDirect input)
          (expectedRotRev input) }
    ,
    { name := "unit/ok/depth4-rotation-preserves-tail"
      run := do
        let input := #[intV 1, intV 2, intV 3, intV 4, intV 5]
        expectOkStack "unit/ok/depth4-rotation-preserves-tail"
          (runRotRevDirect input)
          (expectedRotRev input) }
    ,
    { name := "unit/error/underflow-empty"
      run := do
        expectErr "unit/error/underflow-empty" (runRotRevDirect #[]) .stkUnd }
    ,
    { name := "unit/error/underflow-one"
      run := do
        expectErr "unit/error/underflow-one" (runRotRevDirect #[intV 7]) .stkUnd }
    ,
    { name := "unit/error/underflow-two"
      run := do
        expectErr "unit/error/underflow-two" (runRotRevDirect #[intV 7, intV 8]) .stkUnd }
    ,
    { name := "unit/opcode/decode-encode/rotrev-bitpattern"
      run := do
        match assembleCp0 [rotRevInstr] with
        | .error e => throw (IO.userError s!"assemble/rotrev: expected success, got {reprStr e}")
        | .ok code =>
            if code.bits != natToBits 0x59 8 then
              throw (IO.userError
                s!"assemble/rotrev: expected bits=0x59, got {reprStr code.bits}")
            else if code.refs.size != 0 then
              throw (IO.userError s!"assemble/rotrev: expected no refs, got {code.refs.size}")
            else
              let slice0 := Slice.ofCell code
              let slice1 ← expectDecodeStep "unit/opcode/decode-rotrev" slice0 rotRevInstr 8
              if slice1.bitsRemaining != 0 then
                throw (IO.userError
                  s!"unit/opcode/decode-rotrev: expected code to fully decode, got {slice1.bitsRemaining}")
              else
                pure () }
    ,
    { name := "unit/opcode/decode/boundary-left-and-right"
      run := do
        let sliceRot := Slice.ofCell (Cell.mkOrdinary (natToBits 0x58 8) #[])
        let sliceRight := Slice.ofCell (Cell.mkOrdinary (natToBits 0x5a 8) #[])
        let _ ← expectDecodeStep "unit/opcode/decode/boundary-left" sliceRot .rot 8
        let _ ← expectDecodeStep "unit/opcode/decode/boundary-right" sliceRight .twoSwap 8
        pure () }
    ,
    { name := "unit/opcode/decode/truncated-4bits"
      run := do
        expectDecodeErr "unit/opcode/decode/truncated-4bits" (natToBits 0x5 4) .invOpcode
        expectDecodeErr "unit/opcode/decode/truncated-empty" #[] .invOpcode }
    ,
    { name := "unit/opcode/dispatch/fallback-default"
      run := do
        expectOkStack "unit/opcode/dispatch/fallback-default"
          (runRotRevDirect #[intV 1, intV 2, intV 3])
          (expectedRotRev #[intV 1, intV 2, intV 3]) }
  ]
  oracle := #[
    -- [B1, B5]
    mkCase "ok/depth3/positive" #[intV 10, intV 20, intV 30],
    -- [B1]
    mkCase "ok/depth3/negative" #[intV (-1), intV (-2), intV (-3)],
    -- [B1]
    mkCase "ok/depth3/boundary-max" #[intV maxInt257, intV (maxInt257 - 1), intV (maxInt257 - 2)],
    -- [B1]
    mkCase "ok/depth3/boundary-min" #[intV minInt257, intV (minInt257 + 1), intV (minInt257 + 2)],
    -- [B1]
    mkCase "ok/depth3/zero" #[intV 0, intV 0, intV 0],
    -- [B1]
    mkCase "ok/depth3/symmetry" #[intV 42, intV 42, intV 42],
    -- [B1, B6]
    mkCase "ok/depth3/mixed-null-cell" #[.null, .cell Cell.empty, intV 13],
    -- [B1, B6]
    mkCase "ok/depth3/mixed-cell-null" #[.cell Cell.empty, intV (-1), .null],
    -- [B1, B5]
    mkCase "ok/depth4" #[intV 1, intV 2, intV 3, intV 4],
    -- [B1, B5]
    mkCase "ok/depth4/reversed" #[intV 3, intV 2, intV 1, intV 0],
    -- [B1, B5]
    mkCase "ok/depth5" #[intV 5, intV 6, intV 7, intV 8, intV 9],
    -- [B1, B5]
    mkCase "ok/depth5/mixed" #[.cell Cell.empty, intV 11, .null, intV 22, .cell Cell.empty],
    -- [B1]
    mkCase "ok/depth3/boundary-cross" #[intV (maxInt257 - 1), intV 0, intV minInt257],
    -- [B1]
    mkCase "ok/depth3/random-pool-a" #[intV 17, intV (-17), intV 17],
    -- [B1]
    mkCase "ok/depth3/random-pool-b" #[intV 123456, intV 654321, intV (-99)],
    -- [B1, B6]
    mkCase "ok/depth3/with-null" #[.null, intV 12, intV 13],
    -- [B1, B6]
    mkCase "ok/depth3/with-cell" #[intV 12, .cell Cell.empty, intV 13],
    -- [B2]
    mkCase "error/underflow-empty" #[],
    -- [B3]
    mkCase "error/underflow-one" #[intV 7],
    -- [B4]
    mkCase "error/underflow-two" #[intV 7, intV 8],
    -- [B11]
    mkCase "ok/gas/exact" #[intV 11, intV 12, intV 13] (gasProgram rotrevSetGasExact),
    -- [B12]
    mkCase "error/gas/exact-minus-one" #[intV 11, intV 12, intV 13] (gasProgram rotrevSetGasExactMinusOne),
    -- [B1, B5]
    mkCase "ok/depth6/long" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6],
    -- [B1]
    mkCase "ok/depth3/boundary-low" #[intV 1, intV 0, intV 2],
    -- [B1]
    mkCase "ok/depth3/boundary-high" #[intV (maxInt257 - 2), intV (minInt257 + 2), intV 7],
    -- [B1, B5]
    mkCase "ok/depth4/nested" #[intV 100, intV 200, intV 300, .null],
    -- [B1]
    mkCase "ok/depth5/repeat-op" #[intV 1, intV 2, intV 3, intV 4, intV 5],
    -- [B1]
    mkCase "ok/depth3/identity-duplicates" #[intV 9, intV 9, intV 9],
    -- [B1]
    mkCase "ok/depth3/mixed-ints" #[intV (-1), intV 1, intV (-1)]
  ]
  fuzz := #[
    { seed := 2026030110
      count := 500
      gen := genRotRevFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.ROTREV
