import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.ROT

/-
INSTRUCTION: ROT

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime normal path — when stack size ≥ 3, `.rot` rotates the top triple
   `(x0, x1, x2)` into `(x1, x2, x0)` and returns success.
2. [B2] Runtime shape property — for stack depth > 3, elements below the top three are untouched.
3. [B3] Runtime type behavior — there are no type/range checks in `ROT`; all stack item
   variants are handled uniformly.
4. [B4] Runtime underflow path — empty stack (`size = 0`) raises `.stkUnd`.
5. [B5] Runtime underflow path — one-item stack (`size = 1`) raises `.stkUnd`.
6. [B6] Runtime underflow path — two-item stack (`size = 2`) raises `.stkUnd`.
7. [B7] Assembler encoding — `.rot` is fixed-form, no immediate fields, so encoding has no range-check branches.
8. [B8] Decoder behavior — raw opcode `0x58` decodes to `.rot` and consumes exactly 8 bits.
9. [B9] Decoder behavior — opcode adjacency/aliasing around boundaries:
   `0x57` → `.drop2`, `0x59` → `.rotRev`, `0x5a` → `.twoSwap`.
10. [B10] Decoder behavior — truncated bitstreams (`<8` bits) produce `.invOpcode`.
11. [B11] Gas accounting — base fixed-cost path succeeds with exact computed budget.
12. [B12] Gas accounting — exact-1 budget fails before/at execution.

Gas accounting note: no per-operand variable penalty branch exists for `.rot`; only the fixed
instruction cost path is exercised.

TOTAL BRANCHES: 12

Each oracle test below is tagged by branch coverage.
-/

private def rotId : InstrId := { name := "ROT" }

private def rotInstr : Instr := .rot

private def rotGasExact : Int :=
  computeExactGasBudget rotInstr

private def rotGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rotInstr

private def rotGasLimits : OracleGasLimits :=
  oracleGasLimitsExact rotGasExact

private def rotGasLimitsMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne rotGasExactMinusOne

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rotInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rotId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rotId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def runRotDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackRot rotInstr stack

private def expectedRot (stack : Array Value) : Array Value :=
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

private def gasProgram (limit : Int) : Array Instr :=
  #[.pushInt (.num limit), .tonEnvOp .setGasLimit, rotInstr]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def fullSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xa5 8) #[])

private def noiseCellA : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[]

private def noiseCellB : Cell := Cell.mkOrdinary (natToBits 0x5b 8) #[]

private def genRotFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/shape-0/ok/depth3-small" #[intV 7, intV (-7), intV 12], rng1)
    else if shape = 1 then
      (mkCase "fuzz/shape-1/ok/depth3-boundary" #[intV maxInt257, intV 0, intV minInt257], rng1)
    else if shape = 2 then
      let (x, rng2) := pickInt257Boundary rng1
      let (y, rng3) := pickInt257Boundary rng2
      let (z, rng4) := pickInt257Boundary rng3
      (mkCase "fuzz/shape-2/ok/depth3-boundary-pool" #[intV x, intV y, intV z], rng4)
    else if shape = 3 then
      let (x, rng2) := pickSigned257ish rng1
      let (y, rng3) := pickSigned257ish rng2
      let (z, rng4) := pickSigned257ish rng3
      (mkCase "fuzz/shape-3/ok/depth4-mixed" #[intV x, intV y, intV z, .null], rng4)
    else if shape = 4 then
      let (x, rng2) := pickSigned257ish rng1
      let (y, rng3) := pickSigned257ish rng2
      (mkCase "fuzz/shape-4/ok/depth5-mixed-tail" #[.cell noiseCellA, intV x, .null, intV y, intV 3], rng3)
    else if shape = 5 then
      let (noise, rng2) := pickFromPool (#[(Cell.mkOrdinary #[] #[]), noiseCellA, noiseCellB] : Array Cell) rng1
      (mkCase "fuzz/shape-5/ok/depth5-cell-tail" #[intV 1, intV 2, intV 3, .slice fullSlice, .cell noise], rng2)
    else if shape = 6 then
      let (x, rng2) := pickSigned257ish rng1
      (mkCase "fuzz/shape-6/ok/depth6-mixed-types"
        #[.null, intV x, .cell noiseCellA, .tuple #[], .builder Builder.empty, .cont (.quit 0)], rng2)
    else if shape = 7 then
      (mkCase "fuzz/shape-7/error/underflow-empty" #[], rng1)
    else if shape = 8 then
      (mkCase "fuzz/shape-8/error/underflow-one" #[intV 1], rng1)
    else if shape = 9 then
      (mkCase "fuzz/shape-9/error/underflow-two" #[.null, intV 2], rng1)
    else if shape = 10 then
      (mkCaseCode "fuzz/shape-10/decode/raw-rot" #[intV 3, intV 4, intV 5] (raw8 0x58), rng1)
    else if shape = 11 then
      (mkCaseCode "fuzz/shape-11/decode/raw-rotrev" #[intV 3, intV 4, intV 5] (raw8 0x59), rng1)
    else if shape = 12 then
      (mkCaseCode "fuzz/shape-12/decode/raw-twoswap" #[intV 3, intV 4, intV 5, intV 6] (raw8 0x5a), rng1)
    else if shape = 13 then
      (mkCaseCode "fuzz/shape-13/decode/truncated-4bits" #[intV 7, intV 8, intV 9] (Cell.mkOrdinary (natToBits 0x5 4) #[]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/shape-14/gas/exact" #[intV 11, intV 12, intV 13] (gasProgram rotGasExact) rotGasLimits, rng1)
    else
      (mkCase "fuzz/shape-15/gas/exact-minus-one" #[intV 11, intV 12, intV 13] (gasProgram rotGasExactMinusOne) rotGasLimitsMinusOne, rng1)
  (case, rng2)

def suite : InstrSuite where
  id := rotId
  unit := #[
    { name := "unit/rot/depth3-rotation"
      run := do
        let input := #[intV 1, intV 2, intV 3]
        expectOkStack "unit/rot/depth3-rotation" (runRotDirect input) (expectedRot input)
    },
    { name := "unit/rot/depth4-rotation-preserves-tail"
      run := do
        let input := #[intV 1, intV 2, intV 3, intV 4]
        expectOkStack "unit/rot/depth4-rotation-preserves-tail" (runRotDirect input) (expectedRot input)
    },
    { name := "unit/rot/depth3-mixed-types"
      run := do
        let input := #[.null, .cell Cell.empty, intV 7]
        expectOkStack "unit/rot/depth3-mixed-types" (runRotDirect input) (expectedRot input)
    },
    { name := "unit/rot/error/underflow-empty"
      run := do
        expectErr "unit/rot/error/underflow-empty" (runRotDirect #[]) .stkUnd
    },
    { name := "unit/rot/error/underflow-one"
      run := do
        expectErr "unit/rot/error/underflow-one" (runRotDirect #[intV 7]) .stkUnd
    },
    { name := "unit/rot/error/underflow-two"
      run := do
        expectErr "unit/rot/error/underflow-two" (runRotDirect #[intV 7, intV 8]) .stkUnd
    },
    { name := "unit/rot/encode-fixed/8-bit"
      run := do
        match assembleCp0 [rotInstr] with
        | .error e =>
            throw (IO.userError s!"unit/rot/encode-fixed/8-bit: expected success, got {reprStr e}")
        | .ok code =>
            if code.bits != natToBits 0x58 8 then
              throw (IO.userError
                s!"unit/rot/encode-fixed/8-bit: expected bits=0x58, got {reprStr code.bits}")
            else if code.refs.size != 0 then
              throw (IO.userError
                s!"unit/rot/encode-fixed/8-bit: expected no refs, got {code.refs.size}")
            else
              let slice0 := Slice.ofCell code
              let slice1 ← expectDecodeStep "unit/rot/encode-fixed/8-bit/decode" slice0 rotInstr 8
              if slice1.bitsRemaining != 0 then
                throw (IO.userError
                  s!"unit/rot/encode-fixed/8-bit: expected no trailing bits, got {slice1.bitsRemaining}")
              else
                pure ()
    },
    { name := "unit/rot/decode/adjacent-boundaries"
      run := do
        let left := Slice.ofCell (raw8 0x57)
        let right := Slice.ofCell (raw8 0x59)
        let far := Slice.ofCell (raw8 0x5a)
        let _ ← expectDecodeStep "unit/rot/decode/left-boundary" left .drop2 8
        let _ ← expectDecodeStep "unit/rot/decode/center" right .rotRev 8
        let _ ← expectDecodeStep "unit/rot/decode/right-boundary" far .twoSwap 8
        pure ()
    },
    { name := "unit/rot/decode/truncated-streams"
      run := do
        expectDecodeErr "unit/rot/decode/truncated-4bits" (natToBits 0x5 4) .invOpcode
        expectDecodeErr "unit/rot/decode/truncated-empty" #[] .invOpcode
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/ok/depth3/basic" #[intV 1, intV 2, intV 3],
    -- [B1]
    mkCase "oracle/ok/depth3/negative" #[intV (-1), intV (-2), intV (-3)],
    -- [B1]
    mkCase "oracle/ok/depth3/zero" #[intV 0, intV 0, intV 0],
    -- [B1]
    mkCase "oracle/ok/depth3/max-boundary" #[intV maxInt257, intV (maxInt257 - 1), intV (maxInt257 - 2)],
    -- [B1]
    mkCase "oracle/ok/depth3/min-boundary" #[intV minInt257, intV (minInt257 + 1), intV (minInt257 + 2)],
    -- [B1]
    mkCase "oracle/ok/depth3/identity-pattern" #[intV 9, intV 9, intV 9],
    -- [B1]
    mkCase "oracle/ok/depth3/nontrivial" #[intV 17, intV 42, intV 13],
    -- [B1]
    mkCase "oracle/ok/depth3/reversed-order" #[intV 3, intV 2, intV 1],
    -- [B2]
    mkCase "oracle/ok/depth4/preserve-tail" #[intV 11, intV 12, intV 13, intV 14],
    -- [B2]
    mkCase "oracle/ok/depth5/preserve-tail" #[intV 1, intV 2, intV 3, intV 4, intV 5],
    -- [B2]
    mkCase "oracle/ok/depth8/preserve-tail-heavy" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8],
    -- [B3]
    mkCase "oracle/ok/depth3/mixed-null-cell" #[.null, .cell Cell.empty, intV 13],
    -- [B3]
    mkCase "oracle/ok/depth3/mixed-slice-builder" #[.slice fullSlice, .builder Builder.empty, intV 33],
    -- [B3]
    mkCase "oracle/ok/depth3/mixed-cont-tuple" #[.cont (.quit 0), .tuple #[], intV 7],
    -- [B3]
    mkCase "oracle/ok/depth4/mixed-tail-and-head" #[.null, .cell noiseCellA, intV 3, intV 4],
    -- [B4]
    mkCase "oracle/error/underflow-empty" #[],
    -- [B5]
    mkCase "oracle/error/underflow-one" #[intV 7],
    -- [B6]
    mkCase "oracle/error/underflow-two" #[intV 7, intV 8],
    -- [B7, B8]
    mkCaseCode "oracle/code/rot-encoded" #[intV 11, intV 12, intV 13] (raw8 0x58),
    -- [B9]
    mkCaseCode "oracle/code/neighbor-drop2" #[intV 11, intV 12] (raw8 0x57),
    -- [B9]
    mkCaseCode "oracle/code/neighbor-rotrev" #[intV 11, intV 12, intV 13] (raw8 0x59),
    -- [B9]
    mkCaseCode "oracle/code/neighbor-twoswap" #[intV 11, intV 12, intV 13, intV 14] (raw8 0x5a),
    -- [B10]
    mkCaseCode "oracle/code/error/truncated-4bits" #[] (Cell.mkOrdinary (natToBits 0x5 4) #[]),
    -- [B10]
    mkCaseCode "oracle/code/error/truncated-empty" #[] (Cell.mkOrdinary #[] #[]),
    -- [B11]
    mkCase "oracle/gas/exact-success"
      #[intV 11, intV 12, intV 13]
      (gasProgram rotGasExact)
      rotGasLimits,
    -- [B12]
    mkCase "oracle/gas/exact-minus-one-fails"
      #[intV 11, intV 12, intV 13]
      (gasProgram rotGasExactMinusOne)
      rotGasLimitsMinusOne,
    -- [B1, B2]
    mkCase "oracle/ok/depth6/long-tail" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6],
    -- [B1, B3]
    mkCase "oracle/ok/depth3/mixed-legacy" #[.null, intV (-33), .cell noiseCellB],
    -- [B1, B2]
    mkCase "oracle/ok/depth7/many-different" #[intV 100, intV 200, intV 300, .null, .cell noiseCellA, intV 400, intV 500],
    -- [B1]
    mkCase "oracle/ok/depth3/boundary-max-min" #[intV (maxInt257 - 2), intV minInt257, intV (maxInt257 - 1)],
    -- [B1]
    mkCase "oracle/ok/depth3/boundary-min-max" #[intV (minInt257 + 2), intV (maxInt257 - 2), intV 0],
    -- [B1, B3]
    mkCase "oracle/ok/depth3/mixed-int-null" #[intV (-1), .null, intV 99],
    -- [B1]
    mkCase "oracle/ok/depth3/repeat-zero" #[intV 0, intV 123, intV 0],
    -- [B1, B3]
    mkCase "oracle/ok/depth3/slice-head" #[.slice fullSlice, intV 8, intV 9],
    -- [B1]
    mkCase "oracle/ok/depth4/different-order" #[intV 90, intV 91, intV 92, intV 93],
    -- [B1]
    mkCase "oracle/ok/depth3/alternating-signs" #[intV (-1), intV 2, intV (-3)]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr rotId
      count := 500
      gen := genRotFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.ROT
