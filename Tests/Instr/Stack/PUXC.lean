import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.PUXC

/-
INSTRUCTION: PUXC

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Normal path] — runtime executes when `x < depth` and `y ≤ depth`; effect is:
   - fetch `s[x]`, push copy, swap top with former top, then swap top with index `y`.
   - result is one-item growth in stack and no type checks because all operations are index-only.
2. [Runtime underflow on x] — C++ does `check_underflow_p(x)` before anything else; Lean encodes the same precondition as
   `x < depth`. This branch throws `stkUnd`.
3. [Runtime underflow on y] — for `x` valid and `y > depth`, C++ `check_underflow(y)` triggers `stkUnd`.
4. [Assembler encoding boundaries] — `puxc` arguments are constrained to `[0,15]` each (`x,y ≤ 15`), with no extra immediate bytes.
5. [Assembler boundary values] — `x=0`, `y=0`, `x=15`, `y=15` are valid and round-trip through assembler/disassembler.
6. [Assembler out-of-range rejection] — any `x > 15` or `y > 15` in constructor arguments must fail assembler encoding with `.rangeChk`.
7. [Decoder opcode boundary/round-trip] — decode for opcode byte `0x52` consumes exactly 16 bits and reconstructs `.puxc x y`.
8. [Decoder adjacency safety] — neighboring opcodes (`0x51` XCPU, `0x53` PUSH2) are distinct by first opcode byte; no aliasing into PUXC decode.
9. [Gas edge] — fixed-cost path with `computeExactGasBudget` based on opcode arguments.
10. [Gas success threshold] — `PUSHINT n; SETGASLIMIT; PUXC` succeeds at exact budget (`computeExactGasBudget`).
11. [Gas off-by-one failure] — same sequence with budget one less should fail only due insufficient gas.

TOTAL BRANCHES: 11

- Lean/C++ agree that the branch guard has only runtime stack-depth conditions and no type-paths.
- No variable gas penalty: gas behavior is argument-dependent only through `computeExactGasBudget` (base+stack-op contribution), with no additional runtime-variable branches visible.
- Adjacent opcode checks are in decode space (`0x51`, `0x52`, `0x53`) and are covered by explicit decoder tests.
- If any branch is not hit by oracle tests, the fuzz generator explicitly biases for short-stack underflow and boundary-valid/near-boundary cases.
-/

private def puxcId : InstrId := { name := "PUXC" }

private def v (n : Int) : Value :=
  intV n

private def mkCase
    (name : String)
    (x y : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := puxcId
    program := #[.puxc x y]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPuxcDirect (x y : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPuxc (.puxc x y) stack

private def expectAssembleErr
    (label : String)
    (program : List Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assembler error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assembler error {expected}, got {e}")

private def expectDecodeStep
    (label : String)
    (code : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits code with
  | .error e => throw (IO.userError s!"{label}: decode failed: {e}")
  | .ok (instr, bits, code') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else
        pure code'

private def stack1A : Array Value := #[v 11]
private def stack1B : Array Value := #[.null]
private def stack1C : Array Value := #[.cell Cell.empty]
private def stack2A : Array Value := #[v 101, v 102]
private def stack2B : Array Value := #[v 201, .cell Cell.empty]
private def stack2C : Array Value := #[.null, v 22]
private def stack3A : Array Value := #[v 1, v 2, v 3]
private def stack3B : Array Value := #[v 4, v 5, .null]
private def stack3C : Array Value := #[.cell Cell.empty, v 6, .null]
private def stack4A : Array Value := #[v 11, v 12, v 13, v 14]
private def stack4B : Array Value := #[v 31, .null, v 32, .cell Cell.empty]
private def stack5A : Array Value := #[v 21, v 22, v 23, v 24, v 25]
private def stack8A : Array Value := #[v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8]
private def stack8B : Array Value := #[v 41, .null, .cell Cell.empty, v 42, v 43, v 44, .null, v 45]
private def stack10A : Array Value := #[v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19]
private def stack12A : Array Value := #[v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31]
private def stack15A : Array Value :=
  #[v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15]
private def stack16A : Array Value :=
  #[v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16]

private def genPool : Array Value :=
  #[v 0, v 1, v (-1), v 2, v (-2), v 10, v 255, v (-255), .null, .cell Cell.empty]

private def pickPuxcValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (genPool.size - 1)
  (genPool[idx]!, rng1)

private def genPuxcStack (depth : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut rng := rng0
  let mut acc : Array Value := #[]
  for _ in [0:depth] do
    let (v, rng') := pickPuxcValue rng
    acc := acc.push v
    rng := rng'
  return (acc, rng)

private def genPuxcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 40 then
    -- success-heavy, small-depth and near-boundary swaps
    let (depth, rng2) := randNat rng1 1 6
    let (xSel, rng3) := randNat rng2 0 4
    let (ySel, rng4) := randNat rng3 0 4
    let x : Nat :=
      match xSel with
      | 0 => 0
      | 1 => depth - 1
      | 2 => depth / 2
      | 3 => if depth > 1 then depth - 2 else 0
      | _ => 1
    let y : Nat :=
      match ySel with
      | 0 => 0
      | 1 => 1
      | 2 => depth
      | 3 => if depth > 1 then depth / 2 else 0
      | _ => 0
    let (stack, rng5) := genPuxcStack depth rng4
    let (tag, rng6) := randNat rng5 0 999_999
    let name := s!"fuzz/success-small/d{depth}/{tag}"
    (mkCase name x y stack, rng6)
  else if shape < 70 then
    -- success-heavy, deeper depth cases with boundary y/x values
    let (depth, rng2) := randNat rng1 7 16
    let (xSel, rng3) := randNat rng2 0 4
    let (ySel, rng4) := randNat rng3 0 3
    let x : Nat :=
      match xSel with
      | 0 => 0
      | 1 => 1
      | 2 => if depth > 1 then depth / 2 else 0
      | 3 => if depth > 1 then depth - 1 else 0
      | _ => 15
    let yMax : Nat := if depth > 15 then 15 else depth
    let y : Nat :=
      match ySel with
      | 0 => 0
      | 1 => yMax
      | 2 => if yMax > 0 then yMax - 1 else 0
      | _ => if yMax > 0 then 1 else 0
    let (stack, rng5) := genPuxcStack depth rng4
    let (tag, rng6) := randNat rng5 0 999_999
    let name := s!"fuzz/success-deep/d{depth}/{tag}"
    (mkCase name x y stack, rng6)
  else if shape < 85 then
    -- explicit underflow-x branch (x too large for stack, y unconstrained)
    let (depth, rng2) := randNat rng1 0 14
    let (delta, rng3) := randNat rng2 0 2
    let x0 : Nat := depth + 1 + delta
    let x : Nat := if x0 > 15 then 15 else x0
    let (y, rng4) := randNat rng3 0 15
    let (stack, rng5) := genPuxcStack depth rng4
    let (tag, rng6) := randNat rng5 0 999_999
    let name := s!"fuzz/underflow-x/d{depth}/x{x}/y{y}/{tag}"
    (mkCase name x y stack, rng6)
  else if shape < 95 then
    -- explicit underflow-y branch (x valid, y beyond current depth)
    let (depth, rng2) := randNat rng1 1 14
    let (xSel, rng3) := randNat rng2 0 2
    let x : Nat :=
      match xSel with
      | 0 => 0
      | 1 => depth - 1
      | _ => 1
    let (delta, rng4) := randNat rng3 0 2
    let y0 : Nat := depth + 1 + delta
    let y : Nat := if y0 > 15 then 15 else y0
    let (stack, rng5) := genPuxcStack depth rng4
    let (tag, rng6) := randNat rng5 0 999_999
    let name := s!"fuzz/underflow-y/d{depth}/x{x}/y{y}/{tag}"
    (mkCase name x y stack, rng6)
  else
    -- non-int payloads with legal indices
    let (depth, rng2) := randNat rng1 2 8
    let (xSel, rng3) := randNat rng2 0 2
    let (ySel, rng4) := randNat rng3 0 2
    let x : Nat :=
      match xSel with
      | 0 => 0
      | 1 => 1
      | _ => if depth > 1 then depth - 1 else 0
    let y : Nat :=
      match ySel with
      | 0 => 0
      | 1 => 1
      | _ => depth
    let (stack, rng5) := genPuxcStack depth rng4
    let (tag, rng6) := randNat rng5 0 999_999
    let name := s!"fuzz/nonint/d{depth}/x{x}/y{y}/{tag}"
    (mkCase name x y stack, rng6)

private def puxcGasExact : Int :=
  computeExactGasBudget (.puxc 7 5)

private def puxcGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.puxc 7 5)

private def pouscGasLimitsExact : OracleGasLimits :=
  oracleGasLimitsExact puxcGasExact

private def pouscGasLimitsExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne puxcGasExactMinusOne

/-
  `run` coverage checklist:
  - [B1] success paths are covered by many oracle cases with varying depth and index boundaries.
  - [B2] underflow-x and [B3] underflow-y are explicit cases and fuzz-generated cases.
  - [B4]-[B7] assembler checks are in unit cases (`valid`, `out-of-range`).
  - [B7]-[B8] decoder decode-length and adjacency tests are in unit cases.
  - [B10]-[B11] gas edge cases are explicit oracle cases.
-/
def suite : InstrSuite where
  id := puxcId
  unit := #[
    { name := "unit/assembler/valid-boundaries"
      run := do
        match assembleCp0 [Instr.puxc 0 0] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"unit/assembler/valid/min failed: {e}")
        match assembleCp0 [Instr.puxc 15 15] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"unit/assembler/valid/max failed: {e}")
    }
    ,
    { name := "unit/assembler/out-of-range"
      run := do
        expectAssembleErr "x-over-15" [Instr.puxc 16 0] .rangeChk
        expectAssembleErr "y-over-15" [Instr.puxc 0 16] .rangeChk
    }
    ,
    { name := "unit/decode/round-trip-and-opcode-boundaries" -- [B7,B8]
      run := do
        let code : Array Instr := #[(Instr.xcpu 2 3), (Instr.puxc 7 4), (Instr.push2 10 11), (Instr.puxc 15 15)]
        let codeCell ←
          match assembleCp0 code.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/decode/roundtrip assemble failed: {e}")
        let s0 := Slice.ofCell codeCell
        let s1 ← expectDecodeStep "decode/xcpu" s0 (.xcpu 2 3) 16
        let s2 ← expectDecodeStep "decode/puxc" s1 (.puxc 7 4) 16
        let s3 ← expectDecodeStep "decode/push2" s2 (.push2 10 11) 16
        let s4 ← expectDecodeStep "decode/puxc-max" s3 (.puxc 15 15) 16
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"unit/decode/roundtrip: expected exhausted slice, got {s4.bitsRemaining} bits remaining")
    }
  ]
  oracle := #[
    mkCase "ok/size1-baseline" 0 0 stack1A, -- [B1]
    mkCase "ok/size1-null" 0 0 stack1B, -- [B1]
    mkCase "ok/size1-cell" 0 0 stack1C, -- [B1]
    mkCase "ok/size2-upper-bound" 1 1 stack2A, -- [B1]
    mkCase "ok/size2-x0-y0" 0 0 stack2A, -- [B1]
    mkCase "ok/size2-x0-y1" 0 1 stack2A, -- [B1]
    mkCase "ok/size2-x1-y0" 1 0 stack2A, -- [B1]
    mkCase "ok/size2-x1-y2" 1 2 stack2A, -- [B1]
    mkCase "ok/size2-nonint" 0 1 stack2C, -- [B1]
    mkCase "ok/size3-x0-y2" 0 2 stack3A, -- [B1]
    mkCase "ok/size3-x1-y2" 1 2 stack3A, -- [B1]
    mkCase "ok/size3-x2-y0" 2 0 stack3A, -- [B1]
    mkCase "ok/size3-x2-y3" 2 3 stack3A, -- [B1]
    mkCase "ok/size3-mix" 1 1 stack3B, -- [B1]
    mkCase "ok/size3-null-mix" 1 0 stack3C, -- [B1]
    mkCase "ok/size4-x3-y1" 3 1 stack4A, -- [B1]
    mkCase "ok/size4-x0-y4" 0 4 stack4A, -- [B1]
    mkCase "ok/size4-x2-y3" 2 3 stack4B, -- [B1]
    mkCase "ok/size5-x4-y5" 4 5 stack5A, -- [B1]
    mkCase "ok/size5-x0-y5" 0 5 stack5A, -- [B1]
    mkCase "ok/size8-x7-y0" 7 0 stack8A, -- [B1]
    mkCase "ok/size8-x4-y7" 4 7 stack8A, -- [B1]
    mkCase "ok/size8-x0-y7" 0 7 stack8A, -- [B1]
    mkCase "ok/size8-mix-y7" 3 7 stack8B, -- [B1]
    mkCase "ok/size10-x9-y10" 9 10 stack10A, -- [B1]
    mkCase "ok/size10-x7-y4" 7 4 stack10A, -- [B1]
    mkCase "ok/size12-x11-y12" 11 12 stack12A, -- [B1]
    mkCase "ok/size15-x14-y15" 14 15 stack15A, -- [B1]
    mkCase "ok/size16-x15-y15" 15 15 stack16A, -- [B1]
    mkCase "ok/size16-x0-y15" 0 15 stack16A, -- [B1]
    mkCase "err/x-underflow-empty" 0 0 #[], -- [B2]
    mkCase "err/x-underflow-size1" 1 0 stack1A, -- [B2]
    mkCase "err/x-underflow-size2" 2 0 stack2A, -- [B2]
    mkCase "err/x-underflow-size4" 4 1 stack4A, -- [B2]
    mkCase "err/y-underflow-size1" 0 2 stack1A, -- [B3]
    mkCase "err/y-underflow-size2" 1 4 stack2A, -- [B3]
    mkCase "err/y-underflow-size3-nonint" 0 5 stack2C, -- [B3]
    mkCase "err/y-underflow-size10" 3 15 stack10A, -- [B3]
    { name := "gas/exact-threshold-success"
      instr := puxcId
      program := #[.puxc 7 5]
      initStack := stack12A
      gasLimits := pouscGasLimitsExact }, -- [B10]
    { name := "gas/exact-minus-one-out"
      instr := puxcId
      program := #[.puxc 7 5]
      initStack := stack12A
      gasLimits := pouscGasLimitsExactMinusOne } -- [B11]
  ]
  fuzz := #[
    { seed := 0x7f0a3a1c
      count := 500
      gen := genPuxcFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PUXC
