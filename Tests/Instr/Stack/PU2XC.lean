import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.PU2XC

/-
INSTRUCTION: PU2XC

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Normal path] — runtime success requires `x < depth ∧ y ≤ depth ∧ z ≤ depth + 1`; then the VM does: `push(fetch x)`, `swap 0 1`, `push(fetch y)`, `swap 0 1`, `swap 0 z`.
2. [Runtime underflow path] — if guard fails, execution throws `.stkUnd` with no stack mutation.
3. [Runtime underflow edge] — `x` boundary at `x = depth` is invalid, while `x = depth-1` is valid.
4. [Runtime underflow edge] — `y` boundary at `y = depth + 1` is invalid, while `y = depth` is valid.
5. [Runtime underflow edge] — `z` boundary at `z = depth + 2` is invalid, while `z = depth + 1` is valid.
6. [Runtime index aliasing] — equalities among `x`, `y`, `z` do not error and change permutation of values.
7. [Assembler encoding range] — `.pu2xc x y z` only accepts `x,y,z ∈ [0,15]` and encodes to 24-bit `0x546xyz`.
8. [Assembler error] — any arg > 15 throws `.rangeChk`.
9. [Assembler boundary values] — `0`, `1`, and `15` are accepted for each parameter.
10. [Decoder behavior] — decode prefix `0x546` reads exactly 24 bits and returns `.pu2xc`.
11. [Decoder adjacency] — neighboring prefixes `0x545` and `0x547` are non-`PU2XC` (`PUXCPU`, `PUSH3`) as boundary safety.
12. [Decoder truncation] — insufficient bits for 24-bit dispatch return `.invOpcode`.
13. [Gas edge] — exact cost for a single instruction uses fixed budget from `computeExactGasBudget`.
14. [Gas edge] — exact budget minus one should fail with insufficient gas.

TOTAL BRANCHES: 14

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests must be covered by the fuzzer.
-/

private def pu2xcId : InstrId := { name := "PU2XC" }

private def v (n : Int) : Value :=
  intV n

private def mkCase
    (name : String)
    (x y z : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pu2xcId
    program := #[.pu2xc x y z]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pu2xcId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runPu2xcDirect
    (x y z : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPu2xc (.pu2xc x y z) stack

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
  | .error e =>
      throw (IO.userError s!"{label}: decode failed: {e}")
  | .ok (instr, bits, code') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else
        pure code'

private def intStackLen (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (v (Int.ofNat i))
    return out

private def valueBoundaryPool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 42,
    intV (-42),
    intV maxInt257,
    intV minInt257,
    .null,
    .cell Cell.empty,
    .slice (Slice.ofCell Cell.empty),
    .builder Builder.empty,
    .tuple #[]
  ]

private def pickPu2xcValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (valueBoundaryPool.size - 1)
  (valueBoundaryPool[idx]!, rng1)

private def genPu2xcStack (depth : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut rng := rng0
  let mut acc : Array Value := #[]
  for _ in [0:depth] do
    let (v, rng') := pickPu2xcValue rng
    acc := acc.push v
    rng := rng'
  return (acc, rng)

private def rawPU2XCCode : Cell :=
  Cell.mkOrdinary (natToBits ((0x546 <<< 12) + (0x0a <<< 8) + (0x2 <<< 4) + 0x3) 24) #[]

private def rawPUXCPUCode : Cell :=
  Cell.mkOrdinary (natToBits ((0x545 <<< 12) + (0x0a <<< 8) + (0x2 <<< 4) + 0x3) 24) #[]

private def rawPUSH3Code : Cell :=
  Cell.mkOrdinary (natToBits ((0x547 <<< 12) + (0x0a <<< 8) + (0x2 <<< 4) + 0x3) 24) #[]

private def rawPU2XCTrunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0x54 8) #[]

private def rawPU2XCTrunc15 : Cell :=
  Cell.mkOrdinary (natToBits (0x546345 >>> 1) 15) #[]

private def pu2xcGasExact : Int :=
  computeExactGasBudget (.pu2xc 7 5 9)

private def pu2xcGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.pu2xc 7 5 9)

private def genPu2xcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 35 then
    let (depth, rng2) := randNat rng1 1 6
    let (xSel, rng3) := randNat rng2 0 5
    let (ySel, rng4) := randNat rng3 0 5
    let (zSel, rng5) := randNat rng4 0 5
    let x : Nat :=
      match xSel with
      | 0 => 0
      | 1 => if depth > 0 then depth - 1 else 0
      | 2 => if depth > 1 then depth / 2 else 0
      | 3 => if depth > 2 then 1 else 0
      | 4 => 0
      | _ => 0
    let y : Nat :=
      match ySel with
      | 0 => 0
      | 1 => if depth > 0 then depth else 0
      | 2 => if depth > 1 then depth / 2 else 0
      | 3 => 1
      | 4 => if depth > 0 then depth - 1 else 0
      | _ => 0
    let zMax : Nat := if depth < 15 then depth + 1 else 15
    let z : Nat :=
      match zSel with
      | 0 => 0
      | 1 => 1
      | 2 => depth
      | 3 => if zMax = 0 then 0 else zMax
      | 4 => if zMax > 0 then zMax - 1 else 0
      | _ => zMax
    let (stack, rng6) := genPu2xcStack depth rng5
    let (tag, rng7) := randNat rng6 0 999_999
    ({
      name := s!"fuzz/success-small/{tag}",
      instr := pu2xcId,
      program := #[.pu2xc x y z],
      initStack := stack,
      fuel := 1_000_000
    }, rng7)
  else if shape < 60 then
    let (depth, rng2) := randNat rng1 7 16
    let (xSel, rng3) := randNat rng2 0 4
    let (ySel, rng4) := randNat rng3 0 4
    let (zSel, rng5) := randNat rng4 0 4
    let depthPlusOne : Nat := if depth < 15 then depth + 1 else 15
    let x : Nat :=
      match xSel with
      | 0 => 0
      | 1 => if depth > 0 then depth - 1 else 0
      | 2 => if depth > 1 then depth / 2 else 1
      | 3 => 15
      | _ => 14
    let y : Nat :=
      match ySel with
      | 0 => 0
      | 1 => if depth > 0 then depth else 0
      | 2 => if depth > 3 then depth - 2 else 0
      | 3 => 15
      | _ => 1
    let z : Nat :=
      match zSel with
      | 0 => 1
      | 1 => if depthPlusOne > 0 then depthPlusOne else 0
      | 2 => if depthPlusOne > 1 then depthPlusOne - 1 else 0
      | 3 => 0
      | _ => if depthPlusOne > 2 then 2 else 0
    let (stack, rng6) := genPu2xcStack depthPlusOne rng5
    let (tag, rng7) := randNat rng6 0 999_999
    ({
      name := s!"fuzz/success-large/{tag}",
      instr := pu2xcId,
      program := #[.pu2xc x y z],
      initStack := stack,
      fuel := 1_000_000
    }, rng7)
  else if shape < 75 then
    -- underflow via x > depth
    let (depth, rng2) := randNat rng1 0 14
    let (bias, rng3) := randNat rng2 0 2
    let x : Nat := Nat.min 15 (depth + 1 + bias)
    let (ySel, rng4) := randNat rng3 0 1
    let y : Nat :=
      match ySel with
      | 0 => 0
      | _ => if depth > 0 then depth else 0
    let z : Nat :=
      if depth < 14 then depth + 1 else 15
    let (stack, rng5) := genPu2xcStack depth rng4
    let (tag, rng6) := randNat rng5 0 999_999
    ({
      name := s!"fuzz/underflow-x/{tag}",
      instr := pu2xcId,
      program := #[.pu2xc x y z],
      initStack := stack,
      fuel := 1_000_000
    }, rng6)
  else if shape < 88 then
    -- underflow via y > depth (x, z remain valid-ish)
    let (depth, rng2) := randNat rng1 1 14
    let x : Nat := if depth > 0 then depth - 1 else 0
    let y : Nat := depth + 1
    let z : Nat := if depth < 14 then depth + 1 else 15
    let (stack, rng3) := genPu2xcStack depth rng2
    let (tag, rng4) := randNat rng3 0 999_999
    ({
      name := s!"fuzz/underflow-y/{tag}",
      instr := pu2xcId,
      program := #[.pu2xc x y z],
      initStack := stack,
      fuel := 1_000_000
    }, rng4)
  else if shape < 96 then
    -- underflow via z > depth + 1 (hard boundary)
    let (depth, rng2) := randNat rng1 1 13
    let (xSel, rng3) := randNat rng2 0 1
    let x : Nat :=
      match xSel with
      | 0 => 0
      | _ => if depth > 1 then 1 else 0
    let y : Nat := if depth > 0 then 0 else 0
    let (stack, rng4) := genPu2xcStack depth rng3
    let (tag, rng5) := randNat rng4 0 999_999
    ({
      name := s!"fuzz/underflow-z/{tag}",
      instr := pu2xcId,
      program := #[.pu2xc x y 15],
      initStack := stack,
      fuel := 1_000_000
    }, rng5)
  else
    -- alias-heavy and non-int payload
    let (depth, rng2) := randNat rng1 2 10
    let (x, rng3) := randNat rng2 0 1
    let (z, rng4) := randNat rng3 0 (if depth > 0 then depth else 0)
    let y : Nat := if x = z then x else depth
    let (stack, rng5) := genPu2xcStack depth rng4
    let (tag, rng6) := randNat rng5 0 999_999
    ({
      name := s!"fuzz/alias/{tag}",
      instr := pu2xcId,
      program := #[.pu2xc x y z],
      initStack := stack,
      fuel := 1_000_000
    }, rng6)

/--
  Branch coverage checklist (oracle tags are shown inline; fuzz covers all branches above if oracle misses any):
  - [B1] normal success
  - [B2] underflow failure
  - [B6] aliasing
  - [B7]-[B9] assembler boundaries
  - [B10]-[B12] decoder boundaries
  - [B13]-[B14] gas boundaries
-/

def suite : InstrSuite where
  id := pu2xcId
  unit := #[
    { name := "unit/assembler/valid-boundary"
      run := do
        match assembleCp0 [Instr.pu2xc 0 0 0] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"unit/assembler/valid/min failed: {e}")
        match assembleCp0 [Instr.pu2xc 15 15 15] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"unit/assembler/valid/max failed: {e}")
    }
    ,
    { name := "unit/assembler/out-of-range"
      run := do
        expectAssembleErr "x-over-15" [Instr.pu2xc 16 0 0] .rangeChk
        expectAssembleErr "y-over-15" [Instr.pu2xc 0 16 0] .rangeChk
        expectAssembleErr "z-over-15" [Instr.pu2xc 0 0 16] .rangeChk
    }
    ,
    { name := "unit/decode/round-trip-and-adjacent"
      run := do
        let code : Array Instr := #[(Instr.xcpu2 1 2 3), (Instr.pu2xc 10 11 12), (Instr.push3 7 8 9)]
        let codeCell ←
          match assembleCp0 code.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/decode/roundtrip assemble failed: {e}")
        let s0 := Slice.ofCell codeCell
        let s1 ← expectDecodeStep "decode/xcpu2" s0 (.xcpu2 1 2 3) 24
        let s2 ← expectDecodeStep "decode/pu2xc" s1 (.pu2xc 10 11 12) 24
        let s3 ← expectDecodeStep "decode/push3" s2 (.push3 7 8 9) 24
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"unit/decode/roundtrip: expected exhausted slice, got {s3.bitsRemaining} bits")
    }
    ,
    { name := "unit/dispatch/deep-success"
      run := do
        expectOkStack "dispatch/pu2xc" (runPu2xcDirect 0 0 0 (intStackLen 1)) (#[v 0, v 0, v 0])
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "ok/size1-baseline" 0 0 0 (intStackLen 1),
    mkCase "ok/size2-below-top" 0 1 2 (intStackLen 2),
    mkCase "ok/size2-top-valid" 1 0 2 (intStackLen 3),
    mkCase "ok/size3-boundary" 2 2 3 (intStackLen 3),
    mkCase "ok/size3-noop-x" 0 1 1 (intStackLen 3),
    mkCase "ok/size3-y-zero" 2 0 3 (intStackLen 3),
    mkCase "ok/size4-bigger" 1 3 4 (intStackLen 4),
    mkCase "ok/size4-x2-y4-z3" 2 4 3 (intStackLen 4),
    mkCase "ok/size5-z-top" 4 5 5 (intStackLen 5),
    mkCase "ok/size5-non-int" 4 5 3 (#[v 10, .null, .cell Cell.empty, v 20, .slice (Slice.ofCell Cell.empty)]),
    mkCase "ok/size6-x3" 3 0 6 (intStackLen 6),
    mkCase "ok/size8-zmax" 0 7 8 (intStackLen 8),
    mkCase "ok/size10-long" 9 10 11 (intStackLen 11),
    mkCase "ok/size10-non-int" 3 7 8 (#[(.int (.num 100)), .cell Cell.empty, .null, .slice (Slice.ofCell Cell.empty), .builder Builder.empty, v 1, v 2, v 3, v 4, v 5]),
    mkCase "ok/size16-top-bounds" 15 15 15 (intStackLen 16),
    mkCase "ok/size16-z-max" 4 7 15 (intStackLen 16),
    mkCase "ok/size16-all-zero" 0 0 15 (intStackLen 16),
    mkCase "ok/size15-min-x" 14 15 15 (intStackLen 15),
    mkCase "ok/non-int-top" 0 10 11 (#[(.null), .builder Builder.empty, .slice (Slice.ofCell Cell.empty), .cell Cell.empty, .tuple #[], v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11]),
    mkCase "ok/alias-x-y" 4 4 3 (intStackLen 6),
    mkCase "ok/alias-x-z" 4 1 4 (intStackLen 6),
    mkCase "ok/alias-y-z" 2 5 5 (intStackLen 6),
    mkCase "ok/alias-all" 3 3 3 (intStackLen 4),
    mkCase "ok/alias-with-non-int" 1 1 1 (#[(.null), .cell Cell.empty, .slice (Slice.ofCell Cell.empty), .builder Builder.empty, intV 7, intV 8]),
    -- [B2]
    mkCase "err/x-underflow-empty" 0 0 0 #[],
    mkCase "err/x-underflow-size1" 1 0 0 (intStackLen 1),
    mkCase "err/x-underflow-size2" 2 1 1 (intStackLen 2),
    mkCase "err/x-underflow-size8" 8 1 1 (intStackLen 8),
    mkCase "err/x-underflow-size16" 15 0 0 (intStackLen 16),
    -- [B3]
    mkCase "err/y-underflow-size1" 0 2 0 (intStackLen 1),
    mkCase "err/y-underflow-size2" 0 3 2 (intStackLen 2),
    mkCase "err/y-underflow-size5" 1 5 4 (intStackLen 5),
    mkCase "err/y-underflow-size10" 0 11 6 (intStackLen 10),
    -- [B4]
    mkCase "err/z-underflow-size2" 0 0 5 (intStackLen 2),
    mkCase "err/z-underflow-size4" 1 1 6 (intStackLen 4),
    mkCase "err/z-underflow-size10" 0 3 12 (intStackLen 10),
    mkCase "err/z-underflow-size8" 8 8 10 (intStackLen 8),
    -- [B7-B9]
    mkCase "asm/valid/min" 0 0 0 (intStackLen 2),
    mkCase "asm/valid/edge" 15 15 15 (intStackLen 16),
    mkCase "asm/valid/z-15-depth-15" 5 5 15 (intStackLen 16),
    -- [B10]
    mkCaseCode "decode/pu2xc" (intStackLen 8) rawPU2XCCode,
    mkCaseCode "decode/neighbor-545" (intStackLen 4) rawPUXCPUCode,
    mkCaseCode "decode/neighbor-547" (intStackLen 4) rawPUSH3Code,
    mkCaseCode "decode/truncated-8" #[] rawPU2XCTrunc8,
    mkCaseCode "decode/truncated-15" #[] rawPU2XCTrunc15,
    -- [B13]
    mkCase "gas/exact" 7 5 9 (intStackLen 16) (oracleGasLimitsExact pu2xcGasExact),
    mkCase "gas/exact-minus-one" 7 5 9 (intStackLen 16) (oracleGasLimitsExactMinusOne pu2xcGasExactMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr pu2xcId
      count := 500
      gen := genPu2xcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PU2XC
