import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCPU2

/-
INSTRUCTION: XCPU2

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch branch: instruction selector reaches `.xcpu2` path in `execInstrStack`.
2. [B2] Dispatch miss branch: non-`XCPU2` instructions in stack domain must fall through unchanged via `next`.
3. [B2] Runtime normal path: `st.stack.size > Nat.max (Nat.max x y) z` succeeds, then executes `swap 0 x`, `push(y)`, `push(z+1)`.
4. [B3] Runtime underflow path: `st.stack.size ≤ Nat.max (Nat.max x y) z` triggers `.stkUnd` before any stack mutation (`check_underflow_p`).
5. [B4] Index edge case: `x = 0` is a no-op swap and still follows normal execution.
6. [B5] Index aliasing edge: equalities among x/y/z (for example `x=y`, `x=z`, `y=z`) deterministically change pushed values and are exercised as separate logical paths.
7. [B6] Assembler valid encoding: `.xcpu2 x y z` with each arg in `0..15` encodes as 24-bit `0x543xyz`.
8. [B7] Assembler rejection: any of x/y/z = 16 or above throws `.rangeChk`.
9. [B8] Decoder behavior: 24-bit prefix `0x543` decodes to `.xcpu2`; prefix `0x542` decodes to `.xcpuxc`; short/truncated 24-bit stream throws `.invOpcode`.
10. [B9] Gas edge case: base cost is fixed (`gasPerInstr + totBits`), so exact budget succeeds and exact-minus-one fails out-of-gas.

TOTAL BRANCHES: 9

Assembler category has both accepted and rejection branches explicitly (`.rangeChk`) and no other assembler variants.
Decoder category has success, opcode-alias (adjacent prefix), and truncation branches.
Runtime category has success and underflow branches; index-alias cases are distinct edge branches.
Gas category has a fixed-cost branch only; no variable stack-dependent gas penalty branch was found for this instruction.
-/

private def xcpu2Id : InstrId := { name := "XCPU2" }

private def refCell : Cell := Cell.ofUInt 8 0xa5

private def baseSlice : Slice := Slice.ofCell refCell

private def mkCase
    (name : String)
    (x y z : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xcpu2Id
    program := #[.xcpu2 x y z]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCellSliceCase
    (name : String)
    (x y z : Nat)
    (stack : Array Value) : OracleCase :=
  mkCase name x y z stack

private def runXcpu2Direct
    (x y z : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXcpu2 (.xcpu2 x y z) stack

private def xcpu2SetGasExact : Int :=
  computeExactGasBudget (.xcpu2 0 0 0)

private def xcpu2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xcpu2 0 0 0)

private def decodeWord (x y z : Nat) : Nat :=
  (0x543 <<< 12) + (x <<< 8) + (y <<< 4) + z

def decodeXcpu2 (x y z : Nat) : Except Excno (Instr × Nat × Slice) :=
  decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits (decodeWord x y z) 24) #[]))

def decodeXcpuxc (x y z : Nat) : Except Excno (Instr × Nat × Slice) :=
  let w : Nat := (0x542 <<< 12) + (x <<< 8) + (y <<< 4) + z
  decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits w 24) #[]))

private def mkIntStack (n : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:n] do
    out := out.push (intV (Int.ofNat i))
  out

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng0 : StdGen) : α × StdGen :=
  let (idx, rng1) := randNat rng0 0 (pool.size - 1)
  (pool[idx]!, rng1)

private def idxBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 14, 15]

private def valueBoundaryPool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 17,
    intV (-17),
    .null,
    .cell refCell,
    .slice baseSlice,
    .builder Builder.empty,
    .tuple #[],
    intV maxInt257,
    intV (maxInt257 - 1),
    intV minInt257,
    intV (minInt257 + 1)
  ]

private def genStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool valueBoundaryPool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def mkFuzzCase
    (baseName : String)
    (x y z : Nat)
    (depth : Nat)
    (rng0 : StdGen) : OracleCase × StdGen :=
  let (stack, rng1) := genStack depth rng0
  let (tag, rng2) := randNat rng1 0 999_999
  (mkCase (s!"{baseName}/{tag}") x y z stack, rng2)

private def genXcpu2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    let need : Nat := Nat.max (Nat.max x y) z
    let (pad, rng5) := randNat rng4 0 2
    mkFuzzCase "fuzz/success/balanced" x y z (need + pad + 1) rng5
  else if shape = 1 then
    let (x, rng2) := randNat rng1 0 15
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    let (depth, rng5) := randNat rng4 1 8
    mkFuzzCase s!"fuzz/success/zero-x/{x}-{y}-{z}" 0 y z (max 1 depth) rng5
  else if shape = 2 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (z, rng3) := pickFromPool idxBoundaryPool rng2
    mkFuzzCase "fuzz/success/xx-eq" x x z (max 1 (x + 1)) rng3
  else if shape = 3 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    mkFuzzCase "fuzz/success/yz-eq" x y y (max 1 (y + 1)) rng3
  else if shape = 4 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    mkFuzzCase "fuzz/success/zx-eq" x y x (max 1 (x + 1)) rng3
  else if shape = 5 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    let need : Nat := Nat.max (Nat.max x y) z
    let depth : Nat := if need = 0 then 0 else need
    mkFuzzCase "fuzz/underflow/shallow" x y z depth rng4
  else if shape = 6 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    let need : Nat := Nat.max (Nat.max x y) z
    let (trim, rng5) :=
      if need = 0 then
        (0, rng4)
      else
        let (t, r) := randNat rng4 0 (need - 1)
        (t, r)
    mkFuzzCase "fuzz/underflow/random" x y z trim rng5
  else if shape = 7 then
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    let need : Nat := Nat.max (Nat.max x y) z
    let (pad, rng5) := randNat rng4 0 3
    let (depth, rng6) :=
      if need + pad + 1 > 16 then (16, rng5)
      else (need + pad + 1, rng5)
    mkFuzzCase "fuzz/success/large-depth" x y z depth rng6
  else
    let (x, rng2) := pickFromPool idxBoundaryPool rng1
    let (y, rng3) := pickFromPool idxBoundaryPool rng2
    let (z, rng4) := pickFromPool idxBoundaryPool rng3
    mkFuzzCase "fuzz/underflow/empty" x y z 0 rng4

def suite : InstrSuite where
  id := xcpu2Id
  unit := #[
    { name := "unit/dispatch/fallback-next" 
      run := do
        -- [B1]
        expectOkStack "dispatch-fallback-to-next"
          (runHandlerDirectWithNext (fun i => execInstrStack stubHost i) .add (VM.push (.int (.num 77))) #[])
          #[.int (.num 77)]
    }
    ,
    { name := "unit/dispatch/matched-xcpu2" 
      run := do
        -- [B2]
        expectOkStack "dispatch-xcpu2-normal"
          (runXcpu2Direct 0 0 0 #[intV 11])
          #[intV 11, intV 11, intV 11]
    }
    ,
    { name := "unit/dispatch/underflow" 
      run := do
        -- [B3]
        expectErr "underflow-empty"
          (runXcpu2Direct 1 0 0 #[])
          .stkUnd
    }
    ,
    { name := "unit/stack-path/x0-no-swap" 
      run := do
        -- [B4]
        expectOkStack "xcpu2-x0-swaps-nop"
          (runXcpu2Direct 0 1 2 #[intV 1, intV 2, intV 3])
          #[intV 1, intV 2, intV 3, intV 2, intV 1]
    }
    ,
    { name := "unit/stack-path/alias-x-and-y" 
      run := do
        -- [B5]
        expectOkStack "xcpu2-x-y-alias"
          (runXcpu2Direct 1 1 0 #[intV 1, intV 2, intV 3])
          #[intV 1, intV 3, intV 2, intV 3, intV 2]
    }
    ,
    { name := "unit/encode/decode/assemble-valid-boundary" 
      run := do
        -- [B6]
        match assembleCp0 [ .xcpu2 0 0 0 ] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble-xcpu2-valid: unexpected {e}")
      
    }
    ,
    { name := "unit/encode/assemble-x-invalid" 
      run := do
        -- [B7]
        match assembleCp0 [ .xcpu2 16 0 0 ] with
        | .ok _ => throw (IO.userError "assemble-x-invalid: expected rangeChk")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"assemble-x-invalid: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/encode/assemble-y-invalid" 
      run := do
        -- [B7]
        match assembleCp0 [ .xcpu2 0 16 0 ] with
        | .ok _ => throw (IO.userError "assemble-y-invalid: expected rangeChk")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"assemble-y-invalid: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/encode/assemble-z-invalid" 
      run := do
        -- [B7]
        match assembleCp0 [ .xcpu2 0 0 16 ] with
        | .ok _ => throw (IO.userError "assemble-z-invalid: expected rangeChk")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"assemble-z-invalid: expected rangeChk, got {e}")
    }
    ,
    { name := "unit/decode/round-trip-xcpu2" 
      run := do
        -- [B8]
        match decodeXcpu2 3 4 5 with
        | .ok (.xcpu2 3 4 5, bits, rest) =>
            if bits ≠ 24 then
              throw (IO.userError s!"decode-xcpu2: expected 24 bits, got {bits}")
            else if rest.bitsRemaining ≠ 0 then
              throw (IO.userError s!"decode-xcpu2: expected empty suffix, got {rest.bitsRemaining}")
            else
              pure ()
        | .ok (i, _, _) =>
            throw (IO.userError s!"decode-xcpu2: expected .xcpu2, got {i}")
        | .error e =>
            throw (IO.userError s!"decode-xcpu2: unexpected {e}")
    }
    ,
    { name := "unit/decode/adjacent-prefix-xcpuxc" 
      run := do
        -- [B8]
        match decodeXcpuxc 2 7 9 with
        | .ok (.xcpuxc 2 7 9, _, _) =>
            pure ()
        | .ok (i, _, _) =>
            throw (IO.userError s!"decode-xcpuxc: expected .xcpuxc, got {i}")
        | .error e =>
            throw (IO.userError s!"decode-xcpuxc: unexpected {e}")
    }
    ,
    { name := "unit/decode/truncated-24-prefix" 
      run := do
        -- [B8]
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits 0x54 8) #[])) with
        | .error .invOpcode => pure ()
        | .ok (i, bits, _) =>
            throw (IO.userError s!"decode-truncated: expected invOpcode, got {i} after {bits} bits")
        | .error e => throw (IO.userError s!"decode-truncated: expected invOpcode, got {e}")
    }
  ]
  oracle := #[
    -- [B2, B4] x=0 is swap no-op.
    mkCase "ok/minimal-swap-none" 0 0 0 (#[intV 7]),
    mkCase "ok/depth-two-x0" 0 1 2 (#[intV 1, intV 2, intV 3]),
    mkCase "ok/large-depth-x0" 0 14 15 (mkIntStack 16),
    mkCase "ok/x0-deep-boundary-stack" 0 15 15 (mkIntStack 16),
    mkCase "ok/x0-y2-z3" 0 2 3 (#[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7]),
    mkCase "ok/x0-with-non-int" 0 5 4 (#[intV 1, .null, .cell refCell, .slice baseSlice, .builder Builder.empty, .tuple #[]]),

    -- [B2, B5] aliasing among indices.
    mkCase "ok/alias-x-y" 1 1 0 (#[intV 1, intV 2, intV 3]),
    mkCase "ok/alias-x-y-large" 4 4 9 (mkIntStack 10),
    mkCase "ok/alias-y-z" 1 2 2 (#[intV 11, intV 12, intV 13]),
    mkCase "ok/alias-z-x" 3 4 3 (#[intV 21, intV 22, intV 23, intV 24]),
    mkCase "ok/alias-triple" 5 5 5 (mkIntStack 6),
    mkCase "ok/alias-x-z-non-int" 4 0 4 (#[intV 40, .null, .cell refCell, intV 99]),

    -- [B2] general success coverage.
    mkCase "ok/all-max" 15 15 15 (mkIntStack 16),
    mkCase "ok/max-mixed" 13 14 15 (#[intV 0, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15]),
    mkCase "ok/alternating-non-zero" 2 7 9 (mkIntStack 10),
    mkCase "ok/low-high-low" 2 14 1 (mkIntStack 15),
    mkCase "ok/sparse-stack" 2 8 0 (#[intV 0, .null, intV 2, .cell refCell, intV 4, .builder Builder.empty, intV 6, .slice baseSlice, .tuple #[]]),
    mkCase "ok/contains-large-ints" 3 1 8 (#[intV maxInt257, intV (maxInt257 - 1), intV (minInt257 + 1), intV minInt257]),
    mkCase "ok/mixed-tail-types" 5 0 7 (#[.tuple #[], .builder Builder.empty, .cell refCell, .slice baseSlice, intV 1, intV 2, intV 3, intV 4]),
    mkCase "ok/top-heavy-y" 6 12 4 (#[intV 0, intV 0, intV 0, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7]),
    mkCase "ok/bottom-heavy-z" 7 1 10 (mkIntStack 11),
    mkCase "ok/near-zero-high-z" 3 7 4 (#[intV 9, intV 8, intV 7, intV 6, intV 5]),
    mkCase "ok/randomized-edge" 8 14 13 (#[intV 1, intV 0, intV 9, intV (-1), .null, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9]),

    -- [B3] underflow coverage.
    mkCase "err/underflow-empty" 0 0 0 #[],
    mkCase "err/underflow-empty-x1" 1 0 0 #[],
    mkCase "err/underflow-depth1-needs-one" 1 0 0 (#[intV 9]),
    mkCase "err/underflow-depth1-needs-two" 2 1 0 (#[intV 9]),
    mkCase "err/underflow-depth2-needs-three" 3 1 0 (#[intV 9, intV 10]),
    mkCase "err/underflow-depth2-needs-fifteen" 15 0 0 (mkIntStack 14),
    mkCase "err/underflow-deep-mix" 14 15 7 (#[intV 1, intV 2, intV 3, intV 4]),
    mkCase "err/underflow-mixed" 7 7 7 (#[.null, .cell refCell]),

    -- [B9] gas boundary behavior.
    mkCase "gas/exact-cost-succeeds"
      0 0 0
      (#[intV 33])
      (oracleGasLimitsExact xcpu2SetGasExact)
      1_000_000,
    mkCase "gas/exact-minus-one-fails"
      0 0 0
      (#[intV 32])
      (oracleGasLimitsExactMinusOne xcpu2SetGasExact)
      1_000_000
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xcpu2Id
      count := 500
      gen := genXcpu2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCPU2
