import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.BLKDROP

/-
INSTRUCTION: BLKDROP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch match:
   - `execInstrFlowBlkdrop` handles only `.blkdrop n`; all other instructions go to `next`.

2. [B2] Runtime success path:
   - `n ≤ stack.size`.
   - Result is `stack.take (stack.size - n)`.

3. [B3] Runtime boundary (`n = 0`):
   - Keeps the same stack unchanged.

4. [B4] Runtime boundary (`n = stack.size`):
   - Empties the stack completely.

5. [B5] Runtime underflow path:
   - `n > stack.size` → `.stkUnd`.

6. [B6] Assembler in-range:
   - `n < 16` assembles as opcode `0x5f00 + n`.

7. [B7] Assembler out-of-range:
   - `n ≥ 16` is `.rangeChk`.

8. [B8] Decoder fixed opcode branch:
   - `w16 &&& 0xfff0 = 0x5f00` decodes as `.blkdrop (w16 &&& 0xf)`.

9. [B9] Decoder adjacency:
   - `0x5f0f` is BLKDROP(15), while `0x5f10` and higher nibble values are BLKPUSH.

10. [B10] Decoder malformed/truncated branch:
   - not enough bits (e.g., 8 or 15) decodes as `.invOpcode`.

11. [B11] Gas edge:
   - `instrGas` is fixed-width (`gasPerInstr + totBits`), no n-dependent penalty.
   - Exact-gas success and exact-minus-one failure are both exercised.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any category without VM-runtime branches would be called out here; none are missing.
-/

private def blkdropId : InstrId :=
  { name := "BLKDROP" }

private def blkdropInstr (n : Nat) : Instr :=
  .blkdrop n

private def mkCase
    (name : String)
    (n : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkdropId
    program := #[blkdropInstr n]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (code : Cell)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkdropId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCell (bits : Nat) (len : Nat := 16) : Cell :=
  Cell.mkOrdinary (natToBits bits len) #[]

private def runBlkdropDirect (n : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowBlkdrop (blkdropInstr n) stack

private def typePalette : Array Value :=
  #[.null, intV 7, .cell Cell.empty, intV (-7), .tuple #[], .null]

private def mkTypeStack (size : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:size] do
    out := out.push (typePalette[i % typePalette.size]!)
  return out

private def mkIntAlternatingStack (size : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:size] do
    let n : Int := Int.ofNat (i + 1)
    out := out.push (if i % 2 = 0 then intV n else intV (-n))
  return out

private def sampleFuzzValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 5
  (typePalette[idx % typePalette.size]!, rng1)

private def mkFuzzStack (size : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:size] do
    let (v, rng1) := sampleFuzzValue rng
    out := out.push v
    rng := rng1
  return (out, rng)

private def mkFuzzStackAtLeast (minSize : Nat) (bonusMax : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  let (bonus, rng1) := randNat rng0 0 bonusMax
  mkFuzzStack (minSize + bonus) rng1

private def expectDecodeBlkdrop (label : String) (bits : Nat) (expected : Nat) : IO Unit := do
  match decodeCp0WithBits (mkCodeCell bits |> Slice.ofCell) with
  | .ok (instr, used, rest) =>
      if instr != blkdropInstr expected then
        throw (IO.userError s!"{label}: expected .blkdrop {expected}, got {instr}")
      else if used != 16 then
        throw (IO.userError s!"{label}: expected used=16, got {used}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected decode stream to be exhausted")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")

private def expectDecodeInvOpcode (label : String) (cell : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {instr} ({bits} bits)")

private def expectAssembleBlkdrop (label : String) (n : Nat) : IO Unit := do
  let code ←
    match assembleCp0 [blkdropInstr n] with
    | .ok code => pure code
    | .error e => throw (IO.userError s!"{label}: assemble failed with {e}")
  let s0 := Slice.ofCell code
  let _ ← expectDecodeStep label s0 (blkdropInstr n) 16

private def expectAssembleBlkdropErr (label : String) (n : Nat) : IO Unit := do
  match assembleCp0 [blkdropInstr n] with
  | .ok code =>
      throw (IO.userError s!"{label}: expected range check failure, got code {reprStr code}")
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {e}")

private def exactGasBudget : Int :=
  computeExactGasBudget (blkdropInstr 0)

private def exactGasBudget15 : Int :=
  computeExactGasBudget (blkdropInstr 15)

private def exactGasBudgetMinusOne : Int :=
  computeExactGasBudgetMinusOne (blkdropInstr 0)

private def exactGasLimits : OracleGasLimits :=
  { gasLimit := exactGasBudget
    gasMax := exactGasBudget
    gasCredit := 0 }

private def exactGasLimits15 : OracleGasLimits :=
  { gasLimit := exactGasBudget15
    gasMax := exactGasBudget15
    gasCredit := 0 }

private def exactMinusOneLimits : OracleGasLimits :=
  { gasLimit := exactGasBudgetMinusOne
    gasMax := exactGasBudgetMinusOne
    gasCredit := 0 }

private def genBlkdropFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  match shape with
  | 0 =>
      let (stack, rng2) := mkFuzzStack 0 rng1
      ({ name := "fuzz/shape-0" , instr := blkdropId, program := #[(.blkdrop 0)], initStack := stack }, rng2)
  | 1 =>
      let (stack, rng2) := mkFuzzStackAtLeast 1 4 rng1
      ({ name := "fuzz/shape-1", instr := blkdropId, program := #[(.blkdrop 1)], initStack := stack }, rng2)
  | 2 =>
      let (stack, rng2) := mkFuzzStackAtLeast 2 5 rng1
      ({ name := "fuzz/shape-2", instr := blkdropId, program := #[(.blkdrop 2)], initStack := stack }, rng2)
  | 3 =>
      let (stack, rng2) := mkFuzzStackAtLeast 3 5 rng1
      ({ name := "fuzz/shape-3", instr := blkdropId, program := #[(.blkdrop 3)], initStack := stack }, rng2)
  | 4 =>
      let (stack, rng2) := mkFuzzStackAtLeast 7 4 rng1
      ({ name := "fuzz/shape-4", instr := blkdropId, program := #[(.blkdrop 7)], initStack := stack }, rng2)
  | 5 =>
      let (stack, rng2) := mkFuzzStackAtLeast 8 3 rng1
      ({ name := "fuzz/shape-5", instr := blkdropId, program := #[(.blkdrop 8)], initStack := stack }, rng2)
  | 6 =>
      let (stack, rng2) := mkFuzzStackAtLeast 14 1 rng1
      ({ name := "fuzz/shape-6", instr := blkdropId, program := #[(.blkdrop 14)], initStack := stack }, rng2)
  | 7 =>
      let (stack, rng2) := mkFuzzStackAtLeast 15 0 rng1
      ({ name := "fuzz/shape-7", instr := blkdropId, program := #[(.blkdrop 15)], initStack := stack }, rng2)
  | 8 =>
      let (size, rng2) := randNat rng1 0 4
      let underSize := if size = 0 then 0 else size
      let (stack, rng3) := mkFuzzStack underSize rng2
      ({ name := "fuzz/shape-8", instr := blkdropId, program := #[(.blkdrop 1)], initStack := stack }, rng3)
  | 9 =>
      let (size, rng2) := randNat rng1 0 3
      let (stack, rng3) := mkFuzzStack size rng2
      ({ name := "fuzz/shape-9", instr := blkdropId, program := #[(.blkdrop 3)], initStack := stack }, rng3)
  | 10 =>
      let code := mkCodeCell (0x5f0f) 16
      ({ name := "fuzz/shape-10/raw-blkdrop-boundary", instr := blkdropId, codeCell? := some code, initStack := mkTypeStack 3 }, rng1)
  | _ =>
      let code := mkCodeCell 0x5f10 16
      ({ name := "fuzz/shape-11/raw-blkpush-alias", instr := blkdropId, codeCell? := some code, initStack := mkTypeStack 2 }, rng1)

def suite : InstrSuite where
  id := blkdropId
  unit := #[
    { name := "unit/flow/dispatch-branch"
      run := do
        let ok := runHandlerDirectWithNext execInstrFlowBlkdrop (.blkdrop 1) (VM.push (intV 777)) #[intV 1, intV 2]
        expectOkStack "dispatch-branch" ok #[intV 1]
        let ok2 := runHandlerDirectWithNext execInstrFlowBlkdrop (.add) (VM.push (intV 42)) #[intV 9]
        expectOkStack "fallback-branch" ok2 #[intV 9, intV 42] },
    { name := "unit/asm/min"
      run := do
        expectAssembleBlkdrop "asm/min" 0 },
    { name := "unit/asm/max"
      run := do
        expectAssembleBlkdrop "asm/max" 15 },
    { name := "unit/asm/out-of-range-16"
      run := do
        expectAssembleBlkdropErr "asm/16" 16 },
    { name := "unit/asm/out-of-range-17"
      run := do
        expectAssembleBlkdropErr "asm/17" 17 },
    { name := "unit/decode/roundtrip-0"
      run := do
        expectDecodeBlkdrop "decode/0" 0x5f00 0 },
    { name := "unit/decode/roundtrip-15"
      run := do
        expectDecodeBlkdrop "decode/15" 0x5f0f 15 },
    { name := "unit/decode/alias-low"
      run := do
        match decodeCp0WithBits (mkCodeCell 0x5f10 |> Slice.ofCell) with
        | .ok (instr, bits, rest) =>
            if instr != .blkPush 1 0 then
              throw (IO.userError s!"decode/alias-low: expected BLKPUSH 1,0 got {instr}")
            else if bits != 16 then
              throw (IO.userError s!"decode/alias-low: expected bits=16 got {bits}")
            else if rest.bitsRemaining + rest.refsRemaining != 0 then
              throw (IO.userError s!"decode/alias-low: expected no remaining bits")
        | .error e =>
            throw (IO.userError s!"decode/alias-low: expected decode success, got {e}") },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeInvOpcode "decode/truncated-8" (mkCodeCell 0x5f 8) },
    { name := "unit/decode/truncated-15"
      run := do
        expectDecodeInvOpcode "decode/truncated-15" (mkCodeCell 0x5f00 15) },
    { name := "unit/gas/fixed-across-n"
      run := do
        if exactGasBudget != exactGasBudget15 then
          throw (IO.userError s!"gas mismatch: n=0={exactGasBudget}, n=15={exactGasBudget15}") }
  ]
  oracle := #[
    -- [B2][B3] n=0 runtime success and preserve stack.
    mkCase "runtime/ok/n0-empty" 0 #[],
    mkCase "runtime/ok/n0-preserve-typey" 0 (mkTypeStack 4),
    mkCase "runtime/ok/n0-top-preserved" 0 (mkTypeStack 7),
    -- [B2] n=1 boundary and mixed stacks.
    mkCase "runtime/ok/n1-size1" 1 (#[intV 9]),
    mkCase "runtime/ok/n1-top" 1 (mkTypeStack 3),
    mkCase "runtime/ok/n1-middle" 1 (#[intV 11, intV 12, intV 13, intV 14]),
    -- [B2] n=2 success cases.
    mkCase "runtime/ok/n2" 2 (mkIntAlternatingStack 4),
    mkCase "runtime/ok/n2-type-mix" 2 (#[.null, intV 1, .cell Cell.empty]),
    mkCase "runtime/ok/n2-clear" 2 (mkIntAlternatingStack 2),
    -- [B2] n=3 and n=4 cases.
    mkCase "runtime/ok/n3" 3 (mkTypeStack 6),
    mkCase "runtime/ok/n3-preserve" 3 (mkIntAlternatingStack 6),
    mkCase "runtime/ok/n4" 4 (mkIntAlternatingStack 8),
    mkCase "runtime/ok/n4-preserve-mixed" 4 (mkTypeStack 7),
    -- [B2] n=7 and n=8.
    mkCase "runtime/ok/n7-edge" 7 (mkTypeStack 10),
    mkCase "runtime/ok/n7-full" 7 (mkIntAlternatingStack 7),
    mkCase "runtime/ok/n8" 8 (mkTypeStack 12),
    mkCase "runtime/ok/n8-preserve" 8 (mkIntAlternatingStack 10),
    -- [B2][B4] exact-frame n=14/15 cases.
    mkCase "runtime/ok/n14-full" 14 (mkIntAlternatingStack 14),
    mkCase "runtime/ok/n14-drop" 14 (mkTypeStack 18),
    mkCase "runtime/ok/n15-empty" 15 (mkTypeStack 15),
    mkCase "runtime/ok/n15-partial" 15 (mkTypeStack 17),
    mkCase "runtime/ok/n15-type-mix" 15 (mkTypeStack 16),
    -- [B5] runtime underflow.
    mkCase "runtime/err/underflow/n1-empty" 1 #[],
    mkCase "runtime/err/underflow/n2-one" 2 (mkTypeStack 1),
    mkCase "runtime/err/underflow/n3-two" 3 (mkTypeStack 2),
    mkCase "runtime/err/underflow/n4-three" 4 (mkTypeStack 3),
    mkCase "runtime/err/underflow/n7-six" 7 (mkTypeStack 6),
    mkCase "runtime/err/underflow/n8-seven" 8 (mkTypeStack 7),
    mkCase "runtime/err/underflow/n14-thirteen" 14 (mkTypeStack 13),
    mkCase "runtime/err/underflow/n15-zero" 15 #[],
    mkCase "runtime/err/underflow/n15-fourteen" 15 (mkTypeStack 14),
    -- [B8] decode boundary aliases.
    mkRawCase "decode/raw/0" (mkCodeCell 0x5f00 16) (mkTypeStack 2),
    mkRawCase "decode/raw/15" (mkCodeCell 0x5f0f 16) (mkIntAlternatingStack 15),
    -- [B9] decode aliasing with BLKPUSH.
    mkRawCase "decode/raw/alias-5f10" (mkCodeCell 0x5f10 16) (mkTypeStack 2),
    mkRawCase "decode/raw/alias-5f1f" (mkCodeCell 0x5f1f 16) (mkTypeStack 3),
    -- [B10] decode malformed/truncated.
    mkRawCase "decode/raw/truncated-8" (mkCodeCell 0x5f 8) (mkTypeStack 1),
    mkRawCase "decode/raw/truncated-15" (mkCodeCell 0x5f00 15) (mkTypeStack 1),
    -- [B11] gas edge cases.
    mkCase "gas/exact-success" 4 (mkTypeStack 12) exactGasLimits,
    mkCase "gas/exact-15-success" 15 (mkTypeStack 3) exactGasLimits15,
    mkCase "gas/exact-minus-one-fails" 3 (mkTypeStack 3) exactMinusOneLimits
  ]
  fuzz := #[
    { seed := 2026032801
      count := 500
      gen := genBlkdropFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.BLKDROP
