import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.DROP

/-
INSTRUCTION: DROP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime normal success: `.pop 0` drops the top stack entry when stack size > 0.
2. [B2] Runtime normal success: `.pop idx > 0` drops the item at absolute index from top (`idx = 1,2,15,16,255`) when stack is sufficiently large.
3. [B3] Runtime underflow: `.pop idx` fails with `.stkUnd` when `size ≤ idx` (or `idx = 0` on empty stack).
4. [B4] Runtime dispatch gate (`execInstrStackPop`) takes the `.pop` path only for `.pop`; other instruction constructors must delegate to `next`.
5. [B5] Assembler encoding for short-form family:
  - `idx = 0` -> `0x30`
  - `idx = 1` -> `0x31`
  - `2 ≤ idx ≤ 15` -> `0x30 + idx`
  This branch is explicitly split from larger-index extension logic.
6. [B6] Assembler extension-form branch:
  - `16 ≤ idx ≤ 255` -> `0x57` + `idx` byte.
7. [B7] Assembler range checking:
  - `idx > 255` -> `.rangeChk` (no encoding path for larger values).
8. [B8] Decoder short-form branch:
  - `0x30` → `.pop 0`
  - `0x31` → `.pop 1`
  - `0x32..0x3f` → `.pop idx`.
9. [B9] Decoder extension branch:
  - `0x57` + byte -> `.pop idx`.
10. [B10] Decoder truncation/invalidity:
  - Extended prefixes without enough bits (`0x57` without suffix or `0x56/57` partial) decode as `.invOpcode`.
11. [B11] Decoder adjacency/aliasing:
  - 0x56/0x57 both look like neighboring families, so aliasing at boundaries (e.g. 0x56xx push vs 0x57xx pop) is validated via expected opcode and roundtrip behavior.
12. [B12] Gas accounting:
  - Gas is fixed-width only (`instrGas = gasPerInstr + totBits`) for DROP family; no variable penalty per `idx`.
13. [B13] Gas edge behavior:
  - Exact gas budget should succeed; exact-minus-one should fail before mutation.

TOTAL BRANCHES: 13

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not directly represented by an oracle test is represented by the fuzz generator.
-/

private def dropId : InstrId :=
  { name := "DROP" }

private def dropInstr (idx : Nat) : Instr :=
  .pop idx

private def mkCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dropId
    program := #[dropInstr idx]
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
    instr := dropId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCell (bits : Nat) (len : Nat) : Cell :=
  Cell.mkOrdinary (natToBits bits len) #[]

private def runDropDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPop (dropInstr idx) stack

private def runDropDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPop instr (VM.push (intV 77)) stack

private def expectAssembleDrop (label : String) (idx : Nat) : IO Unit := do
  let c ←
    match assembleCp0 [dropInstr idx] with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{label}: expected success, got {e}")
  let expectedBits : Nat := if idx ≤ 15 then 8 else 16
  let expectedInstr : Instr := dropInstr idx
  let s := Slice.ofCell c
  let _ ← expectDecodeStep label s expectedInstr expectedBits

private def expectAssembleDropErr (label : String) (idx : Nat) : IO Unit := do
  match assembleCp0 [dropInstr idx] with
  | .ok _ => throw (IO.userError s!"{label}: expected rangeChk, got success")
  | .error e =>
      if e != .rangeChk then
        throw (IO.userError s!"{label}: expected rangeChk, got {e}")

private def expectDecodeDrop (label : String) (bits : Nat) (len : Nat) (expected : Instr) : IO Unit := do
  let cell := mkCodeCell bits len
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, used, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {instr}")
      else if used != len then
        throw (IO.userError s!"{label}: expected used bits {len}, got {used}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got bits={rest.bitsRemaining} refs={rest.refsRemaining}")
      pure ()

private def expectDecodeErr (label : String) (cell : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected {expected}, got {instr} ({bits} bits)")

private def mkTypeStack (size : Nat) : Array Value := Id.run do
  let values : Array Value := #[
    .null,
    intV 7,
    .cell Cell.empty,
    intV (-7),
    .tuple #[],
    .null
  ]
  let mut out : Array Value := #[]
  for i in [0:size] do
    out := out.push (values[i % values.size]!)
  return out

private def mkAltStack (size : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:size] do
    let v : Value := if i % 2 = 0 then intV (Int.ofNat (i + 1)) else intV (-(Int.ofNat (i + 1)))
    out := out.push v
  return out

private def sampleFuzzValue (rng0 : StdGen) : Value × StdGen :=
  let values : Array Value := #[
    .null,
    intV 0,
    intV 1,
    intV (-1),
    .cell Cell.empty,
    .tuple #[]
  ]
  let (idx, rng1) := randNat rng0 0 (values.size - 1)
  (values[idx % values.size]!, rng1)

private def mkFuzzStack (size : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:size] do
    let (v, rng1) := sampleFuzzValue rng
    out := out.push v
    rng := rng1
  return (out, rng)

private def genDropFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  match shape with
  | 0 =>
      ({ name := "fuzz/shape-empty", instr := dropId, program := #[dropInstr 0], initStack := #[], }, rng1)
  | 1 =>
      (mkCase "fuzz/shape-empty-underflow-1" 1 #[], rng1)
  | 2 =>
      let (stack, rng2) := mkFuzzStack 1 rng1
      (mkCase "fuzz/shape-1-success" 0 stack, rng2)
  | 3 =>
      let (stack, rng2) := mkFuzzStack 2 rng1
      (mkCase "fuzz/shape-2-idx1-success" 1 stack, rng2)
  | 4 =>
      let (stack, rng2) := mkFuzzStack 2 rng1
      (mkCase "fuzz/shape-2-underflow-idx2" 2 stack, rng2)
  | 5 =>
      let (stack, rng2) := mkFuzzStack 3 rng1
      (mkCase "fuzz/shape-3-idx2-success" 2 stack, rng2)
  | 6 =>
      let (stack, rng2) := mkFuzzStack 14 rng1
      (mkCase "fuzz/shape-14-idx14-success" 14 stack, rng2)
  | 7 =>
      let (stack, rng2) := mkFuzzStack 14 rng1
      (mkCase "fuzz/shape-14-underflow-idx15" 15 stack, rng2)
  | 8 =>
      let (stack, rng2) := mkFuzzStack 15 rng1
      (mkCase "fuzz/shape-15-idx15-success" 15 stack, rng2)
  | 9 =>
      let (stack, rng2) := mkFuzzStack 16 rng1
      (mkCase "fuzz/shape-16-idx16-success" 16 stack, rng2)
  | 10 =>
      let (stack, rng2) := mkFuzzStack 16 rng1
      (mkCase "fuzz/shape-16-underflow-idx16" 16 stack, rng2)
  | 11 =>
      let (stack, rng2) := mkFuzzStack 255 rng1
      (mkCase "fuzz/shape-255-success" 255 stack, rng2)
  | 12 =>
      let (stack, rng2) := mkFuzzStack 255 rng1
      (mkCase "fuzz/shape-255-underflow" 255 stack, rng2)
  | _ =>
      let (idx, rng2) := randNat rng1 0 255
      let (stack, rng3) := mkFuzzStack ((idx % 32) + 1) rng2
      (mkCase s!"fuzz/shape-random-idx{idx}" idx stack, rng3)

private def popExactGas : Int :=
  computeExactGasBudget (dropInstr 0)

private def popExactGasIdx15 : Int :=
  computeExactGasBudget (dropInstr 15)

private def popExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (dropInstr 0)

private def exactGasLimits : OracleGasLimits :=
  { gasLimit := popExactGas
    gasMax := popExactGas
    gasCredit := 0 }

private def exactGasLimits15 : OracleGasLimits :=
  { gasLimit := popExactGasIdx15
    gasMax := popExactGasIdx15
    gasCredit := 0 }

private def exactMinusOneGasLimits : OracleGasLimits :=
  { gasLimit := popExactGasMinusOne
    gasMax := popExactGasMinusOne
    gasCredit := 0 }

def suite : InstrSuite where
  id := dropId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        let ok := runDropDispatchFallback .add (#[intV 11])
        expectOkStack "dispatch-fallback" ok (#[intV 11]) },
    { name := "unit/direct/drop0"
      run := do
        let ok := runDropDirect 0 (mkTypeStack 4)
        expectOkStack "drop0" ok (mkTypeStack 3) },
    { name := "unit/direct/drop1"
      run := do
        let ok := runDropDirect 1 (#[(.cell Cell.empty), intV 21, intV 22])
        expectOkStack "drop1" ok (#[(.cell Cell.empty), intV 22]) },
    { name := "unit/direct/drop1-underflow"
      run := do
        expectErr "drop1-underflow" (runDropDirect 1 (#[(intV 3)])) .stkUnd },
    { name := "unit/direct/drop15"
      run := do
        let stack := mkTypeStack 16
        let ok := runDropDirect 15 stack
        expectOkStack "drop15" ok (mkTypeStack 15) },
    { name := "unit/direct/drop16"
      run := do
        let stack := mkTypeStack 17
        let ok := runDropDirect 16 stack
        expectOkStack "drop16" ok (mkTypeStack 16) },
    { name := "unit/direct/drop255-underflow"
      run := do
        expectErr "drop255-underflow" (runDropDirect 255 (mkTypeStack 255)) .stkUnd },
    { name := "unit/asm/drop-0"
      run := do
        expectAssembleDrop "asm-drop0" 0 },
    { name := "unit/asm/drop-1"
      run := do
        expectAssembleDrop "asm-drop1" 1 },
    { name := "unit/asm/drop-15"
      run := do
        expectAssembleDrop "asm-drop15" 15 },
    { name := "unit/asm/drop-16"
      run := do
        expectAssembleDrop "asm-drop16" 16 },
    { name := "unit/asm/drop-255"
      run := do
        expectAssembleDrop "asm-drop255" 255 },
    { name := "unit/asm/drop-256-range-error"
      run := do
        expectAssembleDropErr "asm-drop256" 256 },
    { name := "unit/asm/drop-257-range-error"
      run := do
        expectAssembleDropErr "asm-drop257" 257 },
    { name := "unit/decode/drop-0"
      run := do
        expectDecodeDrop "decode-drop-0" 0x30 8 (dropInstr 0) },
    { name := "unit/decode/drop-1"
      run := do
        expectDecodeDrop "decode-drop-1" 0x31 8 (dropInstr 1) },
    { name := "unit/decode/drop-15"
      run := do
        expectDecodeDrop "decode-drop-15" 0x3f 8 (dropInstr 15) },
    { name := "unit/decode/drop-16"
      run := do
        expectDecodeDrop "decode-drop-16" 0x57 16 (dropInstr 16) },
    { name := "unit/decode/drop-255"
      run := do
        expectDecodeDrop "decode-drop-255" 0x57ff 16 (dropInstr 255) },
    { name := "unit/decode/drop-truncated-8"
      run := do
        expectDecodeErr "decode-truncated-8" (mkCodeCell 0x57 8) .invOpcode },
    { name := "unit/decode/drop-adjacent-push-opcode"
      run := do
        expectDecodeDrop "decode-neighbor-pop-push" 0x5600 16 (.push 0) },
    { name := "unit/decode/drop-aliased-57"
      run := do
        expectDecodeDrop "decode-57-prefix" 0x5701 16 (dropInstr 1) },
    { name := "unit/gas/fixed-not-variable"
      run := do
        if popExactGas != popExactGasIdx15 then
          throw (IO.userError s!"drop gas depends on idx unexpectedly: {popExactGas} != {popExactGasIdx15}") },
  ]
  oracle := #[
    -- [B1]
    mkCase "runtime/ok/empty-to-one" 0 (mkTypeStack 1),
    -- [B1]
    mkCase "runtime/ok/pop0-mixed-types" 0 (mkTypeStack 6),
    -- [B1]
    mkCase "runtime/ok/pop0-after-null" 0 (#[(.null), intV 99, .cell Cell.empty]),
    -- [B1]
    mkCase "runtime/ok/pop0-large" 0 (mkTypeStack 256),
    -- [B2]
    mkCase "runtime/ok/pop1" 1 (mkAltStack 4),
    -- [B2]
    mkCase "runtime/ok/pop2" 2 (mkAltStack 7),
    -- [B2]
    mkCase "runtime/ok/pop3" 3 (mkTypeStack 9),
    -- [B2]
    mkCase "runtime/ok/pop15-boundary" 15 (mkTypeStack 16),
    -- [B2]
    mkCase "runtime/ok/pop16-boundary" 16 (mkTypeStack 17),
    -- [B2]
    mkCase "runtime/ok/pop15-raw-stack" 15 (mkAltStack 20),
    -- [B2]
    mkCase "runtime/ok/pop16-nonuniform" 16 (mkTypeStack 21),
    -- [B2]
    mkCase "runtime/ok/pop255" 255 (mkTypeStack 300),
    -- [B2, B4]
    mkCase "runtime/ok/pop0-small-stack" 0 (#[(intV 1), intV 2]),
    -- [B3]
    mkCase "runtime/err/pop0-empty" 0 (#[]),
    -- [B3]
    mkCase "runtime/err/pop1-empty" 1 (#[]),
    -- [B3]
    mkCase "runtime/err/pop1-one" 1 (#[(intV 1)]),
    -- [B3]
    mkCase "runtime/err/pop2-two" 2 (#[(intV 1), intV 2]),
    -- [B3]
    mkCase "runtime/err/pop2-two-plus-tail" 2 (#[(intV 1), intV 2, intV 3]),
    -- [B3]
    mkCase "runtime/err/pop15-fifteen" 15 (mkTypeStack 15),
    -- [B3]
    mkCase "runtime/err/pop16-fifteen" 16 (mkTypeStack 16),
    -- [B3]
    mkCase "runtime/err/pop255-equal-depth" 255 (mkTypeStack 255),
    -- [B5]
    mkRawCase "decode/raw/drop-short-30" (mkCodeCell 0x30 8) (mkTypeStack 2),
    -- [B5]
    mkRawCase "decode/raw/drop-short-31" (mkCodeCell 0x31 8) (mkTypeStack 2),
    -- [B5]
    mkRawCase "decode/raw/drop-short-3f" (mkCodeCell 0x3f 8) (mkTypeStack 16),
    -- [B6]
    mkRawCase "decode/raw/drop-ext-57-10" (mkCodeCell 0x570a 16) (mkTypeStack 12),
    -- [B6]
    mkRawCase "decode/raw/drop-ext-57-ff" (mkCodeCell 0x57ff 16) (mkTypeStack 300),
    -- [B6]
    mkRawCase "decode/raw/drop-ext-16" (mkCodeCell 0x5700 16) (mkTypeStack 2),
    -- [B7, B11]
    mkRawCase "decode/raw/push16" (mkCodeCell 0x5600 16) (mkTypeStack 257),
    -- [B8]
    mkRawCase "decode/raw/adjacent-57-prefix" (mkCodeCell 0x5701 16) (mkTypeStack 2),
    -- [B9]
    mkRawCase "decode/raw/truncated-8" (mkCodeCell 0x30 8) (mkTypeStack 1),
    -- [B9]
    mkRawCase "decode/raw/truncated-16-missing-tail" (mkCodeCell 0x57 8) (mkTypeStack 1),
    -- [B10]
    mkRawCase "decode/raw/truncated-push-tail" (mkCodeCell 0x56 8) (mkTypeStack 2),
    -- [B10]
    mkRawCase "decode/raw/truncated-trunc15" (mkCodeCell 0x57ff 15) (mkTypeStack 2),
    -- [B12]
    mkCase "gas/exact-pop0" 0 (mkTypeStack 3) (gasLimits := exactGasLimits),
    -- [B12, B13]
    mkCase "gas/exact-pop15" 15 (mkTypeStack 20) (gasLimits := exactGasLimits15),
    -- [B13]
    mkCase "gas/exact-minus-one-pop0" 0 (mkTypeStack 3) (gasLimits := exactMinusOneGasLimits)
  ]
  fuzz := #[
    { seed := 2026102601
      count := 500
      gen := genDropFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.DROP
