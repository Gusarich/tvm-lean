import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTADDB

/-
INSTRUCTION: DICTADDB

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1: Runtime success path] Slice-key insert miss:
   - Stack order in `execInstrDictDictSetB` is `[builder, key, dict, n]`.
   - `n` is validated via `popNatUpTo 1023`.
   - `key` is a slice; missing bits for width `n` gives `.cellUnd`.
   - `dictSetBuilderWithCells` returns `ok=true` on miss and pushes `newRoot, -1`.
   - `created > 0` may incur dynamic gas `cellCreateGasPrice * created`.

2. [B2: Runtime duplicate path] Slice-key add-hit:
   - Existing key at leaf returns `ok=false`, `newRoot` remains same root, stack pushes `root, 0`.

3. [B3: Runtime prefix-mismatch path] Non-empty dictionary with diverging key prefix:
   - `dictSetGenAuxWithCells` creates fork/new branch and returns `ok=true` (mutation path).

4. [B4: Runtime argument validation] Input domain errors:
   - `n < 0` and `n > 1023` -> `.rangeChk`.
   - if `key` has fewer than `n` bits -> `.cellUnd`.

5. [B5: Runtime stack/type and structural errors]:
   - Underflow before any pop: requires 4 stack values.
   - Dict must be maybe-cell, key must be slice, top value must be builder.
   - Malformed dictionary root can return `.dictErr` from `dictSetBuilderWithCells`.

6. [B6: Assembler encoding] Add-mode for `.dictSetB` is rejected.
   - `.dictSetB false false .add`, `.dictSetB true false .add`, `.dictSetB true true .add` must all encode as `.invOpcode`.

7. [B7: Decoder boundaries] `0xf451`, `0xf452`, `0xf453` decode to `.dictSetB` add variants with signedness bits.
   - Adjacent opcodes `0xf450` and `0xf454` are invalid.

8. [B8: Gas accounting] Base-cost branch is fixed;
   - insertion path may increase gas by variable `created * cellCreateGasPrice`.

TOTAL BRANCHES: 8
-/

private def dictADDBId : InstrId := { name := "DICTADDB" }
private def dictADDBInstr : Instr := .dictSetB false false .add

private def dictADDBCode : Cell := Cell.mkOrdinary (natToBits 0xf451 16) #[]
private def dictIADDBCode : Cell := Cell.mkOrdinary (natToBits 0xf452 16) #[]
private def dictUADDBCode : Cell := Cell.mkOrdinary (natToBits 0xf453 16) #[]
private def dictADDBLowerInvalid : Cell := Cell.mkOrdinary (natToBits 0xf450 16) #[]
private def dictADDBUpperInvalid : Cell := Cell.mkOrdinary (natToBits 0xf454 16) #[]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b01010 5) #[]

private def builderVal : Builder := Builder.empty.storeBits (natToBits 1 1)

private def mkDictCellFromBits (bits : BitString) : Cell :=
  match dictSetBuilderWithCells none bits builderVal .set with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) => Cell.empty
  | .error _ => Cell.empty

private def mkDictCellFromNat (n : Nat) (k : Nat) : Cell :=
  mkDictCellFromBits (natToBits k n)

private def mkADDBStack
    (n : Int)
    (key : Slice)
    (dict : Value := .null)
    (value : Builder := builderVal) : Array Value :=
  #[.builder value, .slice key, dict, intV n]

private def mkADDBStackBits
    (n : Int)
    (keyBits : BitString)
    (dict : Value := .null)
    (value : Builder := builderVal) : Array Value :=
  mkADDBStack n (mkSliceWithBitsRefs keyBits) dict value

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictADDBId
    codeCell? := some dictADDBCode
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
    instr := dictADDBId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictADDBDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSetB dictADDBInstr stack

private def expectAssembleErr (name : String) (expected : Excno) (code : Instr) : IO Unit := do
  match assembleCp0 [code] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{name}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{name}: expected assemble error {expected}, got success")

private def expectDecodeInvOpcode (name : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{name}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{name}: expected invOpcode, got {reprStr instr} ({bits} bits)")

private def expectDecode16 (name : String) (code : Cell) (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{name}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError "{name}: expected no trailing bits")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{name}: expected valid decode, got {e}")

private def dictADDBGasExact : Int := computeExactGasBudget dictADDBInstr
private def dictADDBGasExactMinusOne : Int := computeExactGasBudgetMinusOne dictADDBInstr
private def dictADDBGasInsert : Int := dictADDBGasExact + cellCreateGasPrice
private def dictADDBGasInsertMinusOne : Int :=
  if dictADDBGasInsert > 0 then dictADDBGasInsert - 1 else 0

private def pickNForFuzz (rng0 : StdGen) : Nat × StdGen :=
  let (raw, rng1) := randNat rng0 0 8
  let n : Nat :=
    match raw with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 5
    | 6 => 8
    | 7 => 16
    | _ => 32
  (n, rng1)

private def pickKeyNat (n : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if n = 0 then
    (0, rng0)
  else
    let maxV : Nat := (1 <<< n) - 1
    randNat rng0 0 maxV

private def pickDifferentNat (base : Nat) (n : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if n = 0 then
    (0, rng0)
  else
    let maxV : Nat := (1 <<< n) - 1
    let (candidate, rng1) := randNat rng0 0 maxV
    let next : Nat := if candidate = base then (if base = maxV then 0 else base + 1) else candidate
    (next, rng1)

private def pickUnderfullBits (n : Nat) (rng0 : StdGen) : BitString × StdGen :=
  if n = 0 then
    (#[], rng0)
  else
    let (len, rng1) := randNat rng0 0 (n - 1)
    randBitString len rng1

private def genDICTADDBFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  let (n, rng2) := pickNForFuzz rng1
  let (nI, rng3) := (Int.ofNat n, rng2)
  if shape = 0 then
    (mkCase "fuzz/err/underflow-empty" #[], rng1)
  else if shape = 1 then
    (mkCase "fuzz/err/underflow-one" #[intV 1], rng1)
  else if shape = 2 then
    (mkCase "fuzz/err/underflow-two" #[intV 1, .cell Cell.empty], rng1)
  else if shape = 3 then
    (mkCase "fuzz/err/underflow-three" #[.builder builderVal, intV 1, .cell Cell.empty], rng1)
  else if shape = 4 then
    (mkCase "fuzz/err/n-too-large" (mkADDBStack 1024 (mkSliceWithBitsRefs #[])), rng2)
  else if shape = 5 then
    (mkCase "fuzz/err/n-negative" (mkADDBStack (-1) (mkSliceWithBitsRefs #[])), rng2)
  else if shape = 6 then
    let (k, rng4) := pickKeyNat n rng3
    let d : Value := .cell (mkDictCellFromNat n k)
    (mkCase "fuzz/ok/existing-hit" (mkADDBStackBits nI (natToBits k n) d), rng4)
  else if shape = 7 then
    let (k, rng4) := pickKeyNat n rng3
    let (k2, rng5) := pickDifferentNat k n rng4
    let d : Value := .cell (mkDictCellFromNat n k)
    (mkCase "fuzz/ok/prefix-or-other-miss" (mkADDBStackBits nI (natToBits k2 n) d), rng5)
  else if shape = 8 then
    let (k, rng4) := pickKeyNat n rng3
    (mkCase "fuzz/ok/missing-null" (mkADDBStackBits nI (natToBits k n) .null), rng4)
  else if shape = 9 then
    let (bits, rng4) := pickUnderfullBits n rng3
    (mkCase "fuzz/err/key-underflow" (mkADDBStackBits nI bits .null), rng4)
  else if shape = 10 then
    (mkCase "fuzz/err/type-dict" (mkADDBStackBits 3 (natToBits 3 3) (.int (.num 7))), rng3)
  else if shape = 11 then
    (mkCase "fuzz/err/type-key" #[.builder builderVal, .int (.num 7), .cell (mkDictCellFromBits (natToBits 3 3)), intV 4], rng3)
  else if shape = 12 then
    (mkCase "fuzz/err/type-value" #[.int (.num 1), .slice (mkSliceWithBitsRefs (natToBits 3 3)), .cell (mkDictCellFromBits (natToBits 3 3)), intV 4], rng3)
  else
    (mkCase "fuzz/err/malformed-dict" (mkADDBStackBits 4 (natToBits 1 4) (.cell malformedDict)), rng3)

/-- DICTADDB specific suite. -/
def suite : InstrSuite where
  id := dictADDBId
  unit := #[
    { name := "unit/asm/add-mode-rejected"
      run := do
        expectAssembleErr "unit/asm/dictSetB-add" .invOpcode (.dictSetB false false .add)
        expectAssembleErr "unit/asm/dictSetB-iadd" .invOpcode (.dictSetB true false .add)
        expectAssembleErr "unit/asm/dictSetB-uadd" .invOpcode (.dictSetB true true .add)
        match assembleCp0 [(.dictSetB false false .set)] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"unit/asm/dictSetB-set-should-pass: got {e}")
    },
    { name := "unit/decode/triplet-and-adjacent"
      run := do
        expectDecode16 "unit/decode/0xf451" dictADDBCode (.dictSetB false false .add)
        expectDecode16 "unit/decode/0xf452" dictIADDBCode (.dictSetB true false .add)
        expectDecode16 "unit/decode/0xf453" dictUADDBCode (.dictSetB true true .add)
        expectDecodeInvOpcode "unit/decode/0xf450" dictADDBLowerInvalid
        expectDecodeInvOpcode "unit/decode/0xf454" dictADDBUpperInvalid
    },
    { name := "unit/exec/miss-vs-hit-and-errors"
      run := do
        let expectedMiss1 : Cell := mkDictCellFromBits (natToBits 1 1)
        expectOkStack "unit/exec/miss-n1"
          (runDictADDBDirect (mkADDBStackBits 1 (natToBits 1 1) .null))
          #[.cell expectedMiss1, intV (-1)]

        let rootBits : BitString := natToBits 3 4
        let root : Value := .cell (mkDictCellFromBits rootBits)
        expectOkStack "unit/exec/hit-unchanged"
          (runDictADDBDirect (mkADDBStackBits 4 rootBits root))
          #[root, intV 0]

        expectErr "unit/exec/key-underflow" (runDictADDBDirect (mkADDBStackBits 4 (natToBits 1 1) .null)) .cellUnd
        expectErr "unit/exec/type-key" (runDictADDBDirect (mkADDBStackBits 4 (natToBits 1 1) (.int (.num 7))) .typeChk
        expectErr "unit/exec/type-value" (runDictADDBDirect #[.int (.num 1), .slice (mkSliceWithBitsRefs (natToBits 1 1)), .cell (mkDictCellFromBits (natToBits 1 1)), intV 4]) .typeChk
        expectErr "unit/exec/dict-structural" (runDictADDBDirect (mkADDBStackBits 4 (natToBits 1 4) (.cell malformedDict))) .dictErr
    }
  ]
  oracle := #[
    -- [B1] Add miss on empty dictionary.
    mkCase "ok/miss/null-n0" (mkADDBStackBits 0 #[] .null),
    mkCase "ok/miss/null-n1" (mkADDBStackBits 1 (natToBits 1 1) .null),
    mkCase "ok/miss/null-n4" (mkADDBStackBits 4 (natToBits 11 4) .null),
    mkCase "ok/miss/null-n8" (mkADDBStackBits 8 (natToBits 127 8) .null),

    -- [B1,B3] Add miss with prefix mismatch in non-empty dictionary.
    mkCase "ok/miss/prefix-mismatch-n1" (mkADDBStackBits 1 (natToBits 0 1) (.cell (mkDictCellFromBits (natToBits 1 1))),
    mkCase "ok/miss/prefix-mismatch-n4" (mkADDBStackBits 4 (natToBits 0 4) (.cell (mkDictCellFromBits (natToBits 15 4))),
    mkCase "ok/miss/prefix-mismatch-n8" (mkADDBStackBits 8 (natToBits 0 8) (.cell (mkDictCellFromBits (natToBits 255 8))),

    -- [B2] Add hit (unchanged root).
    mkCase "ok/hit-root-n1" (mkADDBStackBits 1 (natToBits 1 1) (.cell (mkDictCellFromBits (natToBits 1 1))),
    mkCase "ok/hit-root-n4" (mkADDBStackBits 4 (natToBits 3 4) (.cell (mkDictCellFromBits (natToBits 3 4))),
    mkCase "ok/hit-root-n4-max" (mkADDBStackBits 4 (natToBits 15 4) (.cell (mkDictCellFromBits (natToBits 15 4))),

    -- [B4] Input validation: n range.
    mkCase "err/range-n-high" (mkADDBStack 1024 (mkSliceWithBitsRefs #[])),
    mkCase "err/range-n-negative" (mkADDBStack (-1) (mkSliceWithBitsRefs #[])),

    -- [B4] Key-slice size underflow.
    mkCase "err/key-underflow-n4" (mkADDBStackBits 4 (natToBits 1 1) .null),
    mkCase "err/key-underflow-n8" (mkADDBStackBits 8 (natToBits 1 4) .null),

    -- [B5] Stack/type/shape checks.
    mkCase "err/underflow-empty" #[],
    mkCase "err/underflow-one" #[intV 1],
    mkCase "err/underflow-two" #[intV 1, .cell Cell.empty],
    mkCase "err/underflow-three" #[.builder builderVal, intV 1, .cell Cell.empty],
    mkCase "err/type-dict" (mkADDBStackBits 4 (natToBits 7 4) (.int (.num 5))),
    mkCase "err/type-key" #[.builder builderVal, .int (.num 7), .cell (mkDictCellFromBits (natToBits 7 4)), intV 4],
    mkCase "err/type-value" #[.int (.num 1), .slice (mkSliceWithBitsRefs (natToBits 7 4)), .cell (mkDictCellFromBits (natToBits 7 4)), intV 4],
    mkCase "err/malformed-dict" (mkADDBStackBits 4 (natToBits 1 4) (.cell malformedDict)),

    -- [B7] Decoder/encode opcode space checks via raw cells.
    mkCaseCode "decode/adb" (mkADDBStack 4 (mkSliceWithBitsRefs #[])) dictADDBCode,
    mkCaseCode "decode/iadb" (mkADDBStack 4 (mkSliceWithBitsRefs #[]) (dict := .cell (mkDictCellFromBits #[]))) dictIADDBCode,
    mkCaseCode "decode/uadb" (mkADDBStack 4 (mkSliceWithBitsRefs #[]) (dict := .cell (mkDictCellFromBits #[]))) dictUADDBCode,
    mkCaseCode "decode/invalid-lower" #[] dictADDBLowerInvalid,
    mkCaseCode "decode/invalid-upper" #[] dictADDBUpperInvalid,

    -- [B8] Exact-budget probes.
    mkCase "gas/exact-hit" (mkADDBStackBits 4 (natToBits 3 4) (.cell (mkDictCellFromBits (natToBits 3 4))))
      (oracleGasLimitsExact dictADDBGasExact),
    mkCase "gas/exact-hit-minus-one" (mkADDBStackBits 4 (natToBits 3 4) (.cell (mkDictCellFromBits (natToBits 3 4))))
      (oracleGasLimitsExactMinusOne dictADDBGasExactMinusOne),
    mkCase "gas/exact-insert" (mkADDBStackBits 8 (natToBits 1 8) .null) (oracleGasLimitsExact dictADDBGasInsert),
    mkCase "gas/exact-insert-minus-one" (mkADDBStackBits 8 (natToBits 1 8) .null) (oracleGasLimitsExactMinusOne dictADDBGasInsertMinusOne),

    -- Additional high-width noise cases.
    mkCase "ok/noise/n16-hit" (mkADDBStackBits 16 (natToBits 65535 16) (.cell (mkDictCellFromBits (natToBits 65535 16))),
    mkCase "ok/noise/n16-miss" (mkADDBStackBits 16 (natToBits 32767 16) .null),
    mkCase "ok/noise/n32-hit" (mkADDBStackBits 32 (natToBits 1 32) (.cell (mkDictCellFromBits (natToBits 1 32))),
    mkCase "ok/noise/n32-miss" (mkADDBStackBits 32 (natToBits 2 32) .null)
  ]
  fuzz := #[
    { seed := 2026021301
      count := 500
      gen := genDICTADDBFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTADDB
